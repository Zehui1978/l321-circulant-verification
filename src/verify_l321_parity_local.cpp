// Independent finite-local proof for span-13 L(3,2,1) words on Z with steps 1,5.
// C++17, standard library only. Example: g++ -std=c++17 -O2 this_file.cpp -o verify
// Run: ./verify. The program takes no arguments, writes no data files, and
// reports the graph counts, pruning snapshots, parity checks, and the explicit
// length-32 witness used in Lemma 3.4(iii)--(iv).
//
// Each state is a legal word of length 15 over {0,...,13}. An edge shifts the
// word left and appends one legal symbol. ALL starting symbols are enumerated.
// S_0 is the full state set. Simultaneously delete all zero-in/zero-out-degree
// vertices of the induced graph to obtain S_{r+1} from S_r.
//
// Any directed closed walk survives every deletion round. After ten rounds,
// every remaining edge flips the parity of its last symbol. Hence every closed
// walk has even length; no odd-period legal word exists.
//
// A local interpretation needs no SCC argument: a legal word of length 36
// gives a path of 22 state vertices. Its central edge, vertices 10 -> 11,
// survives ten rounds, so its symbols a[24],a[25] have opposite parity.
// More strongly, after nine rounds all surviving states have opposite parity
// at internal positions 7,8. A legal word a[0],...,a[32] of length 33 gives a
// path of 19 state vertices; vertex 9 survives nine rounds. Thus a[16],a[17]
// have opposite parity. Induction proves this survival statement: at round r,
// all path vertices whose indices are at least r from both ends survive.
//
// These are computed finite lemmas, not a claimed non-computational proof.
// The ten-round edge criterion is sharp for this particular pruning procedure:
// four edges failing parity remain after round nine. This does not assert an
// optimal local-window length.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using Word = std::uint64_t;
constexpr int WIDTH = 15;
constexpr int SPAN = 13;
constexpr Word MASK = (Word(1) << (4 * WIDTH)) - 1;

void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error(message);
}

std::vector<std::pair<int,int>> distance_constraints() {
    std::map<int,int> distance{{0,0}};
    std::vector<int> frontier{0};
    for (int radius=1; radius<=3; ++radius) {
        std::vector<int> next;
        for (int x: frontier) for (int step: {-5,-1,1,5}) {
            int y=x+step;
            if (distance.emplace(y,radius).second) next.push_back(y);
        }
        frontier=std::move(next);
    }
    std::vector<std::pair<int,int>> result;
    for (auto [offset,radius]: distance)
        if (offset>0) result.emplace_back(offset,4-radius);
    const std::vector<std::pair<int,int>> expected{
        {1,3},{2,2},{3,1},{4,2},{5,3},{6,2},{7,1},{9,1},{10,2},{11,1},{15,1}
    };
    require(result==expected,"incorrect distance constraints");
    return result;
}

int symbol(Word word, int index) { // chronological positions 0,...,14
    return int((word >> (4*(WIDTH-1-index))) & 15);
}

bool can_append(Word word, int length, int value,
                const std::vector<std::pair<int,int>>& constraints) {
    for (auto [offset,gap]: constraints) {
        if (offset<=length &&
            std::abs(value-int((word>>(4*(offset-1)))&15))<gap) return false;
    }
    return true;
}

void generate(Word word, int length, std::vector<Word>& states,
              const std::vector<std::pair<int,int>>& constraints) {
    if (length==WIDTH) { states.push_back(word); return; }
    for (int value=0; value<=SPAN; ++value)
        if (can_append(word,length,value,constraints))
            generate((word<<4)|Word(value),length+1,states,constraints);
}

int main() {
    try {
        const auto constraints=distance_constraints();
        std::vector<Word> states;
        generate(0,0,states,constraints);
        require(states.size()==110672,"unexpected full-state count");
        std::unordered_map<Word,int> id;
        id.reserve(states.size()*2);
        for (int i=0; i<int(states.size()); ++i)
            require(id.emplace(states[i],i).second,"duplicate generated state");
        std::vector<std::vector<int>> outgoing(states.size()),incoming(states.size());
        for (int i=0; i<int(states.size()); ++i) {
            for (int value=0; value<=SPAN; ++value) {
                if (!can_append(states[i],WIDTH,value,constraints)) continue;
                auto found=id.find(((states[i]<<4)|Word(value))&MASK);
                require(found!=id.end(),"successor missing from full state set");
                int j=found->second;
                outgoing[i].push_back(j);
                incoming[j].push_back(i);
            }
        }
        std::vector<int> indegree(states.size()),outdegree(states.size());
        std::vector<unsigned char> alive(states.size(),1);
        for (int i=0; i<int(states.size()); ++i) {
            indegree[i]=int(incoming[i].size());
            outdegree[i]=int(outgoing[i].size());
        }
        // Independent local check: exact one-sided extendibility. L[r][v]
        // means an r-edge path ends at v, and R[r][v] means one begins at v.
        // Paths meeting in a full length-15 state can be concatenated because
        // every constraint has offset at most 15.
        std::vector<std::vector<unsigned char>> left(11,
            std::vector<unsigned char>(states.size(),1)),right=left;
        for (int r=1; r<=10; ++r) for (int i=0; i<int(states.size()); ++i) {
            left[r][i]=right[r][i]=0;
            for (int j: incoming[i]) if (left[r-1][j]) {left[r][i]=1;break;}
            for (int j: outgoing[i]) if (right[r-1][j]) {right[r][i]=1;break;}
        }
        int witness=-1,bad32=0,bad33=0,bad34=0;
        for (int i=0; i<int(states.size()); ++i) {
            if ((symbol(states[i],7)+symbol(states[i],8))%2!=0) continue;
            if (left[8][i] && right[9][i]) {++bad32;witness=i;}
            if (left[9][i] && right[9][i]) ++bad33;
            if (left[9][i] && right[10][i]) ++bad34;
        }
        require(bad32==4 && bad33==0 && bad34==0,
                "independent extendibility check failed");
        // Produce and directly validate a length-32 central-pair counterexample.
        require(witness>=0,"length-32 witness missing");
        std::vector<int> path{witness};
        int current=witness;
        for (int r=8; r>0; --r) {
            auto found=std::find_if(incoming[current].begin(),incoming[current].end(),
                                   [&](int j){return left[r-1][j]!=0;});
            require(found!=incoming[current].end(),"left witness reconstruction failed");
            current=*found;path.push_back(current);
        }
        std::reverse(path.begin(),path.end());
        current=witness;
        for (int r=9; r>0; --r) {
            auto found=std::find_if(outgoing[current].begin(),outgoing[current].end(),
                                   [&](int j){return right[r-1][j]!=0;});
            require(found!=outgoing[current].end(),"right witness reconstruction failed");
            current=*found;path.push_back(current);
        }
        std::vector<int> example;
        for (int p=0; p<WIDTH; ++p) example.push_back(symbol(states[path[0]],p));
        for (std::size_t p=1; p<path.size(); ++p) example.push_back(symbol(states[path[p]],14));
        require(example.size()==32,"incorrect witness length");
        for (int i=0; i<int(example.size()); ++i) {
            require(example[i]>=0 && example[i]<=SPAN,"witness label out of range");
            for (auto [offset,gap]: constraints) if (i+offset<int(example.size()))
                require(std::abs(example[i]-example[i+offset])>=gap,"illegal witness");
        }
        require((example[15]+example[16])%2==0,"witness central pair is not same parity");
        std::cout<<"Independent extension DP: bad center-state counts for lengths 32,33,34 = "
                 <<bad32<<','<<bad33<<','<<bad34<<"\nLength-32 witness:";
        for (int value: example) std::cout<<' '<<value;
        std::cout<<"\nWitness center pair: "<<example[15]<<' '<<example[16]<<'\n';
        // Columns: surviving vertices, surviving edges, non-flipping edges.
        const std::array<std::array<int,3>,11> expected{{
            {{110672,111010,11206}}, {{64880,66566,4600}},
            {{42068,42270,1748}}, {{30052,30684,818}},
            {{23024,23716,330}}, {{18340,19184,176}},
            {{15540,16196,120}}, {{13560,14120,50}},
            {{12036,12630,10}}, {{10912,11470,4}}, {{9972,10546,0}}
        }};
        std::cout<<"round vertices edges non-flipping-edges\n";
        for (int round=0; round<=10; ++round) {
            if (round>0) {
                std::vector<int> removed;
                for (int i=0; i<int(states.size()); ++i)
                    if (alive[i] && (indegree[i]==0 || outdegree[i]==0))
                        removed.push_back(i);
                // Decide every deletion before updating any degree: synchronous.
                for (int i: removed) alive[i]=0;
                for (int i: removed) {
                    for (int j: outgoing[i]) if (alive[j]) --indegree[j];
                    for (int j: incoming[i]) if (alive[j]) --outdegree[j];
                }
            }
            int vertices=0,edges=0,bad=0;
            for (int i=0; i<int(states.size()); ++i) if (alive[i]) {
                ++vertices;
                for (int j: outgoing[i]) if (alive[j]) {
                    ++edges;
                    if (((states[i]^states[j])&1)==0) ++bad;
                }
                if (round==9)
                    require((symbol(states[i],7)+symbol(states[i],8))%2==1,
                            "length-33 local parity lemma failed");
                if (round==10) for (int p=0; p<14; ++p)
                    require((symbol(states[i],p)+symbol(states[i],p+1))%2==1,
                            "surviving state has a non-flipping adjacent pair");
            }
            require(std::array<int,3>{{vertices,edges,bad}}==expected[round],
                    "unexpected counts at round "+std::to_string(round));
            std::cout<<round<<' '<<vertices<<' '<<edges<<' '<<bad<<'\n';
        }
        std::cout<<"PASS: every legal length-33 word has opposite parities at positions 16,17 (zero-based).\n"
                 <<"PASS: after ten synchronous pruning rounds every surviving edge flips parity.\n"
                 <<"PASS: every closed walk has even length; every periodic legal word has even period.\n";
        return EXIT_SUCCESS;
    } catch (const std::exception& error) {
        std::cerr<<"FAIL: "<<error.what()<<'\n';
        return EXIT_FAILURE;
    }
}
