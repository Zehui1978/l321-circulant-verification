// C++17, standard library only. Complete t=4, span=15 template verifier.
// Build: g++ -std=c++17 -O2 -Wall -Wextra -pedantic verify_l321_templates.cpp -o verify_l321_templates
// Run: ./verify_l321_templates. The program takes no arguments and writes no
// data files. It prints the complete first-return words and checks the cyclic
// core, least-period spectrum, equal multiplicities, and counting recurrences
// used in Lemma 3.4(ii) and Section 5.
// The independent recurrent-core extraction uses source/sink deletion, not SCCs.
// Words printed below emit the FIRST label of each state, before each transition.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <map>
#include <limits>
#include <numeric>
#include <queue>
#include <set>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace std;
using State = uint64_t;
constexpr int width = 12;
constexpr State mask = (State(1) << (4 * width)) - 1;

void check(bool condition, const string& message) {
    if (!condition) throw runtime_error(message);
}

array<int, width + 1> separations() {
    array<int, width + 1> gap{};
    // A walk to a+4b has length at least |a|+|b|; enumerate all candidates.
    for (int a = -3; a <= 3; ++a) for (int b = -3; b <= 3; ++b) {
        const int length = abs(a) + abs(b), offset = abs(a + 4 * b);
        if (length > 0 && length <= 3 && offset > 0)
            gap[offset] = max(gap[offset], 4 - length);
    }
    check(gap == array<int, width + 1>{0,3,2,2,3,2,1,1,2,1,0,0,1}, "Gap table mismatch");
    return gap;
}

struct Automaton {
    array<int, width + 1> gap = separations();
    vector<State> state;
    unordered_map<State, int> number;
    vector<vector<int>> out, in;
    size_t edges = 0;

    bool appendable(State s, int length, int x) const {
        for (int j = 1; j <= min(length, width); ++j)
            if (abs(int((s >> (4 * (j - 1))) & 15) - x) < gap[j]) return false;
        return true;
    }

    Automaton() {
        function<void(State,int)> enumerate = [&](State s, int length) {
            if (length == width) {
                number.emplace(s, int(state.size()));
                state.push_back(s);
                return;
            }
            for (int x = 0; x < 16; ++x)
                if (appendable(s, length, x)) enumerate((s << 4) | State(x), length + 1);
        };
        enumerate(0, 0);
        check(state.size() == 39032, "Incomplete or unexpected state set");
        out.resize(state.size()); in.resize(state.size());
        for (int v = 0; v < int(state.size()); ++v) for (int x = 0; x < 16; ++x) {
            if (!appendable(state[v], width, x)) continue;
            const State target = ((state[v] << 4) | State(x)) & mask;
            const auto found = number.find(target);
            check(found != number.end(), "Generated transition has missing endpoint");
            const int w = found->second;
            out[v].push_back(w); in[w].push_back(v); ++edges;
        }
        check(edges == 24328, "Unexpected edge count");
    }

    int first(int v) const { return int(state[v] >> (4 * (width - 1))); }

    vector<char> trim() const {
        vector<int> indegree(state.size()), outdegree(state.size());
        vector<char> live(state.size(), true), queued(state.size(), false);
        queue<int> pending;
        auto enqueue = [&](int v) {
            if (live[v] && !queued[v] && (indegree[v] == 0 || outdegree[v] == 0)) {
                queued[v] = true; pending.push(v);
            }
        };
        for (int v = 0; v < int(state.size()); ++v) {
            indegree[v] = int(in[v].size()); outdegree[v] = int(out[v].size());
            enqueue(v);
        }
        while (!pending.empty()) {
            const int v = pending.front(); pending.pop();
            live[v] = false;
            for (int w : out[v]) if (live[w]) { --indegree[w]; enqueue(w); }
            for (int w : in[v]) if (live[w]) { --outdegree[w]; enqueue(w); }
        }
        return live;
    }
};

struct Template {
    vector<int> vertices, labels;
};
struct Component {
    vector<int> vertices;
    int start = -1;
    vector<Template> returns;
};

vector<int> canonical(vector<int> word, bool allow_reversal, bool allow_complement) {
    vector<int> best = word;
    for (int reverse_flag = 0; reverse_flag <= int(allow_reversal); ++reverse_flag)
        for (int complement_flag = 0; complement_flag <= int(allow_complement); ++complement_flag) {
            vector<int> candidate = word;
            if (reverse_flag) reverse(candidate.begin(), candidate.end());
            if (complement_flag) for (int& x : candidate) x = 15 - x;
            for (size_t shift = 0; shift < word.size(); ++shift) {
                best = min(best, candidate);
                rotate(candidate.begin(), candidate.begin() + 1, candidate.end());
            }
        }
    return best;
}

void print_word(const vector<int>& word) {
    for (size_t i = 0; i < word.size(); ++i) {
        if (i != 0) cout << ' ';
        cout << word[i];
    }
    cout << '\n';
}

int least_period(const vector<int>& word) {
    for (int length = 1; length <= int(word.size()); ++length) {
        if (word.size() % size_t(length) != 0) continue;
        bool period = true;
        for (int i = length; i < int(word.size()); ++i)
            if (word[i] != word[i % length]) { period = false; break; }
        if (period) return length;
    }
    throw runtime_error("No period found");
}

void verify_periodic(const Automaton& g, const vector<int>& word) {
    check(!word.empty(), "Empty periodic word");
    for (int i = 0; i < int(word.size()); ++i) for (int j = 1; j <= width; ++j)
        check(abs(word[i] - word[(i + j) % word.size()]) >= g.gap[j], "Periodic boundary violation");
}

State encode_window(const vector<int>& word, size_t start) {
    State state = 0;
    for (int j = 0; j < width; ++j)
        state = (state << 4) | State(word[(start + j) % word.size()]);
    return state;
}

uint64_t checked_add(uint64_t a, uint64_t b) {
    check(b <= numeric_limits<uint64_t>::max() - a, "Exact count overflow");
    return a + b;
}

uint64_t checked_multiply(uint64_t a, uint64_t b) {
    check(a == 0 || b <= numeric_limits<uint64_t>::max() / a, "Exact count overflow");
    return a * b;
}

int run() {
    const Automaton g;
    const vector<char> live = g.trim();
    vector<Component> components;
    vector<int> component(g.state.size(), -1);
    for (int start = 0; start < int(g.state.size()); ++start) if (live[start] && component[start] == -1) {
        const int c = int(components.size());
        components.emplace_back();
        vector<int> pending = {start}; component[start] = c;
        for (size_t i = 0; i < pending.size(); ++i) {
            const int v = pending[i]; components[c].vertices.push_back(v);
            for (const vector<int>* neighbours : {&g.out[v], &g.in[v]})
                for (int w : *neighbours) if (live[w] && component[w] == -1) {
                    component[w] = c; pending.push_back(w);
                }
        }
    }
    check(components.size() == 8, "Unexpected recurrent component count");
    set<pair<int,int>> all_core_edges, covered_edges;
    map<pair<int,int>,int> profile;
    size_t core_vertices = 0;
    for (auto& c : components) {
        core_vertices += c.vertices.size();
        vector<int> branches, joins;
        for (int v : c.vertices) {
            int degree_out = 0, degree_in = 0;
            for (int w : g.out[v]) if (live[w]) { ++degree_out; all_core_edges.emplace(v,w); }
            for (int w : g.in[v]) if (live[w]) ++degree_in;
            check(degree_out > 0 && degree_in > 0, "A source/sink survived pruning");
            check(degree_out <= 2 && degree_in <= 2, "Unexpected recurrent degree");
            if (degree_out == 2) branches.push_back(v);
            if (degree_in == 2) joins.push_back(v);
        }
        check(branches.size() == joins.size() && branches.size() <= 1, "Unexpected branch/join count");
        c.start = branches.empty() ? *min_element(c.vertices.begin(), c.vertices.end(),
            [&](int a, int b) { return g.state[a] < g.state[b]; }) : branches[0];
        set<int> covered_vertices;
        for (int first : g.out[c.start]) if (live[first]) {
            Template item;
            item.vertices.push_back(c.start); item.labels.push_back(g.first(c.start));
            covered_edges.emplace(c.start, first); covered_vertices.insert(c.start);
            int v = first;
            while (v != c.start) {
                check(item.vertices.size() <= c.vertices.size(), "A return path does not return");
                check(find(item.vertices.begin(), item.vertices.end(), v) == item.vertices.end(),
                      "A first-return path is not simple");
                item.vertices.push_back(v); item.labels.push_back(g.first(v)); covered_vertices.insert(v);
                int next = -1;
                for (int w : g.out[v]) if (live[w]) {
                    check(next == -1, "A second branch occurs on a return path"); next = w;
                }
                check(next >= 0, "Return path reaches a sink");
                covered_edges.emplace(v, next); v = next;
            }
            verify_periodic(g, item.labels);
            check(least_period(item.labels) == int(item.labels.size()), "A simple cycle word is imprimitive");
            array<int,16> multiplicity{};
            for (int x : item.labels) ++multiplicity[x];
            check(item.labels.size() % 16 == 0, "A return length is not divisible by 16");
            for (int count : multiplicity)
                check(count == int(item.labels.size()/16), "A return word has unbalanced label frequencies");
            for (size_t i = 0; i < item.labels.size(); ++i)
                check(encode_window(item.labels, i) == g.state[item.vertices[i]], "First-label emission mismatch");
            c.returns.push_back(item);
        }
        check(covered_vertices.size() == c.vertices.size(), "Templates do not cover component vertices");
        sort(c.returns.begin(), c.returns.end(), [](const Template& a, const Template& b) {
            return make_pair(a.labels.size(), a.labels) < make_pair(b.labels.size(), b.labels);
        });
        if (branches.empty()) check(c.returns.size() == 1, "A simple cycle has several returns");
        else check(c.vertices.size() == 151 && c.returns.size() == 2 &&
                   c.returns[0].labels.size() == 16 && c.returns[1].labels.size() == 144,
                   "Unexpected branched component profile");
        ++profile[{int(c.vertices.size()), int(c.returns.size())}];
        // Exhaust all pairs of templates: every splice is checked across the
        // complete range 12, and the recorded base state is recovered exactly.
        for (const auto& left : c.returns) for (const auto& right : c.returns) {
            vector<int> pair = left.labels;
            pair.insert(pair.end(), right.labels.begin(), right.labels.end());
            verify_periodic(g, pair);
            check(encode_window(pair, 0) == g.state[c.start] &&
                  encode_window(pair, left.labels.size()) == g.state[c.start], "Return splice lost its base state");
        }
    }
    check(profile == map<pair<int,int>,int>{{{16,1},4},{{32,1},2},{{151,2},2}}, "Unexpected component profile");
    check(core_vertices == 430 && all_core_edges.size() == 432, "Unexpected pruned core size");
    check(covered_edges == all_core_edges, "Templates do not cover every core edge");
    sort(components.begin(), components.end(), [&](const Component& a, const Component& b) {
        return make_pair(a.vertices.size(), g.state[a.start]) < make_pair(b.vertices.size(), g.state[b.start]);
    });
    cout << "PASS full automaton: " << g.state.size() << " states, " << g.edges << " edges\n";
    cout << "PASS source/sink pruning: 430 states, 432 edges, 8 components\n";
    cout << "PASS first-return templates cover every recurrent vertex and edge\n";
    cout << "PASS every return template uses all 16 labels equally often\n";
    cout << "Convention: emit the first label of each state before traversing an edge.\n";
    for (size_t i = 0; i < components.size(); ++i) {
        const auto& c = components[i];
        cout << "Component " << i + 1 << ": vertices=" << c.vertices.size() << " start=";
        vector<int> start_word;
        for (int j = width - 1; j >= 0; --j) start_word.push_back(int((g.state[c.start] >> (4*j)) & 15));
        print_word(start_word);
        for (size_t r = 0; r < c.returns.size(); ++r) {
            cout << "  " << char('A' + r) << " [length " << c.returns[r].labels.size() << "]: ";
            print_word(c.returns[r].labels);
        }
    }
    // Report symmetry orbits of isolated simple cycles, with cyclic rotation,
    // reversal of vertex order, and the label complement x -> 15-x permitted.
    map<vector<int>,int> orbit_sizes;
    for (const auto& c : components) if (c.returns.size() == 1)
        ++orbit_sizes[canonical(c.returns[0].labels, true, true)];
    cout << "Isolated-cycle symmetry orbits: " << orbit_sizes.size() << '\n';
    for (const auto& orbit : orbit_sizes) {
        cout << "  orbit size=" << orbit.second << " representative: "; print_word(orbit.first);
    }
    check(orbit_sizes.size() == 3, "Unexpected isolated-cycle symmetry orbit count");
    for (const auto& orbit : orbit_sizes) check(orbit.second == 2, "Unexpected symmetry orbit size");
    for (auto pair : {make_pair(0,3), make_pair(1,2), make_pair(4,5)}) {
        vector<int> reversed = components[pair.first].returns[0].labels;
        reverse(reversed.begin(), reversed.end());
        check(canonical(reversed, false, false) ==
              canonical(components[pair.second].returns[0].labels, false, false),
              "Claimed isolated-cycle reversal pair fails");
    }
    check(components[6].returns.size() == 2 && components[7].returns.size() == 2, "Branched component indexing");
    for (int r = 0; r < 2; ++r) {
        vector<int> complement = components[6].returns[r].labels;
        for (int& x : complement) x = 15 - x;
        check(complement == components[7].returns[r].labels, "Branched templates are not exact label complements");
    }
    // Match the exact mathematical words printed in the revised manuscript.
    // Enumerate the graph first; these constants are checks, never search seeds.
    const vector<int> published_U = {
        0,5,10,15,3,8,13,1,6,11,4,9,14,2,7,12
    };
    const vector<int> published_V = {
        0,7,14,5,12,3,10,1,8,15,6,13,4,11,2,9
    };
    const vector<int> published_W = {
        0,3,11,14,6,9,1,4,12,15,7,10,2,5,13,0,
        8,11,3,6,14,1,9,12,4,7,15,2,10,13,5,8
    };
    const vector<int> published_A = {
        6,11,4,9,2,14,7,0,12,5,10,3,15,8,1,13
    };
    const vector<int> published_B = {
        6,11,4,9,2,14,7,0,12,5,10,3,8,1,13,6,
        15,11,4,9,2,7,0,12,5,14,10,3,8,1,6,15,
        11,4,13,9,2,7,0,5,14,10,3,12,8,1,6,15,
        4,13,9,2,11,7,0,5,14,3,12,8,1,10,6,15,
        4,13,2,11,7,0,9,5,14,3,12,1,10,6,15,8,
        4,13,2,11,0,9,5,14,7,3,12,1,10,15,8,4,
        13,6,2,11,0,9,14,7,3,12,5,1,10,15,8,13,
        6,2,11,4,0,9,14,7,12,5,1,10,3,15,8,13,
        6,11,4,0,9,2,14,7,12,5,10,3,15,8,1,13
    };
    multiset<vector<int>> expected_isolated, actual_isolated;
    for (const auto& word : {published_U, published_V, published_W}) {
        expected_isolated.insert(canonical(word, false, false));
        vector<int> reversed = word;
        reverse(reversed.begin(), reversed.end());
        expected_isolated.insert(canonical(reversed, false, false));
    }
    for (const auto& c : components) if (c.returns.size() == 1)
        actual_isolated.insert(canonical(c.returns[0].labels, false, false));
    check(actual_isolated == expected_isolated, "Published isolated words differ from enumeration");
    check(components[6].returns[0].labels == published_A &&
          components[6].returns[1].labels == published_B,
          "Published branch words or their alignment differ from enumeration");
    cout << "PASS exact published words U,V,W,A,B and aligned branch state\n";
    cout << "PASS the two branched template pairs are exact label complements\n";
    // Exact rooted word counts are checked against adjacency-walk DP. Counts
    // are of maps Z/nZ -> {0,...,15}, not modulo rotations or complements.
    constexpr int max_length = 320;
    vector<uint64_t> trace(max_length + 1, 0);
    vector<int> core, core_index(g.state.size(), -1);
    for (int v = 0; v < int(g.state.size()); ++v) if (live[v]) {
        core_index[v] = int(core.size()); core.push_back(v);
    }
    vector<vector<int>> adjacency(core.size());
    for (size_t i = 0; i < core.size(); ++i)
        for (int w : g.out[core[i]]) if (live[w]) adjacency[i].push_back(core_index[w]);
    for (int start = 0; start < int(core.size()); ++start) {
        vector<uint64_t> current(core.size(), 0), next(core.size(), 0);
        current[start] = 1;
        for (int n = 1; n <= max_length; ++n) {
            fill(next.begin(), next.end(), 0);
            for (size_t v = 0; v < core.size(); ++v)
                for (int w : adjacency[v]) next[w] = checked_add(next[w], current[v]);
            current.swap(next); trace[n] = checked_add(trace[n], current[start]);
        }
    }
    // H(x)=1/(1-x-x^9), so h_m=h_{m-1}+h_{m-9}.
    vector<uint64_t> h(max_length / 16 + 1, 0);
    h[0] = 1;
    for (int m = 1; m < int(h.size()); ++m) h[m] = checked_add(h[m-1], m >= 9 ? h[m-9] : 0);
    cout << "Rooted word counts N(n) for n=16,32,...,320:";
    for (int n = 1; n <= max_length; ++n) {
        uint64_t expected = 0;
        if (n % 16 == 0) {
            const int m = n / 16;
            expected = checked_add(64 + (m % 2 == 0 ? 64 : 0),
                checked_multiply(32, checked_add(h[m-1], m >= 9 ? checked_multiply(9,h[m-9]) : 0)));
            cout << ' ' << trace[n];
        }
        check(trace[n] == expected, "Rooted count formula differs from adjacency-walk DP");
    }
    cout << "\nPASS exact trace formula through n=320 (all n checked)\n";
    // Return-block B occurs once in A^k B. Distinct branch visits identify its
    // unique long return, so these words have least period 16k+144. Finite tests
    // below are a regression check, not a substitute for that argument.
    for (int k = 0; k <= 100; ++k) {
        vector<int> word;
        const auto& returns = components[6].returns;
        for (int j = 0; j < k; ++j) word.insert(word.end(), returns[0].labels.begin(), returns[0].labels.end());
        word.insert(word.end(), returns[1].labels.begin(), returns[1].labels.end());
        verify_periodic(g, word);
        check(least_period(word) == 16*k + 144, "A^k B least-period regression failed");
    }
    cout << "PASS splice and primitive-period regression checks\n";
    return 0;
}

int main() {
    try { return run(); }
    catch (const exception& error) { cerr << "FAIL: " << error.what() << '\n'; return 1; }
}
