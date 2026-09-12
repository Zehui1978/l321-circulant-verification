// C++17, standard library only.
// Build: g++ -std=c++17 -O2 -Wall -Wextra -pedantic verify_l321_direction1.cpp -o verify_l321
// Run:   ./verify_l321 [--all-starts] [--export DIR] [--check DIR]
// --all-starts builds the full state graphs used in Lemma 3.4.
// --check DIR regenerates every state and edge, then checks the two complete
// rank/residue certificates in DIR without using the SCC computation.
// --export DIR writes the two certificate tables and the four cyclic-core
// state/edge files described in the root README.
// All checks remain active under -DNDEBUG. No SAT/MILP solver is used.
#include <algorithm>
#include <array>
#include <charconv>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using Word = std::uint64_t;
using namespace std;

void require(bool condition, const string& reason) {
    if (!condition) throw runtime_error(reason);
}

struct Instance {
    int t, span, width;
    vector<int> gap;
    Word mask;
    Instance(int step, int limit) : t(step), span(limit), width(3 * step), gap(width + 1, 0) {
        require(width <= 15 && span < 16, "4-bit state encoding capacity exceeded");
        mask = (Word(1) << (4 * width)) - 1;
        // Exhaust all paths of length at most 3 on Z, independently of the old BFS.
        function<void(int,int)> paths = [&](int offset, int length) {
            if (length > 0 && offset != 0) {
                int j = abs(offset);
                gap[j] = max(gap[j], 4 - length);
            }
            if (length < 3)
                for (int d : {-t, -1, 1, t}) paths(offset + d, length + 1);
        };
        paths(0, 0);
    }
    bool append_ok(Word word, int length, int value) const {
        for (int j = 1; j <= min(length, width); ++j) {
            if (gap[j] != 0 && abs(value - int((word >> (4 * (j - 1))) & 15)) < gap[j])
                return false;
        }
        return true;
    }
    string text(Word word) const {
        ostringstream out;
        for (int i = width - 1; i >= 0; --i) {
            if (i != width - 1) out << ',';
            out << ((word >> (4 * i)) & 15);
        }
        return out.str();
    }
};

struct Graph {
    vector<Word> words;
    unordered_map<Word,int> id;
    vector<vector<int>> next, previous;
    int seeds = 0;
    size_t edges = 0;

    int insert(Word word) {
        auto found = id.find(word);
        if (found != id.end()) return found->second;
        require(words.size() < 10000000, "Safety state limit reached; enumeration incomplete");
        int number = int(words.size());
        id.emplace(word, number);
        words.push_back(word);
        next.emplace_back();
        previous.emplace_back();
        return number;
    }
    Graph(const Instance& p, bool all_starts) {
        id.reserve(100000);
        function<void(Word,int)> enumerate = [&](Word word, int length) {
            if (length == p.width) { insert(word); return; }
            for (int value = 0; value <= p.span; ++value)
                if (p.append_ok(word, length, value))
                    enumerate((word << 4) | Word(value), length + 1);
        };
        if (all_starts) enumerate(0, 0);
        else enumerate(0, 1); // The first symbol is zero, not an empty word.
        seeds = int(words.size());
        for (size_t i = 0; i < words.size(); ++i) {
            Word word = words[i]; // Copy before insert can reallocate words.
            for (int value = 0; value <= p.span; ++value) {
                if (!p.append_ok(word, p.width, value)) continue;
                const Word successor = ((word << 4) | Word(value)) & p.mask;
                int target;
                if (all_starts) {
                    const auto found = id.find(successor);
                    require(found != id.end(), "Legal successor missing from complete state set");
                    target = found->second;
                } else {
                    target = insert(successor);
                }
                next[i].push_back(target);
                previous[target].push_back(int(i));
                ++edges;
            }
        }
    }
};

struct Decomposition {
    vector<vector<int>> members;
    vector<int> group, period, phase;
    vector<char> cyclic;

    explicit Decomposition(const Graph& g) {
        // Iterative Kosaraju: different SCC algorithm from the original program.
        int n = int(g.words.size());
        vector<char> seen(n, false);
        vector<int> finish;
        for (int start = 0; start < n; ++start) {
            if (seen[start]) continue;
            vector<pair<int,size_t>> stack = {{start, 0}};
            seen[start] = true;
            while (!stack.empty()) {
                int v = stack.back().first;
                size_t pos = stack.back().second;
                if (pos == g.next[v].size()) {
                    finish.push_back(v); stack.pop_back();
                } else {
                    ++stack.back().second;
                    int w = g.next[v][pos];
                    if (!seen[w]) { seen[w] = true; stack.emplace_back(w, 0); }
                }
            }
        }
        group.assign(n, -1);
        for (auto it = finish.rbegin(); it != finish.rend(); ++it) {
            int start = *it;
            if (group[start] != -1) continue;
            int c = int(members.size());
            members.emplace_back();
            vector<int> stack = {start};
            group[start] = c;
            while (!stack.empty()) {
                int v = stack.back(); stack.pop_back();
                members[c].push_back(v);
                for (int w : g.previous[v]) if (group[w] == -1) {
                    group[w] = c; stack.push_back(w);
                }
            }
        }
        period.assign(members.size(), 0);
        cyclic.assign(members.size(), false);
        phase.assign(n, 0);
        vector<int> depth(n, -1);
        for (int c = 0; c < int(members.size()); ++c) {
            int start = members[c][0];
            depth[start] = 0;
            vector<int> stack = {start};
            while (!stack.empty()) {
                int v = stack.back(); stack.pop_back();
                for (int w : g.next[v]) if (group[w] == c && depth[w] == -1) {
                    depth[w] = depth[v] + 1; stack.push_back(w);
                }
            }
            for (int v : members[c]) for (int w : g.next[v]) {
                if (group[w] != c) {
                    require(group[w] > c, "SCC order must increase on cross-component edges");
                } else {
                    cyclic[c] = true;
                    period[c] = gcd(period[c], abs(depth[v] + 1 - depth[w]));
                }
            }
            if (cyclic[c]) require(period[c] > 0, "Cyclic SCC has zero period");
            for (int v : members[c]) phase[v] = depth[v];
        }
    }
};

// A proof certificate needs no SCC claim: rank never decreases along an edge,
// and for equal ranks the phase increases by 1 modulo m. Summing round a closed
// walk proves its length divisible by m. All vertices, including transients,
// receive a rank and phase. This checker does not call any SCC algorithm.
void check_potential(const Graph& g, const vector<int>& rank,
                     const vector<int>& phase, int modulus) {
    require(modulus >= 2, "Certificate modulus must be at least two");
    require(rank.size() == g.words.size() && phase.size() == rank.size(), "Certificate size");
    for (size_t v = 0; v < g.words.size(); ++v) {
        require(rank[v] >= 0 && phase[v] >= 0 && phase[v] < modulus, "Invalid rank or phase");
        for (int w : g.next[v]) {
            require(rank[w] >= rank[v], "Certificate rank decreases along an edge");
            if (rank[w] == rank[v])
                require(phase[w] == (phase[v] + 1) % modulus,
                        "Certificate phase fails to advance along an internal edge");
        }
    }
}

string stem(const Instance& p) { return "t" + to_string(p.t) + "_s" + to_string(p.span); }

void export_certificate(const filesystem::path& directory, const Instance& p,
                        const Graph& g, const Decomposition& d, int modulus) {
    filesystem::create_directories(directory);
    // Binary mode makes these text artifacts byte-identical on Windows and Unix.
    ofstream cert(directory / (stem(p) + "_certificate.tsv"), ios::binary);
    require(bool(cert), "Cannot write certificate");
    cert << "word_decimal\trank\tphase\n";
    vector<int> order(g.words.size());
    iota(order.begin(), order.end(), 0);
    sort(order.begin(), order.end(), [&](int a, int b) { return g.words[a] < g.words[b]; });
    for (int v : order) cert << g.words[v] << '\t' << d.group[v] << '\t' << d.phase[v] % modulus << '\n';
    ofstream edgefile(directory / (stem(p) + "_core_edges.txt"), ios::binary);
    ofstream phasefile(directory / (stem(p) + "_core_states.csv"), ios::binary);
    require(bool(edgefile) && bool(phasefile), "Cannot write cyclic core");
    phasefile << "state,rank,phase,component_size,component_period\n";
    for (int v : order) if (d.cyclic[d.group[v]]) {
        phasefile << '"' << p.text(g.words[v]) << "\"," << d.group[v] << ','
                  << d.phase[v] % modulus << ',' << d.members[d.group[v]].size()
                  << ',' << d.period[d.group[v]] << '\n';
        vector<int> targets;
        for (int w : g.next[v]) if (d.cyclic[d.group[w]]) targets.push_back(w);
        sort(targets.begin(), targets.end(), [&](int a, int b) { return g.words[a] < g.words[b]; });
        for (int w : targets) edgefile << p.text(g.words[v]) << '>' << p.text(g.words[w]) << '\n';
    }
    cert.close(); edgefile.close(); phasefile.close();
    require(bool(cert) && bool(edgefile) && bool(phasefile), "Error writing certificate data");
}

// No formatted extraction: it can silently accept a partially written final row.
// Each non-header row must contain exactly three nonnegative decimal fields.
template<class Integer>
Integer decimal_field(const string& field) {
    require(!field.empty(), "Empty certificate field");
    require(all_of(field.begin(), field.end(), [](char c) { return c >= '0' && c <= '9'; }),
            "Certificate fields must be unsigned decimal integers");
    Integer value = 0;
    const char* end = field.data() + field.size();
    auto result = from_chars(field.data(), end, value);
    require(result.ec == errc{} && result.ptr == end, "Certificate integer overflow");
    return value;
}

void check_certificate_stream(istream& in, const Graph& g, int modulus) {
    string header;
    require(bool(getline(in, header)), "Missing certificate header");
    if (!header.empty() && header.back() == '\r') header.pop_back();
    require(header == "word_decimal\trank\tphase", "Invalid certificate header");
    vector<int> rank(g.words.size(), -1), phase(g.words.size(), -1);
    string row;
    while (getline(in, row)) {
        if (!row.empty() && row.back() == '\r') row.pop_back();
        size_t first = row.find('\t');
        require(first != string::npos, "Certificate row has fewer than three fields");
        size_t second = row.find('\t', first + 1);
        require(second != string::npos && row.find('\t', second + 1) == string::npos,
                "Certificate row must have exactly three fields");
        Word word = decimal_field<Word>(row.substr(0, first));
        int r = decimal_field<int>(row.substr(first + 1, second - first - 1));
        int q = decimal_field<int>(row.substr(second + 1));
        auto found = g.id.find(word);
        require(found != g.id.end(), "Unknown certificate state");
        int v = found->second;
        require(rank[v] == -1, "Duplicate certificate state");
        rank[v] = r; phase[v] = q;
    }
    require(in.eof() && !in.bad(), "Error reading certificate");
    require(none_of(rank.begin(), rank.end(), [](int r) { return r < 0; }),
            "Missing certificate state");
    check_potential(g, rank, phase, modulus);
}

void import_and_check(const filesystem::path& directory, const Instance& p, const Graph& g, int modulus) {
    // Binary input plus explicit CR removal accepts both LF and CRLF on all hosts.
    ifstream in(directory / (stem(p) + "_certificate.tsv"), ios::binary);
    require(bool(in), "Cannot read certificate");
    check_certificate_stream(in, g, modulus);
    cout << "PASS certificate t=" << p.t << ": every closed-walk length is divisible by " << modulus << '\n';
}

void check_gap_tables(const Instance& p) {
    const vector<int> expected = p.t == 4
        ? vector<int>{0,3,2,2,3,2,1,1,2,1,0,0,1}
        : vector<int>{0,3,2,1,2,3,2,1,0,1,2,1,0,0,0,1};
    require(p.gap == expected, "Incorrect infinite-distance separation table");
    // Independent BFS in actual finite circulants checks all wrapped constraints.
    for (int n = p.width + 1; n <= 2 * p.width + 2; ++n) {
        vector<int> dist(n, -1), direct(n, 0), predicted(n, 0), queue = {0};
        dist[0] = 0;
        for (size_t i = 0; i < queue.size(); ++i) {
            int v = queue[i];
            if (dist[v] == 3) continue;
            for (int step : {-p.t, -1, 1, p.t}) {
                int w = (v + step + n) % n;
                if (dist[w] == -1) { dist[w] = dist[v] + 1; queue.push_back(w); }
            }
        }
        for (int v = 1; v < n; ++v) if (dist[v] > 0 && dist[v] <= 3) direct[v] = 4 - dist[v];
        for (int j = 1; j <= p.width; ++j) for (int sign : {-1,1}) {
            int w = (sign * j + n) % n;
            predicted[w] = max(predicted[w], p.gap[j]);
        }
        require(direct == predicted, "Finite/infinite distance boundary mismatch");
    }
}

void check_additional_lower_bounds() {
    // Complete state graphs one label below each claimed optimum must be acyclic.
    for (auto parameters : {pair<int,int>{4,14}, pair<int,int>{5,12}}) {
        Instance p(parameters.first, parameters.second);
        Graph g(p, true);
        require(g.words.size() == size_t(p.t == 4 ? 1024 : 1746),
                "Smaller-span complete state count mismatch");
        Decomposition d(g);
        require(none_of(d.cyclic.begin(), d.cyclic.end(), [](char x) { return x != 0; }),
                "A smaller-span periodic labeling exists");
        cout << "PASS lower bound t=" << p.t << ": span " << p.span
             << " has no closed walk [" << g.words.size() << " states]\n";
    }
    // A valid period-32 example prevents confusing 16-divisibility with 16-periodicity.
    const vector<int> word = {9,1,14,6,3,11,8,0,13,5,2,10,7,15,12,4,
                             1,9,6,14,11,3,0,8,5,13,10,2,15,7,4,12};
    Instance p(4,15);
    const vector<int> period16 = {0,5,10,15,3,8,13,1,6,11,4,9,14,2,7,12};
    for (int i = 0; i < int(period16.size()); ++i)
        for (int j = 1; j <= p.width; ++j)
            require(abs(period16[i] - period16[(i + j) % period16.size()]) >= p.gap[j],
                    "Period-16 upper-bound construction violates a local constraint");
    for (int i = 0; i < int(word.size()); ++i)
        for (int j = 1; j <= p.width; ++j)
            require(abs(word[i] - word[(i + j) % word.size()]) >= p.gap[j],
                    "Period-32 labeling violates a local constraint");
    require(word[0] != word[16], "Example unexpectedly has period 16");
    cout << "PASS witness: a valid t=4 labeling of period 32 is not 16-periodic\n";
}

void run(int t, int span, bool all_starts, const string& export_dir, const string& check_dir) {
    auto begin = chrono::steady_clock::now();
    Instance p(t, span);
    check_gap_tables(p);
    Graph g(p, all_starts);
    if (all_starts) {
        require(g.seeds == (t == 4 ? 39032 : 110672), "Complete initial state count mismatch");
        require(g.words.size() == size_t(t == 4 ? 39032 : 110672), "Complete state count mismatch");
        require(g.edges == size_t(t == 4 ? 24328 : 111010), "Complete edge count mismatch");
    } else {
        require(g.seeds == (t == 4 ? 972 : 11089), "Initial state count mismatch");
        require(g.words.size() == size_t(t == 4 ? 3284 : 52054), "Reachable state count mismatch");
        require(g.edges == size_t(t == 4 ? 2477 : 51212), "Reachable edge count mismatch");
    }
    int modulus = t == 4 ? 16 : 2;
    if (!check_dir.empty()) { import_and_check(check_dir, p, g, modulus); return; }
    Decomposition d(g);
    map<pair<int,int>,int> summary;
    int core_vertices = 0, core_edges = 0, cyclic_count = 0;
    for (int c = 0; c < int(d.members.size()); ++c) if (d.cyclic[c]) {
        ++summary[{int(d.members[c].size()), d.period[c]}];
        ++cyclic_count;
        core_vertices += int(d.members[c].size());
        require(d.period[c] % modulus == 0, "A cyclic SCC violates the required period");
    }
    for (int v = 0; v < int(g.words.size()); ++v) if (d.cyclic[d.group[v]]) {
        for (int w : g.next[v]) if (d.cyclic[d.group[w]]) {
            ++core_edges;
            if (t == 5) require(((g.words[v] ^ g.words[w]) & 1) == 1, "Cyclic-core parity fails");
        }
    }
    const map<pair<int,int>,int> expected = t == 4
        ? map<pair<int,int>,int>{{{151,16},2},{{32,32},2},{{16,16},4}}
        : map<pair<int,int>,int>{{{4848,2},1},{{14,14},48},{{12,12},26}};
    require(summary == expected, "SCC summary differs from the previous computation");
    if (t == 4) {
        map<int,int> cycle_lengths;
        for (int c = 0; c < int(d.members.size()); ++c) if (d.cyclic[c]) {
            vector<int> branches;
            for (int v : d.members[c]) {
                int degree = 0;
                for (int w : g.next[v]) if (d.group[w] == c) ++degree;
                require(degree >= 1, "Cyclic component has an internal sink");
                if (degree > 1) branches.push_back(v);
            }
            if (branches.empty()) { ++cycle_lengths[int(d.members[c].size())]; continue; }
            require(branches.size() == 1, "Unexpected branching structure");
            int branch = branches[0];
            for (int first : g.next[branch]) if (d.group[first] == c) {
                int v = first, length = 1;
                while (v != branch) {
                    require(length <= int(d.members[c].size()), "Branch path failed to return");
                    int successor = -1;
                    for (int w : g.next[v]) if (d.group[w] == c) {
                        require(successor == -1, "Second branch on return path"); successor = w;
                    }
                    require(successor >= 0, "Return path ends at a sink");
                    v = successor; ++length;
                }
                ++cycle_lengths[length];
            }
        }
        require(cycle_lengths == map<int,int>{{16,6},{32,2},{144,2}}, "Simple-cycle lengths differ");
    }
    require(core_vertices == (t == 4 ? 430 : 5832) && core_edges == (t == 4 ? 432 : 6202), "Cyclic core count mismatch");
    if (!all_starts) {
        require(d.members.size() == size_t(t == 4 ? 2862 : 46297), "SCC count mismatch");
    } else {
        require(d.members.size() == size_t(t == 4 ? 38610 : 104915), "Complete SCC count mismatch");
    }
    vector<int> phase = d.phase;
    for (int& q : phase) q %= modulus;
    check_potential(g, d.group, phase, modulus);
    // Negative control: a corrupted phase must be rejected by the certificate checker.
    for (int v = 0; v < int(g.words.size()); ++v) if (d.cyclic[d.group[v]]) {
        vector<int> damaged = phase;
        damaged[v] = (damaged[v] + 1) % modulus;
        bool rejected = false;
        try { check_potential(g, d.group, damaged, modulus); }
        catch (const runtime_error&) { rejected = true; }
        require(rejected, "Corrupted certificate was accepted");
        break;
    }
    if (!export_dir.empty()) export_certificate(export_dir, p, g, d, modulus);
    cout << "t=" << t << " span=" << span << " mode=" << (all_starts ? "all-starts" : "zero-start")
         << " seeds=" << g.seeds << " states=" << g.words.size() << " edges=" << g.edges
         << " SCCs=" << d.members.size() << " cyclic_SCCs=" << cyclic_count << '\n';
    cout << "cyclic_SCCs(size,period):";
    for (const auto& item : summary) cout << " (" << item.first.first << ',' << item.first.second << ")x" << item.second;
    cout << "\ncore=" << core_vertices << " states," << core_edges << " edges\n";
    cout << "PASS t=" << t << ": every closed-walk length is divisible by " << modulus;
    cout << " [" << chrono::duration<double>(chrono::steady_clock::now() - begin).count() << " s]\n";
}

#ifndef L321_NO_MAIN
int main(int argc, char** argv) {
    try {
        if (argc == 2 && string(argv[1]) == "--help") {
            cout << "Usage: verify_l321_direction1 [--all-starts] [--export DIR | --check DIR]\n"
                 << "No arguments: enumerate the zero-start reachable graphs.\n"
                 << "--all-starts: enumerate every legal state (required for shipped certificates).\n"
                 << "--export DIR: write six certificate/core files; existing files are replaced.\n"
                 << "--check DIR: regenerate graphs and check TSV rank/residue certificates only;\n"
                 << "             no SCCs, lower-span checks, template or local-window checks.\n"
                 << "Instances are fixed: (t,span)=(4,15),(5,13); no circulant-order input.\n";
            return 0;
        }
        bool all_starts = false;
        string export_dir, check_dir;
        for (int i = 1; i < argc; ++i) {
            string option = argv[i];
            if (option == "--all-starts") {
                require(!all_starts, "Duplicate --all-starts option");
                all_starts = true;
            }
            else if (option == "--export" || option == "--check") {
                require(i + 1 < argc, "Missing directory argument");
                string& directory = option == "--export" ? export_dir : check_dir;
                require(directory.empty(), "Duplicate directory option");
                directory = argv[++i];
                require(!directory.empty() && directory.rfind("--", 0) != 0,
                        "Directory must be nonempty and not another option");
            } else throw runtime_error("Unknown option: " + option);
        }
        require(export_dir.empty() || check_dir.empty(), "Use --export or --check, not both");
        if (check_dir.empty()) check_additional_lower_bounds();
        run(4, 15, all_starts, export_dir, check_dir);
        run(5, 13, all_starts, export_dir, check_dir);
        return 0;
    } catch (const exception& error) {
        cerr << "FAIL: " << error.what() << '\n';
        return 1;
    }
}
#endif
