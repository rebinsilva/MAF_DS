#include <algorithm>
#include <array>
#include <cassert>
#include <cctype>
#include <chrono>
#include <climits>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iostream>
#include <iterator>
#include <random>
#include <sstream>
#include <string>
#include <tuple>
#include <unistd.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <atomic>
#include <thread>

static volatile std::sig_atomic_t g_stop = 0;

struct RootedBinaryForest {
    std::unordered_map<int, std::vector<int>> children;
    std::unordered_map<int, int>              parent;
    std::unordered_set<int>                  nodes;
    std::unordered_set<int>                  roots;

    bool contains(int n) const { return nodes.count(n); }
    int  size()          const { return (int)nodes.size(); }

    void add_node(int n) {
        if (!nodes.count(n)) {
            children[n] = {};
            parent[n]   = 0;
            nodes.insert(n);
            roots.insert(n);
        }
    }

    void remove_node(int n) {
        int p = parent[n];
        if (p != 0) {
            auto& pc = children[p];
            pc.erase(std::find(pc.begin(), pc.end(), n));
        }
        for (int c : children[n]) {
            parent[c] = 0;
            roots.insert(c);
        }
        roots.erase(n);
        children.erase(n);
        parent.erase(n);
        nodes.erase(n);
    }

    void add_edge(int u, int v) {
        add_node(u);
        add_node(v);
        children[u].push_back(v);
        parent[v] = u;
        roots.erase(v);
    }

    void add_edges_from(const std::vector<std::pair<int,int>>& edges) {
        for (auto& [u, v] : edges) add_edge(u, v);
    }

    void remove_edge(int u, int v) {
        auto& pc = children[u];
        pc.erase(std::find(pc.begin(), pc.end(), v));
        parent[v] = 0;
        roots.insert(v);
    }

    void remove_edges_from(const std::vector<std::pair<int,int>>& edges) {
        for (auto& [u, v] : edges) {
            auto it = children.find(u);
            if (it != children.end()) {
                auto vit = std::find(it->second.begin(), it->second.end(), v);
                if (vit != it->second.end()) remove_edge(u, v);
            }
        }
    }

    const std::vector<int>& successors(int n) const { return children.at(n); }
    const std::vector<int>& ch(int n)         const { return children.at(n); }
    int  par(int n)                            const { return parent.at(n); }
    int  out_degree(int n)                     const { return (int)children.at(n).size(); }

    std::vector<std::pair<int,int>> edges() const {
        std::vector<std::pair<int,int>> e;
        for (auto& [u, cs] : children)
            for (int v : cs) e.push_back({u, v});
        return e;
    }

    void delete_subtree(int source) {
        std::vector<int> order;
        std::vector<int> stk = {source};
        while (!stk.empty()) {
            int n = stk.back(); stk.pop_back();
            order.push_back(n);
            for (int c : children[n]) stk.push_back(c);
        }
        for (int i = (int)order.size()-1; i >= 0; --i) remove_node(order[i]);
    }

    RootedBinaryForest split_subtree(int source) {
        int p = parent[source];
        if (p != 0) {
            auto& pc = children[p];
            pc.erase(std::find(pc.begin(), pc.end(), source));
            parent[source] = 0;
        }
        roots.erase(source);

        RootedBinaryForest sub;
        std::vector<int> stk = {source};
        while (!stk.empty()) {
            int n = stk.back(); stk.pop_back();
            sub.children[n] = children[n];
            sub.parent[n]   = parent[n];
            nodes.erase(n);
            sub.nodes.insert(n);
            children.erase(n);
            parent.erase(n);
            for (int c : sub.children[n]) stk.push_back(c);
        }
        sub.parent[source] = 0;
        sub.roots.insert(source);
        return sub;
    }

    std::pair<RootedBinaryForest, int> split_subtree_with_parent(int source) {
        int p = parent[source];
        RootedBinaryForest sub = split_subtree(source);
        return {std::move(sub), p};
    }

    void add_subtree(const RootedBinaryForest& subtree, int par_node) {
        assert(subtree.roots.size() == 1);
        int root = *subtree.roots.begin();
        for (auto& [n, cs] : subtree.children) {
            children[n] = cs;
        }
        for (auto& [n, p] : subtree.parent) {
            parent[n] = p;
        }
        nodes.insert(subtree.nodes.begin(), subtree.nodes.end());
        if (par_node == 0) {
            roots.insert(root);
        } else {
            children[par_node].push_back(root);
            parent[root] = par_node;
        }
    }

    RootedBinaryForest copy() const {
        RootedBinaryForest G;
        G.nodes = nodes;
        G.roots = roots;
        G.children.reserve(children.size());
        for (auto& [n, cs] : children) G.children[n] = cs;
        G.parent = parent;
        return G;
    }
};

RootedBinaryForest create_empty_copy(const RootedBinaryForest& G) {
    RootedBinaryForest H;
    size_t n = G.nodes.size();
    H.children.reserve(n); H.parent.reserve(n);
    H.nodes.reserve(n);    H.roots.reserve(n);
    for (int nd : G.nodes) {
        H.children[nd] = {};
        H.parent[nd]   = 0;
        H.nodes.insert(nd);
        H.roots.insert(nd);
    }
    return H;
}

void all_leaves_tree(const RootedBinaryForest& G, int source,
                     std::vector<int>& out) {
    if (source > 0) out.push_back(source);
    for (int v : G.successors(source))
        all_leaves_tree(G, v, out);
}

bool delete_subtree_leaves(RootedBinaryForest& G,
                           const std::unordered_set<int>& leaves, int source) {
    if (leaves.count(source)) {
        G.remove_node(source);
        return true;
    }
    std::vector<int> chs(G.ch(source));
    bool flag = false;
    for (int v : chs)
        if (delete_subtree_leaves(G, leaves, v)) flag = true;
    if (flag) G.remove_node(source);
    return flag;
}

int remove_contract_rooted(RootedBinaryForest& T,
                           const std::unordered_set<int>& leaves, int node) {
    if (leaves.count(node)) return node;
    for (int child : std::vector<int>(T.ch(node)))
        remove_contract_rooted(T, leaves, child);
    int od = T.out_degree(node);
    if (od == 0) { T.remove_node(node); return 0; }
    if (od == 1) {
        int child = T.ch(node)[0];
        int p = T.par(node);
        if (p != 0) T.add_edge(p, child);
        T.remove_node(node);
        return child;
    }
    return node;
}

int find_root(const RootedBinaryForest& G, int node) {
    while (G.par(node) != 0) node = G.par(node);
    return node;
}

int _get_min(const RootedBinaryForest& graph, int node,
             const std::unordered_set<int>& leaves,
             std::unordered_map<int,int>& min_dict) {
    if (leaves.count(node)) { min_dict[node] = node; return node; }
    if (graph.out_degree(node) == 0) { min_dict[node] = INT_MAX; return INT_MAX; }
    int mini = INT_MAX;
    for (int child : graph.successors(node))
        mini = std::min(mini, _get_min(graph, child, leaves, min_dict));
    min_dict[node] = mini;
    return mini;
}

void get_min(const RootedBinaryForest& graph,
             const std::unordered_set<int>& leaves,
             std::unordered_map<int,int>& min_dict) {
    for (int root : graph.roots)
        _get_min(graph, root, leaves, min_dict);
}

std::pair<int,int> find_contracted_root(const RootedBinaryForest& graph,
                                        int node,
                                        const std::unordered_set<int>& leaves,
                                        int n_leaves) {
    if (leaves.count(node)) return {1, node};
    int found = 0;
    for (int child : graph.successors(node)) {
        auto [cl, cr] = find_contracted_root(graph, child, leaves, n_leaves);
        if (cl == n_leaves) return {cl, cr};
        found += cl;
    }
    return {found, node};
}

std::pair<int,int> find_contracted_root2(const RootedBinaryForest& graph,
                                          int root,
                                          const std::unordered_set<int>& leaves,
                                          int n_leaves) {
    std::vector<int> stk = {root};
    std::unordered_map<int,int> found;

    while (!stk.empty()) {
        int node = stk.back();
        if (leaves.count(node)) {
            found[node] = 1;
        } else {
            const auto& chs = graph.successors(node);
            if (chs.empty()) {
                found[node] = 0;
            } else if (!found.count(chs[0])) {
                for (int c : chs) stk.push_back(c);
                continue;
            } else {
                found[node] = 0;
                for (int c : chs) found[node] += found[c];
            }
        }
        stk.pop_back();
        if (found[node] == n_leaves) return {n_leaves, node};
    }
    return {found[root], root};
}

bool compare_trees(int node1, const RootedBinaryForest& T1,
                   const std::unordered_map<int,int>& T1_min,
                   int node2, const RootedBinaryForest& T2,
                   const std::unordered_map<int,int>& T2_min,
                   const std::unordered_set<int>& leaves) {
    if (T1_min.at(node1) != T2_min.at(node2)) return false;

    int d1 = 0, d2 = 0;
    while (true) {
        d1 = T1.out_degree(node1);
        if (d1 == 0) break;
        if (d1 == 1) { node1 = T1.ch(node1)[0]; continue; }
        int n11 = T1.ch(node1)[0], n12 = T1.ch(node1)[1];
        if (T1_min.at(n11) != INT_MAX && T1_min.at(n12) != INT_MAX) break;
        if (T1_min.at(n11) != INT_MAX) { node1 = n11; continue; }
        if (T1_min.at(n12) != INT_MAX) { node1 = n12; continue; }
        d1 = 0; break;
    }
    while (true) {
        d2 = T2.out_degree(node2);
        if (d2 == 0) break;
        if (d2 == 1) { node2 = T2.ch(node2)[0]; continue; }
        int n21 = T2.ch(node2)[0], n22 = T2.ch(node2)[1];
        if (T2_min.at(n21) != INT_MAX && T2_min.at(n22) != INT_MAX) break;
        if (T2_min.at(n21) != INT_MAX) { node2 = n21; continue; }
        if (T2_min.at(n22) != INT_MAX) { node2 = n22; continue; }
        d2 = 0; break;
    }
    if (d1 == 0 && d2 == 0) return true;
    if (d1 == 0 || d2 == 0) return false;

    int n11 = T1.ch(node1)[0], n12 = T1.ch(node1)[1];
    int n21 = T2.ch(node2)[0], n22 = T2.ch(node2)[1];
    if (T1_min.at(n11) > T1_min.at(n12)) std::swap(n11, n12);
    if (T2_min.at(n21) > T2_min.at(n22)) std::swap(n21, n22);

    return compare_trees(n11, T1, T1_min, n21, T2, T2_min, leaves) &&
           compare_trees(n12, T1, T1_min, n22, T2, T2_min, leaves);
}

RootedBinaryForest parse_newick_to_digraph(const std::string& newick_str) {
    RootedBinaryForest G;
    std::vector<int> stk;
    int node_id = -1;
    int current_parent = 0;
    std::string token;

    auto new_internal = [&]() -> int {
        int n = node_id--;
        G.add_node(n);
        return n;
    };

    for (char c : newick_str) {
        if (c == '(') {
            int node = new_internal();
            if (current_parent != 0) G.add_edge(current_parent, node);
            stk.push_back(current_parent);
            current_parent = node;
        } else if (c == ',') {
            if (!token.empty()) {
                int leaf = std::stoi(token);
                G.add_node(leaf);
                G.add_edge(current_parent, leaf);
                token.clear();
            }
        } else if (c == ')') {
            if (!token.empty()) {
                int leaf = std::stoi(token);
                G.add_node(leaf);
                G.add_edge(current_parent, leaf);
                token.clear();
            }
            current_parent = stk.back(); stk.pop_back();
        } else if (c == ';' || c == ' ' || c == '\t' || c == '\n' || c == '\r') {
        } else {
            token += c;
        }
    }
    return G;
}

void tree_to_newick_list(const RootedBinaryForest& g, std::string& out, int root) {
    if (g.out_degree(root) == 0) {
        out += std::to_string(root);
        return;
    }
    out += '(';
    bool first = true;
    for (int child : g.ch(root)) {
        if (!first) out += ',';
        first = false;
        tree_to_newick_list(g, out, child);
    }
    out += ')';
}

std::string tree_to_newick_print(const RootedBinaryForest& g, int root) {
    std::string out;
    tree_to_newick_list(g, out, root);
    out += ';';
    return out;
}

struct TreeDecomposition {
    bool present = false;
    int  tw = -1;
    std::vector<std::vector<int>> bags;
    std::vector<std::pair<int,int>> edges;
};

    inline void skip_ws(const std::string& s, size_t& i) {
        while (i < s.size() && (s[i] == ' ' || s[i] == '\t')) ++i;
    }
    inline int parse_int(const std::string& s, size_t& i) {
        skip_ws(s, i);
        int sign = 1;
        if (i < s.size() && s[i] == '-') { sign = -1; ++i; }
        int v = 0;
        while (i < s.size() && s[i] >= '0' && s[i] <= '9') { v = v*10 + (s[i]-'0'); ++i; }
        return sign * v;
    }
    inline std::vector<int> parse_intlist(const std::string& s, size_t& i) {
        std::vector<int> r;
        skip_ws(s, i);
        if (i >= s.size() || s[i] != '[') return r;
        ++i; skip_ws(s, i);
        while (i < s.size() && s[i] != ']') {
            r.push_back(parse_int(s, i));
            skip_ws(s, i);
            if (i < s.size() && s[i] == ',') ++i;
            skip_ws(s, i);
        }
        if (i < s.size() && s[i] == ']') ++i;
        return r;
    }
    inline std::vector<std::vector<int>> parse_listoflists(const std::string& s, size_t& i) {
        std::vector<std::vector<int>> r;
        skip_ws(s, i);
        if (i >= s.size() || s[i] != '[') return r;
        ++i; skip_ws(s, i);
        while (i < s.size() && s[i] != ']') {
            r.push_back(parse_intlist(s, i));
            skip_ws(s, i);
            if (i < s.size() && s[i] == ',') ++i;
            skip_ws(s, i);
        }
        if (i < s.size() && s[i] == ']') ++i;
        return r;
    }

inline TreeDecomposition parse_treedecomp(const std::string& payload) {
    TreeDecomposition td;
    size_t i = payload.find('[');
    if (i == std::string::npos) return td;
    ++i;
    td.tw = parse_int(payload, i);
    skip_ws(payload, i);
    if (i < payload.size() && payload[i] == ',') ++i;
    td.bags = parse_listoflists(payload, i);
    skip_ws(payload, i);
    if (i < payload.size() && payload[i] == ',') ++i;
    auto raw_edges = parse_listoflists(payload, i);
    for (auto& e : raw_edges)
        if (e.size() >= 2) td.edges.push_back({e[0], e[1]});
    td.present = !td.bags.empty();
    int mb = 0;
    for (auto& b : td.bags) mb = std::max(mb, (int)b.size());
    if (mb > 0) td.tw = mb - 1;
    return td;
}

struct InputData {
    std::vector<RootedBinaryForest> trees;
    int n_leaves = 0;
    TreeDecomposition td;
};

InputData read_input(std::istream& f) {
    InputData data;
    int n_pending = 0;
    std::string line;
    while (std::getline(f, line)) {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (line.empty()) continue;
        if (line[0] == '#') {
            std::string rest = line.substr(1);
            size_t s = rest.find_first_not_of(" \t");
            if (s == std::string::npos) continue;
            rest = rest.substr(s);
            if (rest.size() >= 2 && rest[0] == 'p' && (rest[1] == ' ' || rest[1] == '\t')) {
                int nt; std::istringstream ss(rest.substr(2)); ss >> nt >> data.n_leaves;
                n_pending = nt;
            } else {
                size_t tp = rest.find("treedecomp");
                if (tp != std::string::npos)
                    data.td = parse_treedecomp(rest.substr(tp + 10));
            }
            continue;
        }
        if (n_pending > 0) {
            data.trees.push_back(parse_newick_to_digraph(line));
            --n_pending;
        }
    }
    return data;
}

std::vector<std::tuple<int,int,std::unordered_set<int>>>
find_maximal_common_pendants(RootedBinaryForest T1, RootedBinaryForest T2,
                             const std::unordered_set<int>& leaves) {
    std::unordered_set<int> visited;
    std::unordered_map<int,int> T1_min, T2_min;
    get_min(T1, leaves, T1_min);
    get_min(T2, leaves, T2_min);

    std::vector<std::tuple<int,int,std::unordered_set<int>>> result;

    for (int leaf : leaves) {
        if (visited.count(leaf)) continue;
        int node1 = leaf, node2 = leaf;

        while (T1.par(node1) != 0 && T2.par(node2) != 0) {
            int pred1 = T1.par(node1);
            int pred2 = T2.par(node2);
            const auto& ch1 = T1.ch(pred1);
            const auto& ch2 = T2.ch(pred2);
            bool mismatch = false;
            if (ch1.size() == ch2.size() && ch1.size() == 2) {
                int n11 = ch1[0], n12 = ch1[1];
                int n21 = ch2[0], n22 = ch2[1];
                if (n11 != node1) std::swap(n11, n12);
                if (n21 != node2) std::swap(n21, n22);
                if (!compare_trees(n12, T1, T1_min, n22, T2, T2_min, leaves))
                    mismatch = true;
            } else {
                mismatch = true;
            }
            if (mismatch) {
                std::vector<int> lv; all_leaves_tree(T1, node1, lv);
                std::unordered_set<int> covered(lv.begin(), lv.end());
                visited.insert(covered.begin(), covered.end());
                if (!leaves.count(node1))
                    result.push_back({node1, node2, std::move(covered)});
                goto next_leaf;
            }
            node1 = pred1; node2 = pred2;
        }
        {
            std::vector<int> lv; all_leaves_tree(T1, node1, lv);
            std::unordered_set<int> covered(lv.begin(), lv.end());
            visited.insert(covered.begin(), covered.end());
            if (!leaves.count(node1))
                result.push_back({node1, node2, std::move(covered)});
        }
        next_leaf:;
    }
    return result;
}

struct SubtreeReduction {
    std::unordered_map<int, RootedBinaryForest> replace_map;
};

SubtreeReduction subtree_reduce(RootedBinaryForest& T1, RootedBinaryForest& T2,
                                const std::unordered_set<int>& leaves) {
    SubtreeReduction sr;
    auto pendants = find_maximal_common_pendants(T1.copy(), T2.copy(), leaves);
    for (auto& [node1, node2, covered] : pendants) {
        int replacement = *covered.begin();
        auto [tree1, p1] = T1.split_subtree_with_parent(node1);
        auto [tree2, p2] = T2.split_subtree_with_parent(node2);
        if (p1 != 0) T1.add_edge(p1, replacement); else T1.add_node(replacement);
        if (p2 != 0) T2.add_edge(p2, replacement); else T2.add_node(replacement);
        sr.replace_map[replacement] = std::move(tree1);
    }
    return sr;
}

void restore_subtree(RootedBinaryForest& graph, const SubtreeReduction& sr) {
    for (auto& [leaf, tree] : sr.replace_map) {
        int p = graph.par(leaf);
        graph.remove_node(leaf);
        graph.add_subtree(tree, p);
    }
}

struct ChainReduction {
    std::unordered_map<int, std::vector<int>> chain_map;
};

std::vector<std::vector<int>>
find_common_chains(const RootedBinaryForest& T1, const RootedBinaryForest& T2,
                   const std::unordered_set<int>& leaves) {
    std::unordered_set<int> visited;
    std::vector<std::vector<int>> result;

    for (int leaf : leaves) {
        if (visited.count(leaf)) continue;

        auto it1 = T1.parent.find(leaf);
        if (it1 == T1.parent.end() || it1->second == 0) { visited.insert(leaf); continue; }
        int G1_T1 = it1->second;
        const auto& T1ch = T1.ch(G1_T1);
        if (T1ch.size() != 2) { visited.insert(leaf); continue; }
        int x2_T1 = (T1ch[1] == leaf) ? T1ch[0] : T1ch[1];
        if (!leaves.count(x2_T1)) { visited.insert(leaf); continue; }

        auto it2 = T2.parent.find(leaf);
        if (it2 == T2.parent.end() || it2->second == 0) { visited.insert(leaf); continue; }
        int G1_T2 = it2->second;
        const auto& T2ch = T2.ch(G1_T2);
        if (T2ch.size() != 2) { visited.insert(leaf); continue; }
        int x2_T2 = (T2ch[1] == leaf) ? T2ch[0] : T2ch[1];
        if (x2_T2 != x2_T1) { visited.insert(leaf); continue; }

        std::vector<int> chain = {leaf};
        int node_T1 = G1_T1, node_T2 = G1_T2;

        while (true) {
            int par_T1 = T1.par(node_T1);
            int par_T2 = T2.par(node_T2);
            if (par_T1 == 0 || par_T2 == 0) break;
            const auto& pch1 = T1.ch(par_T1);
            const auto& pch2 = T2.ch(par_T2);
            if (pch1.size() != 2 || pch2.size() != 2) break;
            int sib_T1 = (pch1[1] == node_T1) ? pch1[0] : pch1[1];
            int sib_T2 = (pch2[1] == node_T2) ? pch2[0] : pch2[1];
            if (sib_T1 != sib_T2) break;
            int sib = sib_T1;
            if (!leaves.count(sib) || visited.count(sib)) break;
            chain.push_back(sib);
            node_T1 = par_T1; node_T2 = par_T2;
        }

        if ((int)chain.size() < 3) { visited.insert(leaf); continue; }
        visited.insert(chain.begin(), chain.end());
        result.push_back(std::move(chain));
    }
    return result;
}

void _truncate_chain(RootedBinaryForest& T, const std::vector<int>& chain) {
    int G1 = T.par(chain[0]);
    int G2 = T.par(G1);

    int chain_top = G2;
    for (int i = 2; i < (int)chain.size(); ++i)
        chain_top = T.par(chain_top);
    int above = T.par(chain_top);
    if (above != 0) {
        auto& ac = T.children[above];
        ac.erase(std::find(ac.begin(), ac.end(), chain_top));
        T.parent[chain_top] = 0;
    } else {
        T.roots.erase(chain_top);
    }

    int G3 = T.par(G2);
    if (G3 != 0) {
        auto& gc = T.children[G3];
        gc.erase(std::find(gc.begin(), gc.end(), G2));
        T.parent[G2] = 0;
    }

    int node = G3;
    for (int i = 2; i < (int)chain.size(); ++i) {
        int ci = chain[i];
        int next_node = (node != chain_top && node != 0) ? T.par(node) : 0;

        T.roots.erase(ci);    T.children.erase(ci); T.parent.erase(ci); T.nodes.erase(ci);
        T.roots.erase(node);  T.children.erase(node); T.parent.erase(node); T.nodes.erase(node);
        node = next_node;
    }

    if (above != 0) {
        T.children[above].push_back(G2);
        T.parent[G2] = above;
    } else {
        T.roots.insert(G2);
    }
}

ChainReduction chain_reduce(RootedBinaryForest& T1, RootedBinaryForest& T2,
                             const std::unordered_set<int>& leaves) {
    ChainReduction cr;
    auto chains = find_common_chains(T1, T2, leaves);
    for (auto& chain : chains) {
        _truncate_chain(T1, chain);
        _truncate_chain(T2, chain);
        cr.chain_map[chain[1]] = std::vector<int>(chain.begin()+2, chain.end());
    }
    return cr;
}

void restore_chain(RootedBinaryForest& graph, const ChainReduction& cr, int min_id = 0) {
    int min_in_graph = min_id;
    for (int n : graph.nodes) {
        if (n < 0 && n < min_in_graph) min_in_graph = n;
    }
    int next_id = min_in_graph - 1;
    if (min_id <= next_id) next_id = min_id - 1;

    auto fresh = [&]() -> int { return next_id--; };

    for (auto& [c3, removed] : cr.chain_map) {
        int p2 = graph.par(c3);
        int top = (p2 != 0) ? p2 : c3;
        int top_parent = graph.par(top);

        for (int ci : removed) {
            int new_node = fresh();
            graph.children[new_node] = {};
            graph.parent[new_node]   = 0;
            graph.nodes.insert(new_node);
            graph.children[ci] = {};
            graph.parent[ci]   = 0;
            graph.nodes.insert(ci);

            if (top_parent != 0) {
                auto& tc = graph.children[top_parent];
                tc.erase(std::find(tc.begin(), tc.end(), top));
                graph.parent[top] = 0;
            } else {
                graph.roots.erase(top);
            }

            graph.children[new_node] = {top, ci};
            graph.parent[top] = new_node;
            graph.parent[ci]  = new_node;

            if (top_parent != 0) {
                graph.children[top_parent].push_back(new_node);
                graph.parent[new_node] = top_parent;
            } else {
                graph.roots.insert(new_node);
            }
            top = new_node;
        }
    }
}

struct Cherry32Reduction {
    std::unordered_map<int,int> chain_32_map;
};

std::pair<int,int> _find_pendant_3_chain_for_x3(const RootedBinaryForest& T, int x3,
                                                  const std::unordered_set<int>& leaves) {
    auto pit = T.parent.find(x3);
    if (pit == T.parent.end() || pit->second == 0) return {0,0};
    int G2 = pit->second;
    const auto& G2ch = T.ch(G2);
    if (G2ch.size() != 2) return {0,0};
    int G1 = (G2ch[1] == x3) ? G2ch[0] : G2ch[1];
    if (leaves.count(G1)) return {0,0};
    const auto& G1ch = T.ch(G1);
    if (G1ch.size() != 2) return {0,0};
    int a = G1ch[0], b = G1ch[1];
    if (leaves.count(a) && leaves.count(b)) return {a, b};
    return {0,0};
}

std::vector<std::tuple<int,int,int,int>>
find_32_chains(const RootedBinaryForest& T1, const RootedBinaryForest& T2,
               const std::unordered_set<int>& leaves) {
    std::unordered_set<int> visited;
    std::vector<std::tuple<int,int,int,int>> result;

    for (int x3 : leaves) {
        if (visited.count(x3)) continue;
        bool found = false;
        for (int pass = 0; pass < 2 && !found; ++pass) {
            const RootedBinaryForest& Ta = (pass == 0) ? T1 : T2;
            const RootedBinaryForest& Tb = (pass == 0) ? T2 : T1;
            auto [x1, x2] = _find_pendant_3_chain_for_x3(Ta, x3, leaves);
            if (x1 == 0) continue;
            if (visited.count(x1) || visited.count(x2)) continue;
            auto pit = Tb.parent.find(x3);
            if (pit == Tb.parent.end() || pit->second == 0) continue;
            int P3 = pit->second;
            const auto& P3ch = Tb.ch(P3);
            if (P3ch.size() != 2) continue;
            int other = (P3ch[1] == x3) ? P3ch[0] : P3ch[1];
            if (other == x1 || other == x2) {
                visited.insert(x1); visited.insert(x2); visited.insert(x3);
                result.push_back({x1, x2, x3, other});
                found = true;
            }
        }
        if (!found) visited.insert(x3);
    }
    return result;
}

void _remove_leaf_and_suppress(RootedBinaryForest& T, int leaf) {
    int p = T.par(leaf);
    T.roots.erase(leaf);
    T.children.erase(leaf);
    T.parent.erase(leaf);
    T.nodes.erase(leaf);
    if (p == 0) return;
    auto& pc = T.children[p];
    pc.erase(std::find(pc.begin(), pc.end(), leaf));
    if (pc.size() == 1) {
        int child = pc[0];
        int gp = T.par(p);
        if (gp != 0) {
            auto& gc = T.children[gp];
            auto it = std::find(gc.begin(), gc.end(), p);
            *it = child;
            T.parent[child] = gp;
        } else {
            T.roots.erase(p);
            T.roots.insert(child);
            T.parent[child] = 0;
        }
        T.children.erase(p);
        T.parent.erase(p);
        T.nodes.erase(p);
        T.roots.erase(p);
    }
}

Cherry32Reduction chain_32_reduce(RootedBinaryForest& T1, RootedBinaryForest& T2,
                                   const std::unordered_set<int>& leaves) {
    Cherry32Reduction cr;
    auto chains = find_32_chains(T1, T2, leaves);
    for (auto& [x1, x2, dummy, xi] : chains) {
        int xj = (xi == x1) ? x2 : x1;
        _remove_leaf_and_suppress(T1, xj);
        _remove_leaf_and_suppress(T2, xj);
        cr.chain_32_map[xj] = xi;
    }
    return cr;
}

void restore_32chain(RootedBinaryForest& graph, const Cherry32Reduction& cr) {
    for (auto& [xj, xi] : cr.chain_32_map) {
        if (graph.nodes.count(xj)) {
            int old_parent = graph.par(xj);
            if (old_parent != 0) {
                auto& pc = graph.children[old_parent];
                pc.erase(std::find(pc.begin(), pc.end(), xj));
            } else {
                graph.roots.erase(xj);
            }
        }
        graph.children[xj] = {};
        graph.parent[xj]   = 0;
        graph.nodes.insert(xj);
        graph.roots.insert(xj);
    }
}

struct ReductionEntry {
    SubtreeReduction  sr;
    ChainReduction    cr;
    Cherry32Reduction c32;
};

bool is_agreement_forest(const RootedBinaryForest& rT1,
                         const RootedBinaryForest& T2_in,
                         const std::unordered_set<int>& leaves) {
    RootedBinaryForest rT2 = T2_in.copy();

    std::unordered_set<int> r_roots;
    r_roots.reserve(leaves.size() * 2);
    for (int l : leaves) r_roots.insert(find_root(rT1, l));

    std::unordered_map<int,int> cur_min;
    cur_min.reserve(rT1.nodes.size() * 2);
    get_min(rT1, leaves, cur_min);

    std::vector<int> lv;
    std::unordered_set<int> T1_leaves;
    std::unordered_map<int,int> T2_min;
    for (int T1_root : r_roots) {
        lv.clear();       all_leaves_tree(rT1, T1_root, lv);
        T1_leaves.clear(); T1_leaves.insert(lv.begin(), lv.end());
        int n_T1 = (int)T1_leaves.size();
        int T2_root = find_root(rT2, *T1_leaves.begin());
        auto [nl, T2r] = find_contracted_root(rT2, T2_root, T1_leaves, n_T1);
        T2_root = T2r;
        if (nl != n_T1) return false;
        T2_min.clear();
        _get_min(rT2, T2_root, T1_leaves, T2_min);
        if (!compare_trees(T1_root, rT1, cur_min, T2_root, rT2, T2_min, T1_leaves))
            return false;
        delete_subtree_leaves(rT2, T1_leaves, T2_root);
    }
    return true;
}

int count_components(const RootedBinaryForest& g, const std::unordered_set<int>& leaves) {
    std::unordered_set<int> roots;
    for (int l : leaves) roots.insert(find_root(g, l));
    return (int)roots.size();
}

static int compute_nodeblock(const RootedBinaryForest& T1, int node,
                             const std::unordered_map<int,int>& bol,
                             std::unordered_map<int,int>& nb) {
    if (T1.out_degree(node) == 0) {
        auto it = bol.find(node);
        int b = (it != bol.end()) ? it->second : INT_MIN;
        nb[node] = b;
        return b;
    }
    int agg = 0; bool first = true, mixed = false;
    for (int c : T1.successors(node)) {
        int cb = compute_nodeblock(T1, c, bol, nb);
        if (cb == INT_MIN) mixed = true;
        else if (first) { agg = cb; first = false; }
        else if (agg != cb) mixed = true;
    }
    int val = (mixed || first) ? INT_MIN : agg;
    nb[node] = val;
    return val;
}

RootedBinaryForest build_subforest_from_blocks(const RootedBinaryForest& T1,
        const std::unordered_map<int,int>& block_of_leaf) {
    std::unordered_map<int,int> nb;
    for (int root : T1.roots) compute_nodeblock(T1, root, block_of_leaf, nb);

    RootedBinaryForest result = create_empty_copy(T1);
    for (auto& e : T1.edges()) {
        int u = e.first, v = e.second;
        int bu = nb[u], bv = nb[v];
        if (bu != INT_MIN && bu == bv) result.add_edge(u, v);
    }
    return result;
}

struct Forest {
    int n = 0;
    int cap = 0;
    int next_internal = 0;
    std::vector<int> par;
    std::vector<int> c0, c1;
    std::vector<char> alive;

    void init(int n_, int cap_) {
        n = n_; cap = cap_; next_internal = n_ + 1;
        par.assign(cap + 1, 0);
        c0.assign(cap + 1, 0);
        c1.assign(cap + 1, 0);
        alive.assign(cap + 1, 0);
    }
    inline bool is_leaf(int v) const { return v <= n; }
    inline int  deg(int v) const { return (c0[v] != 0) + (c1[v] != 0); }

    int new_internal() {
        int v = next_internal++;
        alive[v] = 1; par[v] = 0; c0[v] = 0; c1[v] = 0;
        return v;
    }
    void activate_leaf(int leaf) {
        alive[leaf] = 1; par[leaf] = 0; c0[leaf] = 0; c1[leaf] = 0;
    }
    void attach(int p, int c) {
        if (c0[p] == 0) c0[p] = c; else c1[p] = c;
        par[c] = p;
    }
    inline int other_child(int p, int c) const { return c0[p] == c ? c1[p] : c0[p]; }
    void detach_child(int p, int c) {
        if (c0[p] == c) c0[p] = 0; else if (c1[p] == c) c1[p] = 0;
    }
    void replace_child(int p, int oldc, int newc) {
        if (c0[p] == oldc) c0[p] = newc; else if (c1[p] == oldc) c1[p] = newc;
        par[newc] = p;
    }
};

static int parse_newick(const std::string& s, Forest& G) {
    std::vector<int> st;
    int cur = 0, root = 0;
    std::string tok;
    auto flush_leaf = [&]() {
        if (!tok.empty()) {
            int leaf = std::stoi(tok);
            G.activate_leaf(leaf);
            if (cur) G.attach(cur, leaf);
            root = (cur ? root : leaf);
            tok.clear();
        }
    };
    for (char c : s) {
        if (c == '(') {
            int v = G.new_internal();
            if (cur) G.attach(cur, v);
            st.push_back(cur);
            cur = v;
        } else if (c == ',') {
            flush_leaf();
        } else if (c == ')') {
            flush_leaf();
            root = cur;
            cur = st.empty() ? 0 : st.back();
            if (!st.empty()) st.pop_back();
        } else if (c == ';' || c == ' ' || c == '\t' || c == '\n' || c == '\r') {
        } else {
            tok += c;
        }
    }
    flush_leaf();
    return root;
}

struct ChenInput {
    int n = 0;
    Forest T, F;
    int rootT = 0, rootF = 0;
    bool ok = false;
};

static ChenInput chen_read_input(std::istream& in) {
    ChenInput d;
    std::vector<std::string> newicks;
    int pending = 0;
    std::string line;
    while (std::getline(in, line)) {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (line.empty()) continue;
        if (line[0] == '#') {
            size_t s = line.find_first_not_of(" \t", 1);
            if (s == std::string::npos) continue;
            if (line[s] == 'p' && s + 1 < line.size() &&
                (line[s + 1] == ' ' || line[s + 1] == '\t')) {
                int k = 0, nn = 0;
                std::sscanf(line.c_str() + s + 1, "%d %d", &k, &nn);
                d.n = nn;
                pending = k;
            }
            continue;
        }
        if (pending > 0) { newicks.push_back(line); --pending; }
    }
    if (newicks.size() < 2 || d.n <= 0) return d;
    int cap = 2 * d.n + 2;
    d.T.init(d.n, cap);
    d.F.init(d.n, cap);
    d.rootT = parse_newick(newicks[0], d.T);
    d.rootF = parse_newick(newicks[1], d.F);
    d.ok = true;
    return d;
}

struct DSU {
    std::vector<int> p, sz;
    void init(int n) { p.resize(n + 1); sz.assign(n + 1, 1); for (int i = 0; i <= n; ++i) p[i] = i; }
    int find(int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }
    void unite(int a, int b) { a = find(a); b = find(b); if (a == b) return; p[b] = a; sz[a] += sz[b]; }
    int csize(int x) { return sz[find(x)]; }
};

static void remove_leaf(Forest& G, int v) {
    int p = G.par[v];
    G.alive[v] = 0; G.par[v] = 0;
    if (p == 0) return;
    G.detach_child(p, v);
    if (G.deg(p) == 1) {
        int c = G.c0[p] ? G.c0[p] : G.c1[p];
        int gp = G.par[p];
        if (gp != 0) G.replace_child(gp, p, c);
        else         G.par[c] = 0;
        G.alive[p] = 0; G.par[p] = 0; G.c0[p] = 0; G.c1[p] = 0;
    }
}

static int lca(const Forest& G, int a, int b, std::vector<int>& mark, int stamp) {
    for (int x = a; x != 0; x = G.par[x]) mark[x] = stamp;
    for (int x = b; x != 0; x = G.par[x]) if (mark[x] == stamp) return x;
    return 0;
}

static int pendant_count(const Forest& G, int a, int b, int l) {
    int cnt = 0;
    for (int x = a; x != l; x = G.par[x]) ++cnt;
    for (int x = b; x != l; x = G.par[x]) ++cnt;
    cnt -= 2;
    return cnt < 0 ? 0 : cnt;
}

static void cut_pendants(Forest& G, int a, int b, int l,
                         std::vector<int>& onpath, int stamp) {
    for (int x = a; ; x = G.par[x]) { onpath[x] = stamp; if (x == l) break; }
    for (int x = b; ; x = G.par[x]) { onpath[x] = stamp; if (x == l) break; }
    std::vector<int> inner;
    for (int x = a; x != l; x = G.par[x]) if (x != a) inner.push_back(x);
    for (int x = b; x != l; x = G.par[x]) if (x != b) inner.push_back(x);
    inner.push_back(l);
    for (int v : inner) {
        int cc[2] = { G.c0[v], G.c1[v] };
        for (int c : cc) {
            if (c != 0 && onpath[c] != stamp) {
                G.detach_child(v, c);
                G.par[c] = 0;
            }
        }
    }
    for (int v : inner) {
        if (!G.alive[v]) continue;
        if (G.deg(v) == 1) {
            int c = G.c0[v] ? G.c0[v] : G.c1[v];
            int gp = G.par[v];
            if (gp != 0) G.replace_child(gp, v, c);
            else         G.par[c] = 0;
            G.alive[v] = 0; G.par[v] = 0; G.c0[v] = 0; G.c1[v] = 0;
        }
    }
}

struct Validator {
    const Forest& T;
    const Forest& F;
    int n;
    std::vector<int> blockOf;
    Forest Fc;

    Validator(const Forest& T_, const Forest& F_, std::vector<int> blk)
        : T(T_), F(F_), n(T_.n), blockOf(std::move(blk)), Fc(F_) {}

    void leaves_under(const Forest& G, int r, int rep, std::vector<int>& out) {
        if (G.is_leaf(r)) { if (blockOf[r] == rep) out.push_back(r); return; }
        if (G.c0[r]) leaves_under(G, G.c0[r], rep, out);
        if (G.c1[r]) leaves_under(G, G.c1[r], rep, out);
    }

    int minleaf(const Forest& G, int r, const std::vector<char>& inS,
                std::vector<int>& cache) {
        if (G.is_leaf(r)) { int m = inS[r] ? r : INT_MAX_; cache[r] = m; return m; }
        int m = INT_MAX_;
        if (G.c0[r]) m = std::min(m, minleaf(G, G.c0[r], inS, cache));
        if (G.c1[r]) m = std::min(m, minleaf(G, G.c1[r], inS, cache));
        cache[r] = m;
        return m;
    }
    static const int INT_MAX_ = 0x3fffffff;

    void canon(const Forest& G, int r, const std::vector<char>& inS,
               const std::vector<int>& cache, std::string& out) {
        while (true) {
            if (G.is_leaf(r)) { out += std::to_string(r); return; }
            int a = G.c0[r], b = G.c1[r];
            int ma = a ? cache[a] : INT_MAX_;
            int mb = b ? cache[b] : INT_MAX_;
            bool ha = (ma != INT_MAX_), hb = (mb != INT_MAX_);
            if (ha && hb) break;
            if (ha) { r = a; continue; }
            if (hb) { r = b; continue; }
            out += '!'; return;
        }
        int a = G.c0[r], b = G.c1[r];
        if (cache[a] > cache[b]) std::swap(a, b);
        out += '(';
        canon(G, a, inS, cache, out);
        out += ',';
        canon(G, b, inS, cache, out);
        out += ')';
    }

    int root_of(const Forest& G, int v) { while (G.par[v] != 0) v = G.par[v]; return v; }

    std::pair<int,int> contracted_root(const Forest& G, int node,
                                       const std::vector<char>& inS, int need) {
        if (G.is_leaf(node)) return { inS[node] ? 1 : 0, node };
        int found = 0;
        if (G.c0[node]) {
            auto r = contracted_root(G, G.c0[node], inS, need);
            if (r.first == need) return r;
            found += r.first;
        }
        if (G.c1[node]) {
            auto r = contracted_root(G, G.c1[node], inS, need);
            if (r.first == need) return r;
            found += r.first;
        }
        return { found, node };
    }

    void delete_leaves(Forest& G, const std::vector<int>& S) {
        for (int leaf : S) if (G.alive[leaf]) remove_leaf(G, leaf);
    }

    bool valid() {
        std::vector<char> seen(n + 1, 0);
        for (int leaf = 1; leaf <= n; ++leaf) {
            if (seen[leaf]) continue;
            int rep = blockOf[leaf];
            std::vector<int> S;
            for (int x = 1; x <= n; ++x) if (blockOf[x] == rep) { S.push_back(x); seen[x] = 1; }
            std::vector<char> inS(n + 1, 0);
            for (int x : S) inS[x] = 1;
            int need = (int)S.size();

            int tr = root_of(T, S[0]);
            std::vector<int> tc(T.cap + 1, 0);
            minleaf(T, tr, inS, tc);
            std::string ts; canon(T, tr, inS, tc, ts);

            int fr0 = root_of(Fc, S[0]);
            auto cr = contracted_root(Fc, fr0, inS, need);
            if (cr.first != need) return false;
            int fr = cr.second;
            std::vector<int> fc(Fc.cap + 1, 0);
            minleaf(Fc, fr, inS, fc);
            std::string fs; canon(Fc, fr, inS, fc, fs);
            if (ts != fs) return false;

            delete_leaves(Fc, S);
        }
        return true;
    }
};

static int emit_forest(const Forest& T, const std::vector<int>& blockOf, std::string& out) {
    int n = T.n;
    std::vector<std::vector<int>> bucket(n + 1);
    for (int leaf = 1; leaf <= n; ++leaf) bucket[blockOf[leaf]].push_back(leaf);

    std::vector<int> vis(T.cap + 1, 0);
    std::vector<int> mk(T.cap + 1, 0);
    std::vector<std::pair<int,int>> es;
    int stamp = 0;
    int comps = 0;
    bool first = true;

    auto pair_lca = [&](int a, int b) -> int {
        ++stamp;
        for (int x = a; x != 0; x = T.par[x]) vis[x] = stamp;
        for (int x = b; x != 0; x = T.par[x]) if (vis[x] == stamp) return x;
        return a;
    };

    for (int rep = 1; rep <= n; ++rep) {
        auto& S = bucket[rep];
        if (S.empty()) continue;
        ++comps;
        if (!first) out += '\n';
        first = false;

        if (S.size() == 1) { out += std::to_string(S[0]); out += ';'; continue; }

        int l = S[0];
        for (size_t i = 1; i < S.size(); ++i) l = pair_lca(l, S[i]);
        int cstamp = ++stamp;
        for (int leaf : S)
            for (int x = leaf; ; x = T.par[x]) {
                if (mk[x] == cstamp) break;
                mk[x] = cstamp;
                if (x == l) break;
            }

        es.clear();
        es.push_back({l, 0});
        while (!es.empty()) {
            auto& top = es.back();
            int u = top.first;
            if (T.is_leaf(u)) { out += std::to_string(u); es.pop_back(); continue; }
            int c0 = (T.c0[u] && mk[T.c0[u]] == cstamp) ? T.c0[u] : 0;
            int c1 = (T.c1[u] && mk[T.c1[u]] == cstamp) ? T.c1[u] : 0;
            if (c0 && c1) {
                if (top.second == 0) { out += '('; top.second = 1; es.push_back({c0, 0}); }
                else if (top.second == 1) { out += ','; top.second = 2; es.push_back({c1, 0}); }
                else { out += ')'; es.pop_back(); }
            } else {
                int c = c0 ? c0 : c1;
                es.pop_back();
                es.push_back({c, 0});
            }
        }
        out += ';';
    }
    return comps;
}

struct ChenSolver {
    int origN;
    const Forest& masterT;
    const Forest& masterF;

    Forest kT, kF;
    int m = 0;
    std::vector<int> mapToKernel;

    std::vector<int> bestBlock;
    int bestComps;

    std::mt19937 rng;

    ChenSolver(const Forest& T, const Forest& F)
        : origN(T.n), masterT(T), masterF(F), rng(0xC0FFEEu) {
        kernelize();
        bestBlock.resize(m + 1);
        for (int i = 0; i <= m; ++i) bestBlock[i] = i;
        bestComps = m;
    }

    void kernelize() {
        Forest wT = masterT, wF = masterF;
        std::vector<int> uf(origN + 1);
        for (int i = 0; i <= origN; ++i) uf[i] = i;
        std::function<int(int)> find = [&](int x) {
            while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; }
            return x;
        };

        std::vector<int> stk;
        for (int v = origN + 1; v <= wT.cap; ++v)
            if (wT.alive[v] && wT.deg(v) == 2 && wT.is_leaf(wT.c0[v]) && wT.is_leaf(wT.c1[v]))
                stk.push_back(v);
        while (!stk.empty()) {
            int p = stk.back(); stk.pop_back();
            if (!wT.alive[p] || wT.deg(p) != 2) continue;
            int a = wT.c0[p], b = wT.c1[p];
            if (!wT.is_leaf(a) || !wT.is_leaf(b)) continue;
            int pa = wF.par[a], pb = wF.par[b];
            if (pa != 0 && pa == pb && wF.deg(pa) == 2) {
                uf[find(b)] = find(a);
                remove_leaf(wT, b);
                remove_leaf(wF, b);
                int q = wT.par[a];
                if (q != 0 && wT.is_leaf(wT.other_child(q, a))) stk.push_back(q);
            }
        }

        std::vector<int> newLeaf(origN + 1, 0);
        m = 0;
        for (int l = 1; l <= origN; ++l) if (wT.alive[l]) newLeaf[l] = ++m;
        mapToKernel.assign(origN + 1, 0);
        for (int l = 1; l <= origN; ++l) mapToKernel[l] = newLeaf[find(l)];

        kT.init(m, 2 * m + 2);
        kF.init(m, 2 * m + 2);
        for (int i = 1; i <= m; ++i) { kT.activate_leaf(i); kF.activate_leaf(i); }
        build_compact(wT, newLeaf, kT);
        build_compact(wF, newLeaf, kF);
    }

    void build_compact(const Forest& w, const std::vector<int>& newLeaf, Forest& k) {
        std::vector<int> nid(w.cap + 1, 0);
        for (int l = 1; l <= origN; ++l) if (newLeaf[l]) nid[l] = newLeaf[l];
        int nxt = m + 1;
        for (int v = origN + 1; v <= w.cap; ++v) if (w.alive[v]) nid[v] = nxt++;
        for (int v = origN + 1; v <= w.cap; ++v) {
            if (!w.alive[v]) continue;
            int kv = nid[v]; k.alive[kv] = 1; k.par[kv] = 0; k.c0[kv] = 0; k.c1[kv] = 0;
        }
        for (int v = 1; v <= w.cap; ++v) {
            if (!w.alive[v] || !nid[v]) continue;
            int kv = nid[v];
            k.par[kv] = w.par[v] ? nid[w.par[v]] : 0;
            k.c0[kv]  = w.c0[v]  ? nid[w.c0[v]]  : 0;
            k.c1[kv]  = w.c1[v]  ? nid[w.c1[v]]  : 0;
        }
    }

    std::vector<int> descend(int pathThresh, bool randomize) {
        Forest Tt = kT;
        Forest Ff = kF;
        DSU dsu; dsu.init(m);

        std::vector<int> onpath(Tt.cap + 1, 0);
        std::vector<int> mark(Ff.cap + 1, 0);
        int stamp = 1;

        std::vector<int> stack;
        stack.reserve(m);
        for (int v = m + 1; v <= Tt.cap; ++v)
            if (Tt.alive[v] && Tt.deg(v) == 2 && Tt.is_leaf(Tt.c0[v]) && Tt.is_leaf(Tt.c1[v]))
                stack.push_back(v);

        auto push_parent = [&](Forest& G, int leaf) {
            int p = G.par[leaf];
            if (p != 0 && G.is_leaf(G.other_child(p, leaf)))
                stack.push_back(p);
        };

        while (!stack.empty()) {
            if (g_stop) break;
            int p = stack.back(); stack.pop_back();
            if (!Tt.alive[p] || Tt.deg(p) != 2) continue;
            int a = Tt.c0[p], b = Tt.c1[p];
            if (!Tt.is_leaf(a) || !Tt.is_leaf(b)) continue;

            int pa = Ff.par[a], pb = Ff.par[b];
            if (pa != 0 && pa == pb && Ff.deg(pa) == 2) {
                dsu.unite(a, b);
                remove_leaf(Tt, b);
                remove_leaf(Ff, b);
                push_parent(Tt, a);
                continue;
            }

            int l = lca(Ff, a, b, mark, stamp++);
            if (l == 0) {
                int cut = (dsu.csize(a) <= dsu.csize(b)) ? a : b;
                if (randomize && (rng() & 1u)) cut = (cut == a ? b : a);
                int keep = (cut == a ? b : a);
                remove_leaf(Tt, cut);
                remove_leaf(Ff, cut);
                push_parent(Tt, keep);
            } else {
                int np = pendant_count(Ff, a, b, l);
                bool do_path = (np <= pathThresh);
                if (randomize && !do_path && np <= pathThresh + 3)
                    do_path = (rng() & 1u);
                if (do_path) {
                    cut_pendants(Ff, a, b, l, onpath, stamp++);
                    dsu.unite(a, b);
                    remove_leaf(Tt, b);
                    remove_leaf(Ff, b);
                    push_parent(Tt, a);
                } else {
                    int cut = (dsu.csize(a) <= dsu.csize(b)) ? a : b;
                    if (randomize && (rng() & 1u)) cut = (cut == a ? b : a);
                    int keep = (cut == a ? b : a);
                    remove_leaf(Tt, cut);
                    remove_leaf(Ff, cut);
                    push_parent(Tt, keep);
                }
            }
        }

        std::vector<int> block(m + 1);
        for (int i = 1; i <= m; ++i) block[i] = dsu.find(i);
        return block;
    }

    int count_comps(const std::vector<int>& block) {
        std::vector<char> seen(m + 1, 0);
        int c = 0;
        for (int i = 1; i <= m; ++i) if (!seen[block[i]]) { seen[block[i]] = 1; ++c; }
        return c;
    }

    std::vector<int> expand(const std::vector<int>& kblock) const {
        std::vector<int> fb(origN + 1, 0);
        for (int l = 1; l <= origN; ++l) fb[l] = kblock[mapToKernel[l]];
        return fb;
    }

    void consider(std::vector<int>& block) {
        int c = count_comps(block);
        if (c >= bestComps) return;
#ifdef VALIDATE
        std::vector<int> fb = expand(block);
        Validator V(masterT, masterF, fb);
        if (!V.valid()) return;
#endif
        bestBlock = block;
        bestComps = c;
    }

    void run() {
        if (m <= 1) return;
        {
            auto b = descend(1, false);
            if (g_stop) return;
            consider(b);
        }
        int thresh = 1;
        while (!g_stop) {
            auto b = descend(thresh, true);
            if (g_stop) return;
            consider(b);
            thresh = 1 + (int)(rng() % 4);
        }
    }
};

struct Tree {
    int n = 0;
    int root = -1;
    int numNodes = 0;
    std::vector<int> par;
    std::vector<int> cl, cr;
    std::vector<int> tin, tout, dep;
    std::vector<int> post;

    std::vector<int> euler;
    std::vector<int> first;
    std::vector<int> logtab;
    std::vector<std::vector<int>> sparse;

    void resize(int maxId) {
        numNodes = maxId;
        par.assign(maxId + 1, 0);
        cl.assign(maxId + 1, -1);
        cr.assign(maxId + 1, -1);
        tin.assign(maxId + 1, 0);
        tout.assign(maxId + 1, 0);
        dep.assign(maxId + 1, 0);
        first.assign(maxId + 1, -1);
    }

    void build() {
        euler.clear();
        euler.reserve(2 * numNodes);
        post.clear();
        post.reserve(numNodes);
        int timer = 0;
        std::vector<std::pair<int,int>> st;
        st.reserve(numNodes);
        st.push_back({root, 0});
        dep[root] = 0;
        first[root] = -1;
        tin[root] = timer++;
        euler.push_back(root);
        if (first[root] < 0) first[root] = (int)euler.size() - 1;
        while (!st.empty()) {
            auto &top = st.back();
            int v = top.first;
            int &ci = top.second;
            int child = -1;
            if (ci == 0) { child = cl[v]; }
            else if (ci == 1) { child = cr[v]; }
            ci++;
            if (child != -1) {
                dep[child] = dep[v] + 1;
                tin[child] = timer++;
                st.push_back({child, 0});
                euler.push_back(child);
                if (first[child] < 0) first[child] = (int)euler.size() - 1;
            } else if (ci > 2) {
                tout[v] = timer++;
                post.push_back(v);
                st.pop_back();
                if (!st.empty()) euler.push_back(st.back().first);
            }
        }
        buildSparse();
    }

    void buildSparse() {
        int m = (int)euler.size();
        logtab.assign(m + 1, 0);
        for (int i = 2; i <= m; i++) logtab[i] = logtab[i / 2] + 1;
        int K = logtab[m] + 1;
        sparse.assign(K, std::vector<int>(m));
        for (int i = 0; i < m; i++) sparse[0][i] = euler[i];
        for (int k = 1; k < K; k++) {
            int len = 1 << k;
            for (int i = 0; i + len <= m; i++) {
                int a = sparse[k - 1][i];
                int b = sparse[k - 1][i + (len >> 1)];
                sparse[k][i] = (dep[a] <= dep[b]) ? a : b;
            }
        }
    }

    int lca(int u, int v) const {
        if (u == v) return u;
        int a = first[u], b = first[v];
        if (a > b) std::swap(a, b);
        int k = logtab[b - a + 1];
        int x = sparse[k][a];
        int y = sparse[k][b - (1 << k) + 1];
        return (dep[x] <= dep[y]) ? x : y;
    }

    inline bool isAnc(int a, int b) const {
        return tin[a] <= tin[b] && tout[b] <= tout[a];
    }
};

static Tree parseNewick(const std::string &s, int n) {
    Tree T;
    T.n = n;
    int maxId = 2 * n + 5;
    T.resize(maxId);
    int nextInternal = n + 1;
    std::vector<int> stack;
    int curParent = 0;
    std::string tok;
    int lastNode = -1;

    auto flushLeaf = [&](void) {
        if (!tok.empty()) {
            int leaf = std::atoi(tok.c_str());
            tok.clear();
            if (curParent != 0) {
                if (T.cl[curParent] == -1) T.cl[curParent] = leaf;
                else T.cr[curParent] = leaf;
                T.par[leaf] = curParent;
            }
            lastNode = leaf;
        }
    };

    for (char c : s) {
        if (c == '(') {
            int node = nextInternal++;
            if (curParent != 0) {
                if (T.cl[curParent] == -1) T.cl[curParent] = node;
                else T.cr[curParent] = node;
                T.par[node] = curParent;
            }
            stack.push_back(curParent);
            curParent = node;
            lastNode = node;
        } else if (c == ',') {
            flushLeaf();
        } else if (c == ')') {
            flushLeaf();
            lastNode = curParent;
            curParent = stack.back();
            stack.pop_back();
        } else if (c == ';' || std::isspace((unsigned char)c)) {
        } else {
            tok += c;
        }
    }
    flushLeaf();
    T.numNodes = nextInternal - 1;
    T.root = lastNode;
    for (int v = 1; v <= T.numNodes; v++) {
        if (T.par[v] == 0) { T.root = v; break; }
    }
    T.build();
    return T;
}

struct Input {
    int nTrees = 0, nLeaves = 0;
    std::vector<std::string> newicks;
};

static Input readInput(std::istream &in) {
    Input inp;
    std::string line;
    int pending = 0;
    while (std::getline(in, line)) {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (line.empty()) continue;
        if (line[0] == '#') {
            size_t i = 1;
            while (i < line.size() && std::isspace((unsigned char)line[i])) i++;
            if (i < line.size() && line[i] == 'p') {
                std::istringstream ss(line.substr(i + 1));
                ss >> inp.nTrees >> inp.nLeaves;
                pending = inp.nTrees;
            }
            continue;
        }
        if (pending > 0) {
            inp.newicks.push_back(line);
            pending--;
        }
    }
    return inp;
}

static void inducedNewick(const Tree &T, std::vector<int> leaves, std::string &out) {
    if (leaves.size() == 1) { out += std::to_string(leaves[0]); return; }
    std::sort(leaves.begin(), leaves.end(),
              [&](int a, int b) { return T.tin[a] < T.tin[b]; });

    std::vector<int> nodes = leaves;
    for (size_t i = 0; i + 1 < leaves.size(); i++)
        nodes.push_back(T.lca(leaves[i], leaves[i + 1]));
    std::sort(nodes.begin(), nodes.end(),
              [&](int a, int b) { return T.tin[a] < T.tin[b]; });
    nodes.erase(std::unique(nodes.begin(), nodes.end()), nodes.end());

    std::vector<int> vpar(nodes.size(), -1);
    std::vector<std::vector<int>> vchild(nodes.size());
    std::vector<int> stk;
    auto idxOf = [&](int id) {
        int lo = 0, hi = (int)nodes.size() - 1;
        while (lo <= hi) {
            int mid = (lo + hi) / 2;
            if (T.tin[nodes[mid]] == T.tin[id]) return mid;
            if (T.tin[nodes[mid]] < T.tin[id]) lo = mid + 1; else hi = mid - 1;
        }
        return -1;
    };
    for (size_t i = 0; i < nodes.size(); i++) {
        int v = nodes[i];
        while (!stk.empty() && !T.isAnc(stk.back(), v)) stk.pop_back();
        if (!stk.empty()) {
            int p = stk.back();
            vpar[i] = idxOf(p);
            vchild[idxOf(p)].push_back((int)i);
        }
        stk.push_back(v);
    }
    int vroot = 0;
    for (size_t i = 0; i < nodes.size(); i++) if (vpar[i] == -1) { vroot = (int)i; break; }

    std::vector<int> order;
    std::string res;
    std::function<void(int)> emit = [&](int i) {
        if (vchild[i].empty()) { res += std::to_string(nodes[i]); return; }
        res += '(';
        for (size_t k = 0; k < vchild[i].size(); k++) {
            if (k) res += ',';
            emit(vchild[i][k]);
        }
        res += ')';
    };
    emit(vroot);
    out += res;
}

enum { COL_R = 0, COL_B = 1, COL_W = 2 };

struct RedBlueSolver {
    const Tree &T1, &T2;
    int n;

    std::vector<int> comp;
    std::vector<std::vector<int>> members;

    std::vector<char> col;

    std::vector<int> A2, s2, sR, sB, sW;
    bool overlap2 = false;

    std::vector<int> A1, s1, phat;
    std::vector<char> isRoot, hasRootBelow;

    int maxNode;

    RedBlueSolver(const Tree &t1, const Tree &t2, int n_)
        : T1(t1), T2(t2), n(n_) {
        maxNode = std::max(T1.numNodes, T2.numNodes) + 2;
        comp.assign(n + 1, -1);
        col.assign(n + 1, COL_W);
        A2.assign(maxNode, -1); s2.assign(maxNode, 0);
        sR.assign(maxNode, 0);  sB.assign(maxNode, 0); sW.assign(maxNode, 0);
        A1.assign(maxNode, -1); s1.assign(maxNode, 0); phat.assign(maxNode, -1);
        isRoot.assign(maxNode, 0); hasRootBelow.assign(maxNode, 0);
    }

    inline int csz(int c) const { return (int)members[c].size(); }

    void initSingleComponent() {
        members.clear();
        members.emplace_back();
        members[0].reserve(n);
        for (int l = 1; l <= n; l++) { comp[l] = 0; members[0].push_back(l); }
    }

    int lca2set(const std::vector<int> &v) const {
        if (v.empty()) return -1;
        int a = v[0];
        for (size_t i = 1; i < v.size(); i++) a = T2.lca(a, v[i]);
        return a;
    }
    inline bool isAnc2(int a, int b) const { return a >= 0 && b >= 0 && T2.isAnc(a, b); }

    void t2pass(bool withColor) {
        overlap2 = false;
        for (int v : T2.post) {
            if (T2.cl[v] == -1) {
                int c = comp[v];
                A2[v] = c; s2[v] = 1;
                if (withColor) {
                    sR[v] = (col[v] == COL_R);
                    sB[v] = (col[v] == COL_B);
                    sW[v] = (col[v] == COL_W);
                }
                continue;
            }
            int a = T2.cl[v], b = T2.cr[v];
            int ua = (A2[a] >= 0 && s2[a] < csz(A2[a])) ? A2[a] : -1;
            int ub = (A2[b] >= 0 && s2[b] < csz(A2[b])) ? A2[b] : -1;
            int Av, sv, rr = 0, bb = 0, ww = 0;
            if (ua >= 0 && ub >= 0) {
                if (ua != ub) overlap2 = true;
                Av = ua; sv = s2[a] + s2[b];
                if (withColor) { rr = sR[a] + sR[b]; bb = sB[a] + sB[b]; ww = sW[a] + sW[b]; }
            } else if (ua >= 0) {
                Av = ua; sv = s2[a];
                if (withColor) { rr = sR[a]; bb = sB[a]; ww = sW[a]; }
            } else if (ub >= 0) {
                Av = ub; sv = s2[b];
                if (withColor) { rr = sR[b]; bb = sB[b]; ww = sW[b]; }
            } else {
                Av = -1; sv = 0;
            }
            A2[v] = Av; s2[v] = sv;
            if (withColor) { sR[v] = rr; sB[v] = bb; sW[v] = ww; }
        }
    }

    int t1rootPass(std::mt19937 &rng, bool randomized) {
        std::vector<int> lows;
        for (int v : T1.post) {
            if (T1.cl[v] == -1) {
                A1[v] = comp[v]; s1[v] = 1; phat[v] = v;
                isRoot[v] = 0; hasRootBelow[v] = 0;
                continue;
            }
            int a = T1.cl[v], b = T1.cr[v];
            int ua = (A1[a] >= 0 && s1[a] < csz(A1[a])) ? A1[a] : -1;
            int ub = (A1[b] >= 0 && s1[b] < csz(A1[b])) ? A1[b] : -1;
            isRoot[v] = 0;
            if (ua >= 0 && ub >= 0) {
                if (ua != ub) {
                    isRoot[v] = 1;
                    A1[v] = ua; s1[v] = s1[a] + s1[b]; phat[v] = T2.lca(phat[a], phat[b]);
                } else {
                    int A = ua;
                    A1[v] = A; s1[v] = s1[a] + s1[b];
                    int pu = T2.lca(phat[a], phat[b]); phat[v] = pu;
                    if (phat[a] == pu || phat[b] == pu) {
                        isRoot[v] = 1;
                    } else if (s1[v] < csz(A) && A2[pu] == A && s2[pu] == csz(A)) {
                        isRoot[v] = 1;
                    }
                }
            } else if (ua >= 0) {
                A1[v] = ua; s1[v] = s1[a]; phat[v] = phat[a];
            } else if (ub >= 0) {
                A1[v] = ub; s1[v] = s1[b]; phat[v] = phat[b];
            } else {
                A1[v] = -1; s1[v] = 0; phat[v] = -1;
            }
            hasRootBelow[v] = (isRoot[a] || hasRootBelow[a] || isRoot[b] || hasRootBelow[b]);
            if (isRoot[v] && !hasRootBelow[v]) lows.push_back(v);
        }
        if (lows.empty()) return -1;
        if (!randomized) return lows[0];
        return lows[rng() % lows.size()];
    }

    void setColors(int u, bool swapRB) {
        int ca = T1.cl[u], cb = T1.cr[u];
        if (swapRB) std::swap(ca, cb);
        for (int l = 1; l <= n; l++) {
            if (T1.isAnc(ca, l)) col[l] = COL_R;
            else if (T1.isAnc(cb, l)) col[l] = COL_B;
            else col[l] = COL_W;
        }
    }

    void splitByAnc2(int c, int u2) {
        std::vector<int> stay, go;
        for (int l : members[c]) {
            if (T2.isAnc(u2, l)) go.push_back(l);
            else stay.push_back(l);
        }
        if (go.empty() || stay.empty()) return;
        int nc = (int)members.size();
        members.push_back(go);
        for (int l : go) comp[l] = nc;
        members[c] = stay;
    }

    void splitByGroups(int c, std::vector<std::vector<int>> groups) {
        bool firstAssigned = false;
        for (auto &g : groups) {
            if (g.empty()) continue;
            if (!firstAssigned) {
                for (int l : g) comp[l] = c;
                members[c] = g;
                firstAssigned = true;
            } else {
                int nc = (int)members.size();
                for (int l : g) comp[l] = nc;
                members.push_back(std::move(g));
            }
        }
    }

    void makeRBcompatible() {
        while (!g_stop) {
            t2pass(true);
            std::vector<int> lowestBC(members.size(), -1);
            for (int v : T2.post) {
                int c = A2[v];
                if (c >= 0 && sR[v] >= 1 && sB[v] >= 1 && lowestBC[c] == -1)
                    lowestBC[c] = v;
            }
            int target = -1, node = -1;
            for (int c = 0; c < (int)members.size(); c++) {
                if (lowestBC[c] == -1) continue;
                std::vector<int> reds, blues;
                for (int l : members[c]) {
                    if (col[l] == COL_R) reds.push_back(l);
                    else if (col[l] == COL_B) blues.push_back(l);
                }
                int rR = lca2set(reds), rB = lca2set(blues);
                if (rR >= 0 && rB >= 0 && (isAnc2(rR, rB) || isAnc2(rB, rR))) {
                    target = c; node = lowestBC[c]; break;
                }
            }
            if (target == -1) break;
            splitByAnc2(target, node);
        }
    }

    void colorTotals(std::vector<int> &cR, std::vector<int> &cB, std::vector<int> &cW) {
        cR.assign(members.size(), 0);
        cB.assign(members.size(), 0);
        cW.assign(members.size(), 0);
        for (int l = 1; l <= n; l++) {
            int c = comp[l];
            if (col[l] == COL_R) cR[c]++;
            else if (col[l] == COL_B) cB[c]++;
            else cW[c]++;
        }
    }

    void makeSplittable() {
        while (!g_stop) {
            t2pass(true);
            std::vector<int> cR, cB, cW;
            colorTotals(cR, cB, cW);
            int target = -1, node = -1;
            for (int v : T2.post) {
                int c = A2[v];
                if (c < 0) continue;
                int nc = (sR[v] > 0) + (sB[v] > 0) + (sW[v] > 0);
                if (nc != 2) continue;
                bool ok = true;
                if (cR[c] > 0 && !(sR[v] < cR[c])) ok = false;
                if (cB[c] > 0 && !(sB[v] < cB[c])) ok = false;
                if (cW[c] > 0 && !(sW[v] < cW[c])) ok = false;
                if (ok) { target = c; node = v; break; }
            }
            if (target == -1) break;
            splitByAnc2(target, node);
        }
    }

    void splitProc() {
        t2pass(true);
        std::vector<int> cR, cB, cW;
        colorTotals(cR, cB, cW);
        std::vector<int> multis;
        for (int c = 0; c < (int)members.size(); c++) {
            int nc = (cR[c] > 0) + (cB[c] > 0) + (cW[c] > 0);
            if (nc >= 2) multis.push_back(c);
        }
        for (int c : multis) {
            std::vector<int> reds, blues, whites;
            for (int l : members[c]) {
                if (col[l] == COL_R) reds.push_back(l);
                else if (col[l] == COL_B) blues.push_back(l);
                else whites.push_back(l);
            }
            int nc = (!reds.empty()) + (!blues.empty()) + (!whites.empty());
            if (nc == 3) {
                int uR = lca2set(reds), uB = lca2set(blues);
                int u2 = T2.lca(uR, uB);
                int countBelow = 0;
                for (int l : members[c]) if (T2.isAnc(u2, l)) countBelow++;
                if (countBelow < csz(c)) {
                    int sWbelow = 0;
                    for (int l : whites) if (T2.isAnc(u2, l)) sWbelow++;
                    if (sWbelow == 0) {
                        std::vector<int> bw = blues; bw.insert(bw.end(), whites.begin(), whites.end());
                        splitByGroups(c, {reds, bw});
                    } else {
                        std::vector<int> aout, aR, aB, aW;
                        for (int l : members[c]) {
                            if (T2.isAnc(u2, l)) {
                                if (col[l] == COL_R) aR.push_back(l);
                                else if (col[l] == COL_B) aB.push_back(l);
                                else aW.push_back(l);
                            } else aout.push_back(l);
                        }
                        splitByGroups(c, {aout, aR, aB, aW});
                    }
                    continue;
                }
            }
            splitByGroups(c, {reds, blues, whites});
        }
    }

    bool isFeasible(std::mt19937 &rng) {
        t2pass(false);
        if (overlap2) return false;
        return t1rootPass(rng, false) == -1;
    }

    bool redBlue(std::mt19937 &rng, bool randomized) {
        initSingleComponent();
        long cap = 4L * n + 16;
        long it = 0;
        while (true) {
            if (g_stop) return false;
            t2pass(false);
            int u = t1rootPass(rng, randomized);
            if (u == -1) return true;
            bool swapRB = randomized && (rng() & 1u);
            setColors(u, swapRB);
            makeRBcompatible();
            makeSplittable();
            splitProc();
            if (++it > cap) { forceResolve(rng); return !g_stop; }
        }
    }

    void forceResolve(std::mt19937 &rng) {
        while (!g_stop) {
            t2pass(false);
            int u = t1rootPass(rng, false);
            if (u == -1) break;
            int ca = T1.cl[u];
            for (int l = 1; l <= n; l++) {
                if (T1.isAnc(ca, l) && members[comp[l]].size() > 1) {
                    int c = comp[l];
                    std::vector<int> rest;
                    for (int x : members[c]) if (x != l) rest.push_back(x);
                    int nc = (int)members.size();
                    members.push_back({l});
                    comp[l] = nc;
                    members[c] = rest;
                }
            }
        }
    }

    void mergePhase(std::mt19937 &rng) {
        bool changed = true;
        int rounds = 0;
        while (changed && !g_stop && rounds++ < 2 * n) {
            changed = false;
            for (int v : T1.post) {
                if (T1.cl[v] == -1) { A1[v] = comp[v]; s1[v] = 1; continue; }
                int a = T1.cl[v], b = T1.cr[v];
                int ua = (A1[a] >= 0 && s1[a] < csz(A1[a])) ? A1[a] : -1;
                int ub = (A1[b] >= 0 && s1[b] < csz(A1[b])) ? A1[b] : -1;
                if (ua >= 0 && ub >= 0) { A1[v] = ua; s1[v] = s1[a] + s1[b]; }
                else if (ua >= 0) { A1[v] = ua; s1[v] = s1[a]; }
                else if (ub >= 0) { A1[v] = ub; s1[v] = s1[b]; }
                else { A1[v] = -1; s1[v] = 0; }
            }
            std::vector<std::pair<int,int>> cand;
            for (int c = 0; c < (int)members.size(); c++) {
                if (members[c].empty()) continue;
                int r1 = members[c][0];
                for (int l : members[c]) r1 = T1.lca(r1, l);
                int p = T1.par[r1];
                while (p != 0 && (A1[p] == c || A1[p] < 0)) p = T1.par[p];
                if (p != 0 && A1[p] >= 0 && A1[p] != c)
                    cand.push_back({c, A1[p]});
            }
            for (auto &pr : cand) {
                if (g_stop) return;
                int c1 = pr.first, c2 = pr.second;
                if (members[c1].empty() || members[c2].empty()) continue;
                if (c1 == c2) continue;
                std::vector<int> saved2 = members[c2];
                for (int l : saved2) comp[l] = c1;
                members[c1].insert(members[c1].end(), saved2.begin(), saved2.end());
                members[c2].clear();
                if (isFeasible(rng)) {
                    changed = true;
                } else {
                    for (int l : saved2) comp[l] = c2;
                    members[c2] = saved2;
                    std::vector<int> back;
                    for (int l : members[c1]) if (comp[l] == c1) back.push_back(l);
                    members[c1] = back;
                }
            }
        }
    }

    int numComponents() const {
        int cnt = 0;
        for (auto &m : members) if (!m.empty()) cnt++;
        return cnt;
    }

    std::vector<int> snapshot() const { return comp; }
};

static std::string renderForest(const Tree &T1, int n, const std::vector<int> &comp) {
    int maxc = 0;
    for (int l = 1; l <= n; l++) maxc = std::max(maxc, comp[l]);
    std::vector<std::vector<int>> grp(maxc + 1);
    for (int l = 1; l <= n; l++) grp[comp[l]].push_back(l);
    std::string out;
    bool first = true;
    for (auto &g : grp) {
        if (g.empty()) continue;
        if (!first) out += '\n';
        first = false;
        inducedNewick(T1, g, out);
        out += ';';
    }
    return out;
}

struct Reducer {
    RootedBinaryForest T1, T2;
    std::unordered_set<int> orig_leaves, leaves;
    std::vector<ReductionEntry> reduction_stack;
    Reducer(RootedBinaryForest t1, RootedBinaryForest t2, std::unordered_set<int> lv)
        : T1(std::move(t1)), T2(std::move(t2)), orig_leaves(lv), leaves(lv) { _reduce(); }

    void _reduce() {
        while (true) {
            while (true) {
                auto c32 = chain_32_reduce(T1, T2, leaves);
                bool has_c32 = !c32.chain_32_map.empty();
                if (has_c32) {
                    for (auto& [xj, xi] : c32.chain_32_map) leaves.erase(xj);
                    reduction_stack.push_back({{}, {}, std::move(c32)});
                }
                auto cr = chain_reduce(T1, T2, leaves);
                bool has_cr = !cr.chain_map.empty();
                if (has_cr) {
                    for (auto& [c2, removed] : cr.chain_map)
                        for (int r : removed) leaves.erase(r);
                    reduction_stack.push_back({{}, std::move(cr), {}});
                }
                if (!has_c32 && !has_cr) break;
            }
            auto sr = subtree_reduce(T1, T2, leaves);
            if (sr.replace_map.empty()) break;
            for (auto& [leaf, tree] : sr.replace_map) {
                std::vector<int> lv; all_leaves_tree(tree, *tree.roots.begin(), lv);
                for (int l : lv) if (l != leaf) leaves.erase(l);
            }
            reduction_stack.push_back({std::move(sr), {}, {}});
        }
    }

    std::string prepare_solution(const RootedBinaryForest& graph_in) {
        RootedBinaryForest graph = graph_in.copy();

        int all_subtree_min = 0;
        for (auto& entry : reduction_stack)
            for (auto& [leaf, tree] : entry.sr.replace_map)
                for (int n : tree.nodes)
                    if (n < 0 && n < all_subtree_min) all_subtree_min = n;

        for (int i = (int)reduction_stack.size()-1; i >= 0; --i) {
            restore_32chain(graph, reduction_stack[i].c32);
            restore_chain(graph, reduction_stack[i].cr, all_subtree_min);
            restore_subtree(graph, reduction_stack[i].sr);
        }

        std::unordered_set<int> visited;
        std::vector<std::string> out_trees;
        for (int leaf : orig_leaves) {
            if (visited.count(leaf)) continue;
            int root = find_root(graph, leaf);
            root = remove_contract_rooted(graph, orig_leaves, root);
            std::vector<int> lv; all_leaves_tree(graph, root, lv);
            visited.insert(lv.begin(), lv.end());
            out_trees.push_back(tree_to_newick_print(graph, root));
        }
        std::string out;
        for (int i = 0; i < (int)out_trees.size(); ++i) {
            if (i) out += '\n';
            out += out_trees[i];
        }
        return out;
    }

};

static Tree buildTreeFromRBF(const RootedBinaryForest &g, int root,
                             const std::unordered_map<int,int> &fwd, int m) {
    Tree T;
    T.n = m;
    T.resize(2 * m + 5);
    int nextInternal = m + 1;
    std::function<int(int)> rec = [&](int node) -> int {
        const auto &ch = g.children.at(node);
        if (ch.empty()) return fwd.at(node);
        std::vector<int> kids;
        for (int c : ch) kids.push_back(c);
        if (kids.size() == 1) return rec(kids[0]);
        int me = nextInternal++;
        int a = rec(kids[0]);
        int b = rec(kids[1]);
        T.cl[me] = a; T.par[a] = me;
        T.cr[me] = b; T.par[b] = me;
        return me;
    };
    int r = rec(root);
    T.root = r;
    T.numNodes = nextInternal - 1;
    if (T.numNodes < m) T.numNodes = m;
    T.build();
    return T;
}

static void coverRBF(const RootedBinaryForest &T, int node,
                     const std::unordered_map<int,int> &block,
                     const std::unordered_map<int,int> &size,
                     std::unordered_map<int,int> &A, std::unordered_map<int,long> &s) {
    const auto &ch = T.children.at(node);
    if (ch.empty()) {
        auto it = block.find(node);
        A[node] = (it != block.end()) ? it->second : -1;
        s[node] = 1;
        return;
    }
    for (int c : ch) coverRBF(T, c, block, size, A, s);
    int chosen = -1; long tot = 0;
    for (int c : ch) {
        int ac = A[c];
        if (ac != -1) {
            auto sit = size.find(ac);
            long sz = (sit != size.end()) ? sit->second : 0;
            if (s[c] < sz) {
                if (chosen == -1) chosen = ac;
                if (ac == chosen) tot += s[c];
            }
        }
    }
    A[node] = chosen;
    s[node] = (chosen == -1) ? 0 : tot;
}

static RootedBinaryForest buildSubforestSteiner(
        const RootedBinaryForest &T1, int root,
        const std::unordered_map<int,int> &block) {
    std::unordered_map<int,int> size;
    for (auto &kv : block) size[kv.second]++;
    std::unordered_map<int,int> A;
    std::unordered_map<int,long> s;
    A.reserve(T1.nodes.size() * 2);
    s.reserve(T1.nodes.size() * 2);
    coverRBF(T1, root, block, size, A, s);
    RootedBinaryForest res = create_empty_copy(T1);
    for (auto &e : T1.edges()) {
        int u = e.first, v = e.second;
        if (A[v] != -1 && A[u] == A[v]) res.add_edge(u, v);
    }
    return res;
}

static Reducer  *g_reducer = nullptr;
static int             g_redRoot = 0;
static std::vector<int> g_backLabel;
static int             g_m = 0;
static std::vector<int> g_best;
static int             g_bestCost = 0;

static void emitAndExit() {
    signal(SIGINT, SIG_IGN);
    signal(SIGTERM, SIG_IGN);
    std::unordered_map<int,int> block;
    for (int l = 1; l <= g_m; l++) block[g_backLabel[l]] = g_best[l];
    RootedBinaryForest sub = buildSubforestSteiner(g_reducer->T1, g_redRoot, block);
#ifdef TIME_FIRST_PASS
    std::cerr << "emit: bestCost=" << g_bestCost
              << " subforest_components=" << count_components(sub, g_reducer->leaves)
              << " is_af=" << is_agreement_forest(sub, g_reducer->T2, g_reducer->leaves)
              << "\n";
#endif
    std::string s = g_reducer->prepare_solution(sub);
    std::cout << s << '\n';
    std::cout.flush();
    _exit(0);
}

static int uf_find(std::unordered_map<int,int>& par, int x) {
    while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; }
    return x;
}

static void suppress_if_deg1(RootedBinaryForest& T, int v) {
    if (!T.nodes.count(v) || T.out_degree(v) != 1) return;
    int c = T.ch(v)[0];
    int p = T.par(v);
    if (p != 0) {
        auto& pc = T.children[p];
        auto it = std::find(pc.begin(), pc.end(), v);
        *it = c;
        T.parent[c] = p;
    } else {
        T.roots.erase(v);
        T.roots.insert(c);
        T.parent[c] = 0;
    }
    T.children.erase(v); T.parent.erase(v); T.nodes.erase(v); T.roots.erase(v);
}

static int lca_in(const RootedBinaryForest& F, int x, int y) {
    std::unordered_set<int> anc;
    for (int n = x; n != 0; n = F.par(n)) anc.insert(n);
    for (int n = y; n != 0; n = F.par(n)) if (anc.count(n)) return n;
    return 0;
}

static int cut_path_pendants(RootedBinaryForest& F2, int a, int b, int lca) {
    std::unordered_set<int> path;
    for (int n = a; ; n = F2.par(n)) { path.insert(n); if (n == lca) break; }
    for (int n = b; ; n = F2.par(n)) { path.insert(n); if (n == lca) break; }

    std::vector<int> internal;
    for (int v : path) if (v != a && v != b) internal.push_back(v);

    int cuts = 0;
    for (int v : internal) {
        std::vector<int> ch(F2.ch(v));
        for (int c : ch) {
            if (!path.count(c)) { F2.remove_edge(v, c); ++cuts; }
        }
    }
    for (int v : internal) suppress_if_deg1(F2, v);
    return cuts;
}

std::unordered_map<int,int>
wbz_partition(RootedBinaryForest F1, RootedBinaryForest F2,
              const std::unordered_set<int>& active,
              std::mt19937& rng, bool randomize) {
    std::unordered_map<int,int> par;
    std::unordered_map<int,int> sz;
    par.reserve(active.size() * 2);
    for (int l : active) { par[l] = l; sz[l] = 1; }

    auto csize = [&](int x) { return sz[uf_find(par, x)]; };

    auto contract = [&](int keep, int drop) {
        int rk = uf_find(par, keep), rd = uf_find(par, drop);
        par[rd] = rk; sz[rk] += sz[rd];
        _remove_leaf_and_suppress(F1, drop);
        _remove_leaf_and_suppress(F2, drop);
    };

    while (true) {
        {
            std::vector<int> singles;
            for (int nd : F2.roots)
                if (F2.out_degree(nd) == 0 && F1.nodes.count(nd) && F1.par(nd) != 0)
                    singles.push_back(nd);
            for (int s : singles) _remove_leaf_and_suppress(F1, s);
        }

        int pa = 0, a = 0, b = 0;
        for (int nd : F1.nodes) {
            if (F1.out_degree(nd) == 2) {
                int c0 = F1.ch(nd)[0], c1 = F1.ch(nd)[1];
                if (F1.out_degree(c0) == 0 && F1.out_degree(c1) == 0) {
                    pa = nd; a = c0; b = c1; break;
                }
            }
        }
        if (pa == 0) break;

        int fa = F2.par(a), fb = F2.par(b);
        if (fa != 0 && fa == fb && F2.out_degree(fa) == 2) {
            contract(a, b);
            continue;
        }

        int lca = lca_in(F2, a, b);
        if (lca == 0) {
            int cut = (csize(a) <= csize(b)) ? a : b;
            if (randomize && (rng() & 1u)) cut = (cut == a) ? b : a;
            _remove_leaf_and_suppress(F1, cut);
            _remove_leaf_and_suppress(F2, cut);
        } else {
            int npend = 0;
            for (int n = a; n != lca; n = F2.par(n)) ++npend;
            for (int n = b; n != lca; n = F2.par(n)) ++npend;
            npend -= 2;
            bool do_path = (npend <= 2);
            if (randomize) do_path = (npend <= 2) || (npend <= 5 && (rng() & 1u));
            if (do_path) {
                cut_path_pendants(F2, a, b, lca);
                contract(a, b);
            } else {
                int cut = (csize(a) <= csize(b)) ? a : b;
                if (randomize && (rng() & 1u)) cut = (cut == a) ? b : a;
                _remove_leaf_and_suppress(F1, cut);
                _remove_leaf_and_suppress(F2, cut);
            }
        }
    }

    std::unordered_map<int,int> block;
    block.reserve(active.size() * 2);
    for (auto& kv : par) block[kv.first] = uf_find(par, kv.first);
    return block;
}

struct ExactState {
    RootedBinaryForest F1, F2;
    std::unordered_map<int,int> par, sz;
};

static void wbz_exact_rec(ExactState st, int cuts, int& best_cuts,
                          std::unordered_map<int,int>& best_par,
                          long& nodes, long node_cap) {
    if (g_stop || nodes > node_cap) return;
    ++nodes;
    if (cuts >= best_cuts) return;

    auto contract = [&](int keep, int drop) {
        int rk = uf_find(st.par, keep), rd = uf_find(st.par, drop);
        st.par[rd] = rk; st.sz[rk] += st.sz[rd];
        _remove_leaf_and_suppress(st.F1, drop);
        _remove_leaf_and_suppress(st.F2, drop);
    };

    int pa = 0, a = 0, b = 0;
    while (true) {
        std::vector<int> singles;
        for (int nd : st.F2.roots)
            if (st.F2.out_degree(nd) == 0 && st.F1.nodes.count(nd) && st.F1.par(nd) != 0)
                singles.push_back(nd);
        for (int s : singles) _remove_leaf_and_suppress(st.F1, s);

        pa = 0;
        for (int nd : st.F1.nodes) {
            if (st.F1.out_degree(nd) == 2) {
                int c0 = st.F1.ch(nd)[0], c1 = st.F1.ch(nd)[1];
                if (st.F1.out_degree(c0) == 0 && st.F1.out_degree(c1) == 0) {
                    pa = nd; a = c0; b = c1; break;
                }
            }
        }
        if (pa == 0) {
            if (cuts < best_cuts) {
                best_cuts = cuts;
                best_par.clear();
                for (auto& kv : st.par) best_par[kv.first] = uf_find(st.par, kv.first);
            }
            return;
        }
        int fa = st.F2.par(a), fb = st.F2.par(b);
        if (fa != 0 && fa == fb && st.F2.out_degree(fa) == 2) { contract(a, b); continue; }
        break;
    }

    int lca = lca_in(st.F2, a, b);

    {
        ExactState s = st;
        _remove_leaf_and_suppress(s.F1, a);
        _remove_leaf_and_suppress(s.F2, a);
        wbz_exact_rec(std::move(s), cuts + 1, best_cuts, best_par, nodes, node_cap);
    }
    {
        ExactState s = st;
        _remove_leaf_and_suppress(s.F1, b);
        _remove_leaf_and_suppress(s.F2, b);
        wbz_exact_rec(std::move(s), cuts + 1, best_cuts, best_par, nodes, node_cap);
    }
    if (lca != 0) {
        int npend = 0;
        for (int n = a; n != lca; n = st.F2.par(n)) ++npend;
        for (int n = b; n != lca; n = st.F2.par(n)) ++npend;
        npend -= 2;
        if (npend >= 1 && cuts + npend < best_cuts) {
            ExactState s = st;
            cut_path_pendants(s.F2, a, b, lca);
            int rk = uf_find(s.par, a), rd = uf_find(s.par, b);
            s.par[rd] = rk; s.sz[rk] += s.sz[rd];
            _remove_leaf_and_suppress(s.F1, b);
            _remove_leaf_and_suppress(s.F2, b);
            wbz_exact_rec(std::move(s), cuts + npend, best_cuts, best_par, nodes, node_cap);
        }
    }
}

static bool wbz_exact(const RootedBinaryForest& T1, const RootedBinaryForest& T2,
                      const std::unordered_set<int>& active, int ub_cuts,
                      long node_cap, std::unordered_map<int,int>& out_block,
                      int& out_cuts) {
    ExactState st{T1.copy(), T2.copy(), {}, {}};
    for (int l : active) { st.par[l] = l; st.sz[l] = 1; }
    int best_cuts = ub_cuts + 1;
    std::unordered_map<int,int> best_par;
    long nodes = 0;
    wbz_exact_rec(std::move(st), 0, best_cuts, best_par, nodes, node_cap);
    if (g_stop || nodes > node_cap) return false;
    if (best_par.empty()) return false;
    out_block = std::move(best_par);
    out_cuts = best_cuts;
    return true;
}

struct AForest {
    int L = 0, M = 0;
    std::vector<int>               par;
    std::vector<std::array<int,2>> ch;
    std::vector<int8_t>            deg;
    std::vector<uint8_t>          present;

    void init(int M_, int L_) {
        M = M_; L = L_;
        par.assign(M, -1);
        ch.assign(M, std::array<int,2>{{-1,-1}});
        deg.assign(M, 0);
        present.assign(M, 0);
    }
    int find_root(int n) const { while (par[n] != -1) n = par[n]; return n; }
    void add_edge(int u, int v) { ch[u][deg[u]++] = v; par[v] = u; }
    void clear_edges() {
        std::fill(par.begin(), par.end(), -1);
        std::fill(deg.begin(), deg.end(), (int8_t)0);
        std::fill(ch.begin(), ch.end(), std::array<int,2>{{-1,-1}});
    }
    void remove_edge(int u, int v) {
        if (ch[u][0] == v) { ch[u][0] = ch[u][1]; ch[u][1] = -1; }
        else if (ch[u][1] == v) { ch[u][1] = -1; }
        --deg[u];
        par[v] = -1;
    }
    void remove_node(int n) {
        int p = par[n];
        if (p != -1) {
            if (ch[p][0] == n) { ch[p][0] = ch[p][1]; ch[p][1] = -1; }
            else if (ch[p][1] == n) { ch[p][1] = -1; }
            --deg[p];
        }
        for (int i = 0; i < deg[n]; ++i) par[ch[n][i]] = -1;
        present[n] = 0; par[n] = -1; deg[n] = 0; ch[n] = std::array<int,2>{{-1,-1}};
    }
    void remove_leaf_suppress(int leaf) {
        int p = par[leaf];
        present[leaf] = 0; par[leaf] = -1; deg[leaf] = 0;
        if (p == -1) return;
        if (ch[p][0] == leaf) { ch[p][0] = ch[p][1]; ch[p][1] = -1; }
        else if (ch[p][1] == leaf) { ch[p][1] = -1; }
        --deg[p];
        if (deg[p] == 1) {
            int child = ch[p][0], gp = par[p];
            if (gp != -1) { if (ch[gp][0] == p) ch[gp][0] = child; else ch[gp][1] = child; par[child] = gp; }
            else par[child] = -1;
            present[p] = 0; par[p] = -1; deg[p] = 0; ch[p] = std::array<int,2>{{-1,-1}};
        }
    }
    void suppress_if_deg1(int v) {
        if (!present[v] || deg[v] != 1) return;
        int child = ch[v][0], p = par[v];
        if (p != -1) { if (ch[p][0] == v) ch[p][0] = child; else ch[p][1] = child; par[child] = p; }
        else par[child] = -1;
        present[v] = 0; par[v] = -1; deg[v] = 0; ch[v] = std::array<int,2>{{-1,-1}};
    }
};

struct AFSearch {
    AForest T1a, T2a;
    int L = 0, M = 0, I1end = 0;
    std::vector<std::pair<int,int>> t1_edges;
    std::vector<int> dense2orig_leaf, dense2orig_t1;

    AForest best_result, cand, cur;
    int best_cost = 0;

    std::vector<int> t1min, t2min, nb, lv, uf_par, uf_sz, block, tmp_roots, cur_roots,
                     tst_roots, tmp_path, tmp_internal;
    std::vector<uint8_t> inSet, seen;

    void build(const RootedBinaryForest& T1, const RootedBinaryForest& T2,
               const std::unordered_set<int>& leaves) {
        L = (int)leaves.size();
        std::unordered_map<int,int> leaf2dense; leaf2dense.reserve(L * 2);
        dense2orig_leaf.assign(L, 0);
        int idx = 0;
        for (int l : leaves) { leaf2dense[l] = idx; dense2orig_leaf[idx] = l; ++idx; }
        std::unordered_map<int,int> t1map, t2map;
        dense2orig_t1.clear();
        int cursor = L;
        for (int n : T1.nodes) if (!leaves.count(n)) { t1map[n] = cursor; dense2orig_t1.push_back(n); ++cursor; }
        I1end = cursor;
        for (int n : T2.nodes) if (!leaves.count(n)) { t2map[n] = cursor; ++cursor; }
        M = cursor;
        auto d1 = [&](int n){ return leaves.count(n) ? leaf2dense[n] : t1map[n]; };
        auto d2 = [&](int n){ return leaves.count(n) ? leaf2dense[n] : t2map[n]; };
        T1a.init(M, L);
        for (int n : T1.nodes) T1a.present[d1(n)] = 1;
        for (auto& e : T1.edges()) T1a.add_edge(d1(e.first), d1(e.second));
        T2a.init(M, L);
        for (int n : T2.nodes) T2a.present[d2(n)] = 1;
        for (auto& e : T2.edges()) T2a.add_edge(d2(e.first), d2(e.second));
        t1_edges.clear();
        for (auto& e : T1.edges()) t1_edges.push_back({d1(e.first), d1(e.second)});

        t1min.assign(M, 0); t2min.assign(M, 0); nb.assign(M, 0);
        inSet.assign(L, 0); seen.assign(M, 0);
        uf_par.assign(L, 0); uf_sz.assign(L, 0); block.assign(L, 0);

        best_result = T1a; best_result.clear_edges();
        cand = T1a; cur = T1a;
        best_cost = L;
    }

    void af_all_leaves(const AForest& G, int src, std::vector<int>& out) const {
        if (src < L) { out.push_back(src); return; }
        for (int i = 0; i < G.deg[src]; ++i) af_all_leaves(G, G.ch[src][i], out);
    }
    int af_get_min(const AForest& G, int node, const uint8_t* is, std::vector<int>& md) const {
        bool isleaf = (node < L) && (is == nullptr || is[node]);
        if (isleaf) { md[node] = node; return node; }
        if (node < L || G.deg[node] == 0) { md[node] = INT_MAX; return INT_MAX; }
        int mini = INT_MAX;
        for (int i = 0; i < G.deg[node]; ++i) mini = std::min(mini, af_get_min(G, G.ch[node][i], is, md));
        md[node] = mini; return mini;
    }
    std::pair<int,int> af_fcr(const AForest& G, int node, const uint8_t* is, int n) const {
        if (node < L && is[node]) return {1, node};
        int found = 0;
        for (int i = 0; i < G.deg[node]; ++i) {
            auto [cl, cr] = af_fcr(G, G.ch[node][i], is, n);
            if (cl == n) return {cl, cr};
            found += cl;
        }
        return {found, node};
    }
    bool af_compare(const AForest& A, int n1, const std::vector<int>& m1,
                    const AForest& B, int n2, const std::vector<int>& m2) const {
        if (m1[n1] != m2[n2]) return false;
        int d1, d2;
        while (true) {
            d1 = A.deg[n1];
            if (d1 == 0) break;
            if (d1 == 1) { n1 = A.ch[n1][0]; continue; }
            int a = A.ch[n1][0], b = A.ch[n1][1];
            if (m1[a] != INT_MAX && m1[b] != INT_MAX) break;
            if (m1[a] != INT_MAX) { n1 = a; continue; }
            if (m1[b] != INT_MAX) { n1 = b; continue; }
            d1 = 0; break;
        }
        while (true) {
            d2 = B.deg[n2];
            if (d2 == 0) break;
            if (d2 == 1) { n2 = B.ch[n2][0]; continue; }
            int a = B.ch[n2][0], b = B.ch[n2][1];
            if (m2[a] != INT_MAX && m2[b] != INT_MAX) break;
            if (m2[a] != INT_MAX) { n2 = a; continue; }
            if (m2[b] != INT_MAX) { n2 = b; continue; }
            d2 = 0; break;
        }
        if (d1 == 0 && d2 == 0) return true;
        if (d1 == 0 || d2 == 0) return false;
        int a1 = A.ch[n1][0], b1 = A.ch[n1][1], a2 = B.ch[n2][0], b2 = B.ch[n2][1];
        if (m1[a1] > m1[b1]) std::swap(a1, b1);
        if (m2[a2] > m2[b2]) std::swap(a2, b2);
        return af_compare(A, a1, m1, B, a2, m2) && af_compare(A, b1, m1, B, b2, m2);
    }
    bool af_dsl(AForest& G, const uint8_t* is, int source) const {
        if (source < L && is[source]) { G.remove_node(source); return true; }
        int d = G.deg[source], c0 = G.ch[source][0], c1 = G.ch[source][1];
        bool flag = false;
        if (d > 0 && af_dsl(G, is, c0)) flag = true;
        if (d > 1 && af_dsl(G, is, c1)) flag = true;
        if (flag) G.remove_node(source);
        return flag;
    }
    bool af_is_agreement(const AForest& rT1) {
        AForest rT2 = T2a;
        tmp_roots.clear();
        for (int l = 0; l < L; ++l) if (rT1.present[l]) {
            int r = rT1.find_root(l);
            if (!seen[r]) { seen[r] = 1; tmp_roots.push_back(r); }
        }
        for (int r : tmp_roots) af_get_min(rT1, r, nullptr, t1min);
        for (int r : tmp_roots) seen[r] = 0;
        bool ok = true;
        for (int T1_root : tmp_roots) {
            lv.clear(); af_all_leaves(rT1, T1_root, lv);
            int n = (int)lv.size();
            for (int x : lv) inSet[x] = 1;
            int T2_root = rT2.find_root(lv[0]);
            auto [nl, T2r] = af_fcr(rT2, T2_root, inSet.data(), n);
            if (nl != n) ok = false;
            else {
                af_get_min(rT2, T2r, inSet.data(), t2min);
                if (!af_compare(rT1, T1_root, t1min, rT2, T2r, t2min)) ok = false;
                else af_dsl(rT2, inSet.data(), T2r);
            }
            for (int x : lv) inSet[x] = 0;
            if (!ok) break;
        }
        return ok;
    }
    int af_count_components(const AForest& G) {
        tmp_roots.clear();
        for (int l = 0; l < L; ++l) if (G.present[l]) {
            int r = G.find_root(l);
            if (!seen[r]) { seen[r] = 1; tmp_roots.push_back(r); }
        }
        int c = (int)tmp_roots.size();
        for (int r : tmp_roots) seen[r] = 0;
        return c;
    }
    int af_lca(const AForest& G, int x, int y) {
        for (int n = x; n != -1; n = G.par[n]) seen[n] = 1;
        int res = -1;
        for (int n = y; n != -1; n = G.par[n]) if (seen[n]) { res = n; break; }
        for (int n = x; n != -1; n = G.par[n]) seen[n] = 0;
        return res;
    }
    void af_cut_pendants(AForest& F2, int a, int b, int lca) {
        tmp_path.clear();
        for (int n = a; ; n = F2.par[n]) { if (!seen[n]) { seen[n] = 1; tmp_path.push_back(n); } if (n == lca) break; }
        for (int n = b; ; n = F2.par[n]) { if (!seen[n]) { seen[n] = 1; tmp_path.push_back(n); } if (n == lca) break; }
        tmp_internal.clear();
        for (int v : tmp_path) if (v != a && v != b) tmp_internal.push_back(v);
        for (int v : tmp_internal) {
            int d = F2.deg[v], cs[2] = { F2.ch[v][0], F2.ch[v][1] };
            for (int i = 0; i < d; ++i) if (!seen[cs[i]]) F2.remove_edge(v, cs[i]);
        }
        for (int v : tmp_internal) F2.suppress_if_deg1(v);
        for (int v : tmp_path) seen[v] = 0;
    }
    void af_wbz(std::mt19937& rng, bool randomize) {
        AForest F1 = T1a, F2 = T2a;
        for (int l = 0; l < L; ++l) { uf_par[l] = l; uf_sz[l] = 1; }
        auto find = [&](int x){ while (uf_par[x] != x) { uf_par[x] = uf_par[uf_par[x]]; x = uf_par[x]; } return x; };
        auto csize = [&](int x){ return uf_sz[find(x)]; };
        auto contract = [&](int keep, int drop){
            int rk = find(keep), rd = find(drop); uf_par[rd] = rk; uf_sz[rk] += uf_sz[rd];
            F1.remove_leaf_suppress(drop); F2.remove_leaf_suppress(drop);
        };
        while (true) {
            for (int l = 0; l < L; ++l)
                if (F2.present[l] && F2.deg[l] == 0 && F2.par[l] == -1 && F1.present[l] && F1.par[l] != -1)
                    F1.remove_leaf_suppress(l);
            int pa = -1, a = -1, b = -1;
            for (int nd = L; nd < I1end; ++nd) {
                if (F1.present[nd] && F1.deg[nd] == 2) {
                    int c0 = F1.ch[nd][0], c1 = F1.ch[nd][1];
                    if (F1.deg[c0] == 0 && F1.deg[c1] == 0) { pa = nd; a = c0; b = c1; break; }
                }
            }
            if (pa == -1) break;
            int fa = F2.par[a], fb = F2.par[b];
            if (fa != -1 && fa == fb && F2.deg[fa] == 2) { contract(a, b); continue; }
            int lca = af_lca(F2, a, b);
            if (lca == -1) {
                int cut = (csize(a) <= csize(b)) ? a : b;
                if (randomize && (rng() & 1u)) cut = (cut == a) ? b : a;
                F1.remove_leaf_suppress(cut); F2.remove_leaf_suppress(cut);
            } else {
                int npend = 0;
                for (int n = a; n != lca; n = F2.par[n]) ++npend;
                for (int n = b; n != lca; n = F2.par[n]) ++npend;
                npend -= 2;
                bool do_path = (npend <= 2);
                if (randomize) do_path = (npend <= 2) || (npend <= 5 && (rng() & 1u));
                if (do_path) { af_cut_pendants(F2, a, b, lca); contract(a, b); }
                else {
                    int cut = (csize(a) <= csize(b)) ? a : b;
                    if (randomize && (rng() & 1u)) cut = (cut == a) ? b : a;
                    F1.remove_leaf_suppress(cut); F2.remove_leaf_suppress(cut);
                }
            }
        }
        for (int l = 0; l < L; ++l) block[l] = find(l);
    }
    int af_nodeblock(const AForest& G, int node) {
        if (node < L) { nb[node] = block[node]; return block[node]; }
        int agg = 0; bool first = true, mixed = false;
        for (int i = 0; i < G.deg[node]; ++i) {
            int cb = af_nodeblock(G, G.ch[node][i]);
            if (cb == INT_MIN) mixed = true;
            else if (first) { agg = cb; first = false; }
            else if (agg != cb) mixed = true;
        }
        int val = (mixed || first) ? INT_MIN : agg;
        nb[node] = val; return val;
    }
    void af_build_subforest() {
        for (int d = 0; d < M; ++d) if (T1a.present[d] && T1a.par[d] == -1) af_nodeblock(T1a, d);
        cand.clear_edges();
        for (auto& e : t1_edges) {
            int u = e.first, v = e.second;
            if (nb[u] != INT_MIN && nb[u] == nb[v]) cand.add_edge(u, v);
        }
    }
    void run() {
        std::mt19937 rng(1234567u);
        long wbz_iter = 0;
        std::vector<std::pair<int,int>> edges = t1_edges;
        while (true) {
            if (g_stop) return;
            af_wbz(rng, wbz_iter != 0);
            af_build_subforest();
            int c = af_count_components(cand);
            if (c < best_cost && af_is_agreement(cand)) { best_result = cand; best_cost = c; }
            ++wbz_iter;

            cur.clear_edges();
            cur_roots.clear();
            for (int l = 0; l < L; ++l) cur_roots.push_back(l);
            int cur_cost = L;
            int n = 1;
            while (n < (int)edges.size()) {
                if (g_stop) return;
                n = std::min(2 * n, (int)edges.size());
                int k = (int)edges.size() / n, m = (int)edges.size() % n;
                for (int i = n - 1; i >= 0; --i) {
                    if (g_stop) return;
                    int start = i * k + std::min(i, m);
                    int end   = (i + 1) * k + std::min(i + 1, m);
                    std::vector<std::pair<int,int>> subset(edges.begin() + start, edges.begin() + end);
                    for (auto& e : subset) cur.add_edge(e.first, e.second);
                    tst_roots.clear();
                    for (int r : cur_roots) { int nr = cur.find_root(r); if (!seen[nr]) { seen[nr] = 1; tst_roots.push_back(nr); } }
                    for (int r : tst_roots) seen[r] = 0;
                    int tst_cost = (int)tst_roots.size();
                    if (tst_cost < cur_cost && af_is_agreement(cur)) {
                        cur_cost = tst_cost;
                        cur_roots = tst_roots;
                        edges.erase(edges.begin() + start, edges.begin() + end);
                        if (cur_cost < best_cost) { best_result = cur; best_cost = cur_cost; }
                        continue;
                    }
                    for (auto& e : subset) cur.remove_edge(e.first, e.second);
                }
            }
            edges = t1_edges;
            std::shuffle(edges.begin(), edges.end(), rng);
        }
    }
    RootedBinaryForest result_to_rbf() const {
        auto orig = [&](int d){ return d < L ? dense2orig_leaf[d] : dense2orig_t1[d - L]; };
        RootedBinaryForest G;
        for (int d = 0; d < M; ++d) if (best_result.present[d]) G.add_node(orig(d));
        for (int d = 0; d < M; ++d) if (best_result.present[d])
            for (int i = 0; i < best_result.deg[d]; ++i)
                G.add_edge(orig(d), orig(best_result.ch[d][i]));
        return G;
    }
};

struct GraphSeeker {
    RootedBinaryForest        T1, T2;
    std::unordered_set<int>   orig_leaves;
    std::unordered_set<int>   leaves;
    std::vector<ReductionEntry> reduction_stack;
    RootedBinaryForest        result;
    int                        best_cost;

    struct Stats {
        int initial_leaves       = 0;
        int leaves_after         = 0;
        int subtrees_reduced     = 0;
        int subtree_calls        = 0;
        int chains_reduced       = 0;
        int chain_calls          = 0;
        int cherries_reduced     = 0;
        int cherry_calls         = 0;
        int inner_iters          = 0;
        int run_loop_count       = 0;
    } stats;

    AFSearch afs;

    GraphSeeker(RootedBinaryForest t1, RootedBinaryForest t2,
                std::unordered_set<int> lv)
        : T1(std::move(t1)), T2(std::move(t2)),
          orig_leaves(lv), leaves(lv) {
        _reduce();
        result    = create_empty_copy(T1);
        best_cost = (int)leaves.size();
    }

    void _reduce() {
        stats.initial_leaves = (int)leaves.size();
        while (true) {
            while (true) {
                auto c32 = chain_32_reduce(T1, T2, leaves);
                bool has_c32 = !c32.chain_32_map.empty();
                if (has_c32) {
                    stats.cherries_reduced += (int)c32.chain_32_map.size();
                    ++stats.cherry_calls;
                    for (auto& [xj, xi] : c32.chain_32_map) leaves.erase(xj);
                    reduction_stack.push_back({{}, {}, std::move(c32)});
                }
                auto cr = chain_reduce(T1, T2, leaves);
                bool has_cr = !cr.chain_map.empty();
                if (has_cr) {
                    stats.chains_reduced += (int)cr.chain_map.size();
                    ++stats.chain_calls;
                    for (auto& [c2, removed] : cr.chain_map)
                        for (int r : removed) leaves.erase(r);
                    reduction_stack.push_back({{}, std::move(cr), {}});
                }
                if (!has_c32 && !has_cr) break;
                ++stats.inner_iters;
            }
            auto sr = subtree_reduce(T1, T2, leaves);
            if (sr.replace_map.empty()) break;
            stats.subtrees_reduced += (int)sr.replace_map.size();
            ++stats.subtree_calls;
            for (auto& [leaf, tree] : sr.replace_map) {
                std::vector<int> lv; all_leaves_tree(tree, *tree.roots.begin(), lv);
                for (int l : lv) if (l != leaf) leaves.erase(l);
            }
            reduction_stack.push_back({std::move(sr), {}, {}});
        }
        stats.leaves_after = (int)leaves.size();
    }

    std::string prepare_solution(const RootedBinaryForest& graph_in) {
        RootedBinaryForest graph = graph_in.copy();

        int all_subtree_min = 0;
        for (auto& entry : reduction_stack)
            for (auto& [leaf, tree] : entry.sr.replace_map)
                for (int n : tree.nodes)
                    if (n < 0 && n < all_subtree_min) all_subtree_min = n;

        for (int i = (int)reduction_stack.size()-1; i >= 0; --i) {
            restore_32chain(graph, reduction_stack[i].c32);
            restore_chain(graph, reduction_stack[i].cr, all_subtree_min);
            restore_subtree(graph, reduction_stack[i].sr);
        }

        std::unordered_set<int> visited;
        std::vector<std::string> out_trees;
        for (int leaf : orig_leaves) {
            if (visited.count(leaf)) continue;
            int root = find_root(graph, leaf);
            root = remove_contract_rooted(graph, orig_leaves, root);
            std::vector<int> lv; all_leaves_tree(graph, root, lv);
            visited.insert(lv.begin(), lv.end());
            out_trees.push_back(tree_to_newick_print(graph, root));
        }
        std::string out;
        for (int i = 0; i < (int)out_trees.size(); ++i) {
            if (i) out += '\n';
            out += out_trees[i];
        }
        return out;
    }

    bool try_exact(long node_cap) {
        if ((int)leaves.size() <= 1) return false;
        std::mt19937 rng(1u);
        auto b0 = wbz_partition(T1, T2, leaves, rng, false);
        RootedBinaryForest cand0 = build_subforest_from_blocks(T1, b0);
        int ub = count_components(cand0, leaves);
        std::unordered_map<int,int> block; int cuts = 0;
        if (!wbz_exact(T1, T2, leaves, ub - 1, node_cap, block, cuts)) return false;
        RootedBinaryForest cand = build_subforest_from_blocks(T1, block);
        int c = count_components(cand, leaves);
        if (c <= best_cost && is_agreement_forest(cand, T2, leaves)) {
            result = std::move(cand); best_cost = c;
            return true;
        }
        return false;
    }

    void run();
    void do_exit();
};

static GraphSeeker* g_seeker = nullptr;

void GraphSeeker::do_exit() {
    signal(SIGINT,  SIG_IGN);
    signal(SIGTERM, SIG_IGN);
    std::string s = prepare_solution(result);
    std::cout << s << '\n';
    std::cout.flush();
    _exit(0);
}

void GraphSeeker::run() {
    if ((int)leaves.size() == 1) {
        result    = T1.copy();
        best_cost = 1;
        do_exit();
    }

    afs.build(T1, T2, leaves);
    afs.run();
    result    = afs.result_to_rbf();
    best_cost = afs.best_cost;
    do_exit();
}

std::vector<std::tuple<std::vector<int>, std::unordered_set<int>>>
find_maximal_common_pendants_multi(
        const std::vector<RootedBinaryForest>& trees,
        const std::unordered_set<int>& leaves) {
    std::unordered_set<int> visited;
    std::vector<std::unordered_map<int,int>> mins(trees.size());
    for (int i = 0; i < (int)trees.size(); ++i)
        get_min(trees[i], leaves, mins[i]);

    std::vector<std::tuple<std::vector<int>, std::unordered_set<int>>> result;

    for (int leaf : leaves) {
        if (visited.count(leaf)) continue;
        std::vector<int> nodes(trees.size(), leaf);

        auto all_have_parent = [&]() {
            for (int i = 0; i < (int)trees.size(); ++i)
                if (trees[i].par(nodes[i]) == 0) return false;
            return true;
        };

        while (all_have_parent()) {
            std::vector<int> preds;
            for (int i = 0; i < (int)trees.size(); ++i)
                preds.push_back(trees[i].par(nodes[i]));
            bool mismatch = false;
            for (int i = 0; i < (int)trees.size(); ++i)
                if (trees[i].ch(preds[i]).size() != 2) { mismatch = true; break; }
            if (!mismatch) {
                std::vector<int> siblings;
                for (int i = 0; i < (int)trees.size(); ++i) {
                    const auto& ch = trees[i].ch(preds[i]);
                    siblings.push_back((ch[0] == nodes[i]) ? ch[1] : ch[0]);
                }
                for (int i = 1; i < (int)trees.size(); ++i) {
                    if (!compare_trees(siblings[0], trees[0], mins[0],
                                       siblings[i], trees[i], mins[i], leaves)) {
                        mismatch = true; break;
                    }
                }
            }
            if (mismatch) {
                std::vector<int> lv; all_leaves_tree(trees[0], nodes[0], lv);
                std::unordered_set<int> covered(lv.begin(), lv.end());
                visited.insert(covered.begin(), covered.end());
                if (!leaves.count(nodes[0]))
                    result.push_back({nodes, std::move(covered)});
                goto next_leaf2;
            }
            nodes = preds;
        }
        {
            std::vector<int> lv; all_leaves_tree(trees[0], nodes[0], lv);
            std::unordered_set<int> covered(lv.begin(), lv.end());
            visited.insert(covered.begin(), covered.end());
            if (!leaves.count(nodes[0]))
                result.push_back({nodes, std::move(covered)});
        }
        next_leaf2:;
    }
    return result;
}

std::unordered_map<int, RootedBinaryForest>
subtree_reduce_multi(std::vector<RootedBinaryForest>& trees,
                     const std::unordered_set<int>& leaves) {
    std::vector<RootedBinaryForest> copies;
    for (auto& T : trees) copies.push_back(T.copy());

    auto pendants = find_maximal_common_pendants_multi(copies, leaves);
    std::unordered_map<int, RootedBinaryForest> replace_map;

    for (auto& [nodes, covered] : pendants) {
        int replacement = *covered.begin();
        RootedBinaryForest saved;
        std::vector<int> parents;
        for (int i = 0; i < (int)trees.size(); ++i) {
            auto [sub, p] = trees[i].split_subtree_with_parent(nodes[i]);
            parents.push_back(p);
            if (i == 0) saved = std::move(sub);
        }
        for (int i = 0; i < (int)trees.size(); ++i) {
            if (parents[i] != 0) trees[i].add_edge(parents[i], replacement);
            else trees[i].add_node(replacement);
        }
        replace_map[replacement] = std::move(saved);
    }
    return replace_map;
}

static std::atomic<int> g_master_stop{0};

extern "C" void combined_signal(int) {
    g_stop    = 1;
    g_stop = 1;
    g_stop   = 1;
    g_master_stop.store(1);
}

struct Best {
    std::vector<std::string> lines;
    int cost = INT_MAX;
};
static Best g_out;

static void offer(std::vector<std::string> cand) {
    int c = (int)cand.size();
    if (c > 0 && c < g_out.cost) {
        g_out.cost  = c;
        g_out.lines = std::move(cand);
    }
}

static std::vector<std::string> split_lines(const std::string& s) {
    std::vector<std::string> out;
    std::string cur;
    std::istringstream in(s);
    while (std::getline(in, cur)) {
        while (!cur.empty() && (cur.back() == '\r' || cur.back() == ' '))
            cur.pop_back();
        if (!cur.empty()) out.push_back(cur);
    }
    return out;
}

static void emit_and_exit() {
    signal(SIGINT,  SIG_IGN);
    signal(SIGTERM, SIG_IGN);
    for (auto& l : g_out.lines) std::cout << l << '\n';
    std::cout.flush();
    _exit(0);
}

static void run_with_budget(double seconds,
                            const std::function<void()>& body,
                            const std::function<void()>& set_stop) {
    std::atomic<bool> done{false};
    std::thread watch([&]() {
        auto t0 = std::chrono::steady_clock::now();
        while (!done.load(std::memory_order_relaxed)) {
            if (g_master_stop.load()) { set_stop(); break; }
            double el = std::chrono::duration<double>(
                            std::chrono::steady_clock::now() - t0).count();
            if (el >= seconds) { set_stop(); break; }
            std::this_thread::sleep_for(std::chrono::milliseconds(25));
        }
    });
    body();
    done.store(true);
    watch.join();
    if (!g_master_stop.load()) g_stop = 0;
}

static void solve_redblue(const std::string& raw) {

    std::istringstream in(raw);
    InputData data = read_input(in);
    int n = data.n_leaves;
    if (n <= 0 || data.trees.size() < 2) return;

    std::unordered_set<int> allLeaves;
    for (int i = 1; i <= n; i++) allLeaves.insert(i);
    Reducer reducer(std::move(data.trees[0]), std::move(data.trees[1]),
                          std::move(allLeaves));
    g_reducer = &reducer;
    g_redRoot = *reducer.T1.roots.begin();

    std::vector<int> active(reducer.leaves.begin(), reducer.leaves.end());
    std::sort(active.begin(), active.end());
    int m = (int)active.size();
    g_m = m;
    std::unordered_map<int,int> fwd;
    g_backLabel.assign(m + 1, 0);
    for (int i = 0; i < m; i++) { fwd[active[i]] = i + 1; g_backLabel[i + 1] = active[i]; }

    g_best.assign(m + 1, 0);
    for (int l = 1; l <= m; l++) g_best[l] = l - 1;
    g_bestCost = m;

    if (m > 1) {
        int r2 = *reducer.T2.roots.begin();
        Tree mT1 = buildTreeFromRBF(reducer.T1, g_redRoot, fwd, m);
        Tree mT2 = buildTreeFromRBF(reducer.T2, r2, fwd, m);
        RedBlueSolver solver(mT1, mT2, m);
        std::mt19937 rng(12345u);
        auto adopt = [&]() {
            int c = solver.numComponents();
            if (c < g_bestCost) { g_bestCost = c; g_best = solver.snapshot(); }
        };
        if (solver.redBlue(rng, false)) {
            adopt();
            solver.mergePhase(rng);
            adopt();
        }
    }

    std::unordered_map<int,int> block;
    for (int l = 1; l <= g_m; l++) block[g_backLabel[l]] = g_best[l];
    RootedBinaryForest sub = buildSubforestSteiner(reducer.T1, g_redRoot, block);
    std::string s = reducer.prepare_solution(sub);
    offer(split_lines(s));
}

static int solve_chen(const std::string& raw, double budget) {

    std::istringstream in(raw);
    ChenInput d = chen_read_input(in);
    if (!d.ok || d.n <= 1) return INT_MAX;

    ChenSolver solver(d.T, d.F);
    if (budget <= 0.0)
        solver.run();
    else
        run_with_budget(budget, [&]() { solver.run(); },
                             []() { g_stop = 1; });

    std::vector<int> fb = solver.expand(solver.bestBlock);
    std::string out;
    emit_forest(solver.masterT, fb, out);
    auto lines = split_lines(out);
    int cost = (int)lines.size();
    offer(std::move(lines));
    return cost;
}

static int solve_delta(const std::string& raw, double budget) {

    std::istringstream in(raw);
    InputData data = read_input(in);
    int n = data.n_leaves;
    if (data.trees.size() != 2 || n <= 0) return INT_MAX;

    std::unordered_set<int> leaves;
    for (int i = 1; i <= n; ++i) leaves.insert(i);

    GraphSeeker seeker(std::move(data.trees[0]), std::move(data.trees[1]), leaves);
    g_seeker = &seeker;

    if ((int)seeker.leaves.size() <= 1) {
        seeker.result    = seeker.T1.copy();
        seeker.best_cost = (int)seeker.leaves.size();
    } else {
        seeker.afs.build(seeker.T1, seeker.T2, seeker.leaves);
        if (budget <= 0.0)
            seeker.afs.run();
        else
            run_with_budget(budget, [&]() { seeker.afs.run(); },
                                 []() { g_stop = 1; });
        seeker.result    = seeker.afs.result_to_rbf();
        seeker.best_cost = seeker.afs.best_cost;
    }
    std::string s = seeker.prepare_solution(seeker.result);
    auto lines = split_lines(s);
    int cost = (int)lines.size();
    offer(std::move(lines));
    return cost;
}

static void solve_multitree(const std::string& raw) {

    std::istringstream in(raw);
    InputData data = read_input(in);
    int n = data.n_leaves;
    std::unordered_set<int> leaves;
    for (int i = 1; i <= n; ++i) leaves.insert(i);

    auto replace_map = subtree_reduce_multi(data.trees, leaves);
    std::unordered_set<int> to_remove;
    for (auto& kv : replace_map) {
        std::vector<int> lv;
        all_leaves_tree(kv.second, *kv.second.roots.begin(), lv);
        for (int l : lv) if (l != kv.first) to_remove.insert(l);
    }
    std::vector<std::string> lines;
    for (int i = 1; i <= n; ++i) {
        if (to_remove.count(i)) continue;
        auto it = replace_map.find(i);
        if (it == replace_map.end())
            lines.push_back(std::to_string(i) + ";");
        else
            lines.push_back(tree_to_newick_print(it->second, *it->second.roots.begin()));
    }
    offer(std::move(lines));
}

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    signal(SIGINT,  combined_signal);
    signal(SIGTERM, combined_signal);

    std::string raw((std::istreambuf_iterator<char>(std::cin)),
                    std::istreambuf_iterator<char>());

    int n_trees = 0, n_leaves = 0;
    {
        std::istringstream in(raw);
        InputData hdr = read_input(in);
        n_trees  = (int)hdr.trees.size();
        n_leaves = hdr.n_leaves;
    }

    if (n_leaves <= 0) { return 0; }
    if (n_leaves == 1) { std::cout << "1;\n"; return 0; }

    if (n_trees > 2) {
        solve_multitree(raw);
        if (g_out.lines.empty())
            for (int i = 1; i <= n_leaves; ++i) g_out.lines.push_back(std::to_string(i) + ";");
        emit_and_exit();
    }
    if (n_trees < 2) {
        for (int i = 1; i <= n_leaves; ++i) g_out.lines.push_back(std::to_string(i) + ";");
        emit_and_exit();
    }

    solve_redblue(raw);
    if (g_out.lines.empty())
        for (int i = 1; i <= n_leaves; ++i) g_out.lines.push_back(std::to_string(i) + ";");
    if (g_out.cost == INT_MAX) g_out.cost = (int)g_out.lines.size();

    if (!g_master_stop.load())
        solve_delta(raw, 6.0);

    if (!g_master_stop.load())
        solve_chen(raw, -1.0);

    emit_and_exit();
    return 0;
}

