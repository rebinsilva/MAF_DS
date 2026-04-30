#include <algorithm>
#include <array>
#include <cassert>
#include <cctype>
#include <csignal>
#include <cstring>
#include <iostream>
#include <memory>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// Node IDs: 0=NULL_NODE, 1..n_leaves=leaves, n_leaves+1..=internals.
// Both T1 and T2 share the same leaf ID space but have independent internal IDs.
static constexpr int NULL_NODE = 0;


// Immutable rooted binary phylogenetic tree built once during parse.
struct PhyloTree {
    int n_leaves = 0;
    int n_nodes  = 0;
    int root     = NULL_NODE;

    std::vector<int>               par;    // par[v]: parent of v
    std::vector<std::array<int,2>> ch;     // ch[v]: {left, right} children

    std::vector<std::pair<int,int>> edges; // all (parent,child) edges in preorder

    void init(int n_leaves_, int n_nodes_, int root_) {
        n_leaves = n_leaves_;
        n_nodes  = n_nodes_;
        root     = root_;
        par  .assign(n_nodes + 1, NULL_NODE);
        ch   .assign(n_nodes + 1, {NULL_NODE, NULL_NODE});
        edges.clear();
    }

    void add_edge(int p, int c) {
        assert((ch[p][0] == NULL_NODE || ch[p][1] == NULL_NODE) && "node already has 2 children");
        if (ch[p][0] == NULL_NODE) ch[p][0] = c;
        else                        ch[p][1] = c;
        par[c] = p;
        edges.emplace_back(p, c);
    }

    bool is_leaf(int v) const noexcept { return v >= 1 && v <= n_leaves; }

    int out_deg(int v) const noexcept {
        return (ch[v][0] != NULL_NODE) + (ch[v][1] != NULL_NODE);
    }
};


// Mutable copy of a tree used inside agreement_check for local pruning/contraction.
struct MutableTree {
    int n_leaves = 0;
    int n_nodes  = 0;

    std::vector<int>               par;
    std::vector<std::array<int,2>> ch;
    std::vector<bool>              alive; // false = node has been removed

    MutableTree() = default;

    explicit MutableTree(const PhyloTree& t)
        : n_leaves(t.n_leaves), n_nodes(t.n_nodes),
          par(t.par), ch(t.ch),
          alive(t.n_nodes + 1, true)
    {
        alive[NULL_NODE] = false;
    }

    bool is_leaf (int v) const noexcept { return v >= 1 && v <= n_leaves; }
    bool is_alive(int v) const noexcept { return alive[v]; }

    int out_deg(int v) const noexcept {
        return (ch[v][0] != NULL_NODE) + (ch[v][1] != NULL_NODE);
    }

    int only_child(int v) const noexcept {
        if (ch[v][0] != NULL_NODE) return ch[v][0];
        return ch[v][1];
    }

    void unlink_from_parent(int v) {
        int p = par[v];
        if (p == NULL_NODE) return;
        if (ch[p][0] == v) ch[p][0] = NULL_NODE;
        else                ch[p][1] = NULL_NODE;
        par[v] = NULL_NODE;
    }

    // Remove v: detach from parent, clear children, mark dead.
    void remove_node(int v) {
        unlink_from_parent(v);
        ch[v]    = {NULL_NODE, NULL_NODE};
        alive[v] = false;
    }

    // Suppress degree-1 internal node v: rewire its parent directly to its child.
    void contract_node(int v) {
        int child = only_child(v);
        assert(child != NULL_NODE);
        int p = par[v];
        par[child] = p;
        if (p != NULL_NODE) {
            if (ch[p][0] == v) ch[p][0] = child;
            else                ch[p][1] = child;
        }
        ch[v]    = {NULL_NODE, NULL_NODE};
        par[v]   = NULL_NODE;
        alive[v] = false;
    }

    int find_root(int v) const noexcept {
        while (par[v] != NULL_NODE) v = par[v];
        return v;
    }

    // Refill in place from a PhyloTree, reusing existing vector capacity.
    void refill_from(const PhyloTree& t) {
        n_leaves = t.n_leaves;
        n_nodes  = t.n_nodes;
        par      = t.par;
        ch       = t.ch;
        alive.assign(t.n_nodes + 1, true);
        alive[NULL_NODE] = false;
    }

    // Copy in place from another MutableTree, reusing existing vector capacity.
    void copy_from(const MutableTree& other) {
        n_leaves = other.n_leaves;
        n_nodes  = other.n_nodes;
        par      = other.par;
        ch       = other.ch;
        alive    = other.alive;
    }
};


// Union-by-rank DSU without path compression, so every write is O(1)-reversible.
// Tracks n_leaf_comps: number of components containing at least one leaf.
struct DSU {
    std::vector<int> rep;
    std::vector<int> rnk;
    std::vector<int> leaf_cnt;  // leaf_cnt[rep(v)]: leaves in that component
    int n_leaf_comps = 0;

    struct Undo {
        int child_rep, parent_rep;
        int old_rnk;
        int old_lc_child;
        int old_lc_parent;
        bool merged_leaf_comps;
    };
    std::vector<Undo> history; // supports O(1) rollback per unite

    DSU() = default;
    DSU(int n_nodes, int n_leaves) {
        rep     .resize(n_nodes + 1);
        rnk     .assign(n_nodes + 1, 0);
        leaf_cnt.assign(n_nodes + 1, 0);
        for (int i = 1; i <= n_nodes;  ++i) rep[i]      = i;
        for (int i = 1; i <= n_leaves; ++i) leaf_cnt[i] = 1;
        n_leaf_comps = n_leaves;
    }

    // O(log n) without path compression.
    int find(int v) const noexcept {
        while (rep[v] != v) v = rep[v];
        return v;
    }

    void unite(int u, int v) {
        u = find(u);
        v = find(v);
        if (u == v) {
            // Record no-op so checkpoint indices stay consistent.
            history.push_back({u, v, 0, 0, 0, false});
            return;
        }
        if (rnk[u] > rnk[v]) std::swap(u, v); // u becomes child of v
        Undo undo{u, v, rnk[v], leaf_cnt[u], leaf_cnt[v], false};
        rep[u] = v;
        if (rnk[u] == rnk[v]) ++rnk[v];
        bool u_had_leaf = (leaf_cnt[u] > 0);
        bool v_had_leaf = (leaf_cnt[v] > 0);
        leaf_cnt[v] += leaf_cnt[u];
        leaf_cnt[u]  = 0;
        if (u_had_leaf && v_had_leaf) {
            --n_leaf_comps;
            undo.merged_leaf_comps = true;
        }
        history.push_back(undo);
    }

    int  save() const noexcept { return static_cast<int>(history.size()); }

    // Refill in place to avoid reallocation on each outer-loop reset.
    void reset(int n_leaves) {
        std::iota(rep.begin() + 1, rep.end(), 1);
        std::fill(rnk     .begin() + 1, rnk     .end(), 0);
        std::fill(leaf_cnt.begin() + 1, leaf_cnt.end(), 0);
        for (int i = 1; i <= n_leaves; ++i) leaf_cnt[i] = 1;
        n_leaf_comps = n_leaves;
        history.clear();
    }

    void restore(int checkpoint) {
        while (static_cast<int>(history.size()) > checkpoint) {
            auto [cr, pr, old_rnk, old_lc_c, old_lc_p, merged] = history.back();
            history.pop_back();
            if (cr == pr) continue;
            rep[cr]      = cr;
            rnk[pr]      = old_rnk;
            leaf_cnt[cr] = old_lc_c;
            leaf_cnt[pr] = old_lc_p;
            if (merged) ++n_leaf_comps;
        }
    }

    int score() const noexcept { return -n_leaf_comps; }
};


// Incrementally built edge-subset of T1; supports O(batch) checkpoint/restore.
struct MutableForest {
    const PhyloTree& src;

    std::vector<bool>              edge_on; // edge_on[i]: src.edges[i] is active
    std::vector<int>               par;
    std::vector<std::array<int,2>> ch;
    std::vector<int>               n_ch;    // active child count

    DSU dsu;

    struct Checkpoint { int dsu_cp, ops_cp; };
    std::vector<int> ops; // ordered log of added edge indices for rollback

    explicit MutableForest(const PhyloTree& src_)
        : src(src_),
          edge_on(src_.edges.size(), false),
          par    (src_.n_nodes + 1, NULL_NODE),
          ch     (src_.n_nodes + 1, {NULL_NODE, NULL_NODE}),
          n_ch   (src_.n_nodes + 1, 0),
          dsu    (src_.n_nodes, src_.n_leaves) {}

    void add_edge(int idx) {
        assert(!edge_on[idx]);
        auto [p, c] = src.edges[idx];
        edge_on[idx]     = true;
        par[c]           = p;
        ch[p][n_ch[p]++] = c;
        dsu.unite(p, c);
        ops.push_back(idx);
    }

    Checkpoint save() const noexcept {
        return {dsu.save(), static_cast<int>(ops.size())};
    }

    void restore(Checkpoint cp) {
        while (static_cast<int>(ops.size()) > cp.ops_cp) {
            remove_edge_raw(ops.back());
            ops.pop_back();
        }
        dsu.restore(cp.dsu_cp);
    }

    int score() const noexcept { return dsu.score(); }

    void reset() {
        std::fill(edge_on.begin(), edge_on.end(), false);
        std::fill(par    .begin(), par    .end(), NULL_NODE);
        std::fill(ch     .begin(), ch     .end(), std::array<int,2>{NULL_NODE, NULL_NODE});
        std::fill(n_ch   .begin(), n_ch   .end(), 0);
        ops.clear();
        dsu.reset(src.n_leaves);
    }

    MutableTree snapshot() const {
        MutableTree mt;
        mt.n_leaves = src.n_leaves;
        mt.n_nodes  = src.n_nodes;
        mt.par      = par;
        mt.ch       = ch;
        mt.alive    .assign(src.n_nodes + 1, true);
        mt.alive[NULL_NODE] = false;
        return mt;
    }

    // Refill a pre-allocated MutableTree in place (avoids vector reallocation).
    void snapshot_into(MutableTree& mt) const {
        mt.n_leaves = src.n_leaves;
        mt.n_nodes  = src.n_nodes;
        mt.par      = par;
        mt.ch       = ch;
        mt.alive.assign(src.n_nodes + 1, true);
        mt.alive[NULL_NODE] = false;
    }

private:
    // Remove edge from adjacency only; DSU is rolled back separately via history.
    void remove_edge_raw(int idx) {
        auto [p, c] = src.edges[idx];
        edge_on[idx] = false;
        par[c]       = NULL_NODE;
        if (ch[p][0] == c) { ch[p][0] = ch[p][1]; ch[p][1] = NULL_NODE; }
        else                {                        ch[p][1] = NULL_NODE; }
        --n_ch[p];
    }
};


// Prune t to keep only leaves in keep[], then walk off any degree-1 root chain.
// Returns the new root (always alive); caller guarantees >=1 kept leaf below.
// Uses caller-owned scratch vectors to avoid per-call allocation.
static int remove_rooted(MutableTree& t, const bool* keep, int root,
                         std::vector<int>& preorder, std::vector<int>& stk) {

    if (t.is_leaf(root) && keep[root]) return root;

    // Phase 1: pre-order collection (kept leaves are terminals, not expanded).
    preorder.clear();
    stk.clear();
    stk.push_back(root);

    while (!stk.empty()) {
        int v = stk.back(); stk.pop_back();
        if (t.is_leaf(v) && keep[v]) continue;
        preorder.push_back(v);

        if (t.ch[v][1] != NULL_NODE) stk.push_back(t.ch[v][1]);
        if (t.ch[v][0] != NULL_NODE) stk.push_back(t.ch[v][0]);
    }

    // Phase 2: post-order removal — children are processed before their parent.
    for (int i = static_cast<int>(preorder.size()) - 1; i >= 0; --i) {
        int v = preorder[i];
        if (t.out_deg(v) == 0)
            t.remove_node(v);
    }

    // Phase 3: walk off degree-1 chain at the root.
    while (t.alive[root] && !t.is_leaf(root) && t.out_deg(root) == 1) {
        int child        = t.only_child(root);
        t.par[child]     = NULL_NODE;
        t.ch[root]       = {NULL_NODE, NULL_NODE};
        t.alive[root]    = false;
        root             = child;
    }

    return root;
}

// Like remove_rooted but also contracts all degree-1 internal nodes bottom-up.
// Returns the new root, or NULL_NODE if no kept leaf survived.
static int remove_contract_rooted(MutableTree& t, const bool* keep, int root,
                                   std::vector<int>& preorder, std::vector<int>& stk) {

    if (t.is_leaf(root) && keep[root]) return root;

    preorder.clear();
    stk.clear();
    stk.push_back(root);

    while (!stk.empty()) {
        int v = stk.back(); stk.pop_back();
        if (t.is_leaf(v) && keep[v]) continue;
        preorder.push_back(v);
        if (t.ch[v][1] != NULL_NODE) stk.push_back(t.ch[v][1]);
        if (t.ch[v][0] != NULL_NODE) stk.push_back(t.ch[v][0]);
    }

    int new_root = root;
    for (int i = static_cast<int>(preorder.size()) - 1; i >= 0; --i) {
        int v   = preorder[i];
        int deg = t.out_deg(v);
        if (deg == 0) {
            t.remove_node(v);
            if (v == new_root) new_root = NULL_NODE;
        } else if (deg == 1) {
            int child = t.only_child(v);
            t.contract_node(v);
            if (v == new_root) new_root = child;
        }
    }

    return new_root;
}

// Recursive-descent Newick parser; internal node IDs assigned in post-order.
struct NewickParser {
    const std::string& s;
    int         n_leaves;
    std::size_t pos          = 0;
    int         next_internal;  // incremented before use, starts at n_leaves
    PhyloTree&  tree;

    int parse_node() {
        if (s[pos] == '(') {
            ++pos;
            int left = parse_node();
            assert(s[pos] == ','); ++pos;
            int right = parse_node();
            assert(s[pos] == ')'); ++pos;
            int id = ++next_internal;
            tree.add_edge(id, left);
            tree.add_edge(id, right);
            return id;
        }
        // Leaf: read integer label.
        int leaf_id = 0;
        while (pos < s.size() && std::isdigit(static_cast<unsigned char>(s[pos])))
            leaf_id = leaf_id * 10 + (s[pos++] - '0');
        assert(leaf_id >= 1 && leaf_id <= n_leaves);
        return leaf_id;
    }
};

static PhyloTree parse_newick(const std::string& s, int n_leaves) {
    assert(!s.empty() && s.back() == ';');
    PhyloTree tree;

    tree.init(n_leaves, 2 * n_leaves - 1, NULL_NODE);
    tree.edges.reserve(2 * n_leaves - 2);

    NewickParser parser{s, n_leaves, 0, n_leaves, tree};
    tree.root = parser.parse_node();
    assert(parser.s[parser.pos] == ';');
    return tree;
}

struct Input {
    std::vector<PhyloTree> trees;
    int n_leaves = 0;
};

// Parse PACE 2026 format: "#p n_trees n_leaves" header, then n_trees Newick lines.
static Input read_input(std::istream& in) {
    Input result;
    int n_trees   = 0;
    int n_pending = 0;

    std::string line;
    while (std::getline(in, line)) {

        while (!line.empty() && (line.back() == '\r' || line.back() == ' '))
            line.pop_back();

        if (line.empty()) continue;

        if (line[0] == '#') {
            std::istringstream meta(line.substr(1));
            std::string key;
            if (!(meta >> key)) continue;
            if (key == "p") {
                meta >> n_trees >> result.n_leaves;
                n_pending = n_trees;
                result.trees.reserve(n_trees);
            }
            // '#a' and '#x' lines are irrelevant to the heuristic and ignored.
        } else {
            assert(result.n_leaves > 0 && "tree line encountered before '#p' header");
            assert(line.back() == ';');
            result.trees.push_back(parse_newick(line, result.n_leaves));
            if (--n_pending == 0) break;
        }
    }

    assert(static_cast<int>(result.trees.size()) == n_trees);
    return result;
}

// Iterative Newick serialiser. Children sorted by node ID (ascending) to match
// Python's sorted(g[root]) and produce a canonical output string.
static std::string newick(const MutableTree& t, int root) {
    struct Frame { int v; bool children_pushed; };
    std::vector<Frame>       work_stk;
    std::vector<std::string> out_stk;

    work_stk.push_back({root, false});

    while (!work_stk.empty()) {
        auto& [v, pushed] = work_stk.back();

        int c0 = t.ch[v][0], c1 = t.ch[v][1];
        if (c0 != NULL_NODE && c1 != NULL_NODE && c0 > c1) std::swap(c0, c1);

        const int n_ch = (c0 != NULL_NODE) + (c1 != NULL_NODE);

        if (n_ch == 0) {
            out_stk.push_back(std::to_string(v));
            work_stk.pop_back();
        } else if (!pushed) {
            pushed = true;
            if (c1 != NULL_NODE) work_stk.push_back({c1, false});
            if (c0 != NULL_NODE) work_stk.push_back({c0, false});
        } else {
            work_stk.pop_back();
            std::string s = "(";
            if (n_ch == 1) {
                s += out_stk.back();
                out_stk.pop_back();
            } else {
                // c1 result on top (processed last), c0 result below (processed first).
                std::string s1 = out_stk.back(); out_stk.pop_back();
                std::string s0 = out_stk.back(); out_stk.pop_back();
                s += s0;
                s += ',';
                s += s1;
            }
            s += ')';
            out_stk.push_back(std::move(s));
        }
    }

    assert(out_stk.size() == 1);
    return out_stk.front();
}

static void write_forest(const std::vector<std::pair<MutableTree, int>>& forest) {
    for (std::size_t i = 0; i < forest.size(); ++i) {
        if (i > 0) std::cout << '\n';
        std::cout << newick(forest[i].first, forest[i].second) << ';';
    }
    std::cout << '\n';
}


// Persistent scratch buffers for agreement_check — allocated once, reused every call.
struct AgreementScratch {
    MutableTree t1, t2, t2_removed;

    std::unique_ptr<bool[]> keep_all_buf; // keep_all[v] = true for all leaves
    bool*                   keep_all = nullptr;
    std::unique_ptr<bool[]> in_s_buf; // in_s[v] = true for leaves in current S
    bool*                   in_s     = nullptr;

    std::vector<int> dfs_stk, t1_roots, preorder, stk;

    struct HashFrame { int v; bool visited; };
    std::vector<HashFrame> hash_work;
    std::vector<uint64_t>  hash_out;

    void init(int n_nodes, int n_leaves) {
        keep_all_buf = std::make_unique<bool[]>(n_nodes + 1);
        keep_all     = keep_all_buf.get();
        std::fill(keep_all, keep_all + n_nodes + 1, false);
        for (int v = 1; v <= n_leaves; ++v) keep_all[v] = true;

        in_s_buf = std::make_unique<bool[]>(n_leaves + 1);
        in_s     = in_s_buf.get();
        std::fill(in_s, in_s + n_leaves + 1, false);

        dfs_stk  .reserve(n_nodes);
        t1_roots .reserve(n_nodes);
        preorder .reserve(n_nodes);
        stk      .reserve(n_nodes);
        hash_work.reserve(n_nodes);
        hash_out .reserve(n_nodes);
    }
};


// FNV-1a based subtree hash. Children sorted by hash value → canonical regardless
// of internal node ID ordering (which differs between T1 and T2).
static constexpr uint64_t HASH_FNV_PRIME  = 1099511628211ULL;
static constexpr uint64_t HASH_FNV_OFFSET = 14695981039346656037ULL;
static constexpr uint64_t HASH_INTERNAL   = 0xdeadbeefcafe1234ULL;

static uint64_t hash_leaf_id(int v) noexcept {
    return (HASH_FNV_OFFSET ^ static_cast<uint64_t>(v)) * HASH_FNV_PRIME;
}

static uint64_t hash_mix(uint64_t h0, uint64_t h1) noexcept {
    h0 ^= h1 + 0x9e3779b97f4a7c15ULL + (h0 << 6) + (h0 >> 2);
    return h0;
}

static uint64_t subtree_hash(const MutableTree& t, int root,
                              std::vector<AgreementScratch::HashFrame>& work,
                              std::vector<uint64_t>& out) {
    work.clear();
    out .clear();
    work.reserve(t.n_nodes);
    work.push_back({root, false});
    while (!work.empty()) {
        const int  v       = work.back().v;
        const bool visited = work.back().visited;
        if (t.is_leaf(v)) {
            out.push_back(hash_leaf_id(v));
            work.pop_back();
            continue;
        }
        const int c0 = t.ch[v][0], c1 = t.ch[v][1];
        if (!visited) {
            work.back().visited = true;
            if (c1 != NULL_NODE) work.push_back({c1, false});
            if (c0 != NULL_NODE) work.push_back({c0, false});
        } else {
            work.pop_back();
            const int n = (c0 != NULL_NODE) + (c1 != NULL_NODE);
            uint64_t h;
            if (n == 2) {
                uint64_t hb = out.back(); out.pop_back();
                uint64_t ha = out.back(); out.pop_back();
                if (ha > hb) std::swap(ha, hb); // sort → canonical order
                h = hash_mix(hash_mix(HASH_FNV_OFFSET, ha), hb);
            } else {
                uint64_t hc = out.back(); out.pop_back();
                h = hash_mix(HASH_FNV_OFFSET, hc);
            }
            out.push_back(hash_mix(h, HASH_INTERNAL));
        }
    }
    return out.front();
}


// Returns true iff every contracted T1 component matches a T2 subtree restricted
// to the same leaf set. Implements AgreementSpec from the Python original.
static bool agreement_check(const MutableForest& forest, const PhyloTree& T2,
                             AgreementScratch& sc) {
    const int n_leaves = forest.src.n_leaves;
    const int n_nodes  = forest.src.n_nodes;

    // Step 1: snapshot T1 subgraph; contract each WCC and collect non-empty roots.
    forest.snapshot_into(sc.t1);
    sc.t1_roots.clear();
    for (int v = 1; v <= n_nodes; ++v) {
        if (!sc.t1.alive[v] || sc.t1.par[v] != NULL_NODE) continue;
        int r = remove_contract_rooted(sc.t1, sc.keep_all, v,
                                       sc.preorder, sc.stk);
        if (r != NULL_NODE) sc.t1_roots.push_back(r);
    }

    // Step 2: reset T2 working copy.
    sc.t2.refill_from(T2);

    for (const int t1_root : sc.t1_roots) {

        // 3a: collect leaf set S from this T1 component.
        int s_size = 0;
        sc.dfs_stk.push_back(t1_root);
        while (!sc.dfs_stk.empty()) {
            int v = sc.dfs_stk.back(); sc.dfs_stk.pop_back();
            if (sc.t1.is_leaf(v)) { sc.in_s[v] = true; ++s_size; continue; }
            if (sc.t1.ch[v][0] != NULL_NODE) sc.dfs_stk.push_back(sc.t1.ch[v][0]);
            if (sc.t1.ch[v][1] != NULL_NODE) sc.dfs_stk.push_back(sc.t1.ch[v][1]);
        }

        // 3b: find the T2 WCC that contains all of S; partial overlap → false.
        int wcc_root = NULL_NODE;
        for (int v = 1; v <= n_nodes && wcc_root == NULL_NODE; ++v) {
            if (!sc.t2.alive[v] || sc.t2.par[v] != NULL_NODE) continue;
            int found_s = 0;
            sc.dfs_stk.push_back(v);
            while (!sc.dfs_stk.empty()) {
                int u = sc.dfs_stk.back(); sc.dfs_stk.pop_back();
                if (sc.t2.is_leaf(u) && sc.in_s[u]) ++found_s;
                if (sc.t2.ch[u][0] != NULL_NODE) sc.dfs_stk.push_back(sc.t2.ch[u][0]);
                if (sc.t2.ch[u][1] != NULL_NODE) sc.dfs_stk.push_back(sc.t2.ch[u][1]);
            }
            if (found_s == 0)     continue;
            if (found_s < s_size) return false;
            wcc_root = v;
        }
        if (wcc_root == NULL_NODE) return false;

        // 3c: prune T2 WCC to S.
        sc.t2_removed.copy_from(sc.t2);
        int new_wcc_root = remove_rooted(sc.t2_removed, sc.in_s, wcc_root,
                                          sc.preorder, sc.stk);

        // Consume the matched T2 subtree so it won't be reused by later t1_roots.
        sc.dfs_stk.push_back(new_wcc_root);
        while (!sc.dfs_stk.empty()) {
            int u = sc.dfs_stk.back(); sc.dfs_stk.pop_back();
            sc.t2.alive[u] = false;
            if (sc.t2_removed.ch[u][0] != NULL_NODE) sc.dfs_stk.push_back(sc.t2_removed.ch[u][0]);
            if (sc.t2_removed.ch[u][1] != NULL_NODE) sc.dfs_stk.push_back(sc.t2_removed.ch[u][1]);
        }

        // 3d: contract the pruned T2 subtree.
        int contracted_root = remove_contract_rooted(sc.t2_removed, sc.in_s,
                                                      new_wcc_root,
                                                      sc.preorder, sc.stk);
        assert(contracted_root != NULL_NODE);

        // 3e: topology comparison via hash (children sorted by hash → canonical).
        const uint64_t h1 = subtree_hash(sc.t1,         t1_root,
                                          sc.hash_work, sc.hash_out);
        const uint64_t h2 = subtree_hash(sc.t2_removed, contracted_root,
                                          sc.hash_work, sc.hash_out);
        if (h1 != h2) return false;

        std::fill(sc.in_s, sc.in_s + n_leaves + 1, false);
    }

    return true;
}

// Snapshot the committed forest, contract each leaf-bearing component, and return
// one (MutableTree, root) pair per component for output.
static std::vector<std::pair<MutableTree, int>>
prepare_solution(const MutableForest& forest) {
    const int n_leaves = forest.src.n_leaves;
    const int n_nodes  = forest.src.n_nodes;

    MutableTree t = forest.snapshot();

    auto keep_all_buf = std::make_unique<bool[]>(n_nodes + 1);
    bool* keep_all = keep_all_buf.get();
    std::fill(keep_all, keep_all + n_nodes + 1, false);
    for (int v = 1; v <= n_leaves; ++v) keep_all[v] = true;

    std::vector<int> preorder, stk;
    preorder.reserve(n_nodes);
    stk.reserve(n_nodes);

    std::vector<int> contracted_roots;
    for (int v = 1; v <= n_nodes; ++v) {
        if (forest.par[v] != NULL_NODE) continue;
        if (forest.dsu.leaf_cnt[forest.dsu.find(v)] == 0) continue; // no leaves → skip
        int r = remove_contract_rooted(t, keep_all, v, preorder, stk);
        assert(r != NULL_NODE);
        contracted_roots.push_back(r);
    }

    // Share t for all but the last component; move into last to avoid a copy.
    std::vector<std::pair<MutableTree, int>> result;
    result.reserve(contracted_roots.size());
    for (std::size_t i = 0; i < contracted_roots.size(); ++i) {
        if (i + 1 < contracted_roots.size())
            result.emplace_back(t, contracted_roots[i]);
        else
            result.emplace_back(std::move(t), contracted_roots[i]);
    }
    return result;
}

volatile sig_atomic_t g_stop = 0;

static void handle_signal(int) { g_stop = 1; }


// DeltaSearch outer loop: repeatedly shuffles T1 edges, then commits batches via
// a doubling bisection scheme (n doubles each level, slices processed high→low).
struct GraphSeeker {
    const PhyloTree& T1;
    const PhyloTree& T2;
    int              n_leaves;
    MutableForest    forest;
    AgreementScratch scratch;  // reused across all agreement_check calls
    int              best_score;
    std::vector<std::pair<MutableTree, int>> best_output;
    std::mt19937     rng;

    GraphSeeker(const PhyloTree& t1, const PhyloTree& t2, int nl)
        : T1(t1), T2(t2), n_leaves(nl),
          forest(t1),
          best_score(forest.score()),
          rng(std::random_device{}())
    {
        scratch.init(t1.n_nodes, t1.n_leaves);
    }

    void run() {
        std::vector<int> c;
        c.reserve(T1.edges.size());
        c.resize(T1.edges.size());
        std::iota(c.begin(), c.end(), 0);
        std::shuffle(c.begin(), c.end(), rng);

#ifdef DEBUG_AGREEMENT
        int pass_count = 0;
#endif

        while (true) {

            forest.reset();
            int cur_score = forest.score();
            int n = 1;
#ifdef DEBUG_AGREEMENT
            ++pass_count;
            if (pass_count <= 5) {
                std::cerr << "Pass " << pass_count << ": c=[";
                for (int x : c) std::cerr << x << ",";
                std::cerr << "] cur_score=" << cur_score << "\n";
            }
#endif

            while (n < static_cast<int>(c.size())) {
                const int sz = static_cast<int>(c.size());
                n = std::min(2 * n, sz);
                const int k = sz / n;
                const int m = sz % n;

                // Iterate slices high→low so erasing slice i doesn't disturb slices 0..i-1.
                for (int i = n - 1; i >= 0; --i) {
                    if (g_stop) return;
                    const int lo = i * k + std::min(i, m);
                    const int hi = (i + 1) * k + std::min(i + 1, m);

                    auto cp = forest.save();
                    for (int j = lo; j < hi; ++j)
                        forest.add_edge(c[j]);

                    bool ag = agreement_check(forest, T2, scratch);
                    int tst_score = forest.score();
#ifdef DEBUG_AGREEMENT
                    if (pass_count <= 5 && n <= 4) {
                        std::cerr << "  n=" << n << " i=" << i << " lo=" << lo << " hi=" << hi
                                  << " edges=[";
                        for (int j = lo; j < hi; ++j) std::cerr << c[j] << ",";
                        std::cerr << "] score=" << tst_score << " agree=" << ag << "\n";
                    }
#endif
                    if (ag) {
                        if (tst_score > cur_score) {
                            cur_score = tst_score;
                            c.erase(c.begin() + lo, c.begin() + hi);
                            if (cur_score > best_score) {
                                best_score  = cur_score;
                                best_output = prepare_solution(forest);
                            }
                            continue; // slice committed — do NOT restore
                        }
                    }
                    forest.restore(cp);
                }
            }

            if (g_stop) return;
#ifdef SINGLE_PASS
            return;
#endif
            c.resize(T1.edges.size());
            std::iota(c.begin(), c.end(), 0);
            std::shuffle(c.begin(), c.end(), rng);
        }
    }
};


int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    Input inp = read_input(std::cin);
    assert(inp.trees.size() == 2);
    const PhyloTree& T1 = inp.trees[0];
    const PhyloTree& T2 = inp.trees[1];
    const int n_leaves  = inp.n_leaves;

    struct sigaction sa;
    std::memset(&sa, 0, sizeof(sa));
    sa.sa_handler = handle_signal;
    sigaction(SIGTERM, &sa, nullptr);
    sigaction(SIGINT,  &sa, nullptr);

    GraphSeeker seeker(T1, T2, n_leaves);

    // Pre-fill best_output with n_leaves singletons so SIGTERM always yields valid output.
    seeker.best_output.reserve(n_leaves);
    for (int l = 1; l <= n_leaves; ++l) {
        MutableTree mt;
        mt.n_leaves = n_leaves;
        mt.n_nodes  = 2 * n_leaves - 1;
        mt.par  .assign(mt.n_nodes + 1, NULL_NODE);
        mt.ch   .assign(mt.n_nodes + 1, {NULL_NODE, NULL_NODE});
        mt.alive.assign(mt.n_nodes + 1, false);
        mt.alive[l] = true;
        seeker.best_output.emplace_back(std::move(mt), l);
    }

#ifdef DEBUG_AGREEMENT
    {
        AgreementScratch sc;
        sc.init(T1.n_nodes, T1.n_leaves);
        MutableForest dbg(T1);
        std::cerr << "T1 edges:\n";
        for (int i = 0; i < (int)T1.edges.size(); ++i)
            std::cerr << "  [" << i << "] " << T1.edges[i].first << " -> " << T1.edges[i].second << "\n";

        std::cerr << "\nTwo-edge agreement checks:\n";
        for (int a = 0; a < (int)T1.edges.size(); ++a) {
            for (int b = a+1; b < (int)T1.edges.size(); ++b) {
                dbg.reset();
                dbg.add_edge(a); dbg.add_edge(b);
                if (dbg.score() > -n_leaves) {
                    bool ok = agreement_check(dbg, T2, sc);
                    std::cerr << "  [" << a << "," << b << "] score=" << dbg.score()
                              << " agree=" << ok << "\n";
                }
            }
        }
    }
#endif

    seeker.run();

    write_forest(seeker.best_output);
    return 0;
}
