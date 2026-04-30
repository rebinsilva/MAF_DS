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
    int n_leaves = 0, n_nodes = 0, root = NULL_NODE;
    std::vector<int>                par;
    std::vector<std::array<int,2>> ch;
    std::vector<std::pair<int,int>> edges; // all (parent,child) edges in preorder

    void init(int nl, int nn, int r) {
        n_leaves = nl; n_nodes = nn; root = r;
        par  .assign(nn + 1, NULL_NODE);
        ch   .assign(nn + 1, {NULL_NODE, NULL_NODE});
        edges.clear();
    }

    void add_edge(int p, int c) {
        assert(ch[p][0] == NULL_NODE || ch[p][1] == NULL_NODE);
        (ch[p][0] == NULL_NODE ? ch[p][0] : ch[p][1]) = c;
        par[c] = p;
        edges.emplace_back(p, c);
    }

    bool is_leaf (int v) const noexcept { return v >= 1 && v <= n_leaves; }
    int  out_deg (int v) const noexcept { return (ch[v][0] != NULL_NODE) + (ch[v][1] != NULL_NODE); }
};


// Mutable copy of a tree used inside agreement_check for local pruning/contraction.
struct MutableTree {
    int n_leaves = 0, n_nodes = 0;
    std::vector<int>                par;
    std::vector<std::array<int,2>> ch;
    std::vector<bool>               alive;

    MutableTree() = default;
    bool is_leaf(int v) const noexcept { return v >= 1 && v <= n_leaves; }
    int  out_deg(int v) const noexcept { return (ch[v][0] != NULL_NODE) + (ch[v][1] != NULL_NODE); }
    int  only_child(int v) const noexcept { return ch[v][0] != NULL_NODE ? ch[v][0] : ch[v][1]; }

    void unlink_from_parent(int v) {
        int p = par[v]; if (p == NULL_NODE) return;
        (ch[p][0] == v ? ch[p][0] : ch[p][1]) = NULL_NODE;
        par[v] = NULL_NODE;
    }

    void remove_node(int v) {
        unlink_from_parent(v);
        ch[v] = {NULL_NODE, NULL_NODE};
        alive[v] = false;
    }

    // Suppress degree-1 internal node v: rewire its parent directly to its child.
    void contract_node(int v) {
        int c = only_child(v), p = par[v];
        par[c] = p;
        if (p != NULL_NODE) (ch[p][0] == v ? ch[p][0] : ch[p][1]) = c;
        ch[v] = {NULL_NODE, NULL_NODE}; par[v] = NULL_NODE; alive[v] = false;
    }

    // Refill in place from a PhyloTree, reusing existing vector capacity.
    void refill_from(const PhyloTree& t) {
        n_leaves = t.n_leaves; n_nodes = t.n_nodes;
        par = t.par; ch = t.ch;
        alive.assign(t.n_nodes + 1, true); alive[NULL_NODE] = false;
    }

    void copy_from(const MutableTree& o) {
        n_leaves = o.n_leaves; n_nodes = o.n_nodes;
        par = o.par; ch = o.ch; alive = o.alive;
    }
};


// Union-by-rank DSU without path compression so every write is O(1)-reversible.
// Tracks n_leaf_comps: components containing at least one leaf; score = -n_leaf_comps.
struct DSU {
    std::vector<int> rep, rnk, leaf_cnt;
    int n_leaf_comps = 0;

    struct Undo { int cr, pr, old_rnk, old_lc_c, old_lc_p; bool merged; };
    std::vector<Undo> history;

    DSU() = default;
    DSU(int nn, int nl) {
        rep.resize(nn+1); rnk.assign(nn+1,0); leaf_cnt.assign(nn+1,0);
        for (int i=1;i<=nn;++i) rep[i]=i;
        for (int i=1;i<=nl;++i) leaf_cnt[i]=1;
        n_leaf_comps = nl;
    }

    int find(int v) const noexcept { while (rep[v]!=v) v=rep[v]; return v; }

    void unite(int u, int v) {
        u=find(u); v=find(v);
        if (u==v) { history.push_back({u,v,0,0,0,false}); return; }
        if (rnk[u]>rnk[v]) std::swap(u,v);
        Undo ud{u,v,rnk[v],leaf_cnt[u],leaf_cnt[v],false};
        rep[u]=v; if (rnk[u]==rnk[v]) ++rnk[v];
        bool ul=(leaf_cnt[u]>0), vl=(leaf_cnt[v]>0);
        leaf_cnt[v]+=leaf_cnt[u]; leaf_cnt[u]=0;
        if (ul&&vl) { --n_leaf_comps; ud.merged=true; }
        history.push_back(ud);
    }

    int  save()  const noexcept { return (int)history.size(); }
    int  score() const noexcept { return -n_leaf_comps; }

    // Refill in place to avoid reallocation on each outer-loop reset.
    void reset(int nl) {
        std::iota(rep.begin()+1, rep.end(), 1);
        std::fill(rnk.begin()+1,      rnk.end(),      0);
        std::fill(leaf_cnt.begin()+1,  leaf_cnt.end(), 0);
        for (int i=1;i<=nl;++i) leaf_cnt[i]=1;
        n_leaf_comps=nl; history.clear();
    }

    void restore(int cp) {
        while ((int)history.size()>cp) {
            auto [cr,pr,or_,lc_c,lc_p,mg] = history.back(); history.pop_back();
            if (cr==pr) continue;
            rep[cr]=cr; rnk[pr]=or_; leaf_cnt[cr]=lc_c; leaf_cnt[pr]=lc_p;
            if (mg) ++n_leaf_comps;
        }
    }
};


// Incrementally built edge-subset of T1; supports O(batch) checkpoint/restore.
struct MutableForest {
    const PhyloTree& src;
    std::vector<bool>               edge_on;
    std::vector<int>                par;
    std::vector<std::array<int,2>> ch;
    std::vector<int>                n_ch;
    DSU dsu;

    struct Checkpoint { int dsu_cp, ops_cp; };
    std::vector<int> ops; // ordered log of added edge indices for rollback

    explicit MutableForest(const PhyloTree& s)
        : src(s), edge_on(s.edges.size(),false),
          par(s.n_nodes+1,NULL_NODE), ch(s.n_nodes+1,{NULL_NODE,NULL_NODE}),
          n_ch(s.n_nodes+1,0), dsu(s.n_nodes,s.n_leaves) {}

    void add_edge(int idx) {
        auto [p,c] = src.edges[idx];
        edge_on[idx]=true; par[c]=p; ch[p][n_ch[p]++]=c;
        dsu.unite(p,c); ops.push_back(idx);
    }

    Checkpoint save()  const noexcept { return {dsu.save(),(int)ops.size()}; }
    int        score() const noexcept { return dsu.score(); }

    void restore(Checkpoint cp) {
        while ((int)ops.size()>cp.ops_cp) { remove_raw(ops.back()); ops.pop_back(); }
        dsu.restore(cp.dsu_cp);
    }

    void reset() {
        std::fill(edge_on.begin(),edge_on.end(),false);
        std::fill(par.begin(),par.end(),NULL_NODE);
        std::fill(ch.begin(),ch.end(),std::array<int,2>{NULL_NODE,NULL_NODE});
        std::fill(n_ch.begin(),n_ch.end(),0);
        ops.clear(); dsu.reset(src.n_leaves);
    }

    MutableTree snapshot() const {
        MutableTree mt;
        mt.n_leaves=src.n_leaves; mt.n_nodes=src.n_nodes;
        mt.par=par; mt.ch=ch;
        mt.alive.assign(src.n_nodes+1,true); mt.alive[NULL_NODE]=false;
        return mt;
    }

    void snapshot_into(MutableTree& mt) const {
        mt.n_leaves=src.n_leaves; mt.n_nodes=src.n_nodes;
        mt.par=par; mt.ch=ch;
        mt.alive.assign(src.n_nodes+1,true); mt.alive[NULL_NODE]=false;
    }

private:
    // Remove edge from adjacency only; DSU rolled back separately via history.
    void remove_raw(int idx) {
        auto [p,c] = src.edges[idx];
        edge_on[idx]=false; par[c]=NULL_NODE;
        if (ch[p][0]==c) { ch[p][0]=ch[p][1]; ch[p][1]=NULL_NODE; }
        else              {                     ch[p][1]=NULL_NODE; }
        --n_ch[p];
    }
};


// Prune t to kept leaves. If contract=true, also suppresses degree-1 internals.
// Returns new root; contract=false guarantees non-NULL (caller ensures >=1 kept leaf).
static int prune_tree(MutableTree& t, const bool* keep, int root,
                      std::vector<int>& pre, std::vector<int>& stk, bool contract) {
    if (t.is_leaf(root) && keep[root]) return root;
    pre.clear(); stk.clear(); stk.push_back(root);
    while (!stk.empty()) {
        int v = stk.back(); stk.pop_back();
        if (t.is_leaf(v) && keep[v]) continue;
        pre.push_back(v);
        if (t.ch[v][1]!=NULL_NODE) stk.push_back(t.ch[v][1]);
        if (t.ch[v][0]!=NULL_NODE) stk.push_back(t.ch[v][0]);
    }
    int nr = root;
    for (int i=(int)pre.size()-1; i>=0; --i) {
        int v=pre[i], deg=t.out_deg(v);
        if (deg==0) { t.remove_node(v); if (v==nr) nr=NULL_NODE; }
        else if (contract && deg==1) { int c=t.only_child(v); t.contract_node(v); if (v==nr) nr=c; }
    }
    if (!contract) // walk off degree-1 root chain
        while (t.alive[nr] && !t.is_leaf(nr) && t.out_deg(nr)==1) {
            int c=t.only_child(nr);
            t.par[c]=NULL_NODE; t.ch[nr]={NULL_NODE,NULL_NODE}; t.alive[nr]=false; nr=c;
        }
    return nr;
}


struct NewickParser {
    const std::string& s; int n_leaves; std::size_t pos=0; int next; PhyloTree& tree;

    int parse_node() {
        if (s[pos]!='(') {
            int id=0;
            while (pos<s.size() && std::isdigit((unsigned char)s[pos])) id=id*10+(s[pos++]-'0');
            assert(id>=1 && id<=n_leaves); return id;
        }
        ++pos;
        int L=parse_node(); assert(s[pos++]==',');
        int R=parse_node(); assert(s[pos++]==')');
        int id=++next; tree.add_edge(id,L); tree.add_edge(id,R); return id;
    }
};

static PhyloTree parse_newick(const std::string& s, int nl) {
    assert(!s.empty() && s.back()==';');
    PhyloTree t; t.init(nl, 2*nl-1, NULL_NODE); t.edges.reserve(2*nl-2);
    NewickParser p{s, nl, 0, nl, t};
    t.root = p.parse_node();
    return t;
}

static std::pair<std::vector<PhyloTree>,int> read_input(std::istream& in) {
    std::vector<PhyloTree> trees; int n_leaves=0, n_trees=0, pending=0;
    std::string line;
    while (std::getline(in, line)) {
        while (!line.empty() && (line.back()=='\r'||line.back()==' ')) line.pop_back();
        if (line.empty()) continue;
        if (line[0]=='#') {
            std::istringstream m(line.substr(1)); std::string key;
            if (!(m>>key)) continue;
            if (key=="p") { m>>n_trees>>n_leaves; pending=n_trees; trees.reserve(n_trees); }
        } else {
            assert(n_leaves>0 && line.back()==';');
            trees.push_back(parse_newick(line, n_leaves));
            if (--pending==0) break;
        }
    }
    assert((int)trees.size()==n_trees);
    return {std::move(trees), n_leaves};
}

// Iterative Newick serialiser; children sorted by node ID to match Python's sorted(g[root]).
static std::string newick(const MutableTree& t, int root) {
    struct Frame { int v; bool pushed; };
    std::vector<Frame>       ws; ws.push_back({root,false});
    std::vector<std::string> os;
    while (!ws.empty()) {
        auto& [v,pushed] = ws.back();
        int c0=t.ch[v][0], c1=t.ch[v][1];
        if (c0!=NULL_NODE && c1!=NULL_NODE && c0>c1) std::swap(c0,c1);
        int nc=(c0!=NULL_NODE)+(c1!=NULL_NODE);
        if (nc==0) { os.push_back(std::to_string(v)); ws.pop_back(); }
        else if (!pushed) { pushed=true; if(c1!=NULL_NODE)ws.push_back({c1,false}); if(c0!=NULL_NODE)ws.push_back({c0,false}); }
        else {
            ws.pop_back();
            std::string s="(";
            if (nc==1) { s+=os.back(); os.pop_back(); }
            else { std::string s1=os.back();os.pop_back(); std::string s0=os.back();os.pop_back(); s+=s0+','+s1; }
            os.push_back(s+')');
        }
    }
    return os.front();
}

static void write_forest(const std::vector<std::pair<MutableTree,int>>& f) {
    for (std::size_t i=0; i<f.size(); ++i) {
        if (i>0) std::cout<<'\n';
        std::cout << newick(f[i].first, f[i].second) << ';';
    }
    std::cout<<'\n';
}


// Persistent scratch buffers for agreement_check — allocated once, reused every call.
struct AgreementScratch {
    MutableTree t1, t2, t2r;
    std::unique_ptr<bool[]> keep_buf, in_s_buf;
    bool *keep=nullptr, *in_s=nullptr;
    std::vector<int> dfs, roots, pre, stk;
    std::vector<int> ml1, ml2;                 // min leaf ID under each node in t1 / t2r
    std::vector<std::pair<int,int>> cmp_stk;   // scratch for trees_equal

    void init(int nn, int nl) {
        keep_buf=std::make_unique<bool[]>(nn+1); keep=keep_buf.get();
        std::fill(keep,keep+nn+1,false); for(int i=1;i<=nl;++i) keep[i]=true;
        in_s_buf=std::make_unique<bool[]>(nl+1); in_s=in_s_buf.get();
        std::fill(in_s,in_s+nl+1,false);
        dfs.reserve(nn); roots.reserve(nn); pre.reserve(nn); stk.reserve(nn);
        ml1.resize(nn+1); ml2.resize(nn+1); cmp_stk.reserve(nn);
    }
};


// Compute min leaf ID in the subtree rooted at each node.
// Uses negative encoding on stk: push v to pre-visit, pop -v for post-visit.
static void compute_min_leaf(const MutableTree& t, int root,
                              std::vector<int>& stk, std::vector<int>& ml) {
    stk.clear(); stk.push_back(root);
    while (!stk.empty()) {
        int v = stk.back();
        if (v < 0) {
            stk.pop_back(); v = -v;
            int c0=t.ch[v][0], c1=t.ch[v][1];
            ml[v] = std::numeric_limits<int>::max();
            if (c0!=NULL_NODE) ml[v]=std::min(ml[v], ml[c0]);
            if (c1!=NULL_NODE) ml[v]=std::min(ml[v], ml[c1]);
        } else if (t.is_leaf(v)) {
            stk.pop_back(); ml[v]=v;
        } else {
            stk.back()=-v;
            int c0=t.ch[v][0], c1=t.ch[v][1];
            if (c1!=NULL_NODE) stk.push_back(c1);
            if (c0!=NULL_NODE) stk.push_back(c0);
        }
    }
}

// Compare two rooted trees structurally: at each internal node, orient both
// children by min_leaf (smaller goes left) then recurse pair-wise.
static bool trees_equal(const MutableTree& t1, int r1,
                         const MutableTree& t2, int r2,
                         const std::vector<int>& ml1, const std::vector<int>& ml2,
                         std::vector<std::pair<int,int>>& stk) {
    stk.clear(); stk.push_back({r1,r2});
    while (!stk.empty()) {
        auto [v1,v2] = stk.back(); stk.pop_back();
        bool l1=t1.is_leaf(v1), l2=t2.is_leaf(v2);
        if (l1!=l2) return false;
        if (l1) { if (v1!=v2) return false; continue; }
        int a=t1.ch[v1][0], b=t1.ch[v1][1];
        int c=t2.ch[v2][0], d=t2.ch[v2][1];
        int d1=(a!=NULL_NODE)+(b!=NULL_NODE), d2=(c!=NULL_NODE)+(d!=NULL_NODE);
        if (d1!=d2) return false;
        if (d1==2) {
            if (ml1[a]>ml1[b]) std::swap(a,b);
            if (ml2[c]>ml2[d]) std::swap(c,d);
            stk.push_back({b,d}); stk.push_back({a,c});
        } else {
            stk.push_back({a!=NULL_NODE?a:b, c!=NULL_NODE?c:d});
        }
    }
    return true;
}


// Returns true iff every contracted T1 component matches the corresponding T2 subtree.
static bool agreement_check(const MutableForest& forest, const PhyloTree& T2,
                             AgreementScratch& sc) {
    const int nl=forest.src.n_leaves, nn=forest.src.n_nodes;
    forest.snapshot_into(sc.t1);
    sc.roots.clear();
    for (int v=1; v<=nn; ++v) {
        if (!sc.t1.alive[v] || sc.t1.par[v]!=NULL_NODE) continue;
        int r=prune_tree(sc.t1, sc.keep, v, sc.pre, sc.stk, true);
        if (r!=NULL_NODE) sc.roots.push_back(r);
    }
    sc.t2.refill_from(T2);

    for (int t1r : sc.roots) {
        // 3a: collect leaf set S from this T1 component.
        int ss=0;
        sc.dfs.push_back(t1r);
        while (!sc.dfs.empty()) {
            int v=sc.dfs.back(); sc.dfs.pop_back();
            if (sc.t1.is_leaf(v)) { sc.in_s[v]=true; ++ss; continue; }
            if (sc.t1.ch[v][0]!=NULL_NODE) sc.dfs.push_back(sc.t1.ch[v][0]);
            if (sc.t1.ch[v][1]!=NULL_NODE) sc.dfs.push_back(sc.t1.ch[v][1]);
        }

        // 3b: find the T2 WCC containing all of S; partial overlap → false.
        int wr=NULL_NODE;
        for (int v=1; v<=nn && wr==NULL_NODE; ++v) {
            if (!sc.t2.alive[v] || sc.t2.par[v]!=NULL_NODE) continue;
            int fs=0;
            sc.dfs.push_back(v);
            while (!sc.dfs.empty()) {
                int u=sc.dfs.back(); sc.dfs.pop_back();
                if (sc.t2.is_leaf(u) && sc.in_s[u]) ++fs;
                if (sc.t2.ch[u][0]!=NULL_NODE) sc.dfs.push_back(sc.t2.ch[u][0]);
                if (sc.t2.ch[u][1]!=NULL_NODE) sc.dfs.push_back(sc.t2.ch[u][1]);
            }
            if (fs==0) continue;
            if (fs<ss)  return false;
            wr=v;
        }
        if (wr==NULL_NODE) return false;

        // 3c: prune T2 WCC to S.
        sc.t2r.copy_from(sc.t2);
        int nwr=prune_tree(sc.t2r, sc.in_s, wr, sc.pre, sc.stk, false);

        // Consume matched T2 subtree so it won't be reused by later t1_roots.
        sc.dfs.push_back(nwr);
        while (!sc.dfs.empty()) {
            int u=sc.dfs.back(); sc.dfs.pop_back();
            sc.t2.alive[u]=false;
            if (sc.t2r.ch[u][0]!=NULL_NODE) sc.dfs.push_back(sc.t2r.ch[u][0]);
            if (sc.t2r.ch[u][1]!=NULL_NODE) sc.dfs.push_back(sc.t2r.ch[u][1]);
        }

        // 3d: contract pruned T2 subtree, then compare topology via min-leaf ordering.
        int cr=prune_tree(sc.t2r, sc.in_s, nwr, sc.pre, sc.stk, true);
        assert(cr!=NULL_NODE);
        compute_min_leaf(sc.t1,  t1r, sc.stk, sc.ml1);
        compute_min_leaf(sc.t2r, cr,  sc.stk, sc.ml2);
        if (!trees_equal(sc.t1, t1r, sc.t2r, cr, sc.ml1, sc.ml2, sc.cmp_stk)) return false;

        std::fill(sc.in_s, sc.in_s+nl+1, false);
    }
    return true;
}

// Snapshot forest, contract each leaf-bearing component, return one (tree,root) per component.
static std::vector<std::pair<MutableTree,int>>
prepare_solution(const MutableForest& forest) {
    const int nl=forest.src.n_leaves, nn=forest.src.n_nodes;
    MutableTree t=forest.snapshot();
    auto kb=std::make_unique<bool[]>(nn+1); bool* keep=kb.get();
    std::fill(keep,keep+nn+1,false); for(int i=1;i<=nl;++i) keep[i]=true;
    std::vector<int> pre,stk; pre.reserve(nn); stk.reserve(nn);
    std::vector<int> roots;
    for (int v=1; v<=nn; ++v) {
        if (forest.par[v]!=NULL_NODE) continue;
        if (forest.dsu.leaf_cnt[forest.dsu.find(v)]==0) continue;
        roots.push_back(prune_tree(t, keep, v, pre, stk, true));
    }
    std::vector<std::pair<MutableTree,int>> res; res.reserve(roots.size());
    for (std::size_t i=0; i<roots.size(); ++i)
        res.emplace_back(i+1<roots.size() ? t : std::move(t), roots[i]);
    return res;
}

volatile sig_atomic_t g_stop = 0;
static void handle_signal(int) { g_stop=1; }


// DeltaSearch outer loop: shuffles T1 edges, commits batches via doubling bisection.
struct GraphSeeker {
    const PhyloTree& T1; const PhyloTree& T2; int n_leaves;
    MutableForest    forest;
    AgreementScratch scratch;
    int              best_score;
    std::vector<std::pair<MutableTree,int>> best_output;
    std::mt19937     rng;

    GraphSeeker(const PhyloTree& t1, const PhyloTree& t2, int nl)
        : T1(t1), T2(t2), n_leaves(nl), forest(t1),
          best_score(forest.score()), rng(42)
    { scratch.init(t1.n_nodes, t1.n_leaves); }

    void run() {
        std::vector<int> c(T1.edges.size());
        std::iota(c.begin(),c.end(),0);
        std::shuffle(c.begin(),c.end(),rng);

        for(int l=0;l < 2;++l) {
            forest.reset();
            int cur=forest.score(), n=1;

            while (n<(int)c.size()) {
                const int sz=(int)c.size();
                n=std::min(2*n,sz);
                const int k=sz/n, m=sz%n;

                // Iterate slices high→low so erasing i doesn't disturb 0..i-1.
                for (int i=n-1; i>=0; --i) {
                    if (g_stop) return;
                    const int lo=i*k+std::min(i,m), hi=(i+1)*k+std::min(i+1,m);
                    auto cp=forest.save();
                    for (int j=lo; j<hi; ++j) forest.add_edge(c[j]);
                    if (agreement_check(forest,T2,scratch)) {
                        int ts=forest.score();
                        if (ts>cur) {
                            cur=ts; c.erase(c.begin()+lo,c.begin()+hi);
                            if (cur>best_score) { best_score=cur; best_output=prepare_solution(forest); }
                            continue;
                        }
                    }
                    forest.restore(cp);
                }
            }

            if (g_stop) return;
            c.resize(T1.edges.size());
            std::iota(c.begin(),c.end(),0);
            std::shuffle(c.begin(),c.end(),rng);
        }
    }
};


int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    auto [trees, n_leaves] = read_input(std::cin);
    assert(trees.size()==2);
    const PhyloTree& T1=trees[0]; const PhyloTree& T2=trees[1];

    struct sigaction sa; std::memset(&sa,0,sizeof(sa));
    sa.sa_handler=handle_signal;
    sigaction(SIGTERM,&sa,nullptr); sigaction(SIGINT,&sa,nullptr);

    GraphSeeker seeker(T1,T2,n_leaves);

    // Pre-fill best_output with n_leaves singletons so SIGTERM always yields valid output.
    seeker.best_output.reserve(n_leaves);
    for (int l=1; l<=n_leaves; ++l) {
        MutableTree mt;
        mt.n_leaves=n_leaves; mt.n_nodes=2*n_leaves-1;
        mt.par  .assign(mt.n_nodes+1,NULL_NODE);
        mt.ch   .assign(mt.n_nodes+1,{NULL_NODE,NULL_NODE});
        mt.alive.assign(mt.n_nodes+1,false);
        mt.alive[l]=true;
        seeker.best_output.emplace_back(std::move(mt),l);
    }

    seeker.run();
    write_forest(seeker.best_output);
    return 0;
}
