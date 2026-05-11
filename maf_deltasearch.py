#!/usr/bin/env python3
import random
import signal
import sys

class _NodeView:
    def __init__(self, nodes):
        self._nodes = nodes

    def __iter__(self):
        return iter(self._nodes)

    def __contains__(self, n):
        return n in self._nodes


class DiGraph:
    def __init__(self):
        self._succ = {}
        self._pred = {}
        self._node = set()

    def __contains__(self, n):
        return n in self._node

    def __iter__(self):
        return iter(self._node)

    def __len__(self):
        return len(self._node)

    def __getitem__(self, n):
        return self._succ[n]

    def _add_node(self, n):
        if n not in self._succ:
            self._succ[n] = {}
            self._pred[n] = {}
            self._node.add(n)

    def add_node(self, n):
        self._add_node(n)

    def remove_node(self, n):
        for s in list(self._succ[n]):
            del self._pred[s][n]
        for p in list(self._pred[n]):
            del self._succ[p][n]
        del self._succ[n]
        del self._pred[n]
        self._node.discard(n)

    def add_edge(self, u, v):
        self._add_node(u)
        self._add_node(v)
        self._succ[u][v] = {}
        self._pred[v][u] = {}

    def add_edges_from(self, edges):
        for e in edges:
            self.add_edge(e[0], e[1])

    def remove_edge(self, u, v):
        del self._succ[u][v]
        del self._pred[v][u]

    def remove_edges_from(self, edges):
        for e in edges:
            u, v = e[0], e[1]
            if u in self._succ and v in self._succ[u]:
                self.remove_edge(u, v)

    def successors(self, n):
        return iter(self._succ[n])

    def predecessors(self, n):
        return iter(self._pred[n])

    def out_degree(self, n):
        return len(self._succ[n])

    def in_degree(self, n=None):
        if n is not None:
            return len(self._pred[n])
        return ((v, len(p)) for v, p in self._pred.items())

    @property
    def nodes(self):
        return _NodeView(self._node)

    def edges(self):
        return ((u, v) for u, nbrs in self._succ.items() for v in nbrs)

    def copy(self):
        G = DiGraph()
        G._node = set(self._node)
        G._succ = {u: dict(nbrs) for u, nbrs in self._succ.items()}
        G._pred = {u: dict(preds) for u, preds in self._pred.items()}
        return G


def create_empty_copy(G):
    H = DiGraph()
    H._node = set(G._node)
    H._succ = {n: {} for n in G._node}
    H._pred = {n: {} for n in G._node}
    return H


def all_leaves_tree(G, source):
    if G.out_degree(source) == 0:
        yield source
    for v in G._succ[source]:
        yield from all_leaves_tree(G, v)


def delete_subtree(G, leaves, source):
    if source in leaves:
        G.remove_node(source)
        return True
    children = list(G._succ[source])
    flag = False
    for v in children:
        if delete_subtree(G, leaves, v):
            flag = True
    if flag:
        G.remove_node(source)
    return flag


def remove_contract_rooted(T, leaves: frozenset, node):
    if node in leaves:
        assert node in T
        return node
    for child in list(T.successors(node)):
        remove_contract_rooted(T, leaves, child)
    out_deg = T.out_degree(node)
    if out_deg == 0:
        T.remove_node(node)
        return None
    elif out_deg == 1:
        child = next(iter(T.successors(node)))
        preds = list(T.predecessors(node))
        if preds:
            T.add_edge(preds[0], child)
        T.remove_node(node)
        return child
    return node


class NumComponentSpec:
    def __init__(self, graph: DiGraph, all_leaves: frozenset):
        self._all_leaves = all_leaves

    def __call__(self, graph: DiGraph) -> float:
        return -len({find_root(graph, leaf) for leaf in self._all_leaves})


def find_root(graph, node):
    while graph.in_degree(node) == 1:
        node = next(iter(graph.predecessors(node)))
    return node


class AgreementSpec:
    def __init__(self, T2: DiGraph, all_leaves: frozenset):
        self._T2 = T2
        self._all_leaves = all_leaves

    def __call__(self, graph: DiGraph):
        roots = [v for v in graph.nodes if graph.in_degree(v) == 0]
        nxt_roots = set()
        T1_contracted = graph.copy()
        for root in roots:
            root = remove_contract_rooted(T1_contracted, self._all_leaves, root)
            if root is not None:
                nxt_roots.add(root)
        T2 = self._T2.copy()
        for T1_root in nxt_roots:
            T1_leaves = set(all_leaves_tree(T1_contracted, T1_root))
            T2_root = find_root(T2, next(iter(T1_leaves)))
            T2_leaves = set(all_leaves_tree(T2, T2_root))

            if not (T2_leaves >= T1_leaves):
                return False, None

            T2_removed = T2.copy()
            T2_root = remove_contract_rooted(T2_removed, T1_leaves, T2_root)

            if tree_to_newick(T1_contracted, root=T1_root) != tree_to_newick(T2_removed, root=T2_root):
                return False, None

            delete_subtree(T2, T1_leaves, T2_root)

        return True, T1_contracted.copy()

class GraphSeeker:
    def __init__(self, graph: DiGraph, leaves: frozenset[int], score, validity):
        self.graph = graph
        self.leaves = leaves
        self.score = score
        self.valid = validity
        self.result = create_empty_copy(self.graph)
        self.best_score = self.score(self.result)
        self.empty_score = self.best_score
        signal.signal(signal.SIGINT, self.exit)
        signal.signal(signal.SIGTERM, self.exit)

    def run(self):
        c = list(self.graph.edges())
        while True:
            n = 1
            cur_soln = list()
            cur_graph = create_empty_copy(self.graph)
            cur_score = self.empty_score
            while n < len(c):
                n = min(2*n, len(c))
                k, m = divmod(len(c), n)
                for i in range(n-1, -1, -1):
                    tst_subset = c[i*k+min(i, m): (i+1)*k+min(i+1,m)]
                    cs = cur_soln + tst_subset
                    cur_graph.add_edges_from(tst_subset)
                    tst_score = self.score(cur_graph)
                    if tst_score > cur_score:
                        agreement, contracted_graph = self.valid(cur_graph)
                        if agreement:
                            cur_score = tst_score
                            cur_soln = cs
                            del c[i*k+min(i, m): (i+1)*k+min(i+1,m)]
                            if cur_score > self.best_score:
                                self.result = contracted_graph
                                self.best_score = cur_score
                                continue
                    cur_graph.remove_edges_from(tst_subset)
            c = list(self.graph.edges())
            random.shuffle(c)

    def prepare_solution(self, graph):
        visited = set()
        out_trees = []
        for leaf in self.leaves:
            if leaf not in visited:
                root = find_root(graph, leaf)
                out_trees.append(tree_to_newick_print(graph, root=root))
                visited.update(all_leaves_tree(graph, root))
        return "\n".join(out_trees)

    def exit(self, signum, frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        print(self.prepare_solution(self.result))
        sys.exit(0)


def read_input(f):
    n_leaves = None
    n_pending_trees = 0
    trees = []

    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            parts = line.lstrip('#').split()
            if parts and parts[0] == 'p':
                n_pending_trees = int(parts[1])
                n_leaves = int(parts[2])
        else:
            assert line.endswith(';'), "Newick string must end with ';'"
            trees.append(parse_newick_to_digraph(line))
            n_pending_trees -= 1
            if n_pending_trees == 0:
                break

    return trees, n_leaves


def tree_to_newick(g, root=None):
    newick_str, _ = _tree_to_newick(g, root=root)
    return newick_str


def _tree_to_newick(g, root=None):
    if root is None:
        roots = [n for n, d in g.in_degree() if d == 0]
        assert len(roots) == 1
        root = roots[0]
    if len(g[root]) == 0:
        return (str(root), root)
    subgs = sorted((_tree_to_newick(g, root=child) for child in g[root]), key=lambda x: x[1])
    return ("(" + ','.join(x[0] for x in subgs) + ")", subgs[0][1])


def tree_to_newick_list(g, result, root):
    if len(g[root]) == 0:
        result.append(str(root))
        return
    result.append("(")
    for child in g[root]:
        tree_to_newick_list(g, result, root=child)
        result.append(',')
    result[-1] = ')'


def tree_to_newick_print(g, root):
    result = []
    tree_to_newick_list(g, result, root=root)
    result.append(';')
    return ''.join(result)


def parse_newick_to_digraph(newick_str: str) -> DiGraph:
    newick_str = newick_str.strip().rstrip(";")
    G = DiGraph()
    stack = []
    node_id = -1
    current_parent = None
    token = ""

    def new_internal():
        nonlocal node_id
        node = node_id
        node_id -= 1
        G.add_node(node)
        return node

    for char in newick_str:
        if char == "(":
            node = new_internal()
            if current_parent is not None:
                G.add_edge(current_parent, node)
            stack.append(current_parent)
            current_parent = node
        elif char == ",":
            if token.strip():
                leaf = int(token.strip())
                G.add_node(leaf)
                G.add_edge(current_parent, leaf)
                token = ""
        elif char == ")":
            if token.strip():
                leaf = int(token.strip())
                G.add_node(leaf)
                G.add_edge(current_parent, leaf)
                token = ""
            current_parent = stack.pop()
        elif char in " \t\n\r":
            continue
        else:
            token += char

    return G

if __name__ == '__main__':
    random.seed(42)
    trees, n_leaves = read_input(sys.stdin)
    leaves = frozenset(range(1, n_leaves + 1))
    T1, T2 = trees[0], trees[1]
    seeker = GraphSeeker(
        T1, leaves, NumComponentSpec(T1, leaves), AgreementSpec(T2, leaves)
    )
    seeker.run()
