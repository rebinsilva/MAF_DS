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

    def __getitem__(self, n):
        return self._nodes[n]


class DiGraph:
    def __init__(self):
        self._succ = {}
        self._pred = {}
        self._node = {}

    def __contains__(self, n):
        return n in self._node

    def __iter__(self):
        return iter(self._node)

    def __len__(self):
        return len(self._node)

    def __getitem__(self, n):
        return self._succ[n]

    def add_node(self, n):
        if n not in self._succ:
            self._succ[n] = {}
            self._pred[n] = {}
            self._node[n] = {}

    def remove_node(self, n):
        for s in list(self._succ[n]):
            del self._pred[s][n]
        for p in list(self._pred[n]):
            del self._succ[p][n]
        del self._succ[n]
        del self._pred[n]
        del self._node[n]

    def add_edge(self, u, v):
        self.add_node(u)
        self.add_node(v)
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
        G._node = {n: dict(attrs) for n, attrs in self._node.items()}
        G._succ = {u: dict(nbrs) for u, nbrs in self._succ.items()}
        G._pred = {u: dict(preds) for u, preds in self._pred.items()}
        return G


def create_empty_copy(G):
    H = DiGraph()
    H._node = {n: {} for n in G._node}
    H._succ = {n: {} for n in G._node}
    H._pred = {n: {} for n in G._node}
    return H


def all_leaves_tree(G, source):
    if source > 0:
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

def _get_min(graph, node, leaves):
    if node in leaves:
        graph.nodes[node]["min"] = node
        return node
    
    if graph.out_degree(node) == 0:
        graph.nodes[node]["min"] = float('inf')
        return float('inf')
    
    mini = float('inf')
    for child in graph.successors(node):
        mini = min(mini, _get_min(graph, child, leaves))
    
    graph.nodes[node]["min"] = mini
    return mini
    
def find_contracted_root(graph, node, leaves):
    found_leaves = 0
    if node in leaves:
        found_leaves = 1
        return found_leaves, node
    for child in graph.successors(node):
        child_leaves, child_root = find_contracted_root(graph, child, leaves)
        if child_leaves == len(leaves):
            return child_leaves, child_root

        found_leaves += child_leaves
    return found_leaves, node

def get_min(graph, leaves):
    roots = [v for v in graph.nodes if graph.in_degree(v) == 0]
    for root in roots:
        _get_min(graph, root, leaves)

def compare_trees(node1, T1, node2, T2, leaves):
    if T1.nodes[node1]["min"] != T2.nodes[node2]["min"]:
        return False

    while True:
        T1_out_deg = T1.out_degree(node1)
        if T1_out_deg == 0:
            break
        if T1_out_deg == 1:
            node1 = next(iter(T1.successors(node1)))
        if T1_out_deg == 2:
            node11, node12 = T1.successors(node1)
            if T1.nodes[node11]["min"] != float('inf') and T1.nodes[node12]["min"] != float('inf'):
                break
            if T1.nodes[node11]["min"] != float('inf'):
                node1 = node11
                continue
            if T1.nodes[node12]["min"] != float('inf'):
                node1 = node12
                continue
            T1_out_deg = 0
            break
    while True:
        T2_out_deg = T2.out_degree(node2)
        if T2_out_deg == 0:
            break
        if T2_out_deg == 1:
            node2 = next(iter(T2.successors(node2)))
        if T2_out_deg == 2:
            node21, node22 = T2.successors(node2)
            if T2.nodes[node21]["min"] != float('inf') and T2.nodes[node22]["min"] != float('inf'):
                break
            if T2.nodes[node21]["min"] != float('inf'):
                node2 = node21
                continue
            if T2.nodes[node22]["min"] != float('inf'):
                node2 = node22
                continue
            T2_out_deg = 0
            break
            

    if T1_out_deg == 0 and T2_out_deg == 0:
        return True
    
    if T1_out_deg == 0 or T2_out_deg == 0:
        return False
    
    # node11, node12 = T1.successors(node1)
    # node21, node22 = T2.successors(node2)
    if T1.nodes[node11]["min"] > T1.nodes[node12]["min"]:
        node11, node12 = node12, node11
    if T2.nodes[node21]["min"] > T2.nodes[node22]["min"]:
        node21, node22 = node22, node21
    
    return compare_trees(node11, T1, node21, T2, leaves) and compare_trees(node12, T1, node22, T2, leaves)

def find_root(graph, node):
    while graph.in_degree(node) == 1:
        node = next(iter(graph.predecessors(node)))
    return node

class GraphSeeker:
    def __init__(self, T1: DiGraph, T2: DiGraph, leaves: frozenset[int]):
        self.T1 = T1
        self.T2 = T2
        self.leaves = leaves
        self.result = create_empty_copy(self.T1)
        self.best_cost = len(leaves)
        signal.signal(signal.SIGINT, self.exit)
        signal.signal(signal.SIGTERM, self.exit)

    def run(self):
        c = list(self.T1.edges())
        while True:
            n = 1
            cur_graph = create_empty_copy(self.T1)
            cur_roots = set(self.leaves)
            cur_cost = len(self.leaves)
            root_leaves_map = {leaf: {leaf,} for leaf in self.leaves} # T1
            leaf_root_map = {leaf: leaf for leaf in self.leaves}    # T2
            while n < len(c):
                n = min(2*n, len(c))
                k, m = divmod(len(c), n)
                for i in range(n-1, -1, -1):
                    tst_subset = c[i*k+min(i, m): (i+1)*k+min(i+1,m)]
                    cur_graph.add_edges_from(tst_subset)

                    # tst_roots = {find_root(cur_graph, root) for root in cur_roots}
                    tst_leaf_root_map = dict(leaf_root_map)
                    changed_roots = set()
                    tst_roots = set()
                    tst_root_leaves_map = {}
                    for root in cur_roots:
                        new_root = find_root(cur_graph, root)
                        tst_roots.add(new_root)
                        if new_root != root:
                            changed_roots.add(new_root)
                            tst_root_leaves_map.setdefault(new_root, set(root_leaves_map[root])).update(root_leaves_map[root])
                        else:
                            if root not in tst_root_leaves_map:
                                tst_root_leaves_map[root] = set(root_leaves_map[root])
                    tst_cost = len(tst_roots)

                    if tst_cost < cur_cost:
                        get_min(cur_graph, self.leaves)
                        T2 = self.T2.copy()
                        agreement = True
                        for T1_root in tst_roots - changed_roots:
                            T1_leaves =  tst_root_leaves_map[T1_root]
                            T2_root = tst_leaf_root_map[next(iter(T1_leaves))]
                            delete_subtree(T2, T1_leaves, T2_root)
                        for T1_root in changed_roots:
                            T1_leaves =  tst_root_leaves_map[T1_root]
                            T2_root = find_root(T2, next(iter(T1_leaves)))
                            T1_leaves_roots = set(tst_leaf_root_map[leaf] for leaf in T1_leaves)
                            n_leaves, T2_root = find_contracted_root(T2, T2_root, T1_leaves_roots)
                            if not (n_leaves == len(T1_leaves_roots)):
                                agreement = False
                                break
                            _get_min(T2, T2_root, T1_leaves)
                            if not compare_trees(T1_root, cur_graph, T2_root, T2, T1_leaves):
                                agreement = False
                                break

                            for leaf in T1_leaves:
                                tst_leaf_root_map[leaf] = T2_root
                            delete_subtree(T2, T1_leaves, T2_root)
                        if agreement:
                            cur_cost = tst_cost
                            cur_roots = tst_roots
                            root_leaves_map = tst_root_leaves_map
                            leaf_root_map = tst_leaf_root_map
                            del c[i*k+min(i, m): (i+1)*k+min(i+1,m)]
                            if cur_cost < self.best_cost:
                                self.result = cur_graph.copy()
                                self.best_cost = cur_cost
                            continue
                    cur_graph.remove_edges_from(tst_subset)
            c = list(self.T1.edges())
            random.shuffle(c)

    def prepare_solution(self, graph):
        visited = set()
        out_trees = []
        for leaf in self.leaves:
            if leaf not in visited:
                root = find_root(graph, leaf)
                root = remove_contract_rooted(graph, self.leaves, root)
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
    seeker = GraphSeeker(T1, T2, leaves)
    seeker.run()
