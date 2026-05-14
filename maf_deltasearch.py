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

class RootedBinaryForest:
    def __init__(self):
        # TODO: Change the following after full migration to this class
        self._children = {}   # node -> list (len 0, 1, or 2)
        self._parent = {}     # node -> parent node or None
        self._node = {}       # node -> attribute dict
        self.roots = set()    # nodes with no parent

    def __contains__(self, n):
        return n in self._node

    def __iter__(self):
        return iter(self._node)

    def __len__(self):
        return len(self._node)

    def __getitem__(self, n):
        return self._children[n]

    def add_node(self, n):
        if n not in self._node:
            self._children[n] = []
            self._parent[n] = None
            self._node[n] = {}
            self.roots.add(n)

    def remove_node(self, n):
        p = self._parent[n]
        if p is not None:
            self._children[p].remove(n)
        for c in self._children[n]:
            self._parent[c] = None
            self.roots.add(c)
        self.roots.discard(n)
        del self._children[n]
        del self._parent[n]
        del self._node[n]

    def add_edge(self, u, v):
        self.add_node(u)
        self.add_node(v)
        self._children[u].append(v)
        self._parent[v] = u
        self.roots.discard(v)

    def add_edges_from(self, edges):
        for u, v in edges:
            self.add_edge(u, v)

    def remove_edge(self, u, v):
        self._children[u].remove(v)
        self._parent[v] = None
        self.roots.add(v)

    def remove_edges_from(self, edges):
        for u, v in edges:
            if u in self._children and v in self._children[u]:
                self.remove_edge(u, v)

    def successors(self, n):
        return iter(self._children[n])

    def predecessors(self, n):
        p = self._parent[n]
        if p is not None:
            yield p

    def parent(self, n):
        return self._parent[n]

    def children(self, n):
        return self._children[n]

    def out_degree(self, n):
        return len(self._children[n])

    def in_degree(self, n=None):
        if n is not None:
            return 0 if self._parent[n] is None else 1
        return ((v, 0 if p is None else 1) for v, p in self._parent.items())

    @property
    def nodes(self):
        return _NodeView(self._node)

    def edges(self):
        return ((u, v) for u, cs in self._children.items() for v in cs)

    def relabel_node(self, old, new):
        self._node[new] = self._node.pop(old)
        self._children[new] = self._children.pop(old)
        self._parent[new] = self._parent.pop(old)
        if old in self.roots:
            self.roots.discard(old)
            self.roots.add(new)
        p = self._parent[new]
        if p is not None:
            cs = self._children[p]
            cs[cs.index(old)] = new
        for c in self._children[new]:
            self._parent[c] = new
    
    def delete_subtree(self, source):
        children = list(self.successors(source))
        for v in children:
            self.delete_subtree(v)
        self.remove_node(source)

    def copy(self):
        G = RootedBinaryForest()
        G._node = {n: dict(attrs) for n, attrs in self._node.items()}
        G._children = {n: list(cs) for n, cs in self._children.items()}
        G._parent = dict(self._parent)
        G.roots = set(self.roots)
        return G


def create_empty_copy(G):
    H = RootedBinaryForest()
    for n in G._node:
        H._children[n] = []
        H._parent[n] = None
        H._node[n] = {}
        H.roots.add(n)
    return H


def all_leaves_tree(G, source):
    if source > 0:
        yield source
    for v in G.successors(source):
        yield from all_leaves_tree(G, v)


def delete_subtree_leaves(G, leaves, source):
    if source in leaves:
        G.remove_node(source)
        return True
    children = list(G.successors(source))
    flag = False
    for v in children:
        if delete_subtree_leaves(G, leaves, v):
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
        p = T.parent(node)
        if p is not None:
            T.add_edge(p, child)
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
    for root in graph.roots:
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
    while graph.parent(node) is not None:
        node = graph.parent(node)
    return node

class GraphSeeker:
    def __init__(self, T1: RootedBinaryForest, T2: RootedBinaryForest, leaves: frozenset[int]):
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
            while n < len(c):
                n = min(2*n, len(c))
                k, m = divmod(len(c), n)
                for i in range(n-1, -1, -1):
                    tst_subset = c[i*k+min(i, m): (i+1)*k+min(i+1,m)]
                    cur_graph.add_edges_from(tst_subset)

                    # tst_roots = {find_root(cur_graph, root) for root in cur_roots}
                    changed_roots = set()
                    tst_roots = set()
                    for root in cur_roots:
                        new_root = find_root(cur_graph, root)
                        tst_roots.add(new_root)
                        if new_root != root:
                            changed_roots.add(new_root)
                    tst_cost = len(tst_roots)

                    if tst_cost < cur_cost:
                        get_min(cur_graph, self.leaves)
                        T2 = self.T2.copy()
                        agreement = True
                        for T1_root in tst_roots - changed_roots:
                            T1_leaves = set(all_leaves_tree(cur_graph, T1_root))
                            T2_root = find_root(T2, next(iter(T1_leaves)))
                            n_leaves, T2_root = find_contracted_root(T2, T2_root, T1_leaves)
                            delete_subtree_leaves(T2, T1_leaves, T2_root)
                        for T1_root in changed_roots:
                            T1_leaves = set(all_leaves_tree(cur_graph, T1_root))
                            T2_root = find_root(T2, next(iter(T1_leaves)))
                            n_leaves, T2_root = find_contracted_root(T2, T2_root, T1_leaves)
                            if not (n_leaves == len(T1_leaves)):
                                agreement = False
                                break
                            _get_min(T2, T2_root, T1_leaves)
                            if not compare_trees(T1_root, cur_graph, T2_root, T2, T1_leaves):
                                agreement = False
                                break
                            delete_subtree_leaves(T2, T1_leaves, T2_root)
                        if agreement:
                            cur_cost = tst_cost
                            cur_roots = tst_roots
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
        assert len(g.roots) == 1
        root = next(iter(g.roots))
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


def parse_newick_to_digraph(newick_str: str) -> RootedBinaryForest:
    newick_str = newick_str.strip().rstrip(";")
    G = RootedBinaryForest()
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


def find_maximal_common_pendants(T1, T2, leaves):
    visited = set()
    get_min(T1, leaves)
    get_min(T2, leaves)
    for leaf in leaves:
        if leaf in visited:
            continue
        node1 = leaf
        node2 = leaf
        while T1.parent(node1) is not None and T2.parent(node2) is not None:
            pred1 = T1.parent(node1)
            pred2 = T2.parent(node2)

            children1 = list(T1.successors(pred1))
            children2 = list(T2.successors(pred2))
            mismatch = False
            if len(children1) == len(children2):
                assert len(children1) == 2
                node11, node12 = children1
                node21, node22 = children2
                if node11 != node1:
                    node11, node12 = node12, node11
                if node21 != node2:
                    node21, node22 = node22, node21
                if not compare_trees(node12, T1, node22, T2, leaves):
                    mismatch = True
            else:
                mismatch = True

            if mismatch:
                covered_leaves = frozenset(all_leaves_tree(T1, node1))
                visited.update(covered_leaves)
                if node1 not in leaves:
                    yield node1, node2, covered_leaves
                break
            else:
                node1 = pred1
                node2 = pred2
        else:
            covered_leaves = frozenset(all_leaves_tree(T1, node1))
            visited.update(covered_leaves)
            if node1 not in leaves:
                yield node1, node2, covered_leaves

def delete_subtree(G, source):
    children = list(G.successors(source))
    for v in children:
        delete_subtree(G, v)
    G.remove_node(source)

def reduce(T1, T2, leaves):
    subtree_replace_map = {}
    reduced = True
    while reduced:
        reduced = False
        for node1, node2, covered_leaves in find_maximal_common_pendants(T1, T2, leaves):
            reduced = True
            replacement_leaf = next(iter(covered_leaves))
            p1 = T1.parent(node1)
            if p1 is not None:
                T1.add_edge(p1, replacement_leaf)
            p2 = T2.parent(node2)
            if p2 is not None:
                T2.add_edge(p2, replacement_leaf)
            delete_subtree(T1, node1)
            delete_subtree(T2, node2)
            subtree_replace_map[replacement_leaf] = covered_leaves


if __name__ == '__main__':
    random.seed(42)
    trees, n_leaves = read_input(sys.stdin)
    leaves = frozenset(range(1, n_leaves + 1))
    T1, T2 = trees[0], trees[1]
    seeker = GraphSeeker(T1, T2, leaves)
    seeker.run()
