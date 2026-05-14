#!/usr/bin/env python3
import random
import signal
import sys

class Node:
    __slots__ = ('id', 'parent', 'children', 'attrs')

    def __init__(self, node_id):
        self.id = node_id
        self.parent = None   # Node | None
        self.children = []   # list[Node], max len 2
        self.attrs = {}


class _NodeView:
    def __init__(self, nodes):
        self._nodes = nodes  # dict[int, Node]

    def __iter__(self):
        return iter(self._nodes)

    def __contains__(self, n):
        return n in self._nodes

    def __getitem__(self, n):
        return self._nodes[n].attrs


class RootedBinaryForest:
    def __init__(self):
        self._nodes = {}   # int -> Node
        self.roots = set() # set of node IDs with no parent

    def __contains__(self, n):
        return n in self._nodes

    def __iter__(self):
        return iter(self._nodes)

    def __len__(self):
        return len(self._nodes)

    def __getitem__(self, n):
        return [c.id for c in self._nodes[n].children]

    def add_node(self, n):
        if n not in self._nodes:
            self._nodes[n] = Node(n)
            self.roots.add(n)

    def remove_node(self, n):
        node = self._nodes.pop(n)
        if node.parent is not None:
            node.parent.children.remove(node)
        for c in node.children:
            c.parent = None
            self.roots.add(c.id)
        self.roots.discard(n)

    def add_edge(self, u, v):
        self.add_node(u)
        self.add_node(v)
        u_node = self._nodes[u]
        v_node = self._nodes[v]
        u_node.children.append(v_node)
        v_node.parent = u_node
        self.roots.discard(v)

    def add_edges_from(self, edges):
        for u, v in edges:
            self.add_edge(u, v)

    def remove_edge(self, u, v):
        u_node = self._nodes[u]
        v_node = self._nodes[v]
        u_node.children.remove(v_node)
        v_node.parent = None
        self.roots.add(v)

    def remove_edges_from(self, edges):
        for u, v in edges:
            if u in self._nodes and v in self._nodes:
                v_node = self._nodes[v]
                if v_node.parent is self._nodes[u]:
                    self.remove_edge(u, v)

    def successors(self, n):
        return (c.id for c in self._nodes[n].children)

    def predecessors(self, n):
        p = self._nodes[n].parent
        if p is not None:
            yield p.id

    def parent(self, n):
        p = self._nodes[n].parent
        return p.id if p is not None else None

    def children(self, n):
        return [c.id for c in self._nodes[n].children]

    def out_degree(self, n):
        return len(self._nodes[n].children)

    def in_degree(self, n=None):
        if n is not None:
            return 0 if self._nodes[n].parent is None else 1
        return ((n, 0 if node.parent is None else 1) for n, node in self._nodes.items())

    @property
    def nodes(self):
        return _NodeView(self._nodes)

    def edges(self):
        return ((u, c.id) for u, node in self._nodes.items() for c in node.children)

    def split_subtree(self, source):
        source_node = self._nodes[source]
        parent_node = source_node.parent
        if parent_node is not None:
            parent_node.children.remove(source_node)
            source_node.parent = None
        self.roots.discard(source)
        new_forest = RootedBinaryForest()
        stack = [source_node]
        while stack:
            node = stack.pop()
            self._nodes.pop(node.id)
            new_forest._nodes[node.id] = node
            stack.extend(node.children)
        new_forest.roots.add(source)
        return new_forest, parent_node.id if parent_node is not None else None
    
    def add_subtree(self, subtree, parent=None):
        self._nodes.update(subtree._nodes)
        assert len(subtree.roots) == 1
        root = next(iter(subtree.roots))
        if parent is None:
            self.roots.add(root)
        else:
            parent_node = self._nodes[parent]
            parent_node.children.append(self._nodes[root])
            self._nodes[root].parent = parent_node

    def copy(self):
        G = RootedBinaryForest()
        id_to_new = {}
        for n, node in self._nodes.items():
            new_node = Node(n)
            new_node.attrs = dict(node.attrs)
            G._nodes[n] = new_node
            id_to_new[n] = new_node
        for n, node in self._nodes.items():
            new_node = id_to_new[n]
            if node.parent is not None:
                new_node.parent = id_to_new[node.parent.id]
            new_node.children = [id_to_new[c.id] for c in node.children]
        G.roots = set(self.roots)
        return G


def create_empty_copy(G):
    H = RootedBinaryForest()
    for n in G._nodes:
        H._nodes[n] = Node(n)
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

def subtree_reduce(T1, T2, leaves):
    subtree_replace_map = {}
    for node1, node2, covered_leaves in find_maximal_common_pendants(T1.copy(), T2.copy(), leaves):
        replacement_leaf = next(iter(covered_leaves))
        tree1, p1 = T1.split_subtree(node1)
        tree2, p2 = T2.split_subtree(node2)
        if p1 is not None:
            T1.add_edge(p1, replacement_leaf)
        else:
            T1.add_node(replacement_leaf)
        if p2 is not None:
            T2.add_edge(p2, replacement_leaf)
        else:
            T2.add_node(replacement_leaf)
        subtree_replace_map[replacement_leaf] = tree1
    return T1, T2, subtree_replace_map

def restore_subtree(graph, subtree_replace_map):
    for leaf, tree in subtree_replace_map.items():
        parent = graph.parent(leaf)
        graph.remove_node(leaf)
        graph.add_subtree(tree, parent=parent)
    return graph

class GraphSeeker:
    def __init__(self, T1: RootedBinaryForest, T2: RootedBinaryForest, leaves: frozenset[int]):
        self.T1 = T1
        self.T2 = T2
        self.subtree_replace_map = {}
        self.T1, self.T2, self.subtree_replace_map = subtree_reduce(T1, T2, leaves)
        self.orig_leaves = frozenset(leaves)
        to_remove = set()
        for leaf, tree in self.subtree_replace_map.items():
            to_remove.update(all_leaves_tree(tree, next(iter(tree.roots))))
            to_remove.discard(leaf)
        self.leaves = frozenset(leaves - to_remove)
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
        graph = restore_subtree(graph, self.subtree_replace_map)
        for leaf in self.orig_leaves:
            if leaf not in visited:
                root = find_root(graph, leaf)
                root = remove_contract_rooted(graph, self.orig_leaves, root)
                visited.update(all_leaves_tree(graph, root))
                out_trees.append(tree_to_newick_print(graph, root=root))
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
    if g.out_degree(root) == 0:
        return (str(root), root)
    subgs = sorted((_tree_to_newick(g, root=child) for child in g.successors(root)), key=lambda x: x[1])
    return ("(" + ','.join(x[0] for x in subgs) + ")", subgs[0][1])


def tree_to_newick_list(g, result, root):
    if g.out_degree(root) == 0:
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


if __name__ == '__main__':
    random.seed(42)
    trees, n_leaves = read_input(sys.stdin)
    leaves = frozenset(range(1, n_leaves + 1))
    T1, T2 = trees[0], trees[1]
    seeker = GraphSeeker(T1, T2, leaves)
    seeker.run()
