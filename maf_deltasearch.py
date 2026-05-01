#!/usr/bin/env python3
from __future__ import annotations

import io
import random
import signal
import sys

import networkx as nx


def remove_rooted(T: nx.DiGraph, leaves: frozenset, node) -> list[int]:
    if node in leaves:
        return node
    for child in list(T.successors(node)):
        remove_rooted(T, leaves, child)
    out_deg = T.out_degree(node)
    if out_deg == 0:
        T.remove_node(node)
    elif out_deg == 1:
        preds = list(T.predecessors(node))
        if not preds:
            while T.out_degree(node) == 1:
                child = next(iter(T.successors(node)))
                T.remove_node(node)
                node = child
    return node

def remove_contract_rooted(T: nx.DiGraph, leaves: frozenset, node) -> int:
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
        assert child in T
        return child
    assert node in T
    return node


class NumComponentSpec:
    def __init__(self, graph: nx.DiGraph, all_leaves: frozenset):
        assert graph.is_directed(), "NumComponentSpec only works on directed graphs"
        self._all_leaves = all_leaves

    def __call__(self, graph:nx.DiGraph) -> float:
        # print("NUM", graph)
        assert graph.is_directed(), "NumComponentSpec only works on directed graphs"
        score =  -len([comp for comp in nx.weakly_connected_components(graph) if comp & self._all_leaves])
        return score

class AgreementSpec:

    def __init__(self, graph: nx.DiGraph, T2: nx.DiGraph, all_leaves: frozenset):
        assert graph.is_directed(), "AgreementSpec only works on directed graphs"
        self._T2 = T2
        self._all_leaves = all_leaves

    def __call__(self, graph:nx.DiGraph) -> float:
        # print("AGREEMENT", graph)
        assert graph.is_directed(), "AgreementSpec only works on directed graphs"
        roots = [v for v in graph.nodes if graph.in_degree(v) == 0]
        nxt_roots = list()
        T1_contracted = graph.copy()
        for root in roots:
            root = remove_contract_rooted(T1_contracted, self._all_leaves, root)
            if root is not None:
                assert root in T1_contracted
                nxt_roots.append(root)
        T1_roots = set(nxt_roots)
        T2 = self._T2.copy()
        for T1_root in T1_roots:

            # TODO: Simplify to make this faster
            T1_component = nx.descendants(T1_contracted, T1_root) | {T1_root}
            S = frozenset(T1_component & self._all_leaves)
            for comp in nx.weakly_connected_components(T2):
                if S & comp:
                    if comp >= S:
                        chosen_comp = comp
                        break
                    else:
                        return -float("inf")
            else:
                return -float("inf")

            roots = [v for v in chosen_comp if T2.in_degree(v) == 0]
            assert len(roots) == 1, f"component has {len(roots)} roots"
            T2_root = roots[0]
            T2_removed = T2.copy()
            T2_root = remove_rooted(T2_removed, S, T2_root)
            for edge in nx.bfs_edges(T2_removed, T2_root):
                T2.remove_edge(*edge)
            T2_root = remove_contract_rooted(T2_removed, S, T2_root)

            if tree_to_newick(T1_contracted, root=T1_root) != tree_to_newick(T2_removed, root=T2_root):
                return -float("inf")


        return 0.0


# ---------------------------------------------------------------------------
# MAF DeltaSearch solver
# ---------------------------------------------------------------------------

class GraphSeeker:
    def __init__(self, graph: nx.DiGraph, leaves: frozenset[int], score:Callable[[nx.DiGraph], float], validity:Callable[[nx.DiGraph], bool]):
        self.graph = nx.freeze(graph)
        self.leaves = leaves

        self.score = score
        self.valid = validity

        self.result = nx.create_empty_copy(self.graph)
        self.best_score = self.score(self.result)
        self.empty_score = self.best_score
        self.out_trees = [nx.empty_graph(n=[leaf,], create_using=nx.DiGraph) for leaf in leaves]

        # https://optil.io/optilion/help/signals
        signal.signal(signal.SIGINT, self.exit)
        signal.signal(signal.SIGTERM, self.exit)

    def run(self):
        c = list(self.graph.edges())
        while True:
            n = 1
            cur_soln = list()
            cur_graph = nx.create_empty_copy(self.graph)
            cur_score = self.empty_score
            while n < len(c):
                n = min(2*n, len(c))
                k, m = divmod(len(c), n)

                for i in range(n-1, -1, -1):
                    tst_subset = c[i*k+min(i, m): (i+1)*k+min(i+1,m)]
                    cs = cur_soln + tst_subset
                    cur_graph.add_edges_from(tst_subset)
                    if self.valid(cur_graph):
                        tst_score = self.score(cur_graph)
                        if tst_score > cur_score:
                            cur_score = tst_score
                            cur_soln = cs
                            del c[i*k+min(i, m): (i+1)*k+min(i+1,m)]
                            if cur_score > self.best_score:
                                self.result = cur_graph
                                self.best_score = cur_score
                                self.out_trees = self.prepare_solution(self.result)
                                continue
                    cur_graph.remove_edges_from(tst_subset)

            # self.exit(None, None)
            c = list(self.graph.edges())
            random.shuffle(c)

    def prepare_solution(self, graph):
        all_leaves = self.leaves
        out_trees = []
        all_roots = {v for v in graph.nodes() if graph.in_degree(v) == 0}
        for comp in list(nx.weakly_connected_components(graph)):
            if not (comp & all_leaves):
                continue
            roots = list(all_roots & comp)
            assert len(roots) == 1
            root = roots[0]
            root = remove_contract_rooted(graph, all_leaves, root)
            assert root is not None
            tree_nodes = set(nx.descendants(graph, root)) | {root}
            tree = graph.subgraph(tree_nodes)
            out_trees.append(tree.copy())
        return out_trees

    def exit(self, signum, frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        # TODO: Uncomment following line
        # out_trees = self.prepare_solution(self.result)
        write_output(self.out_trees)
        sys.exit(0)


# ---------------------------------------------------------------------------
# PACE 2026 I/O
# https://pacechallenge.org/2026/format/#relevant-subset-of-the-newick-format
# ---------------------------------------------------------------------------

def read_input(f) -> tuple[nx.DiGraph, nx.DiGraph, set]:
    n_leaves = None
    n_trees = None
    a, b = None, None
    parameters = dict()
    all_edges: list[tuple[int, int]] = []
    trees = list()

    for line in f:
        line = line.strip()
        if not line or line.startswith('#'):
            line = line[1:].strip()  # Remove leading '#' for comment lines
            parts = line.split()
            if parts[0] == 'p':
                n_trees = int(parts[1])
                n_leaves = int(parts[2])
                n_pending_trees = n_trees
            elif parts[0] == 'a':
                a, b = float(parts[1]), float(parts[2])
            elif parts[0] == 'x':
                parameter_key, parameter_value = parts[1], parts[2]
                parameters[parameter_key] = parameter_value
        else:
            newick_data = line
            newick_data = newick_data.strip()
            assert newick_data.endswith(';'), "Newick string must end with ';'"
            # newick_data = newick_data[:-1]  + "0" + newick_data[-1]
            # print(newick_data)
            tree = parse_newick_to_digraph(newick_data)
            assert tree.is_directed(), "Input trees must be directed graphs"
            trees.append(tree)
            n_pending_trees -= 1
            if n_pending_trees == 0:
                break

    return trees, n_leaves

# https://stackoverflow.com/a/57393072/9939883
def tree_to_newick(g, root=None):
    if root is None:
        roots = list(filter(lambda p: p[1] == 0, g.in_degree()))
        assert 1 == len(roots)
        root = roots[0][0]
    subgs = []
    if len(g[root]) == 0:
        return str(root)
    for child in sorted(g[root]):
        if len(g[child]) > 0:
            subgs.append(tree_to_newick(g, root=child))
        else:
            subgs.append(str(child))
    return "(" + ','.join(subgs) + ")"

def write_output(trees: list[nx.Graph]) -> None:
    result = []
    for tree in trees:
        newick_string = tree_to_newick(tree) + ';'
        result.append(newick_string)
    print('\n'.join(result))

def parse_newick_to_digraph(newick_str: str) -> nx.DiGraph:
    newick_str = newick_str.strip().rstrip(";")

    G = nx.DiGraph()
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
        T1, leaves, NumComponentSpec(T1, leaves), lambda g: AgreementSpec(g, T2, leaves)(g) > -float("inf")
    )
    seeker.run()
