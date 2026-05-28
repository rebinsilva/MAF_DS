#!/usr/bin/env python3
import os
import random
import signal
import sys

PRINT_STATS = True

class RootedBinaryForest:
    def __init__(self):
        self._children = {}
        self._parent = {}
        self._node = set()
        self.roots = set()

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
            self._node.add(n)
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
        self._node.discard(n)

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
        return self._children[n]

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

    def edges(self):
        return ((u, v) for u, cs in self._children.items() for v in cs)

    def delete_subtree(self, source):
        for c in list(self.successors(source)):
            self.delete_subtree(c)
        self.remove_node(source)

    def split_subtree(self, source):
        parent = self._parent[source]
        if parent is not None:
            self._children[parent].remove(source)
            self._parent[source] = None
        self.roots.discard(source)
        new_forest = RootedBinaryForest()
        stack = [source]
        while stack:
            n = stack.pop()
            new_forest._children[n] = self._children.pop(n)
            new_forest._parent[n] = self._parent.pop(n)
            self._node.discard(n)
            new_forest._node.add(n)
            stack.extend(new_forest._children[n])
        new_forest.roots.add(source)
        return new_forest, parent

    def add_subtree(self, subtree, parent=None):
        assert len(subtree.roots) == 1
        root = next(iter(subtree.roots))
        # Copy children lists so graph mutations don't corrupt the saved subtree
        for n, ch in subtree._children.items():
            self._children[n] = list(ch)
        self._parent.update(subtree._parent)
        self._node.update(subtree._node)
        if parent is None:
            self.roots.add(root)
        else:
            self._children[parent].append(root)
            self._parent[root] = parent

    def copy(self):
        G = RootedBinaryForest()
        G._node = set(self._node)
        G._children = {n: list(cs) for n, cs in self._children.items()}
        G._parent = dict(self._parent)
        G.roots = set(self.roots)
        return G



def create_empty_copy(G):
    H = RootedBinaryForest()
    for n in G._node:
        H._children[n] = []
        H._parent[n] = None
        H._node.add(n)
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

def _get_min(graph, node, leaves, min_dict):
    if node in leaves:
        min_dict[node] = node
        return node

    if graph.out_degree(node) == 0:
        min_dict[node] = float('inf')
        return float('inf')

    mini = float('inf')
    for child in graph.successors(node):
        mini = min(mini, _get_min(graph, child, leaves, min_dict))

    min_dict[node] = mini
    return mini


def find_contracted_root2(graph, root, leaves, n_leaves):
    stack = [root]
    found_leaves = dict()

    while stack:
        node = stack[-1]

        if node in leaves:
            found_leaves[node] = 1
        else:
            children = graph.successors(node)
            if len(children) == 0:
                found_leaves[node] = 0
            elif children[0] not in found_leaves:
                stack.extend(children)
                continue
            else:
                found_leaves[node] = 0
                for child in children:
                    found_leaves[node] += found_leaves[child]
        stack.pop()
        if found_leaves[node] == n_leaves:
            return n_leaves, node

    return found_leaves[root], root

def find_contracted_root(graph, node, leaves, n_leaves):
    if node in leaves:
        return 1, node

    found_leaves = 0
    for child in graph.successors(node):
        child_leaves, child_root = find_contracted_root(graph, child, leaves, n_leaves)
        if child_leaves == n_leaves:
            return child_leaves, child_root

        found_leaves += child_leaves
    return found_leaves, node
    

def get_min(graph, leaves, min_dict):
    for root in graph.roots:
        _get_min(graph, root, leaves, min_dict)

def compare_trees(node1, T1, T1_min, node2, T2, T2_min, leaves):
    if T1_min[node1] != T2_min[node2]:
        return False

    while True:
        T1_out_deg = T1.out_degree(node1)
        if T1_out_deg == 0:
            break
        if T1_out_deg == 1:
            node1 = next(iter(T1.successors(node1)))
        if T1_out_deg == 2:
            node11, node12 = T1.successors(node1)
            if T1_min[node11] != float('inf') and T1_min[node12] != float('inf'):
                break
            if T1_min[node11] != float('inf'):
                node1 = node11
                continue
            if T1_min[node12] != float('inf'):
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
            if T2_min[node21] != float('inf') and T2_min[node22] != float('inf'):
                break
            if T2_min[node21] != float('inf'):
                node2 = node21
                continue
            if T2_min[node22] != float('inf'):
                node2 = node22
                continue
            T2_out_deg = 0
            break

    if T1_out_deg == 0 and T2_out_deg == 0:
        return True

    if T1_out_deg == 0 or T2_out_deg == 0:
        return False

    if T1_min[node11] > T1_min[node12]:
        node11, node12 = node12, node11
    if T2_min[node21] > T2_min[node22]:
        node21, node22 = node22, node21

    return (compare_trees(node11, T1, T1_min, node21, T2, T2_min, leaves) and
            compare_trees(node12, T1, T1_min, node22, T2, T2_min, leaves))

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



def find_common_chains(T1, T2, leaves):
    visited = set()
    for leaf in leaves:
        if leaf in visited:
            continue

        G1_T1 = T1._parent.get(leaf)
        if G1_T1 is None or len(T1._children.get(G1_T1, [])) != 2:
            visited.add(leaf)
            continue
        T1_ch = T1._children[G1_T1]
        x2_T1 = T1_ch[0] if T1_ch[1] == leaf else T1_ch[1]
        if x2_T1 not in leaves:
            visited.add(leaf)
            continue

        G1_T2 = T2._parent.get(leaf)
        if G1_T2 is None or len(T2._children.get(G1_T2, [])) != 2:
            visited.add(leaf)
            continue
        T2_ch = T2._children[G1_T2]
        x2_T2 = T2_ch[0] if T2_ch[1] == leaf else T2_ch[1]
        if x2_T2 != x2_T1:
            visited.add(leaf)
            continue

        chain = [leaf]
        node_T1, node_T2 = G1_T1, G1_T2

        while True:
            par_T1 = T1._parent.get(node_T1)
            par_T2 = T2._parent.get(node_T2)
            if par_T1 is None or par_T2 is None:
                break
            T1_par_ch = T1._children.get(par_T1, [])
            T2_par_ch = T2._children.get(par_T2, [])
            if len(T1_par_ch) != 2 or len(T2_par_ch) != 2:
                break
            sib_T1 = T1_par_ch[0] if T1_par_ch[1] == node_T1 else T1_par_ch[1]
            sib_T2 = T2_par_ch[0] if T2_par_ch[1] == node_T2 else T2_par_ch[1]
            if sib_T1 != sib_T2:
                break
            sib = sib_T1
            if sib not in leaves or sib in visited:
                break
            chain.append(sib)
            node_T1, node_T2 = par_T1, par_T2

        if len(chain) < 3:
            visited.add(leaf)
            continue

        visited.update(chain)
        yield chain


def _truncate_chain(T, chain):
    G1 = T._parent[chain[0]]
    G2 = T._parent[G1]

    chain_top = G2
    for _ in chain[2:]:
        chain_top = T._parent[chain_top]
    above = T._parent[chain_top]
    if above is not None:
        T._children[above].remove(chain_top)
        T._parent[chain_top] = None
    else:
        T.roots.discard(chain_top)

    G3 = T._parent[G2]
    if G3 is not None:
        T._children[G3].remove(G2)
        T._parent[G2] = None

    node = G3
    for ci in chain[2:]:
        next_node = T._parent[node] if node != chain_top else None
        T.roots.discard(ci)
        del T._children[ci]
        del T._parent[ci]
        T._node.discard(ci)
        T.roots.discard(node)
        del T._children[node]
        del T._parent[node]
        T._node.discard(node)
        node = next_node

    if above is not None:
        T._children[above].append(G2)
        T._parent[G2] = above
    else:
        T.roots.add(G2)


def chain_reduce(T1, T2, leaves):
    chain_map = {}
    chains = list(find_common_chains(T1, T2, leaves))
    for chain in chains:
        _truncate_chain(T1, chain)
        _truncate_chain(T2, chain)
        chain_map[chain[1]] = chain[2:]
    return T1, T2, chain_map


def restore_chain(graph, chain_map, min_id=0):
    next_id = [min((n for n in graph._node if n < 0), default=min_id) - 1]
    if min_id <= next_id[0]:
        next_id[0] = min_id - 1

    def fresh():
        nid = next_id[0]
        next_id[0] -= 1
        return nid

    for c3, removed in chain_map.items():
        p2 = graph._parent.get(c3)
        top = p2 if p2 is not None else c3
        top_parent = graph._parent.get(top)

        for ci in removed:
            new_node = fresh()
            graph._children[new_node] = []
            graph._parent[new_node] = None
            graph._node.add(new_node)
            graph._children[ci] = []
            graph._parent[ci] = None
            graph._node.add(ci)

            if top_parent is not None:
                graph._children[top_parent].remove(top)
                graph._parent[top] = None
            else:
                graph.roots.discard(top)

            graph._children[new_node] = [top, ci]
            graph._parent[top] = new_node
            graph._parent[ci] = new_node

            if top_parent is not None:
                graph._children[top_parent].append(new_node)
                graph._parent[new_node] = top_parent
            else:
                graph.roots.add(new_node)

            top = new_node

    return graph


def _find_pendant_3_chain_for_x3(T, x3, leaves):
    G2 = T._parent.get(x3)
    if G2 is None or len(T._children.get(G2, [])) != 2:
        return None
    ch = T._children[G2]
    G1 = ch[0] if ch[1] == x3 else ch[1]
    if G1 in leaves:
        return None
    G1_ch = T._children.get(G1, [])
    if len(G1_ch) != 2:
        return None
    a, b = G1_ch
    if a in leaves and b in leaves:
        return (a, b)
    return None


def find_32_chains(T1, T2, leaves):
    visited = set()
    for x3 in leaves:
        if x3 in visited:
            continue
        found = False
        for Ta, Tb in [(T1, T2), (T2, T1)]:
            pair = _find_pendant_3_chain_for_x3(Ta, x3, leaves)
            if pair is None:
                continue
            x1, x2 = pair
            if x1 in visited or x2 in visited:
                continue
            P3 = Tb._parent.get(x3)
            if P3 is None or len(Tb._children.get(P3, [])) != 2:
                continue
            Tb_ch = Tb._children[P3]
            other = Tb_ch[0] if Tb_ch[1] == x3 else Tb_ch[1]
            if other in (x1, x2):
                visited.update([x1, x2, x3])
                yield (x1, x2, x3, other)
                found = True
                break
        if not found:
            visited.add(x3)


def _remove_leaf_and_suppress(T, leaf):
    p = T._parent.get(leaf)
    T.roots.discard(leaf)
    del T._children[leaf]
    del T._parent[leaf]
    T._node.discard(leaf)
    if p is None:
        return
    T._children[p].remove(leaf)
    if len(T._children[p]) == 1:
        child = T._children[p][0]
        gp = T._parent[p]
        if gp is not None:
            idx = T._children[gp].index(p)
            T._children[gp][idx] = child
            T._parent[child] = gp
        else:
            T.roots.discard(p)
            T.roots.add(child)
            T._parent[child] = None
        del T._children[p]
        del T._parent[p]
        T._node.discard(p)
        T.roots.discard(p)


def chain_32_reduce(T1, T2, leaves):
    chain_32_map = {}
    chains = list(find_32_chains(T1, T2, leaves))
    for x1, x2, _, xi in chains:
        xj = x2 if xi == x1 else x1
        _remove_leaf_and_suppress(T1, xj)
        _remove_leaf_and_suppress(T2, xj)
        chain_32_map[xj] = xi
    return T1, T2, chain_32_map


def restore_32chain(graph, chain_32_map):
    for xj in chain_32_map:
        if xj in graph._node:
            old_parent = graph._parent.get(xj)
            if old_parent is not None:
                if xj in graph._children[old_parent]:
                    graph._children[old_parent].remove(xj)
            else:
                graph.roots.discard(xj)
        graph._children[xj] = []
        graph._parent[xj] = None
        graph._node.add(xj)
        graph.roots.add(xj)
    return graph


class GraphSeeker:
    def __init__(self, T1: RootedBinaryForest, T2: RootedBinaryForest, leaves: frozenset[int]):
        self.T1 = T1
        self.T2 = T2
        self.orig_leaves = frozenset(leaves)
        self.reduction_stack = []
        self.leaves = frozenset(leaves)
        _initial_leaves = len(leaves)
        _subtrees_reduced = 0
        _subtree_calls = 0
        _chains_reduced = 0
        _chain_calls = 0
        _cherries_reduced = 0
        _cherry_calls = 0
        _inner_iters = 0
        while True:
            while True:
                T1_new, T2_new, srmap = subtree_reduce(self.T1, self.T2, self.leaves)
                to_remove = set()
                for leaf, tree in srmap.items():
                    to_remove.update(all_leaves_tree(tree, next(iter(tree.roots))))
                    to_remove.discard(leaf)
                leaves_after_sub = frozenset(self.leaves - to_remove)
                T1_new, T2_new, crmap = chain_reduce(T1_new, T2_new, leaves_after_sub)
                chain_removed = set()
                for removed in crmap.values():
                    chain_removed.update(removed)
                leaves_after_chain = frozenset(leaves_after_sub - chain_removed)
                if not srmap and not crmap:
                    break
                _inner_iters += 1
                if srmap:
                    _subtrees_reduced += len(srmap)
                    _subtree_calls += 1
                if crmap:
                    _chains_reduced += len(crmap)
                    _chain_calls += 1
                self.T1, self.T2 = T1_new, T2_new
                self.leaves = leaves_after_chain
                self.reduction_stack.append((srmap, crmap, {}))
            T1_new, T2_new, c32map = chain_32_reduce(self.T1, self.T2, self.leaves)
            if not c32map:
                break
            _cherries_reduced += len(c32map)
            _cherry_calls += 1
            self.T1, self.T2 = T1_new, T2_new
            self.leaves = frozenset(self.leaves - c32map.keys())
            self.reduction_stack.append(({}, {}, c32map))

        self.stats = {
            'initial_leaves': _initial_leaves,
            'leaves_after_reduction': len(self.leaves),
            'subtrees_reduced': _subtrees_reduced,
            'subtree_calls': _subtree_calls,
            'chains_reduced': _chains_reduced,
            'chain_calls': _chain_calls,
            'cherries_reduced': _cherries_reduced,
            'cherry_calls': _cherry_calls,
            'inner_iters': _inner_iters,
            'run_loop_count': 0,
        }
        self.result = create_empty_copy(self.T1)
        self.best_cost = len(self.leaves)
        signal.signal(signal.SIGINT, self.exit)
        signal.signal(signal.SIGTERM, self.exit)

    def run(self):
        if len(self.leaves) == 1:
            self.result = self.T1.copy()
            self.best_cost = 1
            self.exit(None, None)
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

                    changed_roots = set()
                    tst_roots = set()
                    for root in cur_roots:
                        new_root = find_root(cur_graph, root)
                        tst_roots.add(new_root)
                        if new_root != root:
                            changed_roots.add(new_root)
                    tst_cost = len(tst_roots)

                    if tst_cost < cur_cost:
                        cur_min = {}
                        get_min(cur_graph, self.leaves, cur_min)
                        T2 = self.T2.copy()
                        agreement = True
                        for T1_root in tst_roots - changed_roots:
                            T1_leaves = set(all_leaves_tree(cur_graph, T1_root))
                            T2_root = find_root(T2, next(iter(T1_leaves)))
                            n_leaves, T2_root = find_contracted_root(T2, T2_root, T1_leaves, len(T1_leaves))
                            delete_subtree_leaves(T2, T1_leaves, T2_root)
                        for T1_root in changed_roots:
                            T1_leaves = set(all_leaves_tree(cur_graph, T1_root))
                            n_T1_leaves = len(T1_leaves)
                            T2_root = find_root(T2, next(iter(T1_leaves)))
                            n_leaves, T2_root = find_contracted_root(T2, T2_root, T1_leaves, n_T1_leaves)
                            if n_leaves != n_T1_leaves:
                                agreement = False
                                break
                            T2_min = {}
                            _get_min(T2, T2_root, T1_leaves, T2_min)
                            if not compare_trees(T1_root, cur_graph, cur_min, T2_root, T2, T2_min, T1_leaves):
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
            self.stats['run_loop_count'] += 1
            c = list(self.T1.edges())
            random.shuffle(c)

    def prepare_solution(self, graph):
        visited = set()
        out_trees = []
        all_subtree_min = min(
            (n for srmap, *_ in self.reduction_stack for tree in srmap.values() for n in tree._node if n < 0),
            default=0
        )
        for srmap, crmap, c32map in reversed(self.reduction_stack):
            graph = restore_32chain(graph, c32map)
            graph = restore_chain(graph, crmap, min_id=all_subtree_min)
            graph = restore_subtree(graph, srmap)
        for leaf in self.orig_leaves:
            if leaf not in visited:
                root = find_root(graph, leaf)
                root = remove_contract_rooted(graph, self.orig_leaves, root)
                visited.update(all_leaves_tree(graph, root))
                out_trees.append(tree_to_newick_print(graph, root=root))
        return "\n".join(out_trees)

    def exit(self, signum, frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        self.result_string = self.prepare_solution(self.result)
        if PRINT_STATS:
            s = self.stats
            for key, val in [
                ('initial_leaves',        s['initial_leaves']),
                ('leaves_after_reduction',s['leaves_after_reduction']),
                ('subtrees_reduced',      s['subtrees_reduced']),
                ('subtree_calls',         s['subtree_calls']),
                ('chains_reduced',        s['chains_reduced']),
                ('chain_calls',           s['chain_calls']),
                ('cherries_reduced',      s['cherries_reduced']),
                ('cherry_calls',          s['cherry_calls']),
                ('inner_iters',           s['inner_iters']),
                ('run_loop_completions',  s['run_loop_count']),
                ('n_components',          self.best_cost),
            ]:
                print(f"#s {key} {val}", flush=True)
        print(self.result_string, flush=True)
        os._exit(0)


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
    T1_min = {}
    T2_min = {}
    get_min(T1, leaves, T1_min)
    get_min(T2, leaves, T2_min)
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
                if not compare_trees(node12, T1, T1_min, node22, T2, T2_min, leaves):
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


def find_maximal_common_pendants_multi(trees, leaves):
    visited = set()
    mins = []
    for T in trees:
        m = {}
        get_min(T, leaves, m)
        mins.append(m)

    for leaf in leaves:
        if leaf in visited:
            continue
        nodes = [leaf] * len(trees)

        while all(T.parent(n) is not None for T, n in zip(trees, nodes)):
            preds = [T.parent(n) for T, n in zip(trees, nodes)]
            children_lists = [list(T.successors(p)) for T, p in zip(trees, preds)]

            mismatch = not all(len(ch) == 2 for ch in children_lists)

            if not mismatch:
                siblings = []
                for n, ch in zip(nodes, children_lists):
                    a, b = ch
                    siblings.append(b if a == n else a)
                for i in range(1, len(trees)):
                    if not compare_trees(siblings[0], trees[0], mins[0], siblings[i], trees[i], mins[i], leaves):
                        mismatch = True
                        break

            if mismatch:
                covered_leaves = frozenset(all_leaves_tree(trees[0], nodes[0]))
                visited.update(covered_leaves)
                if nodes[0] not in leaves:
                    yield tuple(nodes), covered_leaves
                break
            else:
                nodes = preds
        else:
            covered_leaves = frozenset(all_leaves_tree(trees[0], nodes[0]))
            visited.update(covered_leaves)
            if nodes[0] not in leaves:
                yield tuple(nodes), covered_leaves


def subtree_reduce_multi(trees, leaves):
    subtree_replace_map = {}
    copies = [T.copy() for T in trees]
    for nodes, covered_leaves in find_maximal_common_pendants_multi(copies, leaves):
        replacement_leaf = next(iter(covered_leaves))
        parents = []
        saved_subtree = None
        for i, (T, node) in enumerate(zip(trees, nodes)):
            subtree, parent = T.split_subtree(node)
            parents.append(parent)
            if i == 0:
                saved_subtree = subtree
        for T, parent in zip(trees, parents):
            if parent is not None:
                T.add_edge(parent, replacement_leaf)
            else:
                T.add_node(replacement_leaf)
        subtree_replace_map[replacement_leaf] = saved_subtree
    return trees, subtree_replace_map


if __name__ == '__main__':
    random.seed(42)
    trees, n_leaves = read_input(sys.stdin)
    leaves = frozenset(range(1, n_leaves + 1))
    if len(trees) > 2:
        _, srmap = subtree_reduce_multi(trees, leaves)
        to_remove = set()
        for leaf, tree in srmap.items():
            to_remove.update(all_leaves_tree(tree, next(iter(tree.roots))))
            to_remove.discard(leaf)
        for leaf in range(1, n_leaves + 1):
            if leaf not in to_remove:
                if leaf not in srmap:
                    print(str(leaf)+";")
                else:
                    print(tree_to_newick(srmap[leaf])+";")
        sys.exit(0)
    T1, T2 = trees[0], trees[1]
    seeker = GraphSeeker(T1, T2, leaves)
    seeker.run()
