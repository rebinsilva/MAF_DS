#!/usr/bin/env python3
from __future__ import annotations

from abc import ABC
from collections.abc import Mapping, Set
import io
from functools import cached_property
import random
import signal
import sys


class NetworkXException(Exception):
    """Base class for exceptions in NetworkX."""
class NetworkXError(NetworkXException):
    """Exception for a serious error in NetworkX"""

def _clear_cache(G):
    if cache := getattr(G, "__networkx_cache__", None):
        cache.clear()

def empty_graph(n=0, create_using=None):
    G = DiGraph()
    try:
        nodes = list(range(n))
    except TypeError:
        nodes = tuple(n)
    else:
        if n < 0:
            raise NetworkXError(f"Negative number of nodes not valid: {n}")
    G.add_nodes_from(nodes)
    return G

def create_empty_copy(G):
    H = DiGraph()
    H.add_nodes_from(G.nodes(data=True))
    H.graph.update(G.graph)
    return H

def bfs_edges(G, source):
    neighbors = G.neighbors
    depth_limit = len(G)

    seen = {source}
    n = len(G)
    depth = 0
    next_parents_children = [(source, neighbors(source))]
    while next_parents_children and depth < depth_limit:
        this_parents_children = next_parents_children
        next_parents_children = []
        for parent, children in this_parents_children:
            for child in children:
                if child not in seen:
                    seen.add(child)
                    next_parents_children.append((child, neighbors(child)))
                    yield parent, child
            if len(seen) == n:
                return
        depth += 1

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

def delete_subtree_edges(G, leaves, source):
    if source in leaves:
        return True
    children = list(G._succ[source])
    flag = False
    for v in children:
        if delete_subtree_edges(G, leaves, v):
            G.remove_edge(source, v)
            flag = True
    return flag

class DiDegreeView:
    def __init__(self, G, nbunch=None, weight=None):
        self._graph = G
        self._succ = G._succ if hasattr(G, "_succ") else G._adj
        self._pred = G._pred if hasattr(G, "_pred") else G._adj
        self._nodes = self._succ if nbunch is None else list(G.nbunch_iter(nbunch))
        self._weight = weight

    def __call__(self, nbunch=None, weight=None):
        if nbunch is None:
            if weight == self._weight:
                return self
            return self.__class__(self._graph, None, weight)
        try:
            if nbunch in self._nodes:
                if weight == self._weight:
                    return self[nbunch]
                return self.__class__(self._graph, None, weight)[nbunch]
        except TypeError:
            pass
        return self.__class__(self._graph, nbunch, weight)

    def __getitem__(self, n):
        weight = self._weight
        succs = self._succ[n]
        preds = self._pred[n]
        if weight is None:
            return len(succs) + len(preds)
        return sum(dd.get(weight, 1) for dd in succs.values()) + sum(
            dd.get(weight, 1) for dd in preds.values()
        )

    def __iter__(self):
        weight = self._weight
        if weight is None:
            for n in self._nodes:
                succs = self._succ[n]
                preds = self._pred[n]
                yield (n, len(succs) + len(preds))
        else:
            for n in self._nodes:
                succs = self._succ[n]
                preds = self._pred[n]
                deg = sum(dd.get(weight, 1) for dd in succs.values()) + sum(
                    dd.get(weight, 1) for dd in preds.values()
                )
                yield (n, deg)

    def __len__(self):
        return len(self._nodes)

    def __str__(self):
        return str(list(self))

    def __repr__(self):
        return f"{self.__class__.__name__}({dict(self)})"

class OutDegreeView(DiDegreeView):
    def __getitem__(self, n):
        nbrs = self._succ[n]
        if self._weight is None:
            return len(nbrs)
        return sum(dd.get(self._weight, 1) for dd in nbrs.values())

    def __iter__(self):
        weight = self._weight
        if weight is None:
            for n in self._nodes:
                succs = self._succ[n]
                yield (n, len(succs))
        else:
            for n in self._nodes:
                succs = self._succ[n]
                deg = sum(dd.get(weight, 1) for dd in succs.values())
                yield (n, deg)

class InDegreeView(DiDegreeView):
    def __getitem__(self, n):
        weight = self._weight
        nbrs = self._pred[n]
        if weight is None:
            return len(nbrs)
        return sum(dd.get(weight, 1) for dd in nbrs.values())

    def __iter__(self):
        weight = self._weight
        if weight is None:
            for n in self._nodes:
                preds = self._pred[n]
                yield (n, len(preds))
        else:
            for n in self._nodes:
                preds = self._pred[n]
                deg = sum(dd.get(weight, 1) for dd in preds.values())
                yield (n, deg)

class AtlasView(Mapping):
    __slots__ = ("_atlas",)

    def __getstate__(self):
        return {"_atlas": self._atlas}

    def __setstate__(self, state):
        self._atlas = state["_atlas"]

    def __init__(self, d):
        self._atlas = d

    def __len__(self):
        return len(self._atlas)

    def __iter__(self):
        return iter(self._atlas)

    def __getitem__(self, key):
        return self._atlas[key]

    def copy(self):
        return {n: self[n].copy() for n in self._atlas}

    def __str__(self):
        return str(self._atlas)  # {nbr: self[nbr] for nbr in self})

    def __repr__(self):
        return f"{self.__class__.__name__}({self._atlas!r})"
class AdjacencyView(AtlasView):

    __slots__ = ()  # Still uses AtlasView slots names _atlas

    def __getitem__(self, name):
        return AtlasView(self._atlas[name])

    def copy(self):
        return {n: self[n].copy() for n in self._atlas}
class EdgeViewABC(ABC):
    pass

class OutEdgeDataView(EdgeViewABC):
    """EdgeDataView for outward edges of DiGraph; See EdgeDataView"""

    __slots__ = (
        "_viewer",
        "_nbunch",
        "_data",
        "_default",
        "_adjdict",
        "_nodes_nbrs",
        "_report",
    )

    def __getstate__(self):
        return {
            "viewer": self._viewer,
            "nbunch": self._nbunch,
            "data": self._data,
            "default": self._default,
        }

    def __setstate__(self, state):
        self.__init__(**state)

    def __init__(self, viewer, nbunch=None, data=False, *, default=None):
        self._viewer = viewer
        adjdict = self._adjdict = viewer._adjdict
        if nbunch is None:
            self._nodes_nbrs = adjdict.items
        else:
            # dict retains order of nodes but acts like a set
            nbunch = dict.fromkeys(viewer._graph.nbunch_iter(nbunch))
            self._nodes_nbrs = lambda: [(n, adjdict[n]) for n in nbunch]
        self._nbunch = nbunch
        self._data = data
        self._default = default
        # Set _report based on data and default
        if data is True:
            self._report = lambda n, nbr, dd: (n, nbr, dd)
        elif data is False:
            self._report = lambda n, nbr, dd: (n, nbr)
        else:  # data is attribute name
            self._report = lambda n, nbr, dd: (
                (n, nbr, dd[data]) if data in dd else (n, nbr, default)
            )

    def __len__(self):
        return sum(len(nbrs) for n, nbrs in self._nodes_nbrs())

    def __iter__(self):
        return (
            self._report(n, nbr, dd)
            for n, nbrs in self._nodes_nbrs()
            for nbr, dd in nbrs.items()
        )

    def __contains__(self, e):
        u, v = e[:2]
        if self._nbunch is not None and u not in self._nbunch:
            return False  # this edge doesn't start in nbunch
        try:
            ddict = self._adjdict[u][v]
        except KeyError:
            return False
        return e == self._report(u, v, ddict)

    def __str__(self):
        return str(list(self))

    def __repr__(self):
        return f"{self.__class__.__name__}({list(self)})"

class OutEdgeView(Set, Mapping, EdgeViewABC):
    """A EdgeView class for outward edges of a DiGraph"""

    __slots__ = ("_adjdict", "_graph", "_nodes_nbrs")

    def __getstate__(self):
        return {"_graph": self._graph, "_adjdict": self._adjdict}

    def __setstate__(self, state):
        self._graph = state["_graph"]
        self._adjdict = state["_adjdict"]
        self._nodes_nbrs = self._adjdict.items

    @classmethod
    def _from_iterable(cls, it):
        return set(it)

    dataview = OutEdgeDataView

    def __init__(self, G):
        self._graph = G
        self._adjdict = G._succ if hasattr(G, "succ") else G._adj
        self._nodes_nbrs = self._adjdict.items

    # Set methods
    def __len__(self):
        return sum(len(nbrs) for n, nbrs in self._nodes_nbrs())

    def __iter__(self):
        for n, nbrs in self._nodes_nbrs():
            for nbr in nbrs:
                yield (n, nbr)

    def __contains__(self, e):
        try:
            u, v = e
            return v in self._adjdict[u]
        except KeyError:
            return False

    # Mapping Methods
    def __getitem__(self, e):
        if isinstance(e, slice):
            raise NetworkXError(
                f"{type(self).__name__} does not support slicing, "
                f"try list(G.edges)[{e.start}:{e.stop}:{e.step}]"
            )
        u, v = e
        try:
            return self._adjdict[u][v]
        except KeyError as err:
            err.add_note(f"The edge {e} is not in the graph")
            raise

    # EdgeDataView methods
    def __call__(self, nbunch=None, data=False, *, default=None):
        if nbunch is None and data is False:
            return self
        return self.dataview(self, nbunch, data, default=default)

    def data(self, data=True, default=None, nbunch=None):
        if nbunch is None and data is False:
            return self
        return self.dataview(self, nbunch, data, default=default)

    # String Methods
    def __str__(self):
        return str(list(self))

    def __repr__(self):
        return f"{self.__class__.__name__}({list(self)})"

class NodeDataView(Set):
    __slots__ = ("_nodes", "_data", "_default")

    def __getstate__(self):
        return {"_nodes": self._nodes, "_data": self._data, "_default": self._default}

    def __setstate__(self, state):
        self._nodes = state["_nodes"]
        self._data = state["_data"]
        self._default = state["_default"]

    def __init__(self, nodedict, data=False, default=None):
        self._nodes = nodedict
        self._data = data
        self._default = default

    @classmethod
    def _from_iterable(cls, it):
        try:
            return set(it)
        except TypeError as err:
            if "unhashable" in str(err):
                msg = " : Could be b/c data=True or your values are unhashable"
                raise TypeError(str(err) + msg) from err
            raise

    def __len__(self):
        return len(self._nodes)

    def __iter__(self):
        data = self._data
        if data is False:
            return iter(self._nodes)
        if data is True:
            return iter(self._nodes.items())
        return (
            (n, dd[data] if data in dd else self._default)
            for n, dd in self._nodes.items()
        )

    def __contains__(self, n):
        try:
            node_in = n in self._nodes
        except TypeError:
            n, d = n
            return n in self._nodes and self[n] == d
        if node_in is True:
            return node_in
        try:
            n, d = n
        except (TypeError, ValueError):
            return False
        return n in self._nodes and self[n] == d

    def __getitem__(self, n):
        if isinstance(n, slice):
            raise nx.NetworkXError(
                f"{type(self).__name__} does not support slicing, "
                f"try list(G.nodes.data())[{n.start}:{n.stop}:{n.step}]"
            )
        ddict = self._nodes[n]
        data = self._data
        if data is False or data is True:
            return ddict
        return ddict[data] if data in ddict else self._default

    def __str__(self):
        return str(list(self))

    def __repr__(self):
        name = self.__class__.__name__
        if self._data is False:
            return f"{name}({tuple(self)})"
        if self._data is True:
            return f"{name}({dict(self)})"
        return f"{name}({dict(self)}, data={self._data!r})"

class NodeView(Mapping, Set):

    __slots__ = ("_nodes",)

    def __getstate__(self):
        return {"_nodes": self._nodes}

    def __setstate__(self, state):
        self._nodes = state["_nodes"]

    def __init__(self, graph):
        self._nodes = graph._node

    # Mapping methods
    def __len__(self):
        return len(self._nodes)

    def __iter__(self):
        return iter(self._nodes)

    def __getitem__(self, n):
        if isinstance(n, slice):
            raise nx.NetworkXError(
                f"{type(self).__name__} does not support slicing, "
                f"try list(G.nodes)[{n.start}:{n.stop}:{n.step}]"
            )
        return self._nodes[n]

    # Set methods
    def __contains__(self, n):
        return n in self._nodes

    @classmethod
    def _from_iterable(cls, it):
        return set(it)

    # DataView method
    def __call__(self, data=False, default=None):
        if data is False:
            return self
        return NodeDataView(self._nodes, data, default)

    def data(self, data=True, default=None):
        if data is False:
            return self
        return NodeDataView(self._nodes, data, default)

    def __str__(self):
        return str(list(self))

    def __repr__(self):
        return f"{self.__class__.__name__}({tuple(self)})"

# https://networkx.org/documentation/stable/_modules/networkx/algorithms/components/weakly_connected.html#weakly_connected_components
def weakly_connected_components(G):
    seen = set()
    n = len(G)  # must be outside the loop to avoid performance hit with graph views
    for v in G:
        if v not in seen:
            c = _plain_bfs(G, n - len(seen), v)
            seen.update(c)
            yield c

def _plain_bfs(G, n, source):
    Gsucc = G._succ
    Gpred = G._pred
    seen = {source}
    nextlevel = [source]

    while nextlevel:
        thislevel = nextlevel
        nextlevel = []
        for v in thislevel:
            for w in Gsucc[v]:
                if w not in seen:
                    seen.add(w)
                    nextlevel.append(w)
            for w in Gpred[v]:
                if w not in seen:
                    seen.add(w)
                    nextlevel.append(w)
            if len(seen) == n:
                return seen
    return seen

# https://networkx.org/documentation/stable/_modules/networkx/classes/digraph.html#DiGraph

class _CachedPropertyResetterAdjAndSucc:
    def __set__(self, obj, value):
        od = obj.__dict__
        od["_adj"] = value
        od["_succ"] = value
        # reset cached properties
        props = [
            "adj",
            "succ",
            "edges",
            "out_edges",
            "degree",
            "out_degree",
            "in_degree",
        ]
        for prop in props:
            if prop in od:
                del od[prop]


class _CachedPropertyResetterPred:
    def __set__(self, obj, value):
        od = obj.__dict__
        od["_pred"] = value
        # reset cached properties
        props = ["pred", "in_edges", "degree", "out_degree", "in_degree"]
        for prop in props:
            if prop in od:
                del od[prop]
class _CachedPropertyResetterNode:

    def __set__(self, obj, value):
        od = obj.__dict__
        od["_node"] = value
        # reset cached properties
        if "nodes" in od:
            del od["nodes"]

class DiGraph:

    __networkx_backend__ = "networkx"

    _node = _CachedPropertyResetterNode()

    node_dict_factory = dict
    node_attr_dict_factory = dict
    adjlist_outer_dict_factory = dict
    adjlist_inner_dict_factory = dict
    edge_attr_dict_factory = dict
    graph_attr_dict_factory = dict

    _adj = _CachedPropertyResetterAdjAndSucc()  # type: ignore[assignment]
    _succ = _adj  # type: ignore[has-type]
    _pred = _CachedPropertyResetterPred()

    def __init__(self, incoming_graph_data=None, **attr):
        self.graph = self.graph_attr_dict_factory()  # dictionary for graph attributes
        self._node = self.node_dict_factory()  # dictionary for node attr
        # We store two adjacency lists:
        # the predecessors of node n are stored in the dict self._pred
        # the successors of node n are stored in the dict self._succ=self._adj
        self._adj = self.adjlist_outer_dict_factory()  # empty adjacency dict successor
        self._pred = self.adjlist_outer_dict_factory()  # predecessor
        # Note: self._succ = self._adj  # successor

        self.__networkx_cache__ = {}
        # attempt to load graph with data
        if incoming_graph_data is not None:
            convert.to_networkx_graph(incoming_graph_data, create_using=self)
        # load graph attributes (must be after convert)
        attr.pop("backend", None)  # Ignore explicit `backend="networkx"`
        self.graph.update(attr)

    def __str__(self):
        return "".join(
            [
                type(self).__name__,
                f" named {self.name!r}" if self.name else "",
                f" with {self.number_of_nodes()} nodes and {self.number_of_edges()} edges",
            ]
        )


    def __iter__(self):
        return iter(self._node)



    def __contains__(self, n):
        try:
            return n in self._node
        except TypeError:
            return False

    def __len__(self):
        return len(self._node)

    def __getitem__(self, n):
        return self.adj[n]

    def copy(self):
        G = self.__class__()
        G.graph.update(self.graph)
        G.add_nodes_from((n, d.copy()) for n, d in self._node.items())
        G.add_edges_from(
            (u, v, datadict.copy())
            for u, nbrs in self._adj.items()
            for v, datadict in nbrs.items()
        )
        return G

    @cached_property
    def nodes(self):
        return NodeView(self)

    @cached_property
    def adj(self):
        return AdjacencyView(self._succ)

    @cached_property
    def succ(self):
        return AdjacencyView(self._succ)

    @cached_property
    def pred(self):
        return AdjacencyView(self._pred)


    def add_node(self, node_for_adding, **attr):
        if node_for_adding not in self._succ:
            if node_for_adding is None:
                raise ValueError("None cannot be a node")
            self._succ[node_for_adding] = self.adjlist_inner_dict_factory()
            self._pred[node_for_adding] = self.adjlist_inner_dict_factory()
            attr_dict = self._node[node_for_adding] = self.node_attr_dict_factory()
            attr_dict.update(attr)
        else:  # update attr even if node already exists
            self._node[node_for_adding].update(attr)
        _clear_cache(self)

    
    def add_nodes_from(self, nodes_for_adding, **attr):
        for n in nodes_for_adding:
            try:
                newnode = n not in self._node
                newdict = attr
            except TypeError:
                n, ndict = n
                newnode = n not in self._node
                newdict = attr.copy()
                newdict.update(ndict)
            if newnode:
                if n is None:
                    raise ValueError("None cannot be a node")
                self._succ[n] = self.adjlist_inner_dict_factory()
                self._pred[n] = self.adjlist_inner_dict_factory()
                self._node[n] = self.node_attr_dict_factory()
            self._node[n].update(newdict)
        _clear_cache(self)


    
    def remove_node(self, n):
        try:
            nbrs = self._succ[n]
            del self._node[n]
        except KeyError as err:  # NetworkXError if n not in self
            raise NetworkXError(f"The node {n} is not in the digraph.") from err
        for u in nbrs:
            del self._pred[u][n]  # remove all edges n-u in digraph
        del self._succ[n]  # remove node from succ
        for u in self._pred[n]:
            del self._succ[u][n]  # remove all edges n-u in digraph
        del self._pred[n]  # remove node from pred
        _clear_cache(self)


    
    def remove_nodes_from(self, nodes):
        for n in nodes:
            try:
                succs = self._succ[n]
                del self._node[n]
                for u in succs:
                    del self._pred[u][n]  # remove all edges n-u in digraph
                del self._succ[n]  # now remove node
                for u in self._pred[n]:
                    del self._succ[u][n]  # remove all edges n-u in digraph
                del self._pred[n]  # now remove node
            except KeyError:
                pass  # silent failure on remove
        _clear_cache(self)


    def add_edge(self, u_of_edge, v_of_edge, **attr):
        u, v = u_of_edge, v_of_edge
        # add nodes
        if u not in self._succ:
            if u is None:
                raise ValueError("None cannot be a node")
            self._succ[u] = self.adjlist_inner_dict_factory()
            self._pred[u] = self.adjlist_inner_dict_factory()
            self._node[u] = self.node_attr_dict_factory()
        if v not in self._succ:
            if v is None:
                raise ValueError("None cannot be a node")
            self._succ[v] = self.adjlist_inner_dict_factory()
            self._pred[v] = self.adjlist_inner_dict_factory()
            self._node[v] = self.node_attr_dict_factory()
        # add the edge
        datadict = self._adj[u].get(v, self.edge_attr_dict_factory())
        datadict.update(attr)
        self._succ[u][v] = datadict
        self._pred[v][u] = datadict
        _clear_cache(self)

    def add_edges_from(self, ebunch_to_add, **attr):
        for e in ebunch_to_add:
            ne = len(e)
            if ne == 3:
                u, v, dd = e
            elif ne == 2:
                u, v = e
                dd = {}
            else:
                raise NetworkXError(f"Edge tuple {e} must be a 2-tuple or 3-tuple.")
            if u not in self._succ:
                if u is None:
                    raise ValueError("None cannot be a node")
                self._succ[u] = self.adjlist_inner_dict_factory()
                self._pred[u] = self.adjlist_inner_dict_factory()
                self._node[u] = self.node_attr_dict_factory()
            if v not in self._succ:
                if v is None:
                    raise ValueError("None cannot be a node")
                self._succ[v] = self.adjlist_inner_dict_factory()
                self._pred[v] = self.adjlist_inner_dict_factory()
                self._node[v] = self.node_attr_dict_factory()
            datadict = self._adj[u].get(v, self.edge_attr_dict_factory())
            datadict.update(attr)
            datadict.update(dd)
            self._succ[u][v] = datadict
            self._pred[v][u] = datadict
        _clear_cache(self)

    
    def remove_edge(self, u, v):
        try:
            del self._succ[u][v]
            del self._pred[v][u]
        except KeyError as err:
            raise NetworkXError(f"The edge {u}-{v} not in graph.") from err
        _clear_cache(self)

    
    def remove_edges_from(self, ebunch):
        for e in ebunch:
            u, v = e[:2]  # ignore edge data
            if u in self._succ and v in self._succ[u]:
                del self._succ[u][v]
                del self._pred[v][u]
        _clear_cache(self)


    def has_successor(self, u, v):
        return u in self._succ and v in self._succ[u]

    def has_predecessor(self, u, v):
        return u in self._pred and v in self._pred[u]

    
    def successors(self, n):
        try:
            return iter(self._succ[n])
        except KeyError as err:
            raise NetworkXError(f"The node {n} is not in the digraph.") from err

# digraph definitions
    neighbors = successors

    def predecessors(self, n):
        try:
            return iter(self._pred[n])
        except KeyError as err:
            raise NetworkXError(f"The node {n} is not in the digraph.") from err



    
    @cached_property
    def edges(self):
        return OutEdgeView(self)

    # alias out_edges to edges
    @cached_property
    def out_edges(self):
        return OutEdgeView(self)

    out_edges.__doc__ = edges.__doc__

    @cached_property
    def in_edges(self):
        return InEdgeView(self)

    @cached_property
    def degree(self):
        return DiDegreeView(self)

    @cached_property
    def in_degree(self):
        return InDegreeView(self)

    @cached_property
    def out_degree(self):
        return OutDegreeView(self)

    
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
        # assert child in T
        return child
    # assert node in T
    return node


class NumComponentSpec:
    def __init__(self, graph: nx.DiGraph, all_leaves: frozenset):
        self._all_leaves = all_leaves

    def __call__(self, graph:nx.DiGraph) -> float:
        # score =  -len([comp for comp in weakly_connected_components(graph) if comp & self._all_leaves])
        score = -len({find_root(graph, leaf) for leaf in self._all_leaves})
        return score

def find_root(graph, node):
    while graph.in_degree(node) == 1:
        node = next(iter(graph.predecessors(node)))
    return node
class AgreementSpec:

    def __init__(self, graph: nx.DiGraph, T2: nx.DiGraph, all_leaves: frozenset):
        self._T2 = T2
        self._all_leaves = all_leaves

    def __call__(self, graph:nx.DiGraph) -> float:
        # print("AGREEMENT", graph)
        roots = [v for v in graph.nodes if graph.in_degree(v) == 0]
        nxt_roots = set()
        T1_contracted = graph.copy()
        for root in roots:
            root = remove_contract_rooted(T1_contracted, self._all_leaves, root)
            if root is not None:
                nxt_roots.add(root)
        T1_roots = nxt_roots
        T2 = self._T2.copy()
        for T1_root in T1_roots:

            # TODO: Simplify to make this faster
            # T1_component = all_vertex_component(T1_contracted, T1_root)
            T1_leaves = set(all_leaves_tree(T1_contracted, T1_root))
            leaf = next(iter(T1_leaves))
            T2_root = find_root(T2, leaf)
            T2_leaves = set(all_leaves_tree(T2, T2_root))

            if not (T2_leaves >= T1_leaves):
                return -float("inf")

            # S = frozenset(T1_leaves & self._all_leaves)
            # for comp in weakly_connected_components(T2):
            #     if S & comp:
            #         if comp >= S:
            #             chosen_comp = comp
            #             break
            #         else:
            #             return -float("inf")
            # else:
            #     return -float("inf")

            # T2_root = find_root(T2, next(iter(chosen_comp)))
            # for v in chosen_comp:
            #     if T2.in_degree(v) == 0:
            #         T2_root = v
            #         break
            # else:
            #     raise ValueError("No root found in T2 for component containing S")
            T2_removed = T2.copy()
            # T2_root = remove_rooted(T2_removed, S, T2_root)
            # T2.remove_edges_from(bfs_edges(T2_removed, T2_root))
            # delete_subtree(T2, S, T2_root)
            # delete_subtree_edges(T2, S, T2_root) # Analyse why delete_subtree doesn't work here
            # for edge in bfs_edges(T2_removed, T2_root):
            #     T2.remove_edge(*edge)
            T2_root = remove_contract_rooted(T2_removed, T1_leaves, T2_root)

            if tree_to_newick(T1_contracted, root=T1_root) != tree_to_newick(T2_removed, root=T2_root):
                return -float("inf")
            
            delete_subtree(T2, T1_leaves, T2_root)
            # delete_subtree_edges(T2, T2_root) # Analyse why delete_subtree doesn't work here
            

        return 0.0


# ---------------------------------------------------------------------------
# MAF DeltaSearch solver
# ---------------------------------------------------------------------------

class GraphSeeker:
    def __init__(self, graph: nx.DiGraph, leaves: frozenset[int], score:Callable[[nx.DiGraph], float], validity:Callable[[nx.DiGraph], bool]):
        self.graph = graph
        self.leaves = leaves

        self.score = score
        self.valid = validity

        self.result = create_empty_copy(self.graph)
        self.best_score = self.score(self.result)
        self.empty_score = self.best_score
        # self.print = self.prepare_solution(self.result)

        # https://optil.io/optilion/help/signals
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
                    if self.valid(cur_graph):
                        tst_score = self.score(cur_graph)
                        if tst_score > cur_score:
                            cur_score = tst_score
                            cur_soln = cs
                            del c[i*k+min(i, m): (i+1)*k+min(i+1,m)]
                            if cur_score > self.best_score:
                                self.result = cur_graph
                                self.best_score = cur_score
                                # self.print = self.prepare_solution(self.result)
                                continue
                    cur_graph.remove_edges_from(tst_subset)

            # self.exit(None, None)
            c = list(self.graph.edges())
            random.shuffle(c)

    def prepare_solution(self, graph):
        visited = set()
        out_trees = []
        for leaf in self.leaves:
            if leaf not in visited:
                root = find_root(graph, leaf)
                root = remove_contract_rooted(graph, self.leaves, root)
                out_tree = tree_to_newick(graph, root=root)
                visited.update(all_leaves_tree(graph, root))
                out_trees.append(out_tree)        
        return ";\n".join(out_trees)+";"


        all_leaves = self.leaves
        out_trees = []
        all_roots = {v for v in graph.nodes() if graph.in_degree(v) == 0}
        for comp in list(weakly_connected_components(graph)):
            if not (comp & all_leaves):
                continue
            roots = list(all_roots & comp)
            assert len(roots) == 1
            root = roots[0]
            root = remove_contract_rooted(graph, all_leaves, root)
            assert root is not None
            out_tree = tree_to_newick(graph, root=root) 
            # tree_nodes = all_vertex_component(graph, root)
            # tree = graph.subgraph(tree_nodes)
            out_trees.append(out_tree)
        return ";\n".join(out_trees)+";"

    def exit(self, signum, frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        # TODO: Uncomment following line
        self.print = self.prepare_solution(self.result)
        print(self.print)
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
            trees.append(tree)
            n_pending_trees -= 1
            if n_pending_trees == 0:
                break

    return trees, n_leaves

# https://stackoverflow.com/a/57393072/9939883
def tree_to_newick(g, root=None):
    newick_str, _ = _tree_to_newick(g, root=root)
    return newick_str

def _tree_to_newick(g, root=None):
    if root is None:
        roots = list(filter(lambda p: p[1] == 0, g.in_degree()))
        assert 1 == len(roots)
        root = roots[0][0]
    subgs = []
    if len(g[root]) == 0:
        return (str(root), root)
    for child in g[root]:
        subgs.append(_tree_to_newick(g, root=child))
    subgs.sort(key=lambda x: x[1])
    myid = min(x[1] for x in subgs)
    return ("(" + ','.join(x[0] for x in subgs) + ")", myid)

def tree_to_newick_list(g, result, root=None):
    if root is None:
        roots = list(filter(lambda p: p[1] == 0, g.in_degree()))
        assert 1 == len(roots)
        root = roots[0][0]
    if len(g[root]) == 0:
        result.append(str(root))
        # return str(root)
        return root
    
    result.append("(")
    representative = float('inf')
    for child in g[root]:
        representative = min(representative, tree_to_newick_list(g, result, root=child))
        result.append(',')
    result[-1] = ')' # replace last comma with closing parenthesis
    return

def tree_to_newick2(g, root=None):
    result = []
    tree_to_newick_list(g, result, root=root)
    return ''.join(result)

def write_output(trees: list[str]) -> None:
    result = []
    for tree in trees:
        newick_string = tree + ';'
        result.append(newick_string)
    print('\n'.join(result))

def parse_newick_to_digraph(newick_str: str) -> nx.DiGraph:
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
        T1, leaves, NumComponentSpec(T1, leaves), lambda g: AgreementSpec(g, T2, leaves)(g) > -float("inf")
    )
    seeker.run()
