# Acyclic undirected graphs

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="graph-theory.acyclic-undirected-graphs.html" class="Module">graph-theory.acyclic-undirected-graphs</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="graph-theory.geometric-realizations-undirected-graphs.html" class="Module">graph-theory.geometric-realizations-undirected-graphs</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="graph-theory.reflecting-maps-undirected-graphs.html" class="Module">graph-theory.reflecting-maps-undirected-graphs</a>
<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
</details>

## Idea

An
{{#concept "acyclic undirected graph" WDID=Q3115453 WD="acyclic graph" Agda=is-acyclic-Undirected-Graph}}
is an [undirected graph](graph-theory.undirected-graphs.md) of which the
[geometric realization](graph-theory.geometric-realizations-undirected-graphs.md)
is [contractible](foundation-core.contractible-types.md).

The notion of acyclic graphs is a generalization of the notion of
[undirected trees](trees.undirected-trees.md). Note that in this library, an
undirected tree is an undirected graph in which the type of
[trails](graph-theory.trails-undirected-graphs.md) between any two points is
contractible. The type of nodes of such undirected trees consequently has
[decidable equality](foundation.decidable-equality.md). On the other hand, there
are acyclic undirected graphs that are not undirected trees in this sense. One
way to obtain them is via
[acyclic types](synthetic-homotopy-theory.acyclic-types.md), which are types of
which the [suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
contractible. The undirected suspension diagram of such types is an acyclic
graph. Furthermore, any [directed tree](trees.directed-trees.md) induces an
acyclic undirected graph by forgetting the directions of the edges.

## Definition

### Acyclic undirected graphs

The following is a preliminary definition that requires us to parametrize over
an extra universe level. This will not be necessary anymore if we constructed a
geometric realization of every undirected graph. Once we did that, we would
simply say that the geometric realization of `G` is contractible.

<pre class="Agda"><a id="is-acyclic-Undirected-Graph"></a><a id="1971" href="graph-theory.acyclic-undirected-graphs.html#1971" class="Function">is-acyclic-Undirected-Graph</a> <a id="1999" class="Symbol">:</a>
  <a id="2003" class="Symbol">{</a><a id="2004" href="graph-theory.acyclic-undirected-graphs.html#2004" class="Bound">l1</a> <a id="2007" href="graph-theory.acyclic-undirected-graphs.html#2007" class="Bound">l2</a> <a id="2010" class="Symbol">:</a> <a id="2012" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2017" class="Symbol">}</a> <a id="2019" class="Symbol">(</a><a id="2020" href="graph-theory.acyclic-undirected-graphs.html#2020" class="Bound">l</a> <a id="2022" class="Symbol">:</a> <a id="2024" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2029" class="Symbol">)</a> <a id="2031" class="Symbol">(</a><a id="2032" href="graph-theory.acyclic-undirected-graphs.html#2032" class="Bound">G</a> <a id="2034" class="Symbol">:</a> <a id="2036" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="2053" href="graph-theory.acyclic-undirected-graphs.html#2004" class="Bound">l1</a> <a id="2056" href="graph-theory.acyclic-undirected-graphs.html#2007" class="Bound">l2</a><a id="2058" class="Symbol">)</a> <a id="2060" class="Symbol">→</a>
  <a id="2064" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2067" class="Symbol">(</a><a id="2068" href="graph-theory.acyclic-undirected-graphs.html#2004" class="Bound">l1</a> <a id="2071" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2073" href="graph-theory.acyclic-undirected-graphs.html#2007" class="Bound">l2</a> <a id="2076" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2078" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2083" href="graph-theory.acyclic-undirected-graphs.html#2020" class="Bound">l</a><a id="2084" class="Symbol">)</a>
<a id="2086" href="graph-theory.acyclic-undirected-graphs.html#1971" class="Function">is-acyclic-Undirected-Graph</a> <a id="2114" href="graph-theory.acyclic-undirected-graphs.html#2114" class="Bound">l</a> <a id="2116" href="graph-theory.acyclic-undirected-graphs.html#2116" class="Bound">G</a> <a id="2118" class="Symbol">=</a>
  <a id="2122" href="graph-theory.geometric-realizations-undirected-graphs.html#1269" class="Function">is-geometric-realization-reflecting-map-Undirected-Graph</a> <a id="2179" href="graph-theory.acyclic-undirected-graphs.html#2114" class="Bound">l</a> <a id="2181" href="graph-theory.acyclic-undirected-graphs.html#2116" class="Bound">G</a>
    <a id="2187" class="Symbol">(</a> <a id="2189" href="graph-theory.reflecting-maps-undirected-graphs.html#2029" class="Function">terminal-reflecting-map-Undirected-Graph</a> <a id="2230" href="graph-theory.acyclic-undirected-graphs.html#2116" class="Bound">G</a><a id="2231" class="Symbol">)</a>
</pre>
## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}

## External links

- [Trees](https://ncatlab.org/nlab/show/tree) at $n$Lab
- [Forests](<https://en.wikipedia.org/wiki/Tree_(graph_theory)#Forest>) at
  Wikipedia
- [Acyclic graphs](https://mathworld.wolfram.com/AcyclicGraph.html) at Wolfram
  MathWorld.
