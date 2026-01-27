# Complete undirected graphs

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="graph-theory.complete-undirected-graphs.html" class="Module">graph-theory.complete-undirected-graphs</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="graph-theory.complete-multipartite-graphs.html" class="Module">graph-theory.complete-multipartite-graphs</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="graph-theory.finite-graphs.html" class="Module">graph-theory.finite-graphs</a>

<a id="276" class="Keyword">open</a> <a id="281" class="Keyword">import</a> <a id="288" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

A
{{#concept "complete undirected graph" Agda=complete-Finite-Undirected-Graph WD="complete graph" WDID=Q45715}}
is a [complete multipartite graph](graph-theory.complete-multipartite-graphs.md)
in which every block has exactly one vertex. In other words, it is an
[undirected graph](graph-theory.undirected-graphs.md) in which every vertex is
connected to every other vertex.

There are many ways of presenting complete undirected graphs. For example, the
type of edges in a complete undirected graph is a
[2-element subtype](univalent-combinatorics.2-element-subtypes.md) of the type
of its vertices.

## Definition

<pre class="Agda"><a id="complete-Finite-Undirected-Graph"></a><a id="977" href="graph-theory.complete-undirected-graphs.html#977" class="Function">complete-Finite-Undirected-Graph</a> <a id="1010" class="Symbol">:</a>
  <a id="1014" class="Symbol">{</a><a id="1015" href="graph-theory.complete-undirected-graphs.html#1015" class="Bound">l</a> <a id="1017" class="Symbol">:</a> <a id="1019" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1024" class="Symbol">}</a> <a id="1026" class="Symbol">→</a> <a id="1028" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1040" href="graph-theory.complete-undirected-graphs.html#1015" class="Bound">l</a> <a id="1042" class="Symbol">→</a> <a id="1044" href="graph-theory.finite-graphs.html#990" class="Function">Finite-Undirected-Graph</a> <a id="1068" href="graph-theory.complete-undirected-graphs.html#1015" class="Bound">l</a> <a id="1070" href="graph-theory.complete-undirected-graphs.html#1015" class="Bound">l</a>
<a id="1072" href="graph-theory.complete-undirected-graphs.html#977" class="Function">complete-Finite-Undirected-Graph</a> <a id="1105" href="graph-theory.complete-undirected-graphs.html#1105" class="Bound">X</a> <a id="1107" class="Symbol">=</a>
  <a id="1111" href="graph-theory.complete-multipartite-graphs.html#3073" class="Function">complete-multipartite-Finite-Undirected-Graph</a> <a id="1157" href="graph-theory.complete-undirected-graphs.html#1105" class="Bound">X</a> <a id="1159" class="Symbol">(λ</a> <a id="1162" href="graph-theory.complete-undirected-graphs.html#1162" class="Bound">x</a> <a id="1164" class="Symbol">→</a> <a id="1166" href="univalent-combinatorics.finite-types.html#6873" class="Function">unit-Finite-Type</a><a id="1182" class="Symbol">)</a>
</pre>
## External links

- [Complete graph](https://d3gt.com/unit.html?complete-graph) at D3 Graph theory
- [Complete graph](https://www.wikidata.org/entity/Q45715) on Wikidata
- [Complete graph](https://en.wikipedia.org/wiki/Complete_graph) on Wikipedia
- [Complete graph](https://mathworld.wolfram.com/CompleteGraph.html) at Wolfram
  MathWorld
