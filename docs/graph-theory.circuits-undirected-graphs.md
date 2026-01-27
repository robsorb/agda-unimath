# Circuits in undirected graphs

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="graph-theory.circuits-undirected-graphs.html" class="Module">graph-theory.circuits-undirected-graphs</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="graph-theory.totally-faithful-morphisms-undirected-graphs.html" class="Module">graph-theory.totally-faithful-morphisms-undirected-graphs</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
</details>

## Idea

A {{#concept "circuit" Agda=circuit-Undirected-Graph WD="cycle" WDID=Q245595}}
in an [undirected graph](graph-theory.undirected-graphs.md) `G` consists of a
[`k`-gon](graph-theory.polygons.md) `H` equipped with a
[totally faithful](graph-theory.totally-faithful-morphisms-undirected-graphs.md)
[morphism](graph-theory.morphisms-undirected-graphs.md) of undirected graphs
from `H` to `G`. In other words, a circuit is a closed walk with no repeated
edges.

## Definition

<pre class="Agda"><a id="935" class="Keyword">module</a> <a id="942" href="graph-theory.circuits-undirected-graphs.html#942" class="Module">_</a>
  <a id="946" class="Symbol">{</a><a id="947" href="graph-theory.circuits-undirected-graphs.html#947" class="Bound">l1</a> <a id="950" href="graph-theory.circuits-undirected-graphs.html#950" class="Bound">l2</a> <a id="953" class="Symbol">:</a> <a id="955" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="960" class="Symbol">}</a> <a id="962" class="Symbol">(</a><a id="963" href="graph-theory.circuits-undirected-graphs.html#963" class="Bound">k</a> <a id="965" class="Symbol">:</a> <a id="967" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="968" class="Symbol">)</a> <a id="970" class="Symbol">(</a><a id="971" href="graph-theory.circuits-undirected-graphs.html#971" class="Bound">G</a> <a id="973" class="Symbol">:</a> <a id="975" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="992" href="graph-theory.circuits-undirected-graphs.html#947" class="Bound">l1</a> <a id="995" href="graph-theory.circuits-undirected-graphs.html#950" class="Bound">l2</a><a id="997" class="Symbol">)</a>
  <a id="1001" class="Keyword">where</a>

  <a id="1010" href="graph-theory.circuits-undirected-graphs.html#1010" class="Function">circuit-Undirected-Graph</a> <a id="1035" class="Symbol">:</a> <a id="1037" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1040" class="Symbol">(</a><a id="1041" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1046" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1052" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1054" href="graph-theory.circuits-undirected-graphs.html#947" class="Bound">l1</a> <a id="1057" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1059" href="graph-theory.circuits-undirected-graphs.html#950" class="Bound">l2</a><a id="1061" class="Symbol">)</a>
  <a id="1065" href="graph-theory.circuits-undirected-graphs.html#1010" class="Function">circuit-Undirected-Graph</a> <a id="1090" class="Symbol">=</a>
    <a id="1096" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1098" class="Symbol">(</a> <a id="1100" href="graph-theory.polygons.html#2279" class="Function">Polygon</a> <a id="1108" href="graph-theory.circuits-undirected-graphs.html#963" class="Bound">k</a><a id="1109" class="Symbol">)</a>
      <a id="1117" class="Symbol">(</a> <a id="1119" class="Symbol">λ</a> <a id="1121" href="graph-theory.circuits-undirected-graphs.html#1121" class="Bound">H</a> <a id="1123" class="Symbol">→</a>
        <a id="1133" href="graph-theory.totally-faithful-morphisms-undirected-graphs.html#1082" class="Function">totally-faithful-hom-Undirected-Graph</a> <a id="1171" class="Symbol">(</a><a id="1172" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a> <a id="1197" href="graph-theory.circuits-undirected-graphs.html#963" class="Bound">k</a> <a id="1199" href="graph-theory.circuits-undirected-graphs.html#1121" class="Bound">H</a><a id="1200" class="Symbol">)</a> <a id="1202" href="graph-theory.circuits-undirected-graphs.html#971" class="Bound">G</a><a id="1203" class="Symbol">)</a>
</pre>
## External links

- [Cycle (Graph Theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>)
  at Wikipedia
- [Graph Cycle](https://mathworld.wolfram.com/GraphCycle.html) at Wolfram
  MathWorld
