# Cycles in undirected graphs

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="graph-theory.cycles-undirected-graphs.html" class="Module">graph-theory.cycles-undirected-graphs</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="195" class="Keyword">open</a> <a id="200" class="Keyword">import</a> <a id="207" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="graph-theory.embeddings-undirected-graphs.html" class="Module">graph-theory.embeddings-undirected-graphs</a>
<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
</details>

## Idea

A
{{#concept "cycle" Agda=cycle-Undirected-Graph Disambiguation="undirected graph" WD="cycle" WDID=Q245595}}
in an [undirected graph](graph-theory.undirected-graphs.md) `G` consists of a
[`k`-gon](graph-theory.polygons.md) `H` equipped with an
[embedding of graphs](graph-theory.embeddings-undirected-graphs.md) from `H`
into `G`.

## Definition

<pre class="Agda"><a id="791" class="Keyword">module</a> <a id="798" href="graph-theory.cycles-undirected-graphs.html#798" class="Module">_</a>
  <a id="802" class="Symbol">{</a><a id="803" href="graph-theory.cycles-undirected-graphs.html#803" class="Bound">l1</a> <a id="806" href="graph-theory.cycles-undirected-graphs.html#806" class="Bound">l2</a> <a id="809" class="Symbol">:</a> <a id="811" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="816" class="Symbol">}</a> <a id="818" class="Symbol">(</a><a id="819" href="graph-theory.cycles-undirected-graphs.html#819" class="Bound">k</a> <a id="821" class="Symbol">:</a> <a id="823" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="824" class="Symbol">)</a> <a id="826" class="Symbol">(</a><a id="827" href="graph-theory.cycles-undirected-graphs.html#827" class="Bound">G</a> <a id="829" class="Symbol">:</a> <a id="831" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="848" href="graph-theory.cycles-undirected-graphs.html#803" class="Bound">l1</a> <a id="851" href="graph-theory.cycles-undirected-graphs.html#806" class="Bound">l2</a><a id="853" class="Symbol">)</a>
  <a id="857" class="Keyword">where</a>

  <a id="866" href="graph-theory.cycles-undirected-graphs.html#866" class="Function">cycle-Undirected-Graph</a> <a id="889" class="Symbol">:</a> <a id="891" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="894" class="Symbol">(</a><a id="895" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="900" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="906" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="908" href="graph-theory.cycles-undirected-graphs.html#803" class="Bound">l1</a> <a id="911" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="913" href="graph-theory.cycles-undirected-graphs.html#806" class="Bound">l2</a><a id="915" class="Symbol">)</a>
  <a id="919" href="graph-theory.cycles-undirected-graphs.html#866" class="Function">cycle-Undirected-Graph</a> <a id="942" class="Symbol">=</a>
    <a id="948" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="950" class="Symbol">(</a><a id="951" href="graph-theory.polygons.html#2279" class="Function">Polygon</a> <a id="959" href="graph-theory.cycles-undirected-graphs.html#819" class="Bound">k</a><a id="960" class="Symbol">)</a> <a id="962" class="Symbol">(λ</a> <a id="965" href="graph-theory.cycles-undirected-graphs.html#965" class="Bound">H</a> <a id="967" class="Symbol">→</a> <a id="969" href="graph-theory.embeddings-undirected-graphs.html#2099" class="Function">emb-Undirected-Graph</a> <a id="990" class="Symbol">(</a><a id="991" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a> <a id="1016" href="graph-theory.cycles-undirected-graphs.html#819" class="Bound">k</a> <a id="1018" href="graph-theory.cycles-undirected-graphs.html#965" class="Bound">H</a><a id="1019" class="Symbol">)</a> <a id="1021" href="graph-theory.cycles-undirected-graphs.html#827" class="Bound">G</a><a id="1022" class="Symbol">)</a>
</pre>
## External links

- [Cycle](https://www.wikidata.org/entity/Q245595) on Wikidata
- [Cycle (graph theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>)
  at Wikipedia
- [Graph cycle](https://mathworld.wolfram.com/GraphCycle.html) at Wolfram
  MathWorld
