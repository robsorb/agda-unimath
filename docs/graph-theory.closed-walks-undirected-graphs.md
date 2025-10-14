# Closed walks in undirected graphs

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="graph-theory.closed-walks-undirected-graphs.html" class="Module">graph-theory.closed-walks-undirected-graphs</a> <a id="97" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="graph-theory.morphisms-undirected-graphs.html" class="Module">graph-theory.morphisms-undirected-graphs</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
</details>

## Idea

A
{{#concept "closed walk" Agda=closed-walk-Undirected-Graph Disambiguation="undirected graph" WDID=Q245595 WD="cycle"}}
of length `k : ℕ` in an [undirected graph](graph-theory.undirected-graphs.md)
`G` is a [morphism](graph-theory.morphisms-undirected-graphs.md) of graphs from
a [`k`-gon](graph-theory.polygons.md) into `G`.

## Definition

<pre class="Agda"><a id="798" class="Keyword">module</a> <a id="805" href="graph-theory.closed-walks-undirected-graphs.html#805" class="Module">_</a>
  <a id="809" class="Symbol">{</a><a id="810" href="graph-theory.closed-walks-undirected-graphs.html#810" class="Bound">l1</a> <a id="813" href="graph-theory.closed-walks-undirected-graphs.html#813" class="Bound">l2</a> <a id="816" class="Symbol">:</a> <a id="818" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="823" class="Symbol">}</a> <a id="825" class="Symbol">(</a><a id="826" href="graph-theory.closed-walks-undirected-graphs.html#826" class="Bound">k</a> <a id="828" class="Symbol">:</a> <a id="830" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="831" class="Symbol">)</a> <a id="833" class="Symbol">(</a><a id="834" href="graph-theory.closed-walks-undirected-graphs.html#834" class="Bound">G</a> <a id="836" class="Symbol">:</a> <a id="838" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="855" href="graph-theory.closed-walks-undirected-graphs.html#810" class="Bound">l1</a> <a id="858" href="graph-theory.closed-walks-undirected-graphs.html#813" class="Bound">l2</a><a id="860" class="Symbol">)</a>
  <a id="864" class="Keyword">where</a>

  <a id="873" href="graph-theory.closed-walks-undirected-graphs.html#873" class="Function">closed-walk-Undirected-Graph</a> <a id="902" class="Symbol">:</a> <a id="904" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="907" class="Symbol">(</a><a id="908" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="913" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="919" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="921" href="graph-theory.closed-walks-undirected-graphs.html#810" class="Bound">l1</a> <a id="924" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="926" href="graph-theory.closed-walks-undirected-graphs.html#813" class="Bound">l2</a><a id="928" class="Symbol">)</a>
  <a id="932" href="graph-theory.closed-walks-undirected-graphs.html#873" class="Function">closed-walk-Undirected-Graph</a> <a id="961" class="Symbol">=</a>
    <a id="967" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="969" class="Symbol">(</a><a id="970" href="graph-theory.polygons.html#2279" class="Function">Polygon</a> <a id="978" href="graph-theory.closed-walks-undirected-graphs.html#826" class="Bound">k</a><a id="979" class="Symbol">)</a> <a id="981" class="Symbol">(λ</a> <a id="984" href="graph-theory.closed-walks-undirected-graphs.html#984" class="Bound">H</a> <a id="986" class="Symbol">→</a> <a id="988" href="graph-theory.morphisms-undirected-graphs.html#1175" class="Function">hom-Undirected-Graph</a> <a id="1009" class="Symbol">(</a><a id="1010" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a> <a id="1035" href="graph-theory.closed-walks-undirected-graphs.html#826" class="Bound">k</a> <a id="1037" href="graph-theory.closed-walks-undirected-graphs.html#984" class="Bound">H</a><a id="1038" class="Symbol">)</a> <a id="1040" href="graph-theory.closed-walks-undirected-graphs.html#834" class="Bound">G</a><a id="1041" class="Symbol">)</a>
</pre>
## External links

- [Cycle](https://www.wikidata.org/entity/Q245595) at Wikidata
- [Cycle (Graph Theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>)
  at Wikipedia
- [Graph Cycle](https://mathworld.wolfram.com/GraphCycle.html) at Wolfram
  MathWorld
