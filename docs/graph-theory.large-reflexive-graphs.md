# Large reflexive graphs

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="graph-theory.large-reflexive-graphs.html" class="Module">graph-theory.large-reflexive-graphs</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A {{#concept "large reflexive graph" Agda=Large-Reflexive-Graph}} is a large
directed graph [equipped](foundation.structure.md) with a loop edge at every
vertex.

## Definition

<pre class="Agda"><a id="429" class="Keyword">record</a>
  <a id="Large-Reflexive-Graph"></a><a id="438" href="graph-theory.large-reflexive-graphs.html#438" class="Record">Large-Reflexive-Graph</a>
  <a id="462" class="Symbol">(</a><a id="463" href="graph-theory.large-reflexive-graphs.html#463" class="Bound">α</a> <a id="465" class="Symbol">:</a> <a id="467" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="473" class="Symbol">→</a> <a id="475" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="480" class="Symbol">)</a> <a id="482" class="Symbol">(</a><a id="483" href="graph-theory.large-reflexive-graphs.html#483" class="Bound">β</a> <a id="485" class="Symbol">:</a> <a id="487" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="493" class="Symbol">→</a> <a id="495" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="501" class="Symbol">→</a> <a id="503" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="508" class="Symbol">)</a> <a id="510" class="Symbol">:</a> <a id="512" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="518" class="Keyword">where</a>

  <a id="527" class="Keyword">field</a>
    <a id="Large-Reflexive-Graph.vertex-Large-Reflexive-Graph"></a><a id="537" href="graph-theory.large-reflexive-graphs.html#537" class="Field">vertex-Large-Reflexive-Graph</a> <a id="566" class="Symbol">:</a> <a id="568" class="Symbol">(</a><a id="569" href="graph-theory.large-reflexive-graphs.html#569" class="Bound">l</a> <a id="571" class="Symbol">:</a> <a id="573" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="578" class="Symbol">)</a> <a id="580" class="Symbol">→</a> <a id="582" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="585" class="Symbol">(</a><a id="586" href="graph-theory.large-reflexive-graphs.html#463" class="Bound">α</a> <a id="588" href="graph-theory.large-reflexive-graphs.html#569" class="Bound">l</a><a id="589" class="Symbol">)</a>

    <a id="Large-Reflexive-Graph.edge-Large-Reflexive-Graph"></a><a id="596" href="graph-theory.large-reflexive-graphs.html#596" class="Field">edge-Large-Reflexive-Graph</a> <a id="623" class="Symbol">:</a>
      <a id="631" class="Symbol">{</a><a id="632" href="graph-theory.large-reflexive-graphs.html#632" class="Bound">l1</a> <a id="635" href="graph-theory.large-reflexive-graphs.html#635" class="Bound">l2</a> <a id="638" class="Symbol">:</a> <a id="640" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="645" class="Symbol">}</a> <a id="647" class="Symbol">→</a>
      <a id="655" href="graph-theory.large-reflexive-graphs.html#537" class="Field">vertex-Large-Reflexive-Graph</a> <a id="684" href="graph-theory.large-reflexive-graphs.html#632" class="Bound">l1</a> <a id="687" class="Symbol">→</a>
      <a id="695" href="graph-theory.large-reflexive-graphs.html#537" class="Field">vertex-Large-Reflexive-Graph</a> <a id="724" href="graph-theory.large-reflexive-graphs.html#635" class="Bound">l2</a> <a id="727" class="Symbol">→</a> <a id="729" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="732" class="Symbol">(</a><a id="733" href="graph-theory.large-reflexive-graphs.html#483" class="Bound">β</a> <a id="735" href="graph-theory.large-reflexive-graphs.html#632" class="Bound">l1</a> <a id="738" href="graph-theory.large-reflexive-graphs.html#635" class="Bound">l2</a><a id="740" class="Symbol">)</a>

    <a id="Large-Reflexive-Graph.refl-Large-Reflexive-Graph"></a><a id="747" href="graph-theory.large-reflexive-graphs.html#747" class="Field">refl-Large-Reflexive-Graph</a> <a id="774" class="Symbol">:</a>
      <a id="782" class="Symbol">{</a><a id="783" href="graph-theory.large-reflexive-graphs.html#783" class="Bound">l</a> <a id="785" class="Symbol">:</a> <a id="787" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="792" class="Symbol">}</a> <a id="794" class="Symbol">(</a><a id="795" href="graph-theory.large-reflexive-graphs.html#795" class="Bound">x</a> <a id="797" class="Symbol">:</a> <a id="799" href="graph-theory.large-reflexive-graphs.html#537" class="Field">vertex-Large-Reflexive-Graph</a> <a id="828" href="graph-theory.large-reflexive-graphs.html#783" class="Bound">l</a><a id="829" class="Symbol">)</a> <a id="831" class="Symbol">→</a>
      <a id="839" href="graph-theory.large-reflexive-graphs.html#596" class="Field">edge-Large-Reflexive-Graph</a> <a id="866" href="graph-theory.large-reflexive-graphs.html#795" class="Bound">x</a> <a id="868" href="graph-theory.large-reflexive-graphs.html#795" class="Bound">x</a>

<a id="871" class="Keyword">open</a> <a id="876" href="graph-theory.large-reflexive-graphs.html#438" class="Module">Large-Reflexive-Graph</a> <a id="898" class="Keyword">public</a>
</pre>
## See also

- [Reflexive graphs](graph-theory.reflexive-graphs.md)

## External links

- [Reflexive graph](https://ncatlab.org/nlab/show/reflexive+graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Reflexive graph](https://mathworld.wolfram.com/ReflexiveGraph.html) at
  Wolfram MathWorld
