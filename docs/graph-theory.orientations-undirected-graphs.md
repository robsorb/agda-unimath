# Orientations of undirected graphs

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="graph-theory.orientations-undirected-graphs.html" class="Module">graph-theory.orientations-undirected-graphs</a> <a id="97" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>

<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

An orientation of an undirected graph is a function that picks a direction for
every edge.

## Definition

<pre class="Agda"><a id="471" class="Keyword">module</a> <a id="478" href="graph-theory.orientations-undirected-graphs.html#478" class="Module">_</a>
  <a id="482" class="Symbol">{</a><a id="483" href="graph-theory.orientations-undirected-graphs.html#483" class="Bound">l1</a> <a id="486" href="graph-theory.orientations-undirected-graphs.html#486" class="Bound">l2</a> <a id="489" class="Symbol">:</a> <a id="491" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="496" class="Symbol">}</a> <a id="498" class="Symbol">(</a><a id="499" href="graph-theory.orientations-undirected-graphs.html#499" class="Bound">G</a> <a id="501" class="Symbol">:</a> <a id="503" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="520" href="graph-theory.orientations-undirected-graphs.html#483" class="Bound">l1</a> <a id="523" href="graph-theory.orientations-undirected-graphs.html#486" class="Bound">l2</a><a id="525" class="Symbol">)</a>
  <a id="529" class="Keyword">where</a>

  <a id="538" href="graph-theory.orientations-undirected-graphs.html#538" class="Function">orientation-Undirected-Graph</a> <a id="567" class="Symbol">:</a> <a id="569" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="572" class="Symbol">(</a><a id="573" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="578" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="584" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="586" href="graph-theory.orientations-undirected-graphs.html#483" class="Bound">l1</a> <a id="589" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="591" href="graph-theory.orientations-undirected-graphs.html#486" class="Bound">l2</a><a id="593" class="Symbol">)</a>
  <a id="597" href="graph-theory.orientations-undirected-graphs.html#538" class="Function">orientation-Undirected-Graph</a> <a id="626" class="Symbol">=</a>
    <a id="632" class="Symbol">(</a> <a id="634" href="graph-theory.orientations-undirected-graphs.html#634" class="Bound">p</a> <a id="636" class="Symbol">:</a> <a id="638" href="graph-theory.undirected-graphs.html#892" class="Function">unordered-pair-vertices-Undirected-Graph</a> <a id="679" href="graph-theory.orientations-undirected-graphs.html#499" class="Bound">G</a><a id="680" class="Symbol">)</a> <a id="682" class="Symbol">→</a>
    <a id="688" href="graph-theory.undirected-graphs.html#1493" class="Function">edge-Undirected-Graph</a> <a id="710" href="graph-theory.orientations-undirected-graphs.html#499" class="Bound">G</a> <a id="712" href="graph-theory.orientations-undirected-graphs.html#634" class="Bound">p</a> <a id="714" class="Symbol">→</a> <a id="716" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="745" class="Number">2</a> <a id="747" class="Symbol">(</a><a id="748" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="752" href="graph-theory.orientations-undirected-graphs.html#634" class="Bound">p</a><a id="753" class="Symbol">)</a>

  <a id="758" href="graph-theory.orientations-undirected-graphs.html#758" class="Function">source-edge-orientation-Undirected-Graph</a> <a id="799" class="Symbol">:</a>
    <a id="805" href="graph-theory.orientations-undirected-graphs.html#538" class="Function">orientation-Undirected-Graph</a> <a id="834" class="Symbol">→</a>
    <a id="840" class="Symbol">(</a><a id="841" href="graph-theory.orientations-undirected-graphs.html#841" class="Bound">p</a> <a id="843" class="Symbol">:</a> <a id="845" href="graph-theory.undirected-graphs.html#892" class="Function">unordered-pair-vertices-Undirected-Graph</a> <a id="886" href="graph-theory.orientations-undirected-graphs.html#499" class="Bound">G</a><a id="887" class="Symbol">)</a> <a id="889" class="Symbol">→</a>
    <a id="895" href="graph-theory.undirected-graphs.html#1493" class="Function">edge-Undirected-Graph</a> <a id="917" href="graph-theory.orientations-undirected-graphs.html#499" class="Bound">G</a> <a id="919" href="graph-theory.orientations-undirected-graphs.html#841" class="Bound">p</a> <a id="921" class="Symbol">→</a> <a id="923" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="947" href="graph-theory.orientations-undirected-graphs.html#499" class="Bound">G</a>
  <a id="951" href="graph-theory.orientations-undirected-graphs.html#758" class="Function">source-edge-orientation-Undirected-Graph</a> <a id="992" href="graph-theory.orientations-undirected-graphs.html#992" class="Bound">d</a> <a id="994" class="Symbol">(</a><a id="995" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="1000" href="graph-theory.orientations-undirected-graphs.html#1000" class="Bound">X</a> <a id="1002" href="graph-theory.orientations-undirected-graphs.html#1002" class="Bound">p</a><a id="1003" class="Symbol">)</a> <a id="1005" href="graph-theory.orientations-undirected-graphs.html#1005" class="Bound">e</a> <a id="1007" class="Symbol">=</a>
    <a id="1013" href="graph-theory.orientations-undirected-graphs.html#1002" class="Bound">p</a> <a id="1015" class="Symbol">(</a><a id="1016" href="graph-theory.orientations-undirected-graphs.html#992" class="Bound">d</a> <a id="1018" class="Symbol">(</a><a id="1019" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="1024" href="graph-theory.orientations-undirected-graphs.html#1000" class="Bound">X</a> <a id="1026" href="graph-theory.orientations-undirected-graphs.html#1002" class="Bound">p</a><a id="1027" class="Symbol">)</a> <a id="1029" href="graph-theory.orientations-undirected-graphs.html#1005" class="Bound">e</a><a id="1030" class="Symbol">)</a>
</pre>
## External links

- [Orientation](https://www.wikidata.org/entity/Q7102401) on Wikidata
- [Orientation (graph theory)](<https://en.wikipedia.org/wiki/Orientation_(graph_theory)>)
  at Wikipedia
- [Graph orientation](https://mathworld.wolfram.com/GraphOrientation.html) at
  Wolfram MathWorld
