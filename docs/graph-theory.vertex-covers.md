# Vertex covers

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="graph-theory.vertex-covers.html" class="Module">graph-theory.vertex-covers</a> <a id="60" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="116" class="Keyword">open</a> <a id="121" class="Keyword">import</a> <a id="128" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="366" class="Keyword">open</a> <a id="371" class="Keyword">import</a> <a id="378" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="405" class="Keyword">open</a> <a id="410" class="Keyword">import</a> <a id="417" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="445" class="Keyword">open</a> <a id="450" class="Keyword">import</a> <a id="457" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>

<a id="489" class="Keyword">open</a> <a id="494" class="Keyword">import</a> <a id="501" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

A **vertex cover** on a [undirect graph](graph-theory.undirected-graphs.md) is a
set of vertices that includes at least one extremity of each edge of the graph.

## Definitions

<pre class="Agda"><a id="vertex-cover"></a><a id="759" href="graph-theory.vertex-covers.html#759" class="Function">vertex-cover</a> <a id="772" class="Symbol">:</a>
  <a id="776" class="Symbol">{</a><a id="777" href="graph-theory.vertex-covers.html#777" class="Bound">l1</a> <a id="780" href="graph-theory.vertex-covers.html#780" class="Bound">l2</a> <a id="783" class="Symbol">:</a> <a id="785" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="790" class="Symbol">}</a> <a id="792" class="Symbol">→</a> <a id="794" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="811" href="graph-theory.vertex-covers.html#777" class="Bound">l1</a> <a id="814" href="graph-theory.vertex-covers.html#780" class="Bound">l2</a> <a id="817" class="Symbol">→</a> <a id="819" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="822" class="Symbol">(</a><a id="823" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="828" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="834" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="836" href="graph-theory.vertex-covers.html#777" class="Bound">l1</a> <a id="839" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="841" href="graph-theory.vertex-covers.html#780" class="Bound">l2</a><a id="843" class="Symbol">)</a>
<a id="845" href="graph-theory.vertex-covers.html#759" class="Function">vertex-cover</a> <a id="858" href="graph-theory.vertex-covers.html#858" class="Bound">G</a> <a id="860" class="Symbol">=</a>
  <a id="864" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="866" class="Symbol">(</a> <a id="868" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="892" href="graph-theory.vertex-covers.html#858" class="Bound">G</a> <a id="894" class="Symbol">→</a> <a id="896" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="900" class="Number">2</a><a id="901" class="Symbol">)</a>
    <a id="907" class="Symbol">(</a> <a id="909" class="Symbol">λ</a> <a id="911" href="graph-theory.vertex-covers.html#911" class="Bound">c</a> <a id="913" class="Symbol">→</a>
      <a id="921" class="Symbol">(</a><a id="922" href="graph-theory.vertex-covers.html#922" class="Bound">p</a> <a id="924" class="Symbol">:</a> <a id="926" href="graph-theory.undirected-graphs.html#892" class="Function">unordered-pair-vertices-Undirected-Graph</a> <a id="967" href="graph-theory.vertex-covers.html#858" class="Bound">G</a><a id="968" class="Symbol">)</a> <a id="970" class="Symbol">→</a>
      <a id="978" href="graph-theory.undirected-graphs.html#1493" class="Function">edge-Undirected-Graph</a> <a id="1000" href="graph-theory.vertex-covers.html#858" class="Bound">G</a> <a id="1002" href="graph-theory.vertex-covers.html#922" class="Bound">p</a> <a id="1004" class="Symbol">→</a>
        <a id="1014" href="foundation.propositional-truncations.html#1578" class="Function">type-trunc-Prop</a>
          <a id="1040" class="Symbol">(</a> <a id="1042" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1044" class="Symbol">(</a><a id="1045" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="1069" href="graph-theory.vertex-covers.html#858" class="Bound">G</a><a id="1070" class="Symbol">)</a>
            <a id="1084" class="Symbol">(</a> <a id="1086" class="Symbol">λ</a> <a id="1088" href="graph-theory.vertex-covers.html#1088" class="Bound">x</a> <a id="1090" class="Symbol">→</a> <a id="1092" href="foundation.unordered-pairs.html#3872" class="Function">is-in-unordered-pair</a> <a id="1113" href="graph-theory.vertex-covers.html#922" class="Bound">p</a> <a id="1115" href="graph-theory.vertex-covers.html#1088" class="Bound">x</a> <a id="1117" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1119" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a> <a id="1122" class="Symbol">(</a><a id="1123" href="graph-theory.vertex-covers.html#911" class="Bound">c</a> <a id="1125" href="graph-theory.vertex-covers.html#1088" class="Bound">x</a><a id="1126" class="Symbol">)</a> <a id="1128" class="Symbol">(</a><a id="1129" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="1133" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1137" class="Symbol">))))</a>
</pre>
## External links

- [Vertex cover](https://en.wikipedia.org/wiki/Vertex_cover) at Wikipedia
- [Vertex cover](https://mathworld.wolfram.com/VertexCover.html) at Wolfram
  MathWorld
- [Vertex cover problem](https://www.wikidata.org/entity/Q924362) on Wikidata
