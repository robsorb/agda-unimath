# Complete multipartite graphs

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="graph-theory.complete-multipartite-graphs.html" class="Module">graph-theory.complete-multipartite-graphs</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="graph-theory.finite-graphs.html" class="Module">graph-theory.finite-graphs</a>

<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="univalent-combinatorics.dependent-function-types.html" class="Module">univalent-combinatorics.dependent-function-types</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="univalent-combinatorics.dependent-pair-types.html" class="Module">univalent-combinatorics.dependent-pair-types</a>
<a id="435" class="Keyword">open</a> <a id="440" class="Keyword">import</a> <a id="447" href="univalent-combinatorics.equality-finite-types.html" class="Module">univalent-combinatorics.equality-finite-types</a>
<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="542" class="Keyword">open</a> <a id="547" class="Keyword">import</a> <a id="554" href="univalent-combinatorics.function-types.html" class="Module">univalent-combinatorics.function-types</a>
</pre>
</details>

## Idea

Consider a family of [finite types](univalent-combinatorics.finite-types.md) `Y`
indexed by a finite type `X`. The
{{#concept "complete multipartite graph" Agda=complete-multipartite-Finite-Undirected-Graph WD="multipartite graph" WDID=Q1718082}}
at `Y` is the [finite undirected graph](graph-theory.finite-graphs.md)
consisting of:

- The finite type of vertices is the
  [dependent pair type](univalent-combinatorics.dependent-pair-types.md)
  `Σ (x : X), Y x`.
- An [unordered pair](foundation.unordered-pairs.md) `f : I → Σ (x : X), Y x` is
  an edge if the induced unordered pair `pr1 ∘ f : I → X` is an
  [embedding](foundation-core.embeddings.md).

**Note:** The formalization of the finite type of edges below is different from
the above description, and needs to be changed.

## Definitions

### Complete multipartite graphs

<pre class="Agda"><a id="1462" class="Keyword">module</a> <a id="1469" href="graph-theory.complete-multipartite-graphs.html#1469" class="Module">_</a>
  <a id="1473" class="Symbol">{</a><a id="1474" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a> <a id="1477" href="graph-theory.complete-multipartite-graphs.html#1477" class="Bound">l2</a> <a id="1480" class="Symbol">:</a> <a id="1482" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1487" class="Symbol">}</a> <a id="1489" class="Symbol">(</a><a id="1490" href="graph-theory.complete-multipartite-graphs.html#1490" class="Bound">X</a> <a id="1492" class="Symbol">:</a> <a id="1494" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1506" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a><a id="1508" class="Symbol">)</a> <a id="1510" class="Symbol">(</a><a id="1511" href="graph-theory.complete-multipartite-graphs.html#1511" class="Bound">Y</a> <a id="1513" class="Symbol">:</a> <a id="1515" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a> <a id="1532" href="graph-theory.complete-multipartite-graphs.html#1490" class="Bound">X</a> <a id="1534" class="Symbol">→</a> <a id="1536" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1548" href="graph-theory.complete-multipartite-graphs.html#1477" class="Bound">l2</a><a id="1550" class="Symbol">)</a>
  <a id="1554" class="Keyword">where</a>

  <a id="1563" href="graph-theory.complete-multipartite-graphs.html#1563" class="Function">vertex-finite-type-complete-multipartite-Finite-Undirected-Graph</a> <a id="1628" class="Symbol">:</a>
    <a id="1634" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1646" class="Symbol">(</a><a id="1647" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a> <a id="1650" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1652" href="graph-theory.complete-multipartite-graphs.html#1477" class="Bound">l2</a><a id="1654" class="Symbol">)</a>
  <a id="1658" href="graph-theory.complete-multipartite-graphs.html#1563" class="Function">vertex-finite-type-complete-multipartite-Finite-Undirected-Graph</a> <a id="1723" class="Symbol">=</a>
    <a id="1729" href="univalent-combinatorics.dependent-pair-types.html#2168" class="Function">Σ-Finite-Type</a> <a id="1743" href="graph-theory.complete-multipartite-graphs.html#1490" class="Bound">X</a> <a id="1745" href="graph-theory.complete-multipartite-graphs.html#1511" class="Bound">Y</a>

  <a id="1750" href="graph-theory.complete-multipartite-graphs.html#1750" class="Function">vertex-complete-multipartite-Finite-Undirected-Graph</a> <a id="1803" class="Symbol">:</a> <a id="1805" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1808" class="Symbol">(</a><a id="1809" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a> <a id="1812" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1814" href="graph-theory.complete-multipartite-graphs.html#1477" class="Bound">l2</a><a id="1816" class="Symbol">)</a>
  <a id="1820" href="graph-theory.complete-multipartite-graphs.html#1750" class="Function">vertex-complete-multipartite-Finite-Undirected-Graph</a> <a id="1873" class="Symbol">=</a>
    <a id="1879" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a>
      <a id="1902" href="graph-theory.complete-multipartite-graphs.html#1563" class="Function">vertex-finite-type-complete-multipartite-Finite-Undirected-Graph</a>

  <a id="1970" href="graph-theory.complete-multipartite-graphs.html#1970" class="Function">unordered-pair-vertices-complete-multipartite-Finite-Undirected-Graph</a> <a id="2040" class="Symbol">:</a>
    <a id="2046" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2049" class="Symbol">(</a><a id="2050" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2055" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2061" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2063" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a> <a id="2066" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2068" href="graph-theory.complete-multipartite-graphs.html#1477" class="Bound">l2</a><a id="2070" class="Symbol">)</a>
  <a id="2074" href="graph-theory.complete-multipartite-graphs.html#1970" class="Function">unordered-pair-vertices-complete-multipartite-Finite-Undirected-Graph</a> <a id="2144" class="Symbol">=</a>
    <a id="2150" href="foundation.unordered-pairs.html#2222" class="Function">unordered-pair</a> <a id="2165" href="graph-theory.complete-multipartite-graphs.html#1750" class="Function">vertex-complete-multipartite-Finite-Undirected-Graph</a>

  <a id="2221" href="graph-theory.complete-multipartite-graphs.html#2221" class="Function">edge-finite-type-complete-multipartite-Finite-Undirected-Graph</a> <a id="2284" class="Symbol">:</a>
    <a id="2290" href="graph-theory.complete-multipartite-graphs.html#1970" class="Function">unordered-pair-vertices-complete-multipartite-Finite-Undirected-Graph</a> <a id="2360" class="Symbol">→</a>
    <a id="2366" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="2378" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a>
  <a id="2383" href="graph-theory.complete-multipartite-graphs.html#2221" class="Function">edge-finite-type-complete-multipartite-Finite-Undirected-Graph</a> <a id="2446" href="graph-theory.complete-multipartite-graphs.html#2446" class="Bound">p</a> <a id="2448" class="Symbol">=</a>
    <a id="2454" class="Symbol">(</a> <a id="2456" href="univalent-combinatorics.dependent-function-types.html#4165" class="Function">Π-Finite-Type</a>
      <a id="2476" class="Symbol">(</a> <a id="2478" href="univalent-combinatorics.2-element-types.html#3447" class="Function">finite-type-2-Element-Type</a> <a id="2505" class="Symbol">(</a><a id="2506" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2510" href="graph-theory.complete-multipartite-graphs.html#2446" class="Bound">p</a><a id="2511" class="Symbol">))</a>
      <a id="2520" class="Symbol">(</a> <a id="2522" class="Symbol">λ</a> <a id="2524" href="graph-theory.complete-multipartite-graphs.html#2524" class="Bound">x</a> <a id="2526" class="Symbol">→</a>
        <a id="2536" href="univalent-combinatorics.dependent-function-types.html#4165" class="Function">Π-Finite-Type</a>
          <a id="2560" class="Symbol">(</a> <a id="2562" href="univalent-combinatorics.2-element-types.html#3447" class="Function">finite-type-2-Element-Type</a> <a id="2589" class="Symbol">(</a><a id="2590" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2594" href="graph-theory.complete-multipartite-graphs.html#2446" class="Bound">p</a><a id="2595" class="Symbol">))</a>
          <a id="2608" class="Symbol">(</a> <a id="2610" class="Symbol">λ</a> <a id="2612" href="graph-theory.complete-multipartite-graphs.html#2612" class="Bound">y</a> <a id="2614" class="Symbol">→</a>
            <a id="2628" href="univalent-combinatorics.equality-finite-types.html#2424" class="Function">Id-Finite-Type</a> <a id="2643" href="graph-theory.complete-multipartite-graphs.html#1490" class="Bound">X</a>
              <a id="2659" class="Symbol">(</a> <a id="2661" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2665" class="Symbol">(</a><a id="2666" href="foundation.unordered-pairs.html#3321" class="Function">element-unordered-pair</a> <a id="2689" href="graph-theory.complete-multipartite-graphs.html#2446" class="Bound">p</a> <a id="2691" href="graph-theory.complete-multipartite-graphs.html#2524" class="Bound">x</a><a id="2692" class="Symbol">))</a>
              <a id="2709" class="Symbol">(</a> <a id="2711" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2715" class="Symbol">(</a><a id="2716" href="foundation.unordered-pairs.html#3321" class="Function">element-unordered-pair</a> <a id="2739" href="graph-theory.complete-multipartite-graphs.html#2446" class="Bound">p</a> <a id="2741" href="graph-theory.complete-multipartite-graphs.html#2612" class="Bound">y</a><a id="2742" class="Symbol">)))))</a> <a id="2748" href="univalent-combinatorics.function-types.html#2576" class="Function Operator">→𝔽</a>
    <a id="2755" class="Symbol">(</a> <a id="2757" href="univalent-combinatorics.finite-types.html#5587" class="Function">empty-Finite-Type</a><a id="2774" class="Symbol">)</a>

  <a id="2779" href="graph-theory.complete-multipartite-graphs.html#2779" class="Function">edge-complete-multipartite-Finite-Undirected-Graph</a> <a id="2830" class="Symbol">:</a>
    <a id="2836" href="graph-theory.complete-multipartite-graphs.html#1970" class="Function">unordered-pair-vertices-complete-multipartite-Finite-Undirected-Graph</a> <a id="2906" class="Symbol">→</a>
    <a id="2912" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2915" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a>
  <a id="2920" href="graph-theory.complete-multipartite-graphs.html#2779" class="Function">edge-complete-multipartite-Finite-Undirected-Graph</a> <a id="2971" href="graph-theory.complete-multipartite-graphs.html#2971" class="Bound">p</a> <a id="2973" class="Symbol">=</a>
    <a id="2979" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a>
      <a id="3002" class="Symbol">(</a> <a id="3004" href="graph-theory.complete-multipartite-graphs.html#2221" class="Function">edge-finite-type-complete-multipartite-Finite-Undirected-Graph</a> <a id="3067" href="graph-theory.complete-multipartite-graphs.html#2971" class="Bound">p</a><a id="3068" class="Symbol">)</a>

  <a id="3073" href="graph-theory.complete-multipartite-graphs.html#3073" class="Function">complete-multipartite-Finite-Undirected-Graph</a> <a id="3119" class="Symbol">:</a>
    <a id="3125" href="graph-theory.finite-graphs.html#990" class="Function">Finite-Undirected-Graph</a> <a id="3149" class="Symbol">(</a><a id="3150" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a> <a id="3153" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3155" href="graph-theory.complete-multipartite-graphs.html#1477" class="Bound">l2</a><a id="3157" class="Symbol">)</a> <a id="3159" href="graph-theory.complete-multipartite-graphs.html#1474" class="Bound">l1</a>
  <a id="3164" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3168" href="graph-theory.complete-multipartite-graphs.html#3073" class="Function">complete-multipartite-Finite-Undirected-Graph</a> <a id="3214" class="Symbol">=</a>
    <a id="3220" href="graph-theory.complete-multipartite-graphs.html#1563" class="Function">vertex-finite-type-complete-multipartite-Finite-Undirected-Graph</a>
  <a id="3287" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3291" href="graph-theory.complete-multipartite-graphs.html#3073" class="Function">complete-multipartite-Finite-Undirected-Graph</a> <a id="3337" class="Symbol">=</a>
    <a id="3343" href="graph-theory.complete-multipartite-graphs.html#2221" class="Function">edge-finite-type-complete-multipartite-Finite-Undirected-Graph</a>
</pre>
## External links

- [Multipartite graph](https://www.wikidata.org/entity/Q1718082) on Wikidata
- [Multipartite graph](https://en.wikipedia.org/wiki/Multipartite_graph) on
  Wikipedia
- [Complete multipartite graph](https://mathworld.wolfram.com/CompleteMultipartiteGraph.html)
  on Wolfram MathWorld
