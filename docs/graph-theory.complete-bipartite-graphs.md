# Complete bipartite graphs

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="graph-theory.complete-bipartite-graphs.html" class="Module">graph-theory.complete-bipartite-graphs</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="graph-theory.finite-graphs.html" class="Module">graph-theory.finite-graphs</a>

<a id="298" class="Keyword">open</a> <a id="303" class="Keyword">import</a> <a id="310" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="350" class="Keyword">open</a> <a id="355" class="Keyword">import</a> <a id="362" href="univalent-combinatorics.cartesian-product-types.html" class="Module">univalent-combinatorics.cartesian-product-types</a>
<a id="410" class="Keyword">open</a> <a id="415" class="Keyword">import</a> <a id="422" href="univalent-combinatorics.coproduct-types.html" class="Module">univalent-combinatorics.coproduct-types</a>
<a id="462" class="Keyword">open</a> <a id="467" class="Keyword">import</a> <a id="474" href="univalent-combinatorics.dependent-pair-types.html" class="Module">univalent-combinatorics.dependent-pair-types</a>
<a id="519" class="Keyword">open</a> <a id="524" class="Keyword">import</a> <a id="531" href="univalent-combinatorics.fibers-of-maps.html" class="Module">univalent-combinatorics.fibers-of-maps</a>
<a id="570" class="Keyword">open</a> <a id="575" class="Keyword">import</a> <a id="582" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

Consider two [finite sets](univalent-combinatorics.finite-types.md) `X` and `Y`.
The
{{#concept "complete bipartite graph" Agda=complete-bipartite-Finite-Undirected-Graph WDID=Q913598 WD="complete bipartite graph"}}
on `X` and `Y` is the [undirected finite graph](graph-theory.finite-graphs.md)
consisting of:

- The finite set of vertices is the
  [coproduct type](univalent-combinatorics.coproduct-types.md) `X + Y`.
- Given an [unordered pair](foundation.unordered-pairs.md) `f : I → X + Y` of
  vertices, the finite type of edges on the unordered pair `(I , f)` is given by

  ```text
    (Σ (x : X), fiber f (inl x))  × (Σ (y : Y), fiber f (inr y)).
  ```

  In other words, an unordered pair of elements of the coproduct type `X + Y` is
  an edge in the complete bipartite graph on `X` and `Y` precisely when one of
  the elements of the unordered pair comes from `X` and the other comes from
  `Y`.

## Definition

<pre class="Agda"><a id="1575" class="Keyword">module</a> <a id="1582" href="graph-theory.complete-bipartite-graphs.html#1582" class="Module">_</a>
  <a id="1586" class="Symbol">{</a><a id="1587" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a> <a id="1590" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a> <a id="1593" class="Symbol">:</a> <a id="1595" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1600" class="Symbol">}</a> <a id="1602" class="Symbol">(</a><a id="1603" href="graph-theory.complete-bipartite-graphs.html#1603" class="Bound">X</a> <a id="1605" class="Symbol">:</a> <a id="1607" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1619" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a><a id="1621" class="Symbol">)</a> <a id="1623" class="Symbol">(</a><a id="1624" href="graph-theory.complete-bipartite-graphs.html#1624" class="Bound">Y</a> <a id="1626" class="Symbol">:</a> <a id="1628" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1640" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a><a id="1642" class="Symbol">)</a>
  <a id="1646" class="Keyword">where</a>

  <a id="1655" href="graph-theory.complete-bipartite-graphs.html#1655" class="Function">vertex-finite-type-complete-bipartite-Finite-Undirected-Graph</a> <a id="1717" class="Symbol">:</a>
    <a id="1723" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1735" class="Symbol">(</a><a id="1736" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a> <a id="1739" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1741" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a><a id="1743" class="Symbol">)</a>
  <a id="1747" href="graph-theory.complete-bipartite-graphs.html#1655" class="Function">vertex-finite-type-complete-bipartite-Finite-Undirected-Graph</a> <a id="1809" class="Symbol">=</a>
    <a id="1815" href="univalent-combinatorics.coproduct-types.html#9191" class="Function">coproduct-Finite-Type</a> <a id="1837" href="graph-theory.complete-bipartite-graphs.html#1603" class="Bound">X</a> <a id="1839" href="graph-theory.complete-bipartite-graphs.html#1624" class="Bound">Y</a>

  <a id="1844" href="graph-theory.complete-bipartite-graphs.html#1844" class="Function">vertex-complete-bipartite-Finite-Undirected-Graph</a> <a id="1894" class="Symbol">:</a> <a id="1896" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1899" class="Symbol">(</a><a id="1900" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a> <a id="1903" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1905" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a><a id="1907" class="Symbol">)</a>
  <a id="1911" href="graph-theory.complete-bipartite-graphs.html#1844" class="Function">vertex-complete-bipartite-Finite-Undirected-Graph</a> <a id="1961" class="Symbol">=</a>
    <a id="1967" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a>
      <a id="1990" href="graph-theory.complete-bipartite-graphs.html#1655" class="Function">vertex-finite-type-complete-bipartite-Finite-Undirected-Graph</a>

  <a id="2055" href="graph-theory.complete-bipartite-graphs.html#2055" class="Function">unordered-pair-vertices-complete-bipartite-Finite-Undirected-Graph</a> <a id="2122" class="Symbol">:</a>
    <a id="2128" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2131" class="Symbol">(</a><a id="2132" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2137" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2143" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2145" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a> <a id="2148" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2150" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a><a id="2152" class="Symbol">)</a>
  <a id="2156" href="graph-theory.complete-bipartite-graphs.html#2055" class="Function">unordered-pair-vertices-complete-bipartite-Finite-Undirected-Graph</a> <a id="2223" class="Symbol">=</a>
    <a id="2229" href="foundation.unordered-pairs.html#2222" class="Function">unordered-pair</a> <a id="2244" href="graph-theory.complete-bipartite-graphs.html#1844" class="Function">vertex-complete-bipartite-Finite-Undirected-Graph</a>

  <a id="2297" href="graph-theory.complete-bipartite-graphs.html#2297" class="Function">edge-finite-type-complete-bipartite-Finite-Undirected-Graph</a> <a id="2357" class="Symbol">:</a>
    <a id="2363" href="graph-theory.complete-bipartite-graphs.html#2055" class="Function">unordered-pair-vertices-complete-bipartite-Finite-Undirected-Graph</a> <a id="2430" class="Symbol">→</a>
    <a id="2436" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="2448" class="Symbol">(</a><a id="2449" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a> <a id="2452" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2454" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a><a id="2456" class="Symbol">)</a>
  <a id="2460" href="graph-theory.complete-bipartite-graphs.html#2297" class="Function">edge-finite-type-complete-bipartite-Finite-Undirected-Graph</a> <a id="2520" href="graph-theory.complete-bipartite-graphs.html#2520" class="Bound">p</a> <a id="2522" class="Symbol">=</a>
    <a id="2528" href="univalent-combinatorics.cartesian-product-types.html#4879" class="Function">product-Finite-Type</a>
      <a id="2554" class="Symbol">(</a> <a id="2556" href="univalent-combinatorics.dependent-pair-types.html#2168" class="Function">Σ-Finite-Type</a> <a id="2570" href="graph-theory.complete-bipartite-graphs.html#1603" class="Bound">X</a>
        <a id="2580" class="Symbol">(</a> <a id="2582" class="Symbol">λ</a> <a id="2584" href="graph-theory.complete-bipartite-graphs.html#2584" class="Bound">x</a> <a id="2586" class="Symbol">→</a>
          <a id="2598" href="univalent-combinatorics.fibers-of-maps.html#3291" class="Function">fiber-Finite-Type</a>
            <a id="2628" class="Symbol">(</a> <a id="2630" href="univalent-combinatorics.2-element-types.html#3447" class="Function">finite-type-2-Element-Type</a> <a id="2657" class="Symbol">(</a><a id="2658" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2662" href="graph-theory.complete-bipartite-graphs.html#2520" class="Bound">p</a><a id="2663" class="Symbol">))</a>
            <a id="2678" class="Symbol">(</a> <a id="2680" href="univalent-combinatorics.coproduct-types.html#9191" class="Function">coproduct-Finite-Type</a> <a id="2702" href="graph-theory.complete-bipartite-graphs.html#1603" class="Bound">X</a> <a id="2704" href="graph-theory.complete-bipartite-graphs.html#1624" class="Bound">Y</a><a id="2705" class="Symbol">)</a>
            <a id="2719" class="Symbol">(</a> <a id="2721" href="foundation.unordered-pairs.html#3321" class="Function">element-unordered-pair</a> <a id="2744" href="graph-theory.complete-bipartite-graphs.html#2520" class="Bound">p</a><a id="2745" class="Symbol">)</a>
            <a id="2759" class="Symbol">(</a> <a id="2761" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="2765" href="graph-theory.complete-bipartite-graphs.html#2584" class="Bound">x</a><a id="2766" class="Symbol">)))</a>
      <a id="2776" class="Symbol">(</a> <a id="2778" href="univalent-combinatorics.dependent-pair-types.html#2168" class="Function">Σ-Finite-Type</a> <a id="2792" href="graph-theory.complete-bipartite-graphs.html#1624" class="Bound">Y</a>
        <a id="2802" class="Symbol">(</a> <a id="2804" class="Symbol">λ</a> <a id="2806" href="graph-theory.complete-bipartite-graphs.html#2806" class="Bound">y</a> <a id="2808" class="Symbol">→</a>
          <a id="2820" href="univalent-combinatorics.fibers-of-maps.html#3291" class="Function">fiber-Finite-Type</a>
            <a id="2850" class="Symbol">(</a> <a id="2852" href="univalent-combinatorics.2-element-types.html#3447" class="Function">finite-type-2-Element-Type</a> <a id="2879" class="Symbol">(</a><a id="2880" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2884" href="graph-theory.complete-bipartite-graphs.html#2520" class="Bound">p</a><a id="2885" class="Symbol">))</a>
            <a id="2900" class="Symbol">(</a> <a id="2902" href="univalent-combinatorics.coproduct-types.html#9191" class="Function">coproduct-Finite-Type</a> <a id="2924" href="graph-theory.complete-bipartite-graphs.html#1603" class="Bound">X</a> <a id="2926" href="graph-theory.complete-bipartite-graphs.html#1624" class="Bound">Y</a><a id="2927" class="Symbol">)</a>
            <a id="2941" class="Symbol">(</a> <a id="2943" href="foundation.unordered-pairs.html#3321" class="Function">element-unordered-pair</a> <a id="2966" href="graph-theory.complete-bipartite-graphs.html#2520" class="Bound">p</a><a id="2967" class="Symbol">)</a>
            <a id="2981" class="Symbol">(</a> <a id="2983" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="2987" href="graph-theory.complete-bipartite-graphs.html#2806" class="Bound">y</a><a id="2988" class="Symbol">)))</a>

  <a id="2995" href="graph-theory.complete-bipartite-graphs.html#2995" class="Function">edge-complete-bipartite-Undirected-Graph</a> <a id="3036" class="Symbol">:</a>
    <a id="3042" href="graph-theory.complete-bipartite-graphs.html#2055" class="Function">unordered-pair-vertices-complete-bipartite-Finite-Undirected-Graph</a> <a id="3109" class="Symbol">→</a>
    <a id="3115" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3118" class="Symbol">(</a><a id="3119" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a> <a id="3122" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3124" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a><a id="3126" class="Symbol">)</a>
  <a id="3130" href="graph-theory.complete-bipartite-graphs.html#2995" class="Function">edge-complete-bipartite-Undirected-Graph</a> <a id="3171" href="graph-theory.complete-bipartite-graphs.html#3171" class="Bound">p</a> <a id="3173" class="Symbol">=</a>
    <a id="3179" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a>
      <a id="3202" class="Symbol">(</a> <a id="3204" href="graph-theory.complete-bipartite-graphs.html#2297" class="Function">edge-finite-type-complete-bipartite-Finite-Undirected-Graph</a> <a id="3264" href="graph-theory.complete-bipartite-graphs.html#3171" class="Bound">p</a><a id="3265" class="Symbol">)</a>

  <a id="3270" href="graph-theory.complete-bipartite-graphs.html#3270" class="Function">complete-bipartite-Finite-Undirected-Graph</a> <a id="3313" class="Symbol">:</a>
    <a id="3319" href="graph-theory.finite-graphs.html#990" class="Function">Finite-Undirected-Graph</a> <a id="3343" class="Symbol">(</a><a id="3344" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a> <a id="3347" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3349" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a><a id="3351" class="Symbol">)</a> <a id="3353" class="Symbol">(</a><a id="3354" href="graph-theory.complete-bipartite-graphs.html#1587" class="Bound">l1</a> <a id="3357" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3359" href="graph-theory.complete-bipartite-graphs.html#1590" class="Bound">l2</a><a id="3361" class="Symbol">)</a>
  <a id="3365" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3369" href="graph-theory.complete-bipartite-graphs.html#3270" class="Function">complete-bipartite-Finite-Undirected-Graph</a> <a id="3412" class="Symbol">=</a>
    <a id="3418" href="graph-theory.complete-bipartite-graphs.html#1655" class="Function">vertex-finite-type-complete-bipartite-Finite-Undirected-Graph</a>
  <a id="3482" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3486" href="graph-theory.complete-bipartite-graphs.html#3270" class="Function">complete-bipartite-Finite-Undirected-Graph</a> <a id="3529" class="Symbol">=</a>
    <a id="3535" href="graph-theory.complete-bipartite-graphs.html#2297" class="Function">edge-finite-type-complete-bipartite-Finite-Undirected-Graph</a>
</pre>
## External links

- [Complete bipartite graph](https://d3gt.com/unit.html?complete-bipartite) at
  D3 Graph Theory
- [Bipartite graphs](https://ncatlab.org/nlab/show/bipartite+graph) at $n$Lab
- [Complete bipartite graph](https://www.wikidata.org/entity/Q913598) at
  Wikidata
- [Complete bipartite graph](https://en.wikipedia.org/wiki/Complete_bipartite_graph)
  at Wikipedia
- [Complete bipartite graphs](https://mathworld.wolfram.com/CompleteBipartiteGraph.html)
  at Wolfram MathWorld
