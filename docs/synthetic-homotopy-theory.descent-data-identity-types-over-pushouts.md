# Descent data for type families of identity types over pushouts

<pre class="Agda"><a id="75" class="Symbol">{-#</a> <a id="79" class="Keyword">OPTIONS</a> <a id="87" class="Pragma">--lossy-unification</a> <a id="107" class="Symbol">#-}</a>

<a id="112" class="Keyword">module</a> <a id="119" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html" class="Module">synthetic-homotopy-theory.descent-data-identity-types-over-pushouts</a> <a id="187" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="398" class="Keyword">open</a> <a id="403" class="Keyword">import</a> <a id="410" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="453" class="Keyword">open</a> <a id="458" class="Keyword">import</a> <a id="465" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="synthetic-homotopy-theory.cocones-under-spans.html" class="Module">synthetic-homotopy-theory.cocones-under-spans</a>
<a id="551" class="Keyword">open</a> <a id="556" class="Keyword">import</a> <a id="563" href="synthetic-homotopy-theory.descent-data-pushouts.html" class="Module">synthetic-homotopy-theory.descent-data-pushouts</a>
<a id="611" class="Keyword">open</a> <a id="616" class="Keyword">import</a> <a id="623" href="synthetic-homotopy-theory.equivalences-descent-data-pushouts.html" class="Module">synthetic-homotopy-theory.equivalences-descent-data-pushouts</a>
<a id="684" class="Keyword">open</a> <a id="689" class="Keyword">import</a> <a id="696" href="synthetic-homotopy-theory.families-descent-data-pushouts.html" class="Module">synthetic-homotopy-theory.families-descent-data-pushouts</a>
</pre>
</details>

## Idea

Given a [cocone](synthetic-homotopy-theory.cocones-under-spans.md) under a
[span diagram](foundation.span-diagrams.md)

```text
        g
    S -----> B
    |        |
  f |        | j
    ∨        ∨
    A -----> X
        i
```

and a point `x₀ : X`, the type family of
[identity types](foundation-core.identity-types.md) based at `x₀`,
`x ↦ (x₀ = x)`, is
[characterized](synthetic-homotopy-theory.families-descent-data-pushouts.md) by
the [descent data](synthetic-homotopy-theory.descent-data-pushouts.md)
`(IA, IB, IS)`, where `IA` and `IB` are families of identity types

```text
  IA a := (x₀ = ia)
  IB b := (x₀ = jb),
```

and the gluing data `IS s : (x₀ = ifs) ≃ (x₀ = jgs)` is given by concatenation
with the coherence of the cocone `H s : ifs = jgs`.

## Definitions

<pre class="Agda"><a id="1565" class="Keyword">module</a> <a id="1572" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1572" class="Module">_</a>
  <a id="1576" class="Symbol">{</a><a id="1577" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1577" class="Bound">l1</a> <a id="1580" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1580" class="Bound">l2</a> <a id="1583" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1583" class="Bound">l3</a> <a id="1586" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1586" class="Bound">l4</a> <a id="1589" class="Symbol">:</a> <a id="1591" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1596" class="Symbol">}</a> <a id="1598" class="Symbol">{</a><a id="1599" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1599" class="Bound">𝒮</a> <a id="1601" class="Symbol">:</a> <a id="1603" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1616" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1577" class="Bound">l1</a> <a id="1619" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1580" class="Bound">l2</a> <a id="1622" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1583" class="Bound">l3</a><a id="1624" class="Symbol">}</a>
  <a id="1628" class="Symbol">{</a><a id="1629" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1629" class="Bound">X</a> <a id="1631" class="Symbol">:</a> <a id="1633" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1636" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1586" class="Bound">l4</a><a id="1638" class="Symbol">}</a> <a id="1640" class="Symbol">(</a><a id="1641" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1641" class="Bound">c</a> <a id="1643" class="Symbol">:</a> <a id="1645" href="synthetic-homotopy-theory.cocones-under-spans.html#1725" class="Function">cocone-span-diagram</a> <a id="1665" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1599" class="Bound">𝒮</a> <a id="1667" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1629" class="Bound">X</a><a id="1668" class="Symbol">)</a>
  <a id="1672" class="Symbol">(</a><a id="1673" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1673" class="Bound">x₀</a> <a id="1676" class="Symbol">:</a> <a id="1678" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1629" class="Bound">X</a><a id="1679" class="Symbol">)</a>
  <a id="1683" class="Keyword">where</a>

  <a id="1692" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1692" class="Function">family-cocone-identity-type-pushout</a> <a id="1728" class="Symbol">:</a> <a id="1730" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1629" class="Bound">X</a> <a id="1732" class="Symbol">→</a> <a id="1734" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1737" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1586" class="Bound">l4</a>
  <a id="1742" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1692" class="Function">family-cocone-identity-type-pushout</a> <a id="1778" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1778" class="Bound">x</a> <a id="1780" class="Symbol">=</a> <a id="1782" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1673" class="Bound">x₀</a> <a id="1785" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1787" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1778" class="Bound">x</a>

  <a id="1792" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1792" class="Function">descent-data-identity-type-pushout</a> <a id="1827" class="Symbol">:</a> <a id="1829" href="synthetic-homotopy-theory.descent-data-pushouts.html#2463" class="Function">descent-data-pushout</a> <a id="1850" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1599" class="Bound">𝒮</a> <a id="1852" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1586" class="Bound">l4</a> <a id="1855" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1586" class="Bound">l4</a>
  <a id="1860" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1864" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1792" class="Function">descent-data-identity-type-pushout</a> <a id="1899" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1899" class="Bound">a</a> <a id="1901" class="Symbol">=</a>
    <a id="1907" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1673" class="Bound">x₀</a> <a id="1910" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1912" href="synthetic-homotopy-theory.cocones-under-spans.html#2060" class="Function">horizontal-map-cocone</a> <a id="1934" class="Symbol">_</a> <a id="1936" class="Symbol">_</a> <a id="1938" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1641" class="Bound">c</a> <a id="1940" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1899" class="Bound">a</a>
  <a id="1944" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1948" class="Symbol">(</a><a id="1949" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1953" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1792" class="Function">descent-data-identity-type-pushout</a><a id="1987" class="Symbol">)</a> <a id="1989" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1989" class="Bound">b</a> <a id="1991" class="Symbol">=</a>
    <a id="1997" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1673" class="Bound">x₀</a> <a id="2000" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2002" href="synthetic-homotopy-theory.cocones-under-spans.html#2125" class="Function">vertical-map-cocone</a> <a id="2022" class="Symbol">_</a> <a id="2024" class="Symbol">_</a> <a id="2026" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1641" class="Bound">c</a> <a id="2028" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1989" class="Bound">b</a>
  <a id="2032" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2036" class="Symbol">(</a><a id="2037" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2041" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1792" class="Function">descent-data-identity-type-pushout</a><a id="2075" class="Symbol">)</a> <a id="2077" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2077" class="Bound">s</a> <a id="2079" class="Symbol">=</a>
    <a id="2085" href="foundation.identity-types.html#4402" class="Function">equiv-concat&#39;</a> <a id="2099" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1673" class="Bound">x₀</a> <a id="2102" class="Symbol">(</a><a id="2103" href="synthetic-homotopy-theory.cocones-under-spans.html#2192" class="Function">coherence-square-cocone</a> <a id="2127" class="Symbol">_</a> <a id="2129" class="Symbol">_</a> <a id="2131" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1641" class="Bound">c</a> <a id="2133" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2077" class="Bound">s</a><a id="2134" class="Symbol">)</a>

  <a id="2139" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2139" class="Function">equiv-descent-data-identity-type-pushout</a> <a id="2180" class="Symbol">:</a>
    <a id="2186" href="synthetic-homotopy-theory.equivalences-descent-data-pushouts.html#2672" class="Function">equiv-descent-data-pushout</a>
      <a id="2219" class="Symbol">(</a> <a id="2221" href="synthetic-homotopy-theory.descent-data-pushouts.html#4993" class="Function">descent-data-family-cocone-span-diagram</a> <a id="2261" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1641" class="Bound">c</a>
        <a id="2271" class="Symbol">(</a> <a id="2273" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1692" class="Function">family-cocone-identity-type-pushout</a><a id="2308" class="Symbol">))</a>
      <a id="2317" class="Symbol">(</a> <a id="2319" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1792" class="Function">descent-data-identity-type-pushout</a><a id="2353" class="Symbol">)</a>
  <a id="2357" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2361" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2139" class="Function">equiv-descent-data-identity-type-pushout</a> <a id="2402" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2402" class="Bound">a</a> <a id="2404" class="Symbol">=</a> <a id="2406" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
  <a id="2417" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2421" class="Symbol">(</a><a id="2422" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2426" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2139" class="Function">equiv-descent-data-identity-type-pushout</a><a id="2466" class="Symbol">)</a> <a id="2468" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2468" class="Bound">b</a> <a id="2470" class="Symbol">=</a> <a id="2472" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
  <a id="2483" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2487" class="Symbol">(</a><a id="2488" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2492" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2139" class="Function">equiv-descent-data-identity-type-pushout</a><a id="2532" class="Symbol">)</a> <a id="2534" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2534" class="Bound">s</a> <a id="2536" class="Symbol">=</a>
    <a id="2542" href="foundation-core.transport-along-identifications.html#3357" class="Function">tr-Id-right</a> <a id="2554" class="Symbol">(</a><a id="2555" href="synthetic-homotopy-theory.cocones-under-spans.html#2192" class="Function">coherence-square-cocone</a> <a id="2579" class="Symbol">_</a> <a id="2581" class="Symbol">_</a> <a id="2583" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1641" class="Bound">c</a> <a id="2585" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2534" class="Bound">s</a><a id="2586" class="Symbol">)</a>

  <a id="2591" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2591" class="Function">family-with-descent-data-identity-type-pushout</a> <a id="2638" class="Symbol">:</a>
    <a id="2644" href="synthetic-homotopy-theory.families-descent-data-pushouts.html#1770" class="Function">family-with-descent-data-pushout</a> <a id="2677" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1641" class="Bound">c</a> <a id="2679" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1586" class="Bound">l4</a> <a id="2682" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1586" class="Bound">l4</a> <a id="2685" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1586" class="Bound">l4</a>
  <a id="2690" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2694" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2591" class="Function">family-with-descent-data-identity-type-pushout</a> <a id="2741" class="Symbol">=</a>
    <a id="2747" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1692" class="Function">family-cocone-identity-type-pushout</a>
  <a id="2785" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2789" class="Symbol">(</a><a id="2790" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2794" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2591" class="Function">family-with-descent-data-identity-type-pushout</a><a id="2840" class="Symbol">)</a> <a id="2842" class="Symbol">=</a>
    <a id="2848" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#1792" class="Function">descent-data-identity-type-pushout</a>
  <a id="2885" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2889" class="Symbol">(</a><a id="2890" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2894" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2591" class="Function">family-with-descent-data-identity-type-pushout</a><a id="2940" class="Symbol">)</a> <a id="2942" class="Symbol">=</a>
    <a id="2948" href="synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.html#2139" class="Function">equiv-descent-data-identity-type-pushout</a>
</pre>