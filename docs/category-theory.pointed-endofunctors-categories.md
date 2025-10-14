# Pointed endofunctors on categories

<pre class="Agda"><a id="47" class="Keyword">module</a> <a id="54" href="category-theory.pointed-endofunctors-categories.html" class="Module">category-theory.pointed-endofunctors-categories</a> <a id="102" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="category-theory.functors-categories.html" class="Module">category-theory.functors-categories</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="category-theory.natural-transformations-functors-categories.html" class="Module">category-theory.natural-transformations-functors-categories</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="category-theory.pointed-endofunctors-precategories.html" class="Module">category-theory.pointed-endofunctors-precategories</a>

<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="425" class="Keyword">open</a> <a id="430" class="Keyword">import</a> <a id="437" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="463" class="Keyword">open</a> <a id="468" class="Keyword">import</a> <a id="475" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An [endofunctor](category-theory.functors-categories.md) `F : C → C` on a
[category](category-theory.categories.md) `C` is said to be
{{#concept "pointed" Disambiguation="endofunctor on a category" Agda=pointed-endofunctor-Category}}
if it comes equipped with a
[natural transformation](category-theory.natural-transformations-functors-categories.md)
`id ⇒ F` from the identity [functor](category-theory.functors-categories.md) to
`F`.

More explicitly, a
{{#concept "pointing" Disambiguation="endofunctor on a category" Agda=pointing-endofunctor-Category}}
of an endofunctor `F : C → C` consists of a family of morphisms `η X : X → F X`
such that for each morphism `f : X → Y` in `C` the diagram

```text
       η X
    X -----> F X
    |         |
  f |         | F f
    ∨         ∨
    Y -----> F Y
       η Y
```

[commutes](category-theory.commuting-squares-of-morphisms-in-precategories.md).

## Definitions

### The structure of a pointing on an endofunctor on a category

<pre class="Agda"><a id="1517" class="Keyword">module</a> <a id="1524" href="category-theory.pointed-endofunctors-categories.html#1524" class="Module">_</a>
  <a id="1528" class="Symbol">{</a><a id="1529" href="category-theory.pointed-endofunctors-categories.html#1529" class="Bound">l1</a> <a id="1532" href="category-theory.pointed-endofunctors-categories.html#1532" class="Bound">l2</a> <a id="1535" class="Symbol">:</a> <a id="1537" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1542" class="Symbol">}</a> <a id="1544" class="Symbol">(</a><a id="1545" href="category-theory.pointed-endofunctors-categories.html#1545" class="Bound">C</a> <a id="1547" class="Symbol">:</a> <a id="1549" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1558" href="category-theory.pointed-endofunctors-categories.html#1529" class="Bound">l1</a> <a id="1561" href="category-theory.pointed-endofunctors-categories.html#1532" class="Bound">l2</a><a id="1563" class="Symbol">)</a> <a id="1565" class="Symbol">(</a><a id="1566" href="category-theory.pointed-endofunctors-categories.html#1566" class="Bound">T</a> <a id="1568" class="Symbol">:</a> <a id="1570" href="category-theory.functors-categories.html#2227" class="Function">functor-Category</a> <a id="1587" href="category-theory.pointed-endofunctors-categories.html#1545" class="Bound">C</a> <a id="1589" href="category-theory.pointed-endofunctors-categories.html#1545" class="Bound">C</a><a id="1590" class="Symbol">)</a>
  <a id="1594" class="Keyword">where</a>

  <a id="1603" href="category-theory.pointed-endofunctors-categories.html#1603" class="Function">pointing-endofunctor-Category</a> <a id="1633" class="Symbol">:</a> <a id="1635" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1638" class="Symbol">(</a><a id="1639" href="category-theory.pointed-endofunctors-categories.html#1529" class="Bound">l1</a> <a id="1642" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1644" href="category-theory.pointed-endofunctors-categories.html#1532" class="Bound">l2</a><a id="1646" class="Symbol">)</a>
  <a id="1650" href="category-theory.pointed-endofunctors-categories.html#1603" class="Function">pointing-endofunctor-Category</a> <a id="1680" class="Symbol">=</a>
    <a id="1686" href="category-theory.pointed-endofunctors-precategories.html#1588" class="Function">pointing-endofunctor-Precategory</a> <a id="1719" class="Symbol">(</a><a id="1720" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1741" href="category-theory.pointed-endofunctors-categories.html#1545" class="Bound">C</a><a id="1742" class="Symbol">)</a> <a id="1744" href="category-theory.pointed-endofunctors-categories.html#1566" class="Bound">T</a>
</pre>
### Pointed endofunctors on a category

<pre class="Agda"><a id="1799" class="Keyword">module</a> <a id="1806" href="category-theory.pointed-endofunctors-categories.html#1806" class="Module">_</a>
  <a id="1810" class="Symbol">{</a><a id="1811" href="category-theory.pointed-endofunctors-categories.html#1811" class="Bound">l1</a> <a id="1814" href="category-theory.pointed-endofunctors-categories.html#1814" class="Bound">l2</a> <a id="1817" class="Symbol">:</a> <a id="1819" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1824" class="Symbol">}</a> <a id="1826" class="Symbol">(</a><a id="1827" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="1829" class="Symbol">:</a> <a id="1831" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1840" href="category-theory.pointed-endofunctors-categories.html#1811" class="Bound">l1</a> <a id="1843" href="category-theory.pointed-endofunctors-categories.html#1814" class="Bound">l2</a><a id="1845" class="Symbol">)</a>
  <a id="1849" class="Keyword">where</a>

  <a id="1858" href="category-theory.pointed-endofunctors-categories.html#1858" class="Function">pointed-endofunctor-Category</a> <a id="1887" class="Symbol">:</a> <a id="1889" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1892" class="Symbol">(</a><a id="1893" href="category-theory.pointed-endofunctors-categories.html#1811" class="Bound">l1</a> <a id="1896" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1898" href="category-theory.pointed-endofunctors-categories.html#1814" class="Bound">l2</a><a id="1900" class="Symbol">)</a>
  <a id="1904" href="category-theory.pointed-endofunctors-categories.html#1858" class="Function">pointed-endofunctor-Category</a> <a id="1933" class="Symbol">=</a>
    <a id="1939" href="category-theory.pointed-endofunctors-precategories.html#1863" class="Function">pointed-endofunctor-Precategory</a> <a id="1971" class="Symbol">(</a><a id="1972" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1993" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="1994" class="Symbol">)</a>

  <a id="1999" class="Keyword">module</a> <a id="2006" href="category-theory.pointed-endofunctors-categories.html#2006" class="Module">_</a>
    <a id="2012" class="Symbol">(</a><a id="2013" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a> <a id="2015" class="Symbol">:</a> <a id="2017" href="category-theory.pointed-endofunctors-categories.html#1858" class="Function">pointed-endofunctor-Category</a><a id="2045" class="Symbol">)</a>
    <a id="2051" class="Keyword">where</a>

    <a id="2062" href="category-theory.pointed-endofunctors-categories.html#2062" class="Function">functor-pointed-endofunctor-Category</a> <a id="2099" class="Symbol">:</a>
      <a id="2107" href="category-theory.functors-categories.html#2227" class="Function">functor-Category</a> <a id="2124" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="2126" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a>
    <a id="2132" href="category-theory.pointed-endofunctors-categories.html#2062" class="Function">functor-pointed-endofunctor-Category</a> <a id="2169" class="Symbol">=</a>
      <a id="2177" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a> <a id="2217" class="Symbol">(</a><a id="2218" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2239" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="2240" class="Symbol">)</a> <a id="2242" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a>

    <a id="2249" href="category-theory.pointed-endofunctors-categories.html#2249" class="Function">obj-pointed-endofunctor-Category</a> <a id="2282" class="Symbol">:</a> <a id="2284" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="2297" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="2299" class="Symbol">→</a> <a id="2301" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="2314" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a>
    <a id="2320" href="category-theory.pointed-endofunctors-categories.html#2249" class="Function">obj-pointed-endofunctor-Category</a> <a id="2353" class="Symbol">=</a>
      <a id="2361" href="category-theory.pointed-endofunctors-precategories.html#2219" class="Function">obj-pointed-endofunctor-Precategory</a> <a id="2397" class="Symbol">(</a><a id="2398" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2419" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="2420" class="Symbol">)</a> <a id="2422" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a>

    <a id="2429" href="category-theory.pointed-endofunctors-categories.html#2429" class="Function">hom-pointed-endofunctor-Category</a> <a id="2462" class="Symbol">:</a>
      <a id="2470" class="Symbol">{</a><a id="2471" href="category-theory.pointed-endofunctors-categories.html#2471" class="Bound">X</a> <a id="2473" href="category-theory.pointed-endofunctors-categories.html#2473" class="Bound">Y</a> <a id="2475" class="Symbol">:</a> <a id="2477" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="2490" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="2491" class="Symbol">}</a> <a id="2493" class="Symbol">→</a>
      <a id="2501" href="category-theory.categories.html#2741" class="Function">hom-Category</a> <a id="2514" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="2516" href="category-theory.pointed-endofunctors-categories.html#2471" class="Bound">X</a> <a id="2518" href="category-theory.pointed-endofunctors-categories.html#2473" class="Bound">Y</a> <a id="2520" class="Symbol">→</a>
      <a id="2528" href="category-theory.categories.html#2741" class="Function">hom-Category</a> <a id="2541" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a>
        <a id="2551" class="Symbol">(</a> <a id="2553" href="category-theory.pointed-endofunctors-categories.html#2249" class="Function">obj-pointed-endofunctor-Category</a> <a id="2586" href="category-theory.pointed-endofunctors-categories.html#2471" class="Bound">X</a><a id="2587" class="Symbol">)</a>
        <a id="2597" class="Symbol">(</a> <a id="2599" href="category-theory.pointed-endofunctors-categories.html#2249" class="Function">obj-pointed-endofunctor-Category</a> <a id="2632" href="category-theory.pointed-endofunctors-categories.html#2473" class="Bound">Y</a><a id="2633" class="Symbol">)</a>
    <a id="2639" href="category-theory.pointed-endofunctors-categories.html#2429" class="Function">hom-pointed-endofunctor-Category</a> <a id="2672" class="Symbol">=</a>
      <a id="2680" href="category-theory.pointed-endofunctors-precategories.html#2416" class="Function">hom-pointed-endofunctor-Precategory</a> <a id="2716" class="Symbol">(</a><a id="2717" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2738" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="2739" class="Symbol">)</a> <a id="2741" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a>

    <a id="2748" href="category-theory.pointed-endofunctors-categories.html#2748" class="Function">preserves-id-pointed-endofunctor-Category</a> <a id="2790" class="Symbol">:</a>
      <a id="2798" class="Symbol">(</a><a id="2799" href="category-theory.pointed-endofunctors-categories.html#2799" class="Bound">X</a> <a id="2801" class="Symbol">:</a> <a id="2803" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="2816" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="2817" class="Symbol">)</a> <a id="2819" class="Symbol">→</a>
      <a id="2827" href="category-theory.pointed-endofunctors-categories.html#2429" class="Function">hom-pointed-endofunctor-Category</a> <a id="2860" class="Symbol">(</a><a id="2861" href="category-theory.categories.html#4126" class="Function">id-hom-Category</a> <a id="2877" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="2879" class="Symbol">{</a><a id="2880" href="category-theory.pointed-endofunctors-categories.html#2799" class="Bound">X</a><a id="2881" class="Symbol">})</a> <a id="2884" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="2892" href="category-theory.categories.html#4126" class="Function">id-hom-Category</a> <a id="2908" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a>
    <a id="2914" href="category-theory.pointed-endofunctors-categories.html#2748" class="Function">preserves-id-pointed-endofunctor-Category</a> <a id="2956" class="Symbol">=</a>
      <a id="2964" href="category-theory.pointed-endofunctors-precategories.html#2761" class="Function">preserves-id-pointed-endofunctor-Precategory</a> <a id="3009" class="Symbol">(</a><a id="3010" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3031" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="3032" class="Symbol">)</a> <a id="3034" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a>

    <a id="3041" href="category-theory.pointed-endofunctors-categories.html#3041" class="Function">preserves-comp-pointed-endofunctor-Category</a> <a id="3085" class="Symbol">:</a>
      <a id="3093" class="Symbol">{</a><a id="3094" href="category-theory.pointed-endofunctors-categories.html#3094" class="Bound">X</a> <a id="3096" href="category-theory.pointed-endofunctors-categories.html#3096" class="Bound">Y</a> <a id="3098" href="category-theory.pointed-endofunctors-categories.html#3098" class="Bound">Z</a> <a id="3100" class="Symbol">:</a> <a id="3102" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="3115" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="3116" class="Symbol">}</a>
      <a id="3124" class="Symbol">(</a><a id="3125" href="category-theory.pointed-endofunctors-categories.html#3125" class="Bound">g</a> <a id="3127" class="Symbol">:</a> <a id="3129" href="category-theory.categories.html#2741" class="Function">hom-Category</a> <a id="3142" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="3144" href="category-theory.pointed-endofunctors-categories.html#3096" class="Bound">Y</a> <a id="3146" href="category-theory.pointed-endofunctors-categories.html#3098" class="Bound">Z</a><a id="3147" class="Symbol">)</a> <a id="3149" class="Symbol">(</a><a id="3150" href="category-theory.pointed-endofunctors-categories.html#3150" class="Bound">f</a> <a id="3152" class="Symbol">:</a> <a id="3154" href="category-theory.categories.html#2741" class="Function">hom-Category</a> <a id="3167" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="3169" href="category-theory.pointed-endofunctors-categories.html#3094" class="Bound">X</a> <a id="3171" href="category-theory.pointed-endofunctors-categories.html#3096" class="Bound">Y</a><a id="3172" class="Symbol">)</a> <a id="3174" class="Symbol">→</a>
      <a id="3182" href="category-theory.pointed-endofunctors-categories.html#2429" class="Function">hom-pointed-endofunctor-Category</a>
        <a id="3223" class="Symbol">(</a> <a id="3225" href="category-theory.categories.html#2995" class="Function">comp-hom-Category</a> <a id="3243" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="3245" href="category-theory.pointed-endofunctors-categories.html#3125" class="Bound">g</a> <a id="3247" href="category-theory.pointed-endofunctors-categories.html#3150" class="Bound">f</a><a id="3248" class="Symbol">)</a> <a id="3250" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="3258" href="category-theory.categories.html#2995" class="Function">comp-hom-Category</a> <a id="3276" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a>
        <a id="3286" class="Symbol">(</a> <a id="3288" href="category-theory.pointed-endofunctors-categories.html#2429" class="Function">hom-pointed-endofunctor-Category</a> <a id="3321" href="category-theory.pointed-endofunctors-categories.html#3125" class="Bound">g</a><a id="3322" class="Symbol">)</a>
        <a id="3332" class="Symbol">(</a> <a id="3334" href="category-theory.pointed-endofunctors-categories.html#2429" class="Function">hom-pointed-endofunctor-Category</a> <a id="3367" href="category-theory.pointed-endofunctors-categories.html#3150" class="Bound">f</a><a id="3368" class="Symbol">)</a>
    <a id="3374" href="category-theory.pointed-endofunctors-categories.html#3041" class="Function">preserves-comp-pointed-endofunctor-Category</a> <a id="3418" class="Symbol">=</a>
      <a id="3426" href="category-theory.pointed-endofunctors-precategories.html#3088" class="Function">preserves-comp-pointed-endofunctor-Precategory</a> <a id="3473" class="Symbol">(</a><a id="3474" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3495" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="3496" class="Symbol">)</a> <a id="3498" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a>

    <a id="3505" href="category-theory.pointed-endofunctors-categories.html#3505" class="Function">pointing-pointed-endofunctor-Category</a> <a id="3543" class="Symbol">:</a>
      <a id="3551" href="category-theory.natural-transformations-functors-categories.html#1571" class="Function">natural-transformation-Category</a> <a id="3583" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="3585" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a>
        <a id="3595" class="Symbol">(</a> <a id="3597" href="category-theory.functors-categories.html#4152" class="Function">id-functor-Category</a> <a id="3617" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="3618" class="Symbol">)</a>
        <a id="3628" class="Symbol">(</a> <a id="3630" href="category-theory.pointed-endofunctors-categories.html#2062" class="Function">functor-pointed-endofunctor-Category</a><a id="3666" class="Symbol">)</a>
    <a id="3672" href="category-theory.pointed-endofunctors-categories.html#3505" class="Function">pointing-pointed-endofunctor-Category</a> <a id="3710" class="Symbol">=</a>
      <a id="3718" href="category-theory.pointed-endofunctors-precategories.html#3598" class="Function">pointing-pointed-endofunctor-Precategory</a> <a id="3759" class="Symbol">(</a><a id="3760" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3781" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="3782" class="Symbol">)</a> <a id="3784" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a>

    <a id="3791" href="category-theory.pointed-endofunctors-categories.html#3791" class="Function">hom-family-pointing-pointed-endofunctor-Category</a> <a id="3840" class="Symbol">:</a>
      <a id="3848" href="category-theory.natural-transformations-functors-categories.html#1113" class="Function">hom-family-functor-Category</a> <a id="3876" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="3878" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a>
        <a id="3888" class="Symbol">(</a> <a id="3890" href="category-theory.functors-categories.html#4152" class="Function">id-functor-Category</a> <a id="3910" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="3911" class="Symbol">)</a>
        <a id="3921" class="Symbol">(</a> <a id="3923" href="category-theory.pointed-endofunctors-categories.html#2062" class="Function">functor-pointed-endofunctor-Category</a><a id="3959" class="Symbol">)</a>
    <a id="3965" href="category-theory.pointed-endofunctors-categories.html#3791" class="Function">hom-family-pointing-pointed-endofunctor-Category</a> <a id="4014" class="Symbol">=</a>
      <a id="4022" href="category-theory.pointed-endofunctors-precategories.html#3831" class="Function">hom-family-pointing-pointed-endofunctor-Precategory</a>
        <a id="4082" class="Symbol">(</a> <a id="4084" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="4105" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="4106" class="Symbol">)</a>
        <a id="4116" class="Symbol">(</a> <a id="4118" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a><a id="4119" class="Symbol">)</a>

    <a id="4126" href="category-theory.pointed-endofunctors-categories.html#4126" class="Function">naturality-pointing-pointed-endofunctor-Category</a> <a id="4175" class="Symbol">:</a>
      <a id="4183" href="category-theory.natural-transformations-functors-categories.html#1312" class="Function">is-natural-transformation-Category</a> <a id="4218" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a> <a id="4220" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a>
        <a id="4230" class="Symbol">(</a> <a id="4232" href="category-theory.functors-categories.html#4152" class="Function">id-functor-Category</a> <a id="4252" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="4253" class="Symbol">)</a>
        <a id="4263" class="Symbol">(</a> <a id="4265" href="category-theory.pointed-endofunctors-categories.html#2062" class="Function">functor-pointed-endofunctor-Category</a><a id="4301" class="Symbol">)</a>
        <a id="4311" class="Symbol">(</a> <a id="4313" href="category-theory.pointed-endofunctors-categories.html#3791" class="Function">hom-family-pointing-pointed-endofunctor-Category</a><a id="4361" class="Symbol">)</a>
    <a id="4367" href="category-theory.pointed-endofunctors-categories.html#4126" class="Function">naturality-pointing-pointed-endofunctor-Category</a> <a id="4416" class="Symbol">=</a>
      <a id="4424" href="category-theory.pointed-endofunctors-precategories.html#4271" class="Function">naturality-pointing-pointed-endofunctor-Precategory</a>
        <a id="4484" class="Symbol">(</a> <a id="4486" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="4507" href="category-theory.pointed-endofunctors-categories.html#1827" class="Bound">C</a><a id="4508" class="Symbol">)</a> <a id="4510" href="category-theory.pointed-endofunctors-categories.html#2013" class="Bound">F</a>
</pre>