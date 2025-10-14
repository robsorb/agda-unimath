# Copointed endofunctors on precategories

<pre class="Agda"><a id="52" class="Keyword">module</a> <a id="59" href="category-theory.copointed-endofunctors-precategories.html" class="Module">category-theory.copointed-endofunctors-precategories</a> <a id="112" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="category-theory.natural-transformations-functors-precategories.html" class="Module">category-theory.natural-transformations-functors-precategories</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An [endofunctor](category-theory.functors-precategories.md) `F : C → C` on a
[precategory](category-theory.precategories.md) `C` is said to be
{{#concept "copointed" Disambiguation="endofunctor on a category" Agda=copointed-endofunctor-Precategory}}
if it comes equipped with a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
`F ⇒ id` from `F` to the identity
[functor](category-theory.functors-precategories.md).

More explicitly, a
{{#concept "copointing" Disambiguation="endofunctor on a precategory" Agda=copointing-endofunctor-Precategory}}
of an endofunctor `F : C → C` consists of a family of morphisms `ε X : F X → X`
such that for each morphism `f : X → Y` in `C` the diagram

```text
           ε X
      F X -----> X
       |         |
  F f  |         | f
       ∨         ∨
      F Y -----> Y
           ε Y
```

[commutes](category-theory.commuting-squares-of-morphisms-in-precategories.md).

## Definitions

### The structure of a copointing on an endofunctor on a precategory

<pre class="Agda"><a id="1529" class="Keyword">module</a> <a id="1536" href="category-theory.copointed-endofunctors-precategories.html#1536" class="Module">_</a>
  <a id="1540" class="Symbol">{</a><a id="1541" href="category-theory.copointed-endofunctors-precategories.html#1541" class="Bound">l1</a> <a id="1544" href="category-theory.copointed-endofunctors-precategories.html#1544" class="Bound">l2</a> <a id="1547" class="Symbol">:</a> <a id="1549" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1554" class="Symbol">}</a> <a id="1556" class="Symbol">(</a><a id="1557" href="category-theory.copointed-endofunctors-precategories.html#1557" class="Bound">C</a> <a id="1559" class="Symbol">:</a> <a id="1561" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1573" href="category-theory.copointed-endofunctors-precategories.html#1541" class="Bound">l1</a> <a id="1576" href="category-theory.copointed-endofunctors-precategories.html#1544" class="Bound">l2</a><a id="1578" class="Symbol">)</a> <a id="1580" class="Symbol">(</a><a id="1581" href="category-theory.copointed-endofunctors-precategories.html#1581" class="Bound">T</a> <a id="1583" class="Symbol">:</a> <a id="1585" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="1605" href="category-theory.copointed-endofunctors-precategories.html#1557" class="Bound">C</a> <a id="1607" href="category-theory.copointed-endofunctors-precategories.html#1557" class="Bound">C</a><a id="1608" class="Symbol">)</a>
  <a id="1612" class="Keyword">where</a>

  <a id="1621" href="category-theory.copointed-endofunctors-precategories.html#1621" class="Function">copointing-endofunctor-Precategory</a> <a id="1656" class="Symbol">:</a> <a id="1658" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1661" class="Symbol">(</a><a id="1662" href="category-theory.copointed-endofunctors-precategories.html#1541" class="Bound">l1</a> <a id="1665" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1667" href="category-theory.copointed-endofunctors-precategories.html#1544" class="Bound">l2</a><a id="1669" class="Symbol">)</a>
  <a id="1673" href="category-theory.copointed-endofunctors-precategories.html#1621" class="Function">copointing-endofunctor-Precategory</a> <a id="1708" class="Symbol">=</a>
    <a id="1714" href="category-theory.natural-transformations-functors-precategories.html#1811" class="Function">natural-transformation-Precategory</a> <a id="1749" href="category-theory.copointed-endofunctors-precategories.html#1557" class="Bound">C</a> <a id="1751" href="category-theory.copointed-endofunctors-precategories.html#1557" class="Bound">C</a> <a id="1753" href="category-theory.copointed-endofunctors-precategories.html#1581" class="Bound">T</a> <a id="1755" class="Symbol">(</a><a id="1756" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="1779" href="category-theory.copointed-endofunctors-precategories.html#1557" class="Bound">C</a><a id="1780" class="Symbol">)</a>
</pre>
### Copointed endofunctors on a precategory

<pre class="Agda"><a id="1840" class="Keyword">module</a> <a id="1847" href="category-theory.copointed-endofunctors-precategories.html#1847" class="Module">_</a>
  <a id="1851" class="Symbol">{</a><a id="1852" href="category-theory.copointed-endofunctors-precategories.html#1852" class="Bound">l1</a> <a id="1855" href="category-theory.copointed-endofunctors-precategories.html#1855" class="Bound">l2</a> <a id="1858" class="Symbol">:</a> <a id="1860" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1865" class="Symbol">}</a> <a id="1867" class="Symbol">(</a><a id="1868" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="1870" class="Symbol">:</a> <a id="1872" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1884" href="category-theory.copointed-endofunctors-precategories.html#1852" class="Bound">l1</a> <a id="1887" href="category-theory.copointed-endofunctors-precategories.html#1855" class="Bound">l2</a><a id="1889" class="Symbol">)</a>
  <a id="1893" class="Keyword">where</a>

  <a id="1902" href="category-theory.copointed-endofunctors-precategories.html#1902" class="Function">copointed-endofunctor-Precategory</a> <a id="1936" class="Symbol">:</a> <a id="1938" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1941" class="Symbol">(</a><a id="1942" href="category-theory.copointed-endofunctors-precategories.html#1852" class="Bound">l1</a> <a id="1945" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1947" href="category-theory.copointed-endofunctors-precategories.html#1855" class="Bound">l2</a><a id="1949" class="Symbol">)</a>
  <a id="1953" href="category-theory.copointed-endofunctors-precategories.html#1902" class="Function">copointed-endofunctor-Precategory</a> <a id="1987" class="Symbol">=</a>
    <a id="1993" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1995" class="Symbol">(</a><a id="1996" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="2016" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2018" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="2019" class="Symbol">)</a> <a id="2021" class="Symbol">(</a><a id="2022" href="category-theory.copointed-endofunctors-precategories.html#1621" class="Function">copointing-endofunctor-Precategory</a> <a id="2057" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="2058" class="Symbol">)</a>

  <a id="2063" class="Keyword">module</a> <a id="2070" href="category-theory.copointed-endofunctors-precategories.html#2070" class="Module">_</a>
    <a id="2076" class="Symbol">(</a><a id="2077" href="category-theory.copointed-endofunctors-precategories.html#2077" class="Bound">F</a> <a id="2079" class="Symbol">:</a> <a id="2081" href="category-theory.copointed-endofunctors-precategories.html#1902" class="Function">copointed-endofunctor-Precategory</a><a id="2114" class="Symbol">)</a>
    <a id="2120" class="Keyword">where</a>

    <a id="2131" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a> <a id="2173" class="Symbol">:</a>
      <a id="2181" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="2201" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2203" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
    <a id="2209" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a> <a id="2251" class="Symbol">=</a>
      <a id="2259" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2263" href="category-theory.copointed-endofunctors-precategories.html#2077" class="Bound">F</a>

    <a id="2270" href="category-theory.copointed-endofunctors-precategories.html#2270" class="Function">obj-copointed-endofunctor-Precategory</a> <a id="2308" class="Symbol">:</a>
      <a id="2316" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2332" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2334" class="Symbol">→</a> <a id="2336" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2352" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
    <a id="2358" href="category-theory.copointed-endofunctors-precategories.html#2270" class="Function">obj-copointed-endofunctor-Precategory</a> <a id="2396" class="Symbol">=</a>
      <a id="2404" href="category-theory.functors-precategories.html#4132" class="Function">obj-functor-Precategory</a> <a id="2428" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2430" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2432" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a>

    <a id="2479" href="category-theory.copointed-endofunctors-precategories.html#2479" class="Function">hom-copointed-endofunctor-Precategory</a> <a id="2517" class="Symbol">:</a>
      <a id="2525" class="Symbol">{</a><a id="2526" href="category-theory.copointed-endofunctors-precategories.html#2526" class="Bound">X</a> <a id="2528" href="category-theory.copointed-endofunctors-precategories.html#2528" class="Bound">Y</a> <a id="2530" class="Symbol">:</a> <a id="2532" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2548" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="2549" class="Symbol">}</a> <a id="2551" class="Symbol">→</a>
      <a id="2559" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="2575" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2577" href="category-theory.copointed-endofunctors-precategories.html#2526" class="Bound">X</a> <a id="2579" href="category-theory.copointed-endofunctors-precategories.html#2528" class="Bound">Y</a> <a id="2581" class="Symbol">→</a>
      <a id="2589" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="2605" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="2615" class="Symbol">(</a> <a id="2617" href="category-theory.copointed-endofunctors-precategories.html#2270" class="Function">obj-copointed-endofunctor-Precategory</a> <a id="2655" href="category-theory.copointed-endofunctors-precategories.html#2526" class="Bound">X</a><a id="2656" class="Symbol">)</a>
        <a id="2666" class="Symbol">(</a> <a id="2668" href="category-theory.copointed-endofunctors-precategories.html#2270" class="Function">obj-copointed-endofunctor-Precategory</a> <a id="2706" href="category-theory.copointed-endofunctors-precategories.html#2528" class="Bound">Y</a><a id="2707" class="Symbol">)</a>
    <a id="2713" href="category-theory.copointed-endofunctors-precategories.html#2479" class="Function">hom-copointed-endofunctor-Precategory</a> <a id="2751" class="Symbol">=</a>
      <a id="2759" href="category-theory.functors-precategories.html#4257" class="Function">hom-functor-Precategory</a> <a id="2783" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2785" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2787" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a>

    <a id="2834" href="category-theory.copointed-endofunctors-precategories.html#2834" class="Function">preserves-id-copointed-endofunctor-Precategory</a> <a id="2881" class="Symbol">:</a>
      <a id="2889" class="Symbol">(</a><a id="2890" href="category-theory.copointed-endofunctors-precategories.html#2890" class="Bound">X</a> <a id="2892" class="Symbol">:</a> <a id="2894" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2910" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="2911" class="Symbol">)</a> <a id="2913" class="Symbol">→</a>
      <a id="2921" href="category-theory.copointed-endofunctors-precategories.html#2479" class="Function">hom-copointed-endofunctor-Precategory</a> <a id="2959" class="Symbol">(</a><a id="2960" href="category-theory.precategories.html#6934" class="Function">id-hom-Precategory</a> <a id="2979" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="2981" class="Symbol">{</a><a id="2982" href="category-theory.copointed-endofunctors-precategories.html#2890" class="Bound">X</a><a id="2983" class="Symbol">})</a> <a id="2986" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="2994" href="category-theory.precategories.html#6934" class="Function">id-hom-Precategory</a> <a id="3013" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
    <a id="3019" href="category-theory.copointed-endofunctors-precategories.html#2834" class="Function">preserves-id-copointed-endofunctor-Precategory</a> <a id="3066" class="Symbol">=</a>
      <a id="3074" href="category-theory.functors-precategories.html#5389" class="Function">preserves-id-functor-Precategory</a> <a id="3107" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="3109" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="3119" class="Symbol">(</a> <a id="3121" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a><a id="3162" class="Symbol">)</a>

    <a id="3169" href="category-theory.copointed-endofunctors-precategories.html#3169" class="Function">preserves-comp-copointed-endofunctor-Precategory</a> <a id="3218" class="Symbol">:</a>
      <a id="3226" class="Symbol">{</a><a id="3227" href="category-theory.copointed-endofunctors-precategories.html#3227" class="Bound">X</a> <a id="3229" href="category-theory.copointed-endofunctors-precategories.html#3229" class="Bound">Y</a> <a id="3231" href="category-theory.copointed-endofunctors-precategories.html#3231" class="Bound">Z</a> <a id="3233" class="Symbol">:</a> <a id="3235" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="3251" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="3252" class="Symbol">}</a>
      <a id="3260" class="Symbol">(</a><a id="3261" href="category-theory.copointed-endofunctors-precategories.html#3261" class="Bound">g</a> <a id="3263" class="Symbol">:</a> <a id="3265" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="3281" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="3283" href="category-theory.copointed-endofunctors-precategories.html#3229" class="Bound">Y</a> <a id="3285" href="category-theory.copointed-endofunctors-precategories.html#3231" class="Bound">Z</a><a id="3286" class="Symbol">)</a> <a id="3288" class="Symbol">(</a><a id="3289" href="category-theory.copointed-endofunctors-precategories.html#3289" class="Bound">f</a> <a id="3291" class="Symbol">:</a> <a id="3293" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="3309" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="3311" href="category-theory.copointed-endofunctors-precategories.html#3227" class="Bound">X</a> <a id="3313" href="category-theory.copointed-endofunctors-precategories.html#3229" class="Bound">Y</a><a id="3314" class="Symbol">)</a> <a id="3316" class="Symbol">→</a>
      <a id="3324" href="category-theory.copointed-endofunctors-precategories.html#2479" class="Function">hom-copointed-endofunctor-Precategory</a>
        <a id="3370" class="Symbol">(</a> <a id="3372" href="category-theory.precategories.html#5247" class="Function">comp-hom-Precategory</a> <a id="3393" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="3395" href="category-theory.copointed-endofunctors-precategories.html#3261" class="Bound">g</a> <a id="3397" href="category-theory.copointed-endofunctors-precategories.html#3289" class="Bound">f</a><a id="3398" class="Symbol">)</a> <a id="3400" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="3408" href="category-theory.precategories.html#5247" class="Function">comp-hom-Precategory</a> <a id="3429" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="3439" class="Symbol">(</a> <a id="3441" href="category-theory.copointed-endofunctors-precategories.html#2479" class="Function">hom-copointed-endofunctor-Precategory</a> <a id="3479" href="category-theory.copointed-endofunctors-precategories.html#3261" class="Bound">g</a><a id="3480" class="Symbol">)</a>
        <a id="3490" class="Symbol">(</a> <a id="3492" href="category-theory.copointed-endofunctors-precategories.html#2479" class="Function">hom-copointed-endofunctor-Precategory</a> <a id="3530" href="category-theory.copointed-endofunctors-precategories.html#3289" class="Bound">f</a><a id="3531" class="Symbol">)</a>
    <a id="3537" href="category-theory.copointed-endofunctors-precategories.html#3169" class="Function">preserves-comp-copointed-endofunctor-Precategory</a> <a id="3586" class="Symbol">=</a>
      <a id="3594" href="category-theory.functors-precategories.html#4893" class="Function">preserves-comp-functor-Precategory</a> <a id="3629" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="3631" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="3641" class="Symbol">(</a> <a id="3643" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a><a id="3684" class="Symbol">)</a>

    <a id="3691" href="category-theory.copointed-endofunctors-precategories.html#3691" class="Function">copointing-copointed-endofunctor-Precategory</a> <a id="3736" class="Symbol">:</a>
      <a id="3744" href="category-theory.natural-transformations-functors-precategories.html#1811" class="Function">natural-transformation-Precategory</a> <a id="3779" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="3781" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="3791" class="Symbol">(</a> <a id="3793" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a><a id="3834" class="Symbol">)</a>
        <a id="3844" class="Symbol">(</a> <a id="3846" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="3869" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="3870" class="Symbol">)</a>
    <a id="3876" href="category-theory.copointed-endofunctors-precategories.html#3691" class="Function">copointing-copointed-endofunctor-Precategory</a> <a id="3921" class="Symbol">=</a> <a id="3923" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3927" href="category-theory.copointed-endofunctors-precategories.html#2077" class="Bound">F</a>

    <a id="3934" href="category-theory.copointed-endofunctors-precategories.html#3934" class="Function">hom-family-copointing-copointed-endofunctor-Precategory</a> <a id="3990" class="Symbol">:</a>
      <a id="3998" href="category-theory.natural-transformations-functors-precategories.html#1346" class="Function">hom-family-functor-Precategory</a> <a id="4029" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="4031" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="4041" class="Symbol">(</a> <a id="4043" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a><a id="4084" class="Symbol">)</a>
        <a id="4094" class="Symbol">(</a> <a id="4096" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="4119" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="4120" class="Symbol">)</a>
    <a id="4126" href="category-theory.copointed-endofunctors-precategories.html#3934" class="Function">hom-family-copointing-copointed-endofunctor-Precategory</a> <a id="4182" class="Symbol">=</a>
      <a id="4190" href="category-theory.natural-transformations-functors-precategories.html#2033" class="Function">hom-family-natural-transformation-Precategory</a> <a id="4236" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="4238" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="4248" class="Symbol">(</a> <a id="4250" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a><a id="4291" class="Symbol">)</a>
        <a id="4301" class="Symbol">(</a> <a id="4303" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="4326" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="4327" class="Symbol">)</a>
        <a id="4337" class="Symbol">(</a> <a id="4339" href="category-theory.copointed-endofunctors-precategories.html#3691" class="Function">copointing-copointed-endofunctor-Precategory</a><a id="4383" class="Symbol">)</a>

    <a id="4390" href="category-theory.copointed-endofunctors-precategories.html#4390" class="Function">naturality-copointing-copointed-endofunctor-Precategory</a> <a id="4446" class="Symbol">:</a>
      <a id="4454" href="category-theory.natural-transformations-functors-precategories.html#1543" class="Function">is-natural-transformation-Precategory</a> <a id="4492" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="4494" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="4504" class="Symbol">(</a> <a id="4506" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a><a id="4547" class="Symbol">)</a>
        <a id="4557" class="Symbol">(</a> <a id="4559" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="4582" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="4583" class="Symbol">)</a>
        <a id="4593" class="Symbol">(</a> <a id="4595" href="category-theory.copointed-endofunctors-precategories.html#3934" class="Function">hom-family-copointing-copointed-endofunctor-Precategory</a><a id="4650" class="Symbol">)</a>
    <a id="4656" href="category-theory.copointed-endofunctors-precategories.html#4390" class="Function">naturality-copointing-copointed-endofunctor-Precategory</a> <a id="4712" class="Symbol">=</a>
      <a id="4720" href="category-theory.natural-transformations-functors-precategories.html#2342" class="Function">naturality-natural-transformation-Precategory</a> <a id="4766" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a> <a id="4768" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a>
        <a id="4778" class="Symbol">(</a> <a id="4780" href="category-theory.copointed-endofunctors-precategories.html#2131" class="Function">functor-copointed-endofunctor-Precategory</a><a id="4821" class="Symbol">)</a>
        <a id="4831" class="Symbol">(</a> <a id="4833" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="4856" href="category-theory.copointed-endofunctors-precategories.html#1868" class="Bound">C</a><a id="4857" class="Symbol">)</a>
        <a id="4867" class="Symbol">(</a> <a id="4869" href="category-theory.copointed-endofunctors-precategories.html#3691" class="Function">copointing-copointed-endofunctor-Precategory</a><a id="4913" class="Symbol">)</a>
</pre>
## See also

- [Pointed endofunctors](category-theory.pointed-endofunctors-precategories.md)
  for the dual concept.
