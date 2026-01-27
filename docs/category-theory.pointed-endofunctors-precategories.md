# Pointed endofunctors on precategories

<pre class="Agda"><a id="50" class="Keyword">module</a> <a id="57" href="category-theory.pointed-endofunctors-precategories.html" class="Module">category-theory.pointed-endofunctors-precategories</a> <a id="108" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="164" class="Keyword">open</a> <a id="169" class="Keyword">import</a> <a id="176" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="category-theory.natural-transformations-functors-precategories.html" class="Module">category-theory.natural-transformations-functors-precategories</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="377" class="Keyword">open</a> <a id="382" class="Keyword">import</a> <a id="389" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An [endofunctor](category-theory.functors-precategories.md) `F : C → C` on a
[precategory](category-theory.precategories.md) `C` is said to be
{{#concept "pointed" Disambiguation="endofunctor on a category" Agda=pointed-endofunctor-Precategory}}
if it comes equipped with a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
`id ⇒ F` from the identity [functor](category-theory.functors-precategories.md)
to `F`.

More explicitly, a
{{#concept "pointing" Disambiguation="endofunctor on a precategory" Agda=pointing-endofunctor-Precategory}}
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

### The structure of a pointing on an endofunctor on a precategory

<pre class="Agda"><a id="1496" class="Keyword">module</a> <a id="1503" href="category-theory.pointed-endofunctors-precategories.html#1503" class="Module">_</a>
  <a id="1507" class="Symbol">{</a><a id="1508" href="category-theory.pointed-endofunctors-precategories.html#1508" class="Bound">l1</a> <a id="1511" href="category-theory.pointed-endofunctors-precategories.html#1511" class="Bound">l2</a> <a id="1514" class="Symbol">:</a> <a id="1516" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1521" class="Symbol">}</a> <a id="1523" class="Symbol">(</a><a id="1524" href="category-theory.pointed-endofunctors-precategories.html#1524" class="Bound">C</a> <a id="1526" class="Symbol">:</a> <a id="1528" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1540" href="category-theory.pointed-endofunctors-precategories.html#1508" class="Bound">l1</a> <a id="1543" href="category-theory.pointed-endofunctors-precategories.html#1511" class="Bound">l2</a><a id="1545" class="Symbol">)</a> <a id="1547" class="Symbol">(</a><a id="1548" href="category-theory.pointed-endofunctors-precategories.html#1548" class="Bound">T</a> <a id="1550" class="Symbol">:</a> <a id="1552" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="1572" href="category-theory.pointed-endofunctors-precategories.html#1524" class="Bound">C</a> <a id="1574" href="category-theory.pointed-endofunctors-precategories.html#1524" class="Bound">C</a><a id="1575" class="Symbol">)</a>
  <a id="1579" class="Keyword">where</a>

  <a id="1588" href="category-theory.pointed-endofunctors-precategories.html#1588" class="Function">pointing-endofunctor-Precategory</a> <a id="1621" class="Symbol">:</a> <a id="1623" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1626" class="Symbol">(</a><a id="1627" href="category-theory.pointed-endofunctors-precategories.html#1508" class="Bound">l1</a> <a id="1630" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1632" href="category-theory.pointed-endofunctors-precategories.html#1511" class="Bound">l2</a><a id="1634" class="Symbol">)</a>
  <a id="1638" href="category-theory.pointed-endofunctors-precategories.html#1588" class="Function">pointing-endofunctor-Precategory</a> <a id="1671" class="Symbol">=</a>
    <a id="1677" href="category-theory.natural-transformations-functors-precategories.html#1811" class="Function">natural-transformation-Precategory</a> <a id="1712" href="category-theory.pointed-endofunctors-precategories.html#1524" class="Bound">C</a> <a id="1714" href="category-theory.pointed-endofunctors-precategories.html#1524" class="Bound">C</a> <a id="1716" class="Symbol">(</a><a id="1717" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="1740" href="category-theory.pointed-endofunctors-precategories.html#1524" class="Bound">C</a><a id="1741" class="Symbol">)</a> <a id="1743" href="category-theory.pointed-endofunctors-precategories.html#1548" class="Bound">T</a>
</pre>
### Pointed endofunctors on a precategory

<pre class="Agda"><a id="1801" class="Keyword">module</a> <a id="1808" href="category-theory.pointed-endofunctors-precategories.html#1808" class="Module">_</a>
  <a id="1812" class="Symbol">{</a><a id="1813" href="category-theory.pointed-endofunctors-precategories.html#1813" class="Bound">l1</a> <a id="1816" href="category-theory.pointed-endofunctors-precategories.html#1816" class="Bound">l2</a> <a id="1819" class="Symbol">:</a> <a id="1821" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1826" class="Symbol">}</a> <a id="1828" class="Symbol">(</a><a id="1829" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="1831" class="Symbol">:</a> <a id="1833" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1845" href="category-theory.pointed-endofunctors-precategories.html#1813" class="Bound">l1</a> <a id="1848" href="category-theory.pointed-endofunctors-precategories.html#1816" class="Bound">l2</a><a id="1850" class="Symbol">)</a>
  <a id="1854" class="Keyword">where</a>

  <a id="1863" href="category-theory.pointed-endofunctors-precategories.html#1863" class="Function">pointed-endofunctor-Precategory</a> <a id="1895" class="Symbol">:</a> <a id="1897" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1900" class="Symbol">(</a><a id="1901" href="category-theory.pointed-endofunctors-precategories.html#1813" class="Bound">l1</a> <a id="1904" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1906" href="category-theory.pointed-endofunctors-precategories.html#1816" class="Bound">l2</a><a id="1908" class="Symbol">)</a>
  <a id="1912" href="category-theory.pointed-endofunctors-precategories.html#1863" class="Function">pointed-endofunctor-Precategory</a> <a id="1944" class="Symbol">=</a>
    <a id="1950" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1952" class="Symbol">(</a><a id="1953" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="1973" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="1975" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="1976" class="Symbol">)</a> <a id="1978" class="Symbol">(</a><a id="1979" href="category-theory.pointed-endofunctors-precategories.html#1588" class="Function">pointing-endofunctor-Precategory</a> <a id="2012" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="2013" class="Symbol">)</a>

  <a id="2018" class="Keyword">module</a> <a id="2025" href="category-theory.pointed-endofunctors-precategories.html#2025" class="Module">_</a>
    <a id="2031" class="Symbol">(</a><a id="2032" href="category-theory.pointed-endofunctors-precategories.html#2032" class="Bound">F</a> <a id="2034" class="Symbol">:</a> <a id="2036" href="category-theory.pointed-endofunctors-precategories.html#1863" class="Function">pointed-endofunctor-Precategory</a><a id="2067" class="Symbol">)</a>
    <a id="2073" class="Keyword">where</a>

    <a id="2084" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a> <a id="2124" class="Symbol">:</a>
      <a id="2132" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="2152" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="2154" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
    <a id="2160" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a> <a id="2200" class="Symbol">=</a>
      <a id="2208" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2212" href="category-theory.pointed-endofunctors-precategories.html#2032" class="Bound">F</a>

    <a id="2219" href="category-theory.pointed-endofunctors-precategories.html#2219" class="Function">obj-pointed-endofunctor-Precategory</a> <a id="2255" class="Symbol">:</a> <a id="2257" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2273" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="2275" class="Symbol">→</a> <a id="2277" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2293" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
    <a id="2299" href="category-theory.pointed-endofunctors-precategories.html#2219" class="Function">obj-pointed-endofunctor-Precategory</a> <a id="2335" class="Symbol">=</a>
      <a id="2343" href="category-theory.functors-precategories.html#4132" class="Function">obj-functor-Precategory</a> <a id="2367" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="2369" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="2371" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a>

    <a id="2416" href="category-theory.pointed-endofunctors-precategories.html#2416" class="Function">hom-pointed-endofunctor-Precategory</a> <a id="2452" class="Symbol">:</a>
      <a id="2460" class="Symbol">{</a><a id="2461" href="category-theory.pointed-endofunctors-precategories.html#2461" class="Bound">X</a> <a id="2463" href="category-theory.pointed-endofunctors-precategories.html#2463" class="Bound">Y</a> <a id="2465" class="Symbol">:</a> <a id="2467" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2483" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="2484" class="Symbol">}</a> <a id="2486" class="Symbol">→</a>
      <a id="2494" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="2510" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="2512" href="category-theory.pointed-endofunctors-precategories.html#2461" class="Bound">X</a> <a id="2514" href="category-theory.pointed-endofunctors-precategories.html#2463" class="Bound">Y</a> <a id="2516" class="Symbol">→</a>
      <a id="2524" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="2540" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="2550" class="Symbol">(</a> <a id="2552" href="category-theory.pointed-endofunctors-precategories.html#2219" class="Function">obj-pointed-endofunctor-Precategory</a> <a id="2588" href="category-theory.pointed-endofunctors-precategories.html#2461" class="Bound">X</a><a id="2589" class="Symbol">)</a>
        <a id="2599" class="Symbol">(</a> <a id="2601" href="category-theory.pointed-endofunctors-precategories.html#2219" class="Function">obj-pointed-endofunctor-Precategory</a> <a id="2637" href="category-theory.pointed-endofunctors-precategories.html#2463" class="Bound">Y</a><a id="2638" class="Symbol">)</a>
    <a id="2644" href="category-theory.pointed-endofunctors-precategories.html#2416" class="Function">hom-pointed-endofunctor-Precategory</a> <a id="2680" class="Symbol">=</a>
      <a id="2688" href="category-theory.functors-precategories.html#4257" class="Function">hom-functor-Precategory</a> <a id="2712" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="2714" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="2716" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a>

    <a id="2761" href="category-theory.pointed-endofunctors-precategories.html#2761" class="Function">preserves-id-pointed-endofunctor-Precategory</a> <a id="2806" class="Symbol">:</a>
      <a id="2814" class="Symbol">(</a><a id="2815" href="category-theory.pointed-endofunctors-precategories.html#2815" class="Bound">X</a> <a id="2817" class="Symbol">:</a> <a id="2819" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2835" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="2836" class="Symbol">)</a> <a id="2838" class="Symbol">→</a>
      <a id="2846" href="category-theory.pointed-endofunctors-precategories.html#2416" class="Function">hom-pointed-endofunctor-Precategory</a> <a id="2882" class="Symbol">(</a><a id="2883" href="category-theory.precategories.html#6934" class="Function">id-hom-Precategory</a> <a id="2902" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="2904" class="Symbol">{</a><a id="2905" href="category-theory.pointed-endofunctors-precategories.html#2815" class="Bound">X</a><a id="2906" class="Symbol">})</a> <a id="2909" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="2917" href="category-theory.precategories.html#6934" class="Function">id-hom-Precategory</a> <a id="2936" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
    <a id="2942" href="category-theory.pointed-endofunctors-precategories.html#2761" class="Function">preserves-id-pointed-endofunctor-Precategory</a> <a id="2987" class="Symbol">=</a>
      <a id="2995" href="category-theory.functors-precategories.html#5389" class="Function">preserves-id-functor-Precategory</a> <a id="3028" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="3030" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="3040" class="Symbol">(</a> <a id="3042" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a><a id="3081" class="Symbol">)</a>

    <a id="3088" href="category-theory.pointed-endofunctors-precategories.html#3088" class="Function">preserves-comp-pointed-endofunctor-Precategory</a> <a id="3135" class="Symbol">:</a>
      <a id="3143" class="Symbol">{</a><a id="3144" href="category-theory.pointed-endofunctors-precategories.html#3144" class="Bound">X</a> <a id="3146" href="category-theory.pointed-endofunctors-precategories.html#3146" class="Bound">Y</a> <a id="3148" href="category-theory.pointed-endofunctors-precategories.html#3148" class="Bound">Z</a> <a id="3150" class="Symbol">:</a> <a id="3152" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="3168" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="3169" class="Symbol">}</a>
      <a id="3177" class="Symbol">(</a><a id="3178" href="category-theory.pointed-endofunctors-precategories.html#3178" class="Bound">g</a> <a id="3180" class="Symbol">:</a> <a id="3182" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="3198" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="3200" href="category-theory.pointed-endofunctors-precategories.html#3146" class="Bound">Y</a> <a id="3202" href="category-theory.pointed-endofunctors-precategories.html#3148" class="Bound">Z</a><a id="3203" class="Symbol">)</a> <a id="3205" class="Symbol">(</a><a id="3206" href="category-theory.pointed-endofunctors-precategories.html#3206" class="Bound">f</a> <a id="3208" class="Symbol">:</a> <a id="3210" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="3226" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="3228" href="category-theory.pointed-endofunctors-precategories.html#3144" class="Bound">X</a> <a id="3230" href="category-theory.pointed-endofunctors-precategories.html#3146" class="Bound">Y</a><a id="3231" class="Symbol">)</a> <a id="3233" class="Symbol">→</a>
      <a id="3241" href="category-theory.pointed-endofunctors-precategories.html#2416" class="Function">hom-pointed-endofunctor-Precategory</a>
        <a id="3285" class="Symbol">(</a> <a id="3287" href="category-theory.precategories.html#5247" class="Function">comp-hom-Precategory</a> <a id="3308" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="3310" href="category-theory.pointed-endofunctors-precategories.html#3178" class="Bound">g</a> <a id="3312" href="category-theory.pointed-endofunctors-precategories.html#3206" class="Bound">f</a><a id="3313" class="Symbol">)</a> <a id="3315" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="3323" href="category-theory.precategories.html#5247" class="Function">comp-hom-Precategory</a> <a id="3344" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="3354" class="Symbol">(</a> <a id="3356" href="category-theory.pointed-endofunctors-precategories.html#2416" class="Function">hom-pointed-endofunctor-Precategory</a> <a id="3392" href="category-theory.pointed-endofunctors-precategories.html#3178" class="Bound">g</a><a id="3393" class="Symbol">)</a>
        <a id="3403" class="Symbol">(</a> <a id="3405" href="category-theory.pointed-endofunctors-precategories.html#2416" class="Function">hom-pointed-endofunctor-Precategory</a> <a id="3441" href="category-theory.pointed-endofunctors-precategories.html#3206" class="Bound">f</a><a id="3442" class="Symbol">)</a>
    <a id="3448" href="category-theory.pointed-endofunctors-precategories.html#3088" class="Function">preserves-comp-pointed-endofunctor-Precategory</a> <a id="3495" class="Symbol">=</a>
      <a id="3503" href="category-theory.functors-precategories.html#4893" class="Function">preserves-comp-functor-Precategory</a> <a id="3538" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="3540" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="3550" class="Symbol">(</a> <a id="3552" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a><a id="3591" class="Symbol">)</a>

    <a id="3598" href="category-theory.pointed-endofunctors-precategories.html#3598" class="Function">pointing-pointed-endofunctor-Precategory</a> <a id="3639" class="Symbol">:</a>
      <a id="3647" href="category-theory.natural-transformations-functors-precategories.html#1811" class="Function">natural-transformation-Precategory</a> <a id="3682" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="3684" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="3694" class="Symbol">(</a> <a id="3696" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="3719" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="3720" class="Symbol">)</a>
        <a id="3730" class="Symbol">(</a> <a id="3732" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a><a id="3771" class="Symbol">)</a>
    <a id="3777" href="category-theory.pointed-endofunctors-precategories.html#3598" class="Function">pointing-pointed-endofunctor-Precategory</a> <a id="3818" class="Symbol">=</a> <a id="3820" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3824" href="category-theory.pointed-endofunctors-precategories.html#2032" class="Bound">F</a>

    <a id="3831" href="category-theory.pointed-endofunctors-precategories.html#3831" class="Function">hom-family-pointing-pointed-endofunctor-Precategory</a> <a id="3883" class="Symbol">:</a>
      <a id="3891" href="category-theory.natural-transformations-functors-precategories.html#1346" class="Function">hom-family-functor-Precategory</a> <a id="3922" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="3924" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="3934" class="Symbol">(</a> <a id="3936" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="3959" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="3960" class="Symbol">)</a>
        <a id="3970" class="Symbol">(</a> <a id="3972" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a><a id="4011" class="Symbol">)</a>
    <a id="4017" href="category-theory.pointed-endofunctors-precategories.html#3831" class="Function">hom-family-pointing-pointed-endofunctor-Precategory</a> <a id="4069" class="Symbol">=</a>
      <a id="4077" href="category-theory.natural-transformations-functors-precategories.html#2033" class="Function">hom-family-natural-transformation-Precategory</a> <a id="4123" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="4125" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="4135" class="Symbol">(</a> <a id="4137" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="4160" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="4161" class="Symbol">)</a>
        <a id="4171" class="Symbol">(</a> <a id="4173" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a><a id="4212" class="Symbol">)</a>
        <a id="4222" class="Symbol">(</a> <a id="4224" href="category-theory.pointed-endofunctors-precategories.html#3598" class="Function">pointing-pointed-endofunctor-Precategory</a><a id="4264" class="Symbol">)</a>

    <a id="4271" href="category-theory.pointed-endofunctors-precategories.html#4271" class="Function">naturality-pointing-pointed-endofunctor-Precategory</a> <a id="4323" class="Symbol">:</a>
      <a id="4331" href="category-theory.natural-transformations-functors-precategories.html#1543" class="Function">is-natural-transformation-Precategory</a> <a id="4369" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="4371" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="4381" class="Symbol">(</a> <a id="4383" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="4406" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="4407" class="Symbol">)</a>
        <a id="4417" class="Symbol">(</a> <a id="4419" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a><a id="4458" class="Symbol">)</a>
        <a id="4468" class="Symbol">(</a> <a id="4470" href="category-theory.pointed-endofunctors-precategories.html#3831" class="Function">hom-family-pointing-pointed-endofunctor-Precategory</a><a id="4521" class="Symbol">)</a>
    <a id="4527" href="category-theory.pointed-endofunctors-precategories.html#4271" class="Function">naturality-pointing-pointed-endofunctor-Precategory</a> <a id="4579" class="Symbol">=</a>
      <a id="4587" href="category-theory.natural-transformations-functors-precategories.html#2342" class="Function">naturality-natural-transformation-Precategory</a> <a id="4633" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a> <a id="4635" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a>
        <a id="4645" class="Symbol">(</a> <a id="4647" href="category-theory.functors-precategories.html#6226" class="Function">id-functor-Precategory</a> <a id="4670" href="category-theory.pointed-endofunctors-precategories.html#1829" class="Bound">C</a><a id="4671" class="Symbol">)</a>
        <a id="4681" class="Symbol">(</a> <a id="4683" href="category-theory.pointed-endofunctors-precategories.html#2084" class="Function">functor-pointed-endofunctor-Precategory</a><a id="4722" class="Symbol">)</a>
        <a id="4732" class="Symbol">(</a> <a id="4734" href="category-theory.pointed-endofunctors-precategories.html#3598" class="Function">pointing-pointed-endofunctor-Precategory</a><a id="4774" class="Symbol">)</a>
</pre>
## See also

- [Copointed endofunctors](category-theory.copointed-endofunctors-precategories.md)
  for the dual concept.
