# The Yoneda lemma for categories

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="category-theory.yoneda-lemma-categories.html" class="Module">category-theory.yoneda-lemma-categories</a> <a id="91" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="147" class="Keyword">open</a> <a id="152" class="Keyword">import</a> <a id="159" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="category-theory.copresheaf-categories.html" class="Module">category-theory.copresheaf-categories</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="category-theory.natural-transformations-functors-from-small-to-large-categories.html" class="Module">category-theory.natural-transformations-functors-from-small-to-large-categories</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="category-theory.representable-functors-categories.html" class="Module">category-theory.representable-functors-categories</a>
<a id="390" class="Keyword">open</a> <a id="395" class="Keyword">import</a> <a id="402" href="category-theory.yoneda-lemma-precategories.html" class="Module">category-theory.yoneda-lemma-precategories</a>

<a id="446" class="Keyword">open</a> <a id="451" class="Keyword">import</a> <a id="458" href="foundation.category-of-sets.html" class="Module">foundation.category-of-sets</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="522" class="Keyword">open</a> <a id="527" class="Keyword">import</a> <a id="534" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The
{{#concept "Yoneda lemma" Disambiguation="for set-level categories" WD="Yoneda lemma" WDID=Q320577 Agda=lemma-yoneda-Category}}
states that, given a [category](category-theory.categories.md) `C`, an object
`c`, and a [functor](category-theory.functors-categories.md) `F` from `C` to the
[category of sets](foundation.category-of-sets.md)

```text
  F : C → Set,
```

there is an [equivalence](foundation-core.equivalences.md) between the
[set of natural transformations](category-theory.natural-transformations-functors-categories.md)
from the functor
[represented](category-theory.representable-functors-categories.md) by `c` to
`F` and the [set](foundation-core.sets.md) `F c`.

```text
  Nat(Hom(c , -) , F) ≃ F c
```

More precisely, the Yoneda lemma asserts that the map from the type of natural
transformations to the type `F c` defined by evaluating the component of the
natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## Theorem

### The Yoneda lemma into the large category of sets

<pre class="Agda"><a id="1633" class="Keyword">module</a> <a id="1640" href="category-theory.yoneda-lemma-categories.html#1640" class="Module">_</a>
  <a id="1644" class="Symbol">{</a><a id="1645" href="category-theory.yoneda-lemma-categories.html#1645" class="Bound">l1</a> <a id="1648" href="category-theory.yoneda-lemma-categories.html#1648" class="Bound">l2</a> <a id="1651" href="category-theory.yoneda-lemma-categories.html#1651" class="Bound">l3</a> <a id="1654" class="Symbol">:</a> <a id="1656" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1661" class="Symbol">}</a> <a id="1663" class="Symbol">(</a><a id="1664" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a> <a id="1666" class="Symbol">:</a> <a id="1668" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1677" href="category-theory.yoneda-lemma-categories.html#1645" class="Bound">l1</a> <a id="1680" href="category-theory.yoneda-lemma-categories.html#1648" class="Bound">l2</a><a id="1682" class="Symbol">)</a> <a id="1684" class="Symbol">(</a><a id="1685" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a> <a id="1687" class="Symbol">:</a> <a id="1689" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="1702" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="1703" class="Symbol">)</a>
  <a id="1707" class="Symbol">(</a><a id="1708" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a> <a id="1710" class="Symbol">:</a> <a id="1712" href="category-theory.copresheaf-categories.html#3237" class="Function">copresheaf-Precategory</a> <a id="1735" class="Symbol">(</a><a id="1736" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1757" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="1758" class="Symbol">)</a> <a id="1760" href="category-theory.yoneda-lemma-categories.html#1651" class="Bound">l3</a><a id="1762" class="Symbol">)</a>
  <a id="1766" class="Keyword">where</a>

  <a id="1775" href="category-theory.yoneda-lemma-categories.html#1775" class="Function">map-yoneda-Category</a> <a id="1795" class="Symbol">:</a>
    <a id="1801" href="category-theory.copresheaf-categories.html#5182" class="Function">hom-copresheaf-Precategory</a>
      <a id="1834" class="Symbol">(</a> <a id="1836" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1857" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="1858" class="Symbol">)</a> <a id="1860" class="Symbol">(</a><a id="1861" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="1892" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a> <a id="1894" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a><a id="1895" class="Symbol">)</a> <a id="1897" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a> <a id="1899" class="Symbol">→</a>
    <a id="1905" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="1936" class="Symbol">(</a><a id="1937" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1958" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="1959" class="Symbol">)</a> <a id="1961" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a> <a id="1963" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a>
  <a id="1967" href="category-theory.yoneda-lemma-categories.html#1775" class="Function">map-yoneda-Category</a> <a id="1987" class="Symbol">=</a>
    <a id="1993" href="category-theory.yoneda-lemma-precategories.html#2102" class="Function">map-yoneda-Precategory</a> <a id="2016" class="Symbol">(</a><a id="2017" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2038" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="2039" class="Symbol">)</a> <a id="2041" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a> <a id="2043" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>
</pre>
The inverse to the Yoneda map:

<pre class="Agda">  <a id="2092" href="category-theory.yoneda-lemma-categories.html#2092" class="Function">hom-family-extension-yoneda-Category</a> <a id="2129" class="Symbol">:</a>
    <a id="2135" class="Symbol">(</a><a id="2136" href="category-theory.yoneda-lemma-categories.html#2136" class="Bound">u</a> <a id="2138" class="Symbol">:</a> <a id="2140" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="2171" class="Symbol">(</a><a id="2172" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2193" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="2194" class="Symbol">)</a> <a id="2196" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a> <a id="2198" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a><a id="2199" class="Symbol">)</a> <a id="2201" class="Symbol">→</a>
    <a id="2207" href="category-theory.natural-transformations-functors-from-small-to-large-categories.html#1473" class="Function">hom-family-functor-Small-Large-Category</a>
      <a id="2253" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a> <a id="2255" href="foundation.category-of-sets.html#3338" class="Function">Set-Large-Category</a> <a id="2274" class="Symbol">(</a><a id="2275" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="2306" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a> <a id="2308" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a><a id="2309" class="Symbol">)</a> <a id="2311" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>
  <a id="2315" href="category-theory.yoneda-lemma-categories.html#2092" class="Function">hom-family-extension-yoneda-Category</a> <a id="2352" class="Symbol">=</a>
    <a id="2358" href="category-theory.yoneda-lemma-precategories.html#2528" class="Function">hom-family-extension-yoneda-Precategory</a> <a id="2398" class="Symbol">(</a><a id="2399" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2420" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="2421" class="Symbol">)</a> <a id="2423" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a> <a id="2425" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>

  <a id="2430" href="category-theory.yoneda-lemma-categories.html#2430" class="Function">naturality-extension-yoneda-Category</a> <a id="2467" class="Symbol">:</a>
    <a id="2473" class="Symbol">(</a><a id="2474" href="category-theory.yoneda-lemma-categories.html#2474" class="Bound">u</a> <a id="2476" class="Symbol">:</a> <a id="2478" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="2509" class="Symbol">(</a><a id="2510" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2531" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="2532" class="Symbol">)</a> <a id="2534" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a> <a id="2536" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a><a id="2537" class="Symbol">)</a> <a id="2539" class="Symbol">→</a>
    <a id="2545" href="category-theory.natural-transformations-functors-from-small-to-large-categories.html#1700" class="Function">is-natural-transformation-Small-Large-Category</a>
      <a id="2598" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a> <a id="2600" href="foundation.category-of-sets.html#3338" class="Function">Set-Large-Category</a> <a id="2619" class="Symbol">(</a><a id="2620" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="2651" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a> <a id="2653" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a><a id="2654" class="Symbol">)</a> <a id="2656" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>
      <a id="2664" class="Symbol">(</a> <a id="2666" href="category-theory.yoneda-lemma-categories.html#2092" class="Function">hom-family-extension-yoneda-Category</a> <a id="2703" href="category-theory.yoneda-lemma-categories.html#2474" class="Bound">u</a><a id="2704" class="Symbol">)</a>
  <a id="2708" href="category-theory.yoneda-lemma-categories.html#2430" class="Function">naturality-extension-yoneda-Category</a> <a id="2745" class="Symbol">=</a>
    <a id="2751" href="category-theory.yoneda-lemma-precategories.html#2861" class="Function">naturality-extension-yoneda-Precategory</a> <a id="2791" class="Symbol">(</a><a id="2792" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2813" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="2814" class="Symbol">)</a> <a id="2816" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a> <a id="2818" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>

  <a id="2823" href="category-theory.yoneda-lemma-categories.html#2823" class="Function">extension-yoneda-Category</a> <a id="2849" class="Symbol">:</a>
    <a id="2855" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="2886" class="Symbol">(</a><a id="2887" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2908" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="2909" class="Symbol">)</a> <a id="2911" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a> <a id="2913" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a> <a id="2915" class="Symbol">→</a>
    <a id="2921" href="category-theory.copresheaf-categories.html#5182" class="Function">hom-copresheaf-Precategory</a>
      <a id="2954" class="Symbol">(</a> <a id="2956" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2977" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="2978" class="Symbol">)</a> <a id="2980" class="Symbol">(</a><a id="2981" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="3012" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a> <a id="3014" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a><a id="3015" class="Symbol">)</a> <a id="3017" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>
  <a id="3021" href="category-theory.yoneda-lemma-categories.html#2823" class="Function">extension-yoneda-Category</a> <a id="3047" class="Symbol">=</a>
    <a id="3053" href="category-theory.yoneda-lemma-precategories.html#3363" class="Function">extension-yoneda-Precategory</a> <a id="3082" class="Symbol">(</a><a id="3083" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3104" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="3105" class="Symbol">)</a> <a id="3107" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a> <a id="3109" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>

  <a id="3114" href="category-theory.yoneda-lemma-categories.html#3114" class="Function">lemma-yoneda-Category</a> <a id="3136" class="Symbol">:</a> <a id="3138" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="3147" href="category-theory.yoneda-lemma-categories.html#1775" class="Function">map-yoneda-Category</a>
  <a id="3169" href="category-theory.yoneda-lemma-categories.html#3114" class="Function">lemma-yoneda-Category</a> <a id="3191" class="Symbol">=</a> <a id="3193" href="category-theory.yoneda-lemma-precategories.html#4571" class="Function">lemma-yoneda-Precategory</a> <a id="3218" class="Symbol">(</a><a id="3219" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3240" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="3241" class="Symbol">)</a> <a id="3243" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a> <a id="3245" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>

  <a id="3250" href="category-theory.yoneda-lemma-categories.html#3250" class="Function">equiv-lemma-yoneda-Category</a> <a id="3278" class="Symbol">:</a>
    <a id="3284" href="category-theory.copresheaf-categories.html#5182" class="Function">hom-copresheaf-Precategory</a>
      <a id="3317" class="Symbol">(</a> <a id="3319" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3340" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="3341" class="Symbol">)</a> <a id="3343" class="Symbol">(</a><a id="3344" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="3375" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a> <a id="3377" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a><a id="3378" class="Symbol">)</a> <a id="3380" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a> <a id="3382" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="3388" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="3419" class="Symbol">(</a><a id="3420" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3441" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="3442" class="Symbol">)</a> <a id="3444" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a> <a id="3446" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a>
  <a id="3450" href="category-theory.yoneda-lemma-categories.html#3250" class="Function">equiv-lemma-yoneda-Category</a> <a id="3478" class="Symbol">=</a>
    <a id="3484" href="category-theory.yoneda-lemma-precategories.html#4828" class="Function">equiv-lemma-yoneda-Precategory</a> <a id="3515" class="Symbol">(</a><a id="3516" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3537" href="category-theory.yoneda-lemma-categories.html#1664" class="Bound">C</a><a id="3538" class="Symbol">)</a> <a id="3540" href="category-theory.yoneda-lemma-categories.html#1685" class="Bound">c</a> <a id="3542" href="category-theory.yoneda-lemma-categories.html#1708" class="Bound">F</a>
</pre>
## Corollaries

### The Yoneda lemma for representable functors

An important special-case of the Yoneda lemma is when `F` is itself a
representable functor `F = Hom(-, d)`.

<pre class="Agda"><a id="3732" class="Keyword">module</a> <a id="3739" href="category-theory.yoneda-lemma-categories.html#3739" class="Module">_</a>
  <a id="3743" class="Symbol">{</a><a id="3744" href="category-theory.yoneda-lemma-categories.html#3744" class="Bound">l1</a> <a id="3747" href="category-theory.yoneda-lemma-categories.html#3747" class="Bound">l2</a> <a id="3750" class="Symbol">:</a> <a id="3752" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3757" class="Symbol">}</a> <a id="3759" class="Symbol">(</a><a id="3760" href="category-theory.yoneda-lemma-categories.html#3760" class="Bound">C</a> <a id="3762" class="Symbol">:</a> <a id="3764" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="3773" href="category-theory.yoneda-lemma-categories.html#3744" class="Bound">l1</a> <a id="3776" href="category-theory.yoneda-lemma-categories.html#3747" class="Bound">l2</a><a id="3778" class="Symbol">)</a> <a id="3780" class="Symbol">(</a><a id="3781" href="category-theory.yoneda-lemma-categories.html#3781" class="Bound">c</a> <a id="3783" href="category-theory.yoneda-lemma-categories.html#3783" class="Bound">d</a> <a id="3785" class="Symbol">:</a> <a id="3787" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="3800" href="category-theory.yoneda-lemma-categories.html#3760" class="Bound">C</a><a id="3801" class="Symbol">)</a>
  <a id="3805" class="Keyword">where</a>

  <a id="3814" href="category-theory.yoneda-lemma-categories.html#3814" class="Function">equiv-lemma-yoneda-representable-Category</a> <a id="3856" class="Symbol">:</a>
    <a id="3862" href="category-theory.copresheaf-categories.html#5182" class="Function">hom-copresheaf-Precategory</a>
      <a id="3895" class="Symbol">(</a> <a id="3897" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3918" href="category-theory.yoneda-lemma-categories.html#3760" class="Bound">C</a><a id="3919" class="Symbol">)</a>
      <a id="3927" class="Symbol">(</a> <a id="3929" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="3960" href="category-theory.yoneda-lemma-categories.html#3760" class="Bound">C</a> <a id="3962" href="category-theory.yoneda-lemma-categories.html#3781" class="Bound">c</a><a id="3963" class="Symbol">)</a>
      <a id="3971" class="Symbol">(</a> <a id="3973" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="4004" href="category-theory.yoneda-lemma-categories.html#3760" class="Bound">C</a> <a id="4006" href="category-theory.yoneda-lemma-categories.html#3783" class="Bound">d</a><a id="4007" class="Symbol">)</a> <a id="4009" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="4015" href="category-theory.categories.html#2741" class="Function">hom-Category</a> <a id="4028" href="category-theory.yoneda-lemma-categories.html#3760" class="Bound">C</a> <a id="4030" href="category-theory.yoneda-lemma-categories.html#3783" class="Bound">d</a> <a id="4032" href="category-theory.yoneda-lemma-categories.html#3781" class="Bound">c</a>
  <a id="4036" href="category-theory.yoneda-lemma-categories.html#3814" class="Function">equiv-lemma-yoneda-representable-Category</a> <a id="4078" class="Symbol">=</a>
    <a id="4084" href="category-theory.yoneda-lemma-categories.html#3250" class="Function">equiv-lemma-yoneda-Category</a> <a id="4112" href="category-theory.yoneda-lemma-categories.html#3760" class="Bound">C</a> <a id="4114" href="category-theory.yoneda-lemma-categories.html#3781" class="Bound">c</a> <a id="4116" class="Symbol">(</a><a id="4117" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="4148" href="category-theory.yoneda-lemma-categories.html#3760" class="Bound">C</a> <a id="4150" href="category-theory.yoneda-lemma-categories.html#3783" class="Bound">d</a><a id="4151" class="Symbol">)</a>
</pre>
## See also

- [Presheaf categories](category-theory.presheaf-categories.md)

## External links

- [The Yoneda embedding](https://1lab.dev/Cat.Functor.Hom.html#the-yoneda-embedding)
  at 1lab
- [Yoneda lemma](https://ncatlab.org/nlab/show/Yoneda+lemma) at $n$Lab
- [The Yoneda lemma](https://www.math3ma.com/blog/the-yoneda-lemma) at Math3ma
- [Yoneda lemma](https://en.wikipedia.org/wiki/Yoneda_lemma) at Wikipedia
- [Yoneda lemma](https://www.wikidata.org/wiki/Q320577) at Wikidata
