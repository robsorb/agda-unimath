# The Yoneda lemma for precategories

<pre class="Agda"><a id="47" class="Keyword">module</a> <a id="54" href="category-theory.yoneda-lemma-precategories.html" class="Module">category-theory.yoneda-lemma-precategories</a> <a id="97" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="category-theory.copresheaf-categories.html" class="Module">category-theory.copresheaf-categories</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="category-theory.functors-from-small-to-large-precategories.html" class="Module">category-theory.functors-from-small-to-large-precategories</a>
<a id="274" class="Keyword">open</a> <a id="279" class="Keyword">import</a> <a id="286" href="category-theory.natural-transformations-functors-from-small-to-large-precategories.html" class="Module">category-theory.natural-transformations-functors-from-small-to-large-precategories</a>
<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
<a id="411" class="Keyword">open</a> <a id="416" class="Keyword">import</a> <a id="423" href="category-theory.representable-functors-precategories.html" class="Module">category-theory.representable-functors-precategories</a>

<a id="477" class="Keyword">open</a> <a id="482" class="Keyword">import</a> <a id="489" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="536" class="Keyword">open</a> <a id="541" class="Keyword">import</a> <a id="548" href="foundation.category-of-sets.html" class="Module">foundation.category-of-sets</a>
<a id="576" class="Keyword">open</a> <a id="581" class="Keyword">import</a> <a id="588" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="620" class="Keyword">open</a> <a id="625" class="Keyword">import</a> <a id="632" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="656" class="Keyword">open</a> <a id="661" class="Keyword">import</a> <a id="668" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="703" class="Keyword">open</a> <a id="708" class="Keyword">import</a> <a id="715" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="741" class="Keyword">open</a> <a id="746" class="Keyword">import</a> <a id="753" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="775" class="Keyword">open</a> <a id="780" class="Keyword">import</a> <a id="787" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="813" class="Keyword">open</a> <a id="818" class="Keyword">import</a> <a id="825" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="845" class="Keyword">open</a> <a id="850" class="Keyword">import</a> <a id="857" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The
{{#concept "Yoneda lemma" Disambiguation="for set-level precategories" WD="Yoneda lemma" WDID=Q320577 Agda=lemma-yoneda-Precategory}}
states that, given a [precategory](category-theory.precategories.md) `C`, an
object `c`, and a [functor](category-theory.functors-precategories.md) `F` from
`C` to the [category of sets](foundation.category-of-sets.md)

```text
  F : C → Set,
```

there is an [equivalence](foundation-core.equivalences.md) between the
[set of natural transformations](category-theory.natural-transformations-functors-precategories.md)
from the functor
[represented](category-theory.representable-functors-precategories.md) by `c` to
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

<pre class="Agda"><a id="1977" class="Keyword">module</a> <a id="1984" href="category-theory.yoneda-lemma-precategories.html#1984" class="Module">_</a>
  <a id="1988" class="Symbol">{</a><a id="1989" href="category-theory.yoneda-lemma-precategories.html#1989" class="Bound">l1</a> <a id="1992" href="category-theory.yoneda-lemma-precategories.html#1992" class="Bound">l2</a> <a id="1995" href="category-theory.yoneda-lemma-precategories.html#1995" class="Bound">l3</a> <a id="1998" class="Symbol">:</a> <a id="2000" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2005" class="Symbol">}</a> <a id="2007" class="Symbol">(</a><a id="2008" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2010" class="Symbol">:</a> <a id="2012" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="2024" href="category-theory.yoneda-lemma-precategories.html#1989" class="Bound">l1</a> <a id="2027" href="category-theory.yoneda-lemma-precategories.html#1992" class="Bound">l2</a><a id="2029" class="Symbol">)</a> <a id="2031" class="Symbol">(</a><a id="2032" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a> <a id="2034" class="Symbol">:</a> <a id="2036" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="2052" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a><a id="2053" class="Symbol">)</a>
  <a id="2057" class="Symbol">(</a><a id="2058" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="2060" class="Symbol">:</a> <a id="2062" href="category-theory.copresheaf-categories.html#3237" class="Function">copresheaf-Precategory</a> <a id="2085" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2087" href="category-theory.yoneda-lemma-precategories.html#1995" class="Bound">l3</a><a id="2089" class="Symbol">)</a>
  <a id="2093" class="Keyword">where</a>

  <a id="2102" href="category-theory.yoneda-lemma-precategories.html#2102" class="Function">map-yoneda-Precategory</a> <a id="2125" class="Symbol">:</a>
    <a id="2131" href="category-theory.copresheaf-categories.html#5182" class="Function">hom-copresheaf-Precategory</a> <a id="2158" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2160" class="Symbol">(</a><a id="2161" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="2195" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2197" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="2198" class="Symbol">)</a> <a id="2200" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="2202" class="Symbol">→</a>
    <a id="2208" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="2239" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2241" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="2243" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a>
  <a id="2247" href="category-theory.yoneda-lemma-precategories.html#2102" class="Function">map-yoneda-Precategory</a> <a id="2270" href="category-theory.yoneda-lemma-precategories.html#2270" class="Bound">σ</a> <a id="2272" class="Symbol">=</a>
    <a id="2278" href="category-theory.natural-transformations-functors-from-small-to-large-precategories.html#2463" class="Function">hom-natural-transformation-Small-Large-Precategory</a>
      <a id="2335" class="Symbol">(</a> <a id="2337" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a><a id="2338" class="Symbol">)</a>
      <a id="2346" class="Symbol">(</a> <a id="2348" href="foundation.category-of-sets.html#2036" class="Function">Set-Large-Precategory</a><a id="2369" class="Symbol">)</a>
      <a id="2377" class="Symbol">(</a> <a id="2379" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="2413" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2415" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="2416" class="Symbol">)</a>
      <a id="2424" class="Symbol">(</a> <a id="2426" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a><a id="2427" class="Symbol">)</a>
      <a id="2435" class="Symbol">(</a> <a id="2437" href="category-theory.yoneda-lemma-precategories.html#2270" class="Bound">σ</a><a id="2438" class="Symbol">)</a>
      <a id="2446" class="Symbol">(</a> <a id="2448" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="2449" class="Symbol">)</a>
      <a id="2457" class="Symbol">(</a> <a id="2459" href="category-theory.precategories.html#6934" class="Function">id-hom-Precategory</a> <a id="2478" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a><a id="2479" class="Symbol">)</a>
</pre>
The inverse to the Yoneda map:

<pre class="Agda">  <a id="2528" href="category-theory.yoneda-lemma-precategories.html#2528" class="Function">hom-family-extension-yoneda-Precategory</a> <a id="2568" class="Symbol">:</a>
    <a id="2574" class="Symbol">(</a><a id="2575" href="category-theory.yoneda-lemma-precategories.html#2575" class="Bound">u</a> <a id="2577" class="Symbol">:</a> <a id="2579" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="2610" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2612" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="2614" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="2615" class="Symbol">)</a> <a id="2617" class="Symbol">→</a>
    <a id="2623" href="category-theory.natural-transformations-functors-from-small-to-large-precategories.html#1569" class="Function">hom-family-functor-Small-Large-Precategory</a>
      <a id="2672" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2674" href="foundation.category-of-sets.html#2036" class="Function">Set-Large-Precategory</a> <a id="2696" class="Symbol">(</a><a id="2697" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="2731" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2733" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="2734" class="Symbol">)</a> <a id="2736" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a>
  <a id="2740" href="category-theory.yoneda-lemma-precategories.html#2528" class="Function">hom-family-extension-yoneda-Precategory</a> <a id="2780" href="category-theory.yoneda-lemma-precategories.html#2780" class="Bound">u</a> <a id="2782" href="category-theory.yoneda-lemma-precategories.html#2782" class="Bound">x</a> <a id="2784" href="category-theory.yoneda-lemma-precategories.html#2784" class="Bound">f</a> <a id="2786" class="Symbol">=</a>
    <a id="2792" href="category-theory.functors-from-small-to-large-precategories.html#3497" class="Function">hom-functor-Small-Large-Precategory</a> <a id="2828" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2830" href="foundation.category-of-sets.html#2036" class="Function">Set-Large-Precategory</a> <a id="2852" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="2854" href="category-theory.yoneda-lemma-precategories.html#2784" class="Bound">f</a> <a id="2856" href="category-theory.yoneda-lemma-precategories.html#2780" class="Bound">u</a>

  <a id="2861" href="category-theory.yoneda-lemma-precategories.html#2861" class="Function">naturality-extension-yoneda-Precategory</a> <a id="2901" class="Symbol">:</a>
    <a id="2907" class="Symbol">(</a><a id="2908" href="category-theory.yoneda-lemma-precategories.html#2908" class="Bound">u</a> <a id="2910" class="Symbol">:</a> <a id="2912" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="2943" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="2945" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="2947" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="2948" class="Symbol">)</a> <a id="2950" class="Symbol">→</a>
    <a id="2956" href="category-theory.natural-transformations-functors-from-small-to-large-precategories.html#1831" class="Function">is-natural-transformation-Small-Large-Precategory</a>
      <a id="3012" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="3014" href="foundation.category-of-sets.html#2036" class="Function">Set-Large-Precategory</a> <a id="3036" class="Symbol">(</a><a id="3037" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="3071" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="3073" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="3074" class="Symbol">)</a> <a id="3076" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a>
      <a id="3084" class="Symbol">(</a> <a id="3086" href="category-theory.yoneda-lemma-precategories.html#2528" class="Function">hom-family-extension-yoneda-Precategory</a> <a id="3126" href="category-theory.yoneda-lemma-precategories.html#2908" class="Bound">u</a><a id="3127" class="Symbol">)</a>
  <a id="3131" href="category-theory.yoneda-lemma-precategories.html#2861" class="Function">naturality-extension-yoneda-Precategory</a> <a id="3171" href="category-theory.yoneda-lemma-precategories.html#3171" class="Bound">u</a> <a id="3173" href="category-theory.yoneda-lemma-precategories.html#3173" class="Bound">g</a> <a id="3175" class="Symbol">=</a>
    <a id="3181" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a>
      <a id="3195" class="Symbol">(</a> <a id="3197" class="Symbol">λ</a> <a id="3199" href="category-theory.yoneda-lemma-precategories.html#3199" class="Bound">f</a> <a id="3201" class="Symbol">→</a>
        <a id="3211" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a>
          <a id="3229" class="Symbol">(</a> <a id="3231" href="foundation-core.identity-types.html#6358" class="Function">inv</a>
            <a id="3247" class="Symbol">(</a> <a id="3249" href="category-theory.functors-from-small-to-large-precategories.html#4283" class="Function">preserves-comp-functor-Small-Large-Precategory</a>
                <a id="3312" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="3314" href="foundation.category-of-sets.html#2036" class="Function">Set-Large-Precategory</a> <a id="3336" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="3338" href="category-theory.yoneda-lemma-precategories.html#3173" class="Bound">g</a> <a id="3340" href="category-theory.yoneda-lemma-precategories.html#3199" class="Bound">f</a><a id="3341" class="Symbol">))</a>
          <a id="3354" class="Symbol">(</a> <a id="3356" href="category-theory.yoneda-lemma-precategories.html#3171" class="Bound">u</a><a id="3357" class="Symbol">))</a>

  <a id="3363" href="category-theory.yoneda-lemma-precategories.html#3363" class="Function">extension-yoneda-Precategory</a> <a id="3392" class="Symbol">:</a>
    <a id="3398" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="3429" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="3431" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="3433" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a> <a id="3435" class="Symbol">→</a>
    <a id="3441" href="category-theory.copresheaf-categories.html#5182" class="Function">hom-copresheaf-Precategory</a> <a id="3468" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="3470" class="Symbol">(</a><a id="3471" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="3505" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="3507" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="3508" class="Symbol">)</a> <a id="3510" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a>
  <a id="3514" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3518" class="Symbol">(</a><a id="3519" href="category-theory.yoneda-lemma-precategories.html#3363" class="Function">extension-yoneda-Precategory</a> <a id="3548" href="category-theory.yoneda-lemma-precategories.html#3548" class="Bound">u</a><a id="3549" class="Symbol">)</a> <a id="3551" class="Symbol">=</a>
    <a id="3557" href="category-theory.yoneda-lemma-precategories.html#2528" class="Function">hom-family-extension-yoneda-Precategory</a> <a id="3597" href="category-theory.yoneda-lemma-precategories.html#3548" class="Bound">u</a>
  <a id="3601" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3605" class="Symbol">(</a><a id="3606" href="category-theory.yoneda-lemma-precategories.html#3363" class="Function">extension-yoneda-Precategory</a> <a id="3635" href="category-theory.yoneda-lemma-precategories.html#3635" class="Bound">u</a><a id="3636" class="Symbol">)</a> <a id="3638" class="Symbol">=</a>
    <a id="3644" href="category-theory.yoneda-lemma-precategories.html#2861" class="Function">naturality-extension-yoneda-Precategory</a> <a id="3684" href="category-theory.yoneda-lemma-precategories.html#3635" class="Bound">u</a>
</pre>
The inverse is an inverse:

<pre class="Agda">  <a id="3729" href="category-theory.yoneda-lemma-precategories.html#3729" class="Function">is-section-extension-yoneda-Precategory</a> <a id="3769" class="Symbol">:</a>
    <a id="3775" class="Symbol">(</a> <a id="3777" href="category-theory.yoneda-lemma-precategories.html#2102" class="Function">map-yoneda-Precategory</a> <a id="3800" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
      <a id="3808" href="category-theory.yoneda-lemma-precategories.html#3363" class="Function">extension-yoneda-Precategory</a><a id="3836" class="Symbol">)</a> <a id="3838" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="3844" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="3849" href="category-theory.yoneda-lemma-precategories.html#3729" class="Function">is-section-extension-yoneda-Precategory</a> <a id="3889" class="Symbol">=</a>
    <a id="3895" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a>
      <a id="3909" class="Symbol">(</a> <a id="3911" href="category-theory.functors-from-small-to-large-precategories.html#4843" class="Function">preserves-id-functor-Small-Large-Precategory</a>
          <a id="3966" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="3968" href="foundation.category-of-sets.html#2036" class="Function">Set-Large-Precategory</a> <a id="3990" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="3992" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="3993" class="Symbol">)</a>

  <a id="3998" href="category-theory.yoneda-lemma-precategories.html#3998" class="Function">is-retraction-extension-yoneda-Precategory</a> <a id="4041" class="Symbol">:</a>
    <a id="4047" class="Symbol">(</a> <a id="4049" href="category-theory.yoneda-lemma-precategories.html#3363" class="Function">extension-yoneda-Precategory</a> <a id="4078" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
      <a id="4086" href="category-theory.yoneda-lemma-precategories.html#2102" class="Function">map-yoneda-Precategory</a><a id="4108" class="Symbol">)</a> <a id="4110" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="4116" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="4121" href="category-theory.yoneda-lemma-precategories.html#3998" class="Function">is-retraction-extension-yoneda-Precategory</a> <a id="4164" href="category-theory.yoneda-lemma-precategories.html#4164" class="Bound">σ</a> <a id="4166" class="Symbol">=</a>
    <a id="4172" href="foundation-core.subtypes.html#3976" class="Function">eq-type-subtype</a>
      <a id="4194" class="Symbol">(</a> <a id="4196" href="category-theory.natural-transformations-functors-from-small-to-large-precategories.html#5417" class="Function">is-natural-transformation-prop-Small-Large-Precategory</a>
        <a id="4259" class="Symbol">(</a> <a id="4261" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a><a id="4262" class="Symbol">)</a> <a id="4264" href="foundation.category-of-sets.html#2036" class="Function">Set-Large-Precategory</a> <a id="4286" class="Symbol">(</a><a id="4287" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="4321" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="4323" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="4324" class="Symbol">)</a> <a id="4326" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a><a id="4327" class="Symbol">)</a>
      <a id="4335" class="Symbol">(</a> <a id="4337" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a>
        <a id="4353" class="Symbol">(</a> <a id="4355" class="Symbol">λ</a> <a id="4357" href="category-theory.yoneda-lemma-precategories.html#4357" class="Bound">x</a> <a id="4359" class="Symbol">→</a>
          <a id="4371" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a>
            <a id="4391" class="Symbol">(</a> <a id="4393" class="Symbol">λ</a> <a id="4395" href="category-theory.yoneda-lemma-precategories.html#4395" class="Bound">f</a> <a id="4397" class="Symbol">→</a>
              <a id="4413" class="Symbol">(</a> <a id="4415" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a>
                <a id="4439" class="Symbol">(</a> <a id="4441" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4445" href="category-theory.yoneda-lemma-precategories.html#4164" class="Bound">σ</a> <a id="4447" href="category-theory.yoneda-lemma-precategories.html#4395" class="Bound">f</a><a id="4448" class="Symbol">)</a>
                <a id="4466" class="Symbol">(</a> <a id="4468" href="category-theory.precategories.html#6934" class="Function">id-hom-Precategory</a> <a id="4487" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a><a id="4488" class="Symbol">))</a> <a id="4491" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
              <a id="4507" class="Symbol">(</a> <a id="4509" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4512" class="Symbol">(</a><a id="4513" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4517" href="category-theory.yoneda-lemma-precategories.html#4164" class="Bound">σ</a> <a id="4519" href="category-theory.yoneda-lemma-precategories.html#4357" class="Bound">x</a><a id="4520" class="Symbol">)</a> <a id="4522" class="Symbol">(</a><a id="4523" href="category-theory.precategories.html#7322" class="Function">right-unit-law-comp-hom-Precategory</a> <a id="4559" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="4561" href="category-theory.yoneda-lemma-precategories.html#4395" class="Bound">f</a><a id="4562" class="Symbol">)))))</a>

  <a id="4571" href="category-theory.yoneda-lemma-precategories.html#4571" class="Function">lemma-yoneda-Precategory</a> <a id="4596" class="Symbol">:</a> <a id="4598" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="4607" href="category-theory.yoneda-lemma-precategories.html#2102" class="Function">map-yoneda-Precategory</a>
  <a id="4632" href="category-theory.yoneda-lemma-precategories.html#4571" class="Function">lemma-yoneda-Precategory</a> <a id="4657" class="Symbol">=</a>
    <a id="4663" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
      <a id="4692" class="Symbol">(</a> <a id="4694" href="category-theory.yoneda-lemma-precategories.html#3363" class="Function">extension-yoneda-Precategory</a><a id="4722" class="Symbol">)</a>
      <a id="4730" class="Symbol">(</a> <a id="4732" href="category-theory.yoneda-lemma-precategories.html#3729" class="Function">is-section-extension-yoneda-Precategory</a><a id="4771" class="Symbol">)</a>
      <a id="4779" class="Symbol">(</a> <a id="4781" href="category-theory.yoneda-lemma-precategories.html#3998" class="Function">is-retraction-extension-yoneda-Precategory</a><a id="4823" class="Symbol">)</a>

  <a id="4828" href="category-theory.yoneda-lemma-precategories.html#4828" class="Function">equiv-lemma-yoneda-Precategory</a> <a id="4859" class="Symbol">:</a>
    <a id="4865" href="category-theory.copresheaf-categories.html#5182" class="Function">hom-copresheaf-Precategory</a> <a id="4892" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="4894" class="Symbol">(</a><a id="4895" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="4929" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="4931" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a><a id="4932" class="Symbol">)</a> <a id="4934" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="4936" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="4942" href="category-theory.copresheaf-categories.html#3647" class="Function">element-copresheaf-Precategory</a> <a id="4973" href="category-theory.yoneda-lemma-precategories.html#2008" class="Bound">C</a> <a id="4975" href="category-theory.yoneda-lemma-precategories.html#2058" class="Bound">F</a> <a id="4977" href="category-theory.yoneda-lemma-precategories.html#2032" class="Bound">c</a>
  <a id="4981" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4985" href="category-theory.yoneda-lemma-precategories.html#4828" class="Function">equiv-lemma-yoneda-Precategory</a> <a id="5016" class="Symbol">=</a> <a id="5018" href="category-theory.yoneda-lemma-precategories.html#2102" class="Function">map-yoneda-Precategory</a>
  <a id="5043" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5047" href="category-theory.yoneda-lemma-precategories.html#4828" class="Function">equiv-lemma-yoneda-Precategory</a> <a id="5078" class="Symbol">=</a> <a id="5080" href="category-theory.yoneda-lemma-precategories.html#4571" class="Function">lemma-yoneda-Precategory</a>
</pre>
## Corollaries

### The Yoneda lemma for representable functors

An important special-case of the Yoneda lemma is when `F` is itself a
representable functor `F = Hom(-, d)`.

<pre class="Agda"><a id="5293" class="Keyword">module</a> <a id="5300" href="category-theory.yoneda-lemma-precategories.html#5300" class="Module">_</a>
  <a id="5304" class="Symbol">{</a><a id="5305" href="category-theory.yoneda-lemma-precategories.html#5305" class="Bound">l1</a> <a id="5308" href="category-theory.yoneda-lemma-precategories.html#5308" class="Bound">l2</a> <a id="5311" class="Symbol">:</a> <a id="5313" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5318" class="Symbol">}</a> <a id="5320" class="Symbol">(</a><a id="5321" href="category-theory.yoneda-lemma-precategories.html#5321" class="Bound">C</a> <a id="5323" class="Symbol">:</a> <a id="5325" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="5337" href="category-theory.yoneda-lemma-precategories.html#5305" class="Bound">l1</a> <a id="5340" href="category-theory.yoneda-lemma-precategories.html#5308" class="Bound">l2</a><a id="5342" class="Symbol">)</a> <a id="5344" class="Symbol">(</a><a id="5345" href="category-theory.yoneda-lemma-precategories.html#5345" class="Bound">c</a> <a id="5347" href="category-theory.yoneda-lemma-precategories.html#5347" class="Bound">d</a> <a id="5349" class="Symbol">:</a> <a id="5351" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="5367" href="category-theory.yoneda-lemma-precategories.html#5321" class="Bound">C</a><a id="5368" class="Symbol">)</a>
  <a id="5372" class="Keyword">where</a>

  <a id="5381" href="category-theory.yoneda-lemma-precategories.html#5381" class="Function">equiv-lemma-yoneda-representable-Precategory</a> <a id="5426" class="Symbol">:</a>
    <a id="5432" href="category-theory.copresheaf-categories.html#5182" class="Function">hom-copresheaf-Precategory</a> <a id="5459" href="category-theory.yoneda-lemma-precategories.html#5321" class="Bound">C</a>
      <a id="5467" class="Symbol">(</a> <a id="5469" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="5503" href="category-theory.yoneda-lemma-precategories.html#5321" class="Bound">C</a> <a id="5505" href="category-theory.yoneda-lemma-precategories.html#5345" class="Bound">c</a><a id="5506" class="Symbol">)</a>
      <a id="5514" class="Symbol">(</a> <a id="5516" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="5550" href="category-theory.yoneda-lemma-precategories.html#5321" class="Bound">C</a> <a id="5552" href="category-theory.yoneda-lemma-precategories.html#5347" class="Bound">d</a><a id="5553" class="Symbol">)</a> <a id="5555" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="5561" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="5577" href="category-theory.yoneda-lemma-precategories.html#5321" class="Bound">C</a> <a id="5579" href="category-theory.yoneda-lemma-precategories.html#5347" class="Bound">d</a> <a id="5581" href="category-theory.yoneda-lemma-precategories.html#5345" class="Bound">c</a>
  <a id="5585" href="category-theory.yoneda-lemma-precategories.html#5381" class="Function">equiv-lemma-yoneda-representable-Precategory</a> <a id="5630" class="Symbol">=</a>
    <a id="5636" href="category-theory.yoneda-lemma-precategories.html#4828" class="Function">equiv-lemma-yoneda-Precategory</a> <a id="5667" href="category-theory.yoneda-lemma-precategories.html#5321" class="Bound">C</a> <a id="5669" href="category-theory.yoneda-lemma-precategories.html#5345" class="Bound">c</a> <a id="5671" class="Symbol">(</a><a id="5672" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="5706" href="category-theory.yoneda-lemma-precategories.html#5321" class="Bound">C</a> <a id="5708" href="category-theory.yoneda-lemma-precategories.html#5347" class="Bound">d</a><a id="5709" class="Symbol">)</a>
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
