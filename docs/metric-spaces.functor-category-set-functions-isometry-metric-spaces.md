# The functor from the precategory of metric spaces and isometries to the precategory of sets

<pre class="Agda"><a id="104" class="Keyword">module</a> <a id="111" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html" class="Module">metric-spaces.functor-category-set-functions-isometry-metric-spaces</a> <a id="179" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="category-theory.conservative-functors-precategories.html" class="Module">category-theory.conservative-functors-precategories</a>
<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="category-theory.faithful-functors-precategories.html" class="Module">category-theory.faithful-functors-precategories</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="410" class="Keyword">open</a> <a id="415" class="Keyword">import</a> <a id="422" href="category-theory.isomorphisms-in-precategories.html" class="Module">category-theory.isomorphisms-in-precategories</a>
<a id="468" class="Keyword">open</a> <a id="473" class="Keyword">import</a> <a id="480" href="category-theory.maps-precategories.html" class="Module">category-theory.maps-precategories</a>
<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="558" class="Keyword">open</a> <a id="563" class="Keyword">import</a> <a id="570" href="foundation.category-of-sets.html" class="Module">foundation.category-of-sets</a>
<a id="598" class="Keyword">open</a> <a id="603" class="Keyword">import</a> <a id="610" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="642" class="Keyword">open</a> <a id="647" class="Keyword">import</a> <a id="654" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="678" class="Keyword">open</a> <a id="683" class="Keyword">import</a> <a id="690" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="725" class="Keyword">open</a> <a id="730" class="Keyword">import</a> <a id="737" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="763" class="Keyword">open</a> <a id="768" class="Keyword">import</a> <a id="775" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="824" class="Keyword">open</a> <a id="829" class="Keyword">import</a> <a id="836" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="858" class="Keyword">open</a> <a id="863" class="Keyword">import</a> <a id="870" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="896" class="Keyword">open</a> <a id="901" class="Keyword">import</a> <a id="908" href="foundation.isomorphisms-of-sets.html" class="Module">foundation.isomorphisms-of-sets</a>
<a id="940" class="Keyword">open</a> <a id="945" class="Keyword">import</a> <a id="952" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="972" class="Keyword">open</a> <a id="977" class="Keyword">import</a> <a id="984" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="1012" class="Keyword">open</a> <a id="1017" class="Keyword">import</a> <a id="1024" href="metric-spaces.category-of-metric-spaces-and-isometries.html" class="Module">metric-spaces.category-of-metric-spaces-and-isometries</a>
<a id="1079" class="Keyword">open</a> <a id="1084" class="Keyword">import</a> <a id="1091" href="metric-spaces.isometries-metric-spaces.html" class="Module">metric-spaces.isometries-metric-spaces</a>
<a id="1130" class="Keyword">open</a> <a id="1135" class="Keyword">import</a> <a id="1142" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="1170" class="Keyword">open</a> <a id="1175" class="Keyword">import</a> <a id="1182" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-isometries</a>
</pre>
</details>

## Idea

Because carrier types of [metric spaces](metric-spaces.metric-spaces.md) are
[sets](foundation.sets.md), there's a forgetful
[functor](category-theory.functors-precategories.md) from the
[category of metric spaces and isometries](metric-spaces.category-of-metric-spaces-and-isometries.md)
to the [category of sets](foundation.category-of-sets.md). Moreover, since the
map from an isometry to its carrier map is an
[embedding](foundation.embeddings.md), this functor is
[faithful](category-theory.faithful-functors-precategories.md). Finally, because
the inverse of an isometric equivalence is an isometry, this functor is also
[conservative](category-theory.conservative-functors-precategories.md).

## Definition

### The forgetful functor from metric spaces and isometries to sets and functions

<pre class="Agda"><a id="2072" class="Keyword">module</a> <a id="2079" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2079" class="Module">_</a>
  <a id="2083" class="Symbol">(</a><a id="2084" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2084" class="Bound">l1</a> <a id="2087" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2087" class="Bound">l2</a> <a id="2090" class="Symbol">:</a> <a id="2092" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2097" class="Symbol">)</a>
  <a id="2101" class="Keyword">where</a>

  <a id="2110" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2110" class="Function">functor-set-functions-isometry-Metric-Space</a> <a id="2154" class="Symbol">:</a>
    <a id="2160" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a>
      <a id="2186" class="Symbol">(</a><a id="2187" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a> <a id="2221" class="Symbol">{</a><a id="2222" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2084" class="Bound">l1</a><a id="2224" class="Symbol">}</a> <a id="2226" class="Symbol">{</a><a id="2227" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2087" class="Bound">l2</a><a id="2229" class="Symbol">})</a>
      <a id="2238" class="Symbol">(</a><a id="2239" href="foundation.category-of-sets.html#3605" class="Function">Set-Precategory</a> <a id="2255" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2084" class="Bound">l1</a><a id="2257" class="Symbol">)</a>
  <a id="2261" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2265" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2110" class="Function">functor-set-functions-isometry-Metric-Space</a> <a id="2309" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2309" class="Bound">A</a> <a id="2311" class="Symbol">=</a>
      <a id="2319" href="metric-spaces.metric-spaces.html#11131" class="Function">set-Metric-Space</a> <a id="2336" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2309" class="Bound">A</a>
  <a id="2340" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2344" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2110" class="Function">functor-set-functions-isometry-Metric-Space</a> <a id="2388" class="Symbol">=</a>
    <a id="2394" class="Symbol">(</a> <a id="2396" class="Symbol">λ</a> <a id="2398" class="Symbol">{</a><a id="2399" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2399" class="Bound">A</a> <a id="2401" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2401" class="Bound">B</a><a id="2402" class="Symbol">}</a> <a id="2404" class="Symbol">→</a> <a id="2406" href="metric-spaces.isometries-metric-spaces.html#3174" class="Function">map-isometry-Metric-Space</a> <a id="2432" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2399" class="Bound">A</a> <a id="2434" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2401" class="Bound">B</a><a id="2435" class="Symbol">)</a> <a id="2437" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="2443" class="Symbol">(</a> <a id="2445" class="Symbol">(</a> <a id="2447" class="Symbol">λ</a> <a id="2449" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2449" class="Bound">g</a> <a id="2451" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2451" class="Bound">f</a> <a id="2453" class="Symbol">→</a> <a id="2455" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="2459" class="Symbol">)</a> <a id="2461" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2463" class="Symbol">(</a> <a id="2465" class="Symbol">λ</a> <a id="2467" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2467" class="Bound">A</a> <a id="2469" class="Symbol">→</a> <a id="2471" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="2475" class="Symbol">))</a>
</pre>
## Properties

### The functor from metric spaces and isometries to sets and functions is faithful

<pre class="Agda"><a id="2591" class="Keyword">module</a> <a id="2598" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2598" class="Module">_</a>
  <a id="2602" class="Symbol">(</a><a id="2603" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2603" class="Bound">l1</a> <a id="2606" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2606" class="Bound">l2</a> <a id="2609" class="Symbol">:</a> <a id="2611" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2616" class="Symbol">)</a>
  <a id="2620" class="Keyword">where</a>

  <a id="2629" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2629" class="Function">is-faithful-functor-set-functions-isometry-Metric-Space</a> <a id="2685" class="Symbol">:</a>
    <a id="2691" href="category-theory.faithful-functors-precategories.html#1279" class="Function">is-faithful-functor-Precategory</a>
      <a id="2729" class="Symbol">(</a><a id="2730" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a><a id="2763" class="Symbol">)</a>
      <a id="2771" class="Symbol">(</a><a id="2772" href="foundation.category-of-sets.html#3605" class="Function">Set-Precategory</a> <a id="2788" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2603" class="Bound">l1</a><a id="2790" class="Symbol">)</a>
      <a id="2798" class="Symbol">(</a><a id="2799" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2110" class="Function">functor-set-functions-isometry-Metric-Space</a> <a id="2843" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2603" class="Bound">l1</a> <a id="2846" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2606" class="Bound">l2</a><a id="2848" class="Symbol">)</a>
  <a id="2852" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2629" class="Function">is-faithful-functor-set-functions-isometry-Metric-Space</a> <a id="2908" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2908" class="Bound">A</a> <a id="2910" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2910" class="Bound">B</a> <a id="2912" class="Symbol">=</a>
    <a id="2918" href="foundation-core.subtypes.html#4868" class="Function">is-emb-inclusion-subtype</a> <a id="2943" class="Symbol">(</a><a id="2944" href="metric-spaces.isometries-metric-spaces.html#1943" class="Function">is-isometry-prop-Metric-Space</a> <a id="2974" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2908" class="Bound">A</a> <a id="2976" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2910" class="Bound">B</a><a id="2977" class="Symbol">)</a>
</pre>
### The functor from metric spaces and isometries to sets and functions is conservative

<pre class="Agda"><a id="3081" class="Keyword">module</a> <a id="3088" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3088" class="Module">_</a>
  <a id="3092" class="Symbol">(</a><a id="3093" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3093" class="Bound">l1</a> <a id="3096" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3096" class="Bound">l2</a> <a id="3099" class="Symbol">:</a> <a id="3101" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3106" class="Symbol">)</a>
  <a id="3110" class="Keyword">where</a>

  <a id="3119" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3119" class="Function">is-conservative-functor-set-functions-isometry-Metric-Space</a> <a id="3179" class="Symbol">:</a>
    <a id="3185" href="category-theory.conservative-functors-precategories.html#1192" class="Function">is-conservative-functor-Precategory</a>
      <a id="3227" class="Symbol">(</a><a id="3228" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a><a id="3261" class="Symbol">)</a>
      <a id="3269" class="Symbol">(</a><a id="3270" href="foundation.category-of-sets.html#3605" class="Function">Set-Precategory</a> <a id="3286" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3093" class="Bound">l1</a><a id="3288" class="Symbol">)</a>
      <a id="3296" class="Symbol">(</a><a id="3297" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#2110" class="Function">functor-set-functions-isometry-Metric-Space</a> <a id="3341" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3093" class="Bound">l1</a> <a id="3344" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3096" class="Bound">l2</a><a id="3346" class="Symbol">)</a>
  <a id="3350" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3119" class="Function">is-conservative-functor-set-functions-isometry-Metric-Space</a>
    <a id="3414" class="Symbol">{</a><a id="3415" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3415" class="Bound">A</a><a id="3416" class="Symbol">}</a> <a id="3418" class="Symbol">{</a><a id="3419" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3419" class="Bound">B</a><a id="3420" class="Symbol">}</a> <a id="3422" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3422" class="Bound">f</a> <a id="3424" class="Symbol">=</a>
    <a id="3430" class="Symbol">(</a> <a id="3432" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#2836" class="Function">is-iso-is-equiv-isometry-Metric-Space</a> <a id="3470" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3415" class="Bound">A</a> <a id="3472" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3419" class="Bound">B</a> <a id="3474" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3422" class="Bound">f</a><a id="3475" class="Symbol">)</a> <a id="3477" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
    <a id="3483" class="Symbol">(</a> <a id="3485" href="foundation.isomorphisms-of-sets.html#2042" class="Function">is-equiv-is-iso-Set</a>
      <a id="3511" class="Symbol">(</a> <a id="3513" href="metric-spaces.metric-spaces.html#11131" class="Function">set-Metric-Space</a> <a id="3530" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3415" class="Bound">A</a><a id="3531" class="Symbol">)</a>
      <a id="3539" class="Symbol">(</a> <a id="3541" href="metric-spaces.metric-spaces.html#11131" class="Function">set-Metric-Space</a> <a id="3558" href="metric-spaces.functor-category-set-functions-isometry-metric-spaces.html#3419" class="Bound">B</a><a id="3559" class="Symbol">))</a>
</pre>