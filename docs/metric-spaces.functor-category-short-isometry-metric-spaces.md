# The inclusion of isometries into the category of metric spaces and short maps

<pre class="Agda"><a id="90" class="Keyword">module</a> <a id="97" href="metric-spaces.functor-category-short-isometry-metric-spaces.html" class="Module">metric-spaces.functor-category-short-isometry-metric-spaces</a> <a id="157" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="213" class="Keyword">open</a> <a id="218" class="Keyword">import</a> <a id="225" href="category-theory.conservative-functors-precategories.html" class="Module">category-theory.conservative-functors-precategories</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="category-theory.faithful-functors-precategories.html" class="Module">category-theory.faithful-functors-precategories</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="category-theory.isomorphisms-in-precategories.html" class="Module">category-theory.isomorphisms-in-precategories</a>
<a id="446" class="Keyword">open</a> <a id="451" class="Keyword">import</a> <a id="458" href="category-theory.maps-precategories.html" class="Module">category-theory.maps-precategories</a>
<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="category-theory.split-essentially-surjective-functors-precategories.html" class="Module">category-theory.split-essentially-surjective-functors-precategories</a>

<a id="616" class="Keyword">open</a> <a id="621" class="Keyword">import</a> <a id="628" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="660" class="Keyword">open</a> <a id="665" class="Keyword">import</a> <a id="672" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="696" class="Keyword">open</a> <a id="701" class="Keyword">import</a> <a id="708" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="743" class="Keyword">open</a> <a id="748" class="Keyword">import</a> <a id="755" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="804" class="Keyword">open</a> <a id="809" class="Keyword">import</a> <a id="816" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="838" class="Keyword">open</a> <a id="843" class="Keyword">import</a> <a id="850" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="876" class="Keyword">open</a> <a id="881" class="Keyword">import</a> <a id="888" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="916" class="Keyword">open</a> <a id="921" class="Keyword">import</a> <a id="928" href="metric-spaces.isometries-metric-spaces.html" class="Module">metric-spaces.isometries-metric-spaces</a>
<a id="967" class="Keyword">open</a> <a id="972" class="Keyword">import</a> <a id="979" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-isometries</a>
<a id="1037" class="Keyword">open</a> <a id="1042" class="Keyword">import</a> <a id="1049" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-short-functions</a>
<a id="1112" class="Keyword">open</a> <a id="1117" class="Keyword">import</a> <a id="1124" href="metric-spaces.short-functions-metric-spaces.html" class="Module">metric-spaces.short-functions-metric-spaces</a>
</pre>
</details>

## Idea

Because every [isometry](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is also
[short](metric-spaces.short-functions-metric-spaces.md), there's a
[functor](category-theory.functors-precategories.md) between the
[category of metric spaces and isometries](metric-spaces.category-of-metric-spaces-and-isometries.md)
to the
[category of metric spaces and short maps](metric-spaces.category-of-metric-spaces-and-short-functions.md).

Since this functor is the identity on objects, it is an equivalence on objects.
Moreover, since the map from isometry to short maps is an
[embedding](foundation.embeddings.md), this functor is
[faithful](category-theory.faithful-functors-precategories.md). Finally, because
short [isomorphisms](category-theory.isomorphisms-in-precategories.md) are
isometries, this functor is also
[conservative](category-theory.conservative-functors-precategories.md).

## Definition

### The functor between the category of metric spaces and isometries to the category of metric spaces and short maps

<pre class="Agda"><a id="2272" class="Keyword">module</a> <a id="2279" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2279" class="Module">_</a>
  <a id="2283" class="Symbol">(</a><a id="2284" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2284" class="Bound">l1</a> <a id="2287" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2287" class="Bound">l2</a> <a id="2290" class="Symbol">:</a> <a id="2292" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2297" class="Symbol">)</a>
  <a id="2301" class="Keyword">where</a>

  <a id="2310" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2310" class="Function">functor-short-isometry-Metric-Space</a> <a id="2346" class="Symbol">:</a>
    <a id="2352" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a>
      <a id="2378" class="Symbol">(</a><a id="2379" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a> <a id="2413" class="Symbol">{</a><a id="2414" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2284" class="Bound">l1</a><a id="2416" class="Symbol">}</a> <a id="2418" class="Symbol">{</a><a id="2419" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2287" class="Bound">l2</a><a id="2421" class="Symbol">})</a>
      <a id="2430" class="Symbol">(</a><a id="2431" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#1557" class="Function">precategory-short-function-Metric-Space</a> <a id="2471" class="Symbol">{</a><a id="2472" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2284" class="Bound">l1</a><a id="2474" class="Symbol">}</a> <a id="2476" class="Symbol">{</a><a id="2477" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2287" class="Bound">l2</a><a id="2479" class="Symbol">})</a>
  <a id="2484" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2488" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2310" class="Function">functor-short-isometry-Metric-Space</a> <a id="2524" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2524" class="Bound">A</a> <a id="2526" class="Symbol">=</a> <a id="2528" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2524" class="Bound">A</a>
  <a id="2532" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2536" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2310" class="Function">functor-short-isometry-Metric-Space</a> <a id="2572" class="Symbol">=</a>
    <a id="2578" class="Symbol">(</a> <a id="2580" class="Symbol">λ</a> <a id="2582" class="Symbol">{</a><a id="2583" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2583" class="Bound">A</a> <a id="2585" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2585" class="Bound">B</a><a id="2586" class="Symbol">}</a> <a id="2588" class="Symbol">→</a> <a id="2590" href="metric-spaces.short-functions-metric-spaces.html#9723" class="Function">short-isometry-Metric-Space</a> <a id="2618" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2583" class="Bound">A</a> <a id="2620" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2585" class="Bound">B</a><a id="2621" class="Symbol">)</a> <a id="2623" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="2629" class="Symbol">(</a> <a id="2631" class="Symbol">(</a> <a id="2633" class="Symbol">λ</a> <a id="2635" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2635" class="Bound">g</a> <a id="2637" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2637" class="Bound">f</a> <a id="2639" class="Symbol">→</a> <a id="2641" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="2645" class="Symbol">)</a> <a id="2647" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2649" class="Symbol">(</a> <a id="2651" class="Symbol">λ</a> <a id="2653" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2653" class="Bound">A</a> <a id="2655" class="Symbol">→</a> <a id="2657" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="2661" class="Symbol">))</a>
</pre>
## Properties

### The functor from isometries to short maps is an equivalence on objects

<pre class="Agda"><a id="2768" class="Keyword">module</a> <a id="2775" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2775" class="Module">_</a>
  <a id="2779" class="Symbol">(</a><a id="2780" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2780" class="Bound">l1</a> <a id="2783" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2783" class="Bound">l2</a> <a id="2786" class="Symbol">:</a> <a id="2788" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2793" class="Symbol">)</a>
  <a id="2797" class="Keyword">where</a>

  <a id="2806" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2806" class="Function">is-equiv-obj-functor-short-isometry-Metric-Space</a> <a id="2855" class="Symbol">:</a>
    <a id="2861" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a>
      <a id="2876" class="Symbol">(</a> <a id="2878" href="category-theory.functors-precategories.html#4132" class="Function">obj-functor-Precategory</a>
        <a id="2910" class="Symbol">(</a> <a id="2912" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a><a id="2945" class="Symbol">)</a>
        <a id="2955" class="Symbol">(</a> <a id="2957" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#1557" class="Function">precategory-short-function-Metric-Space</a><a id="2996" class="Symbol">)</a>
        <a id="3006" class="Symbol">(</a> <a id="3008" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2310" class="Function">functor-short-isometry-Metric-Space</a> <a id="3044" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2780" class="Bound">l1</a> <a id="3047" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2783" class="Bound">l2</a><a id="3049" class="Symbol">))</a>
  <a id="3054" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2806" class="Function">is-equiv-obj-functor-short-isometry-Metric-Space</a> <a id="3103" class="Symbol">=</a> <a id="3105" href="foundation-core.equivalences.html#3753" class="Function">is-equiv-id</a>
</pre>
### The functor from isometries to short maps is faithful

<pre class="Agda"><a id="3189" class="Keyword">module</a> <a id="3196" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3196" class="Module">_</a>
  <a id="3200" class="Symbol">(</a><a id="3201" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3201" class="Bound">l1</a> <a id="3204" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3204" class="Bound">l2</a> <a id="3207" class="Symbol">:</a> <a id="3209" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3214" class="Symbol">)</a>
  <a id="3218" class="Keyword">where</a>

  <a id="3227" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3227" class="Function">is-faithful-functor-short-isometry-Metric-Space</a> <a id="3275" class="Symbol">:</a>
    <a id="3281" href="category-theory.faithful-functors-precategories.html#1279" class="Function">is-faithful-functor-Precategory</a>
      <a id="3319" class="Symbol">(</a><a id="3320" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a><a id="3353" class="Symbol">)</a>
      <a id="3361" class="Symbol">(</a><a id="3362" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#1557" class="Function">precategory-short-function-Metric-Space</a><a id="3401" class="Symbol">)</a>
      <a id="3409" class="Symbol">(</a><a id="3410" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2310" class="Function">functor-short-isometry-Metric-Space</a> <a id="3446" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3201" class="Bound">l1</a> <a id="3449" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3204" class="Bound">l2</a><a id="3451" class="Symbol">)</a>
  <a id="3455" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3227" class="Function">is-faithful-functor-short-isometry-Metric-Space</a> <a id="3503" class="Symbol">=</a>
    <a id="3509" href="metric-spaces.short-functions-metric-spaces.html#9964" class="Function">is-emb-short-isometry-Metric-Space</a>
</pre>
### The functor from isometries to short maps is conservative

<pre class="Agda"><a id="3620" class="Keyword">module</a> <a id="3627" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3627" class="Module">_</a>
  <a id="3631" class="Symbol">(</a><a id="3632" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3632" class="Bound">l1</a> <a id="3635" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3635" class="Bound">l2</a> <a id="3638" class="Symbol">:</a> <a id="3640" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3645" class="Symbol">)</a>
  <a id="3649" class="Keyword">where</a>

  <a id="3658" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3658" class="Function">is-conservative-functor-short-isometry-Metric-Space</a> <a id="3710" class="Symbol">:</a>
    <a id="3716" href="category-theory.conservative-functors-precategories.html#1192" class="Function">is-conservative-functor-Precategory</a>
      <a id="3758" class="Symbol">(</a><a id="3759" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a><a id="3792" class="Symbol">)</a>
      <a id="3800" class="Symbol">(</a><a id="3801" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#1557" class="Function">precategory-short-function-Metric-Space</a><a id="3840" class="Symbol">)</a>
      <a id="3848" class="Symbol">(</a><a id="3849" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#2310" class="Function">functor-short-isometry-Metric-Space</a> <a id="3885" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3632" class="Bound">l1</a> <a id="3888" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3635" class="Bound">l2</a><a id="3890" class="Symbol">)</a>
  <a id="3894" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3658" class="Function">is-conservative-functor-short-isometry-Metric-Space</a> <a id="3946" class="Symbol">{</a><a id="3947" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3947" class="Bound">A</a><a id="3948" class="Symbol">}</a> <a id="3950" class="Symbol">{</a><a id="3951" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3951" class="Bound">B</a><a id="3952" class="Symbol">}</a> <a id="3954" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3954" class="Bound">f</a> <a id="3956" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3956" class="Bound">H</a> <a id="3958" class="Symbol">=</a>
    <a id="3964" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#2836" class="Function">is-iso-is-equiv-isometry-Metric-Space</a>
      <a id="4008" class="Symbol">(</a> <a id="4010" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3947" class="Bound">A</a><a id="4011" class="Symbol">)</a>
      <a id="4019" class="Symbol">(</a> <a id="4021" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3951" class="Bound">B</a><a id="4022" class="Symbol">)</a>
      <a id="4030" class="Symbol">(</a> <a id="4032" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3954" class="Bound">f</a><a id="4033" class="Symbol">)</a>
      <a id="4041" class="Symbol">(</a> <a id="4043" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#2306" class="Function">is-equiv-is-iso-short-function-Metric-Space</a>
        <a id="4095" class="Symbol">(</a> <a id="4097" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3947" class="Bound">A</a><a id="4098" class="Symbol">)</a>
        <a id="4108" class="Symbol">(</a> <a id="4110" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3951" class="Bound">B</a><a id="4111" class="Symbol">)</a>
        <a id="4121" class="Symbol">(</a> <a id="4123" href="metric-spaces.short-functions-metric-spaces.html#9723" class="Function">short-isometry-Metric-Space</a> <a id="4151" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3947" class="Bound">A</a> <a id="4153" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3951" class="Bound">B</a> <a id="4155" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3954" class="Bound">f</a><a id="4156" class="Symbol">)</a>
        <a id="4166" class="Symbol">(</a> <a id="4168" href="metric-spaces.functor-category-short-isometry-metric-spaces.html#3956" class="Bound">H</a><a id="4169" class="Symbol">))</a>
</pre>