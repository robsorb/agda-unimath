# Zigzags between sequential diagrams

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.zigzags-sequential-diagrams</a> <a id="109" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="165" class="Keyword">open</a> <a id="170" class="Keyword">import</a> <a id="177" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="foundation.commuting-squares-of-homotopies.html" class="Module">foundation.commuting-squares-of-homotopies</a>
<a id="321" class="Keyword">open</a> <a id="326" class="Keyword">import</a> <a id="333" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="foundation.commuting-triangles-of-maps.html" class="Module">foundation.commuting-triangles-of-maps</a>
<a id="421" class="Keyword">open</a> <a id="426" class="Keyword">import</a> <a id="433" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="465" class="Keyword">open</a> <a id="470" class="Keyword">import</a> <a id="477" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="501" class="Keyword">open</a> <a id="506" class="Keyword">import</a> <a id="513" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="539" class="Keyword">open</a> <a id="544" class="Keyword">import</a> <a id="551" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="573" class="Keyword">open</a> <a id="578" class="Keyword">import</a> <a id="585" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="608" class="Keyword">open</a> <a id="613" class="Keyword">import</a> <a id="620" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="647" class="Keyword">open</a> <a id="652" class="Keyword">import</a> <a id="659" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="705" class="Keyword">open</a> <a id="710" class="Keyword">import</a> <a id="717" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.cocones-under-sequential-diagrams</a>
<a id="777" class="Keyword">open</a> <a id="782" class="Keyword">import</a> <a id="789" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html" class="Module">synthetic-homotopy-theory.functoriality-sequential-colimits</a>
<a id="849" class="Keyword">open</a> <a id="854" class="Keyword">import</a> <a id="861" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.morphisms-sequential-diagrams</a>
<a id="917" class="Keyword">open</a> <a id="922" class="Keyword">import</a> <a id="929" href="synthetic-homotopy-theory.sequential-diagrams.html" class="Module">synthetic-homotopy-theory.sequential-diagrams</a>
<a id="975" class="Keyword">open</a> <a id="980" class="Keyword">import</a> <a id="987" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.shifts-sequential-diagrams</a>
<a id="1040" class="Keyword">open</a> <a id="1045" class="Keyword">import</a> <a id="1052" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html" class="Module">synthetic-homotopy-theory.universal-property-sequential-colimits</a>
</pre>
</details>

## Idea

A
{{#concept "zigzag" Disambiguation="sequential diagrams" Agda=zigzag-sequential-diagram}}
between [sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)` and `(B, b)` is a pair of families of maps

```text
  fₙ : Aₙ → Bₙ
  gₙ : Bₙ → Aₙ₊₁
```

and [coherences](foundation-core.commuting-triangles-of-maps.md) between them,
such that they fit in the following diagram:

```text
       a₀        a₁
  A₀ -----> A₁ -----> A₂ -----> ⋯
   \       ∧ \       ∧
    \     /   \ f₁  /
  f₀ \   / g₀  \   / g₁
      ∨ /       ∨ /
      B₀ -----> B₁ -----> ⋯ .
           b₀
```

Given [colimits](synthetic-homotopy-theory.sequential-colimits.md) `X` of `A`
and `Y` of `B`, the zigzag induces maps `f∞ : X → Y` and `g∞ : Y → X`, which we
show to be mutually inverse [equivalences](foundation-core.equivalences.md).

## Definitions

### A zigzag between sequential diagrams

<pre class="Agda"><a id="2040" class="Keyword">module</a> <a id="2047" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2047" class="Module">_</a>
  <a id="2051" class="Symbol">{</a><a id="2052" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2052" class="Bound">l1</a> <a id="2055" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2055" class="Bound">l2</a> <a id="2058" class="Symbol">:</a> <a id="2060" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2065" class="Symbol">}</a> <a id="2067" class="Symbol">(</a><a id="2068" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2068" class="Bound">A</a> <a id="2070" class="Symbol">:</a> <a id="2072" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="2091" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2052" class="Bound">l1</a><a id="2093" class="Symbol">)</a> <a id="2095" class="Symbol">(</a><a id="2096" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2096" class="Bound">B</a> <a id="2098" class="Symbol">:</a> <a id="2100" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="2119" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2055" class="Bound">l2</a><a id="2121" class="Symbol">)</a>
  <a id="2125" class="Keyword">where</a>

  <a id="2134" class="Keyword">module</a> <a id="2141" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2141" class="Module">_</a>
    <a id="2147" class="Symbol">(</a><a id="2148" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2148" class="Bound">f</a> <a id="2150" class="Symbol">:</a>
      <a id="2158" class="Symbol">(</a><a id="2159" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2159" class="Bound">n</a> <a id="2161" class="Symbol">:</a> <a id="2163" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2164" class="Symbol">)</a> <a id="2166" class="Symbol">→</a>
      <a id="2174" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="2200" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2068" class="Bound">A</a> <a id="2202" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2159" class="Bound">n</a> <a id="2204" class="Symbol">→</a> <a id="2206" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="2232" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2096" class="Bound">B</a> <a id="2234" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2159" class="Bound">n</a><a id="2235" class="Symbol">)</a>
    <a id="2241" class="Symbol">(</a><a id="2242" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2242" class="Bound">g</a> <a id="2244" class="Symbol">:</a>
      <a id="2252" class="Symbol">(</a><a id="2253" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2253" class="Bound">n</a> <a id="2255" class="Symbol">:</a> <a id="2257" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2258" class="Symbol">)</a> <a id="2260" class="Symbol">→</a>
      <a id="2268" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="2294" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2096" class="Bound">B</a> <a id="2296" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2253" class="Bound">n</a> <a id="2298" class="Symbol">→</a> <a id="2300" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="2326" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2068" class="Bound">A</a> <a id="2328" class="Symbol">(</a><a id="2329" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2336" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2253" class="Bound">n</a><a id="2337" class="Symbol">))</a>
    <a id="2344" class="Keyword">where</a>

    <a id="2355" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2355" class="Function">coherence-upper-triangle-zigzag-sequential-diagram</a> <a id="2406" class="Symbol">:</a> <a id="2408" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2411" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2052" class="Bound">l1</a>
    <a id="2418" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2355" class="Function">coherence-upper-triangle-zigzag-sequential-diagram</a> <a id="2469" class="Symbol">=</a>
      <a id="2477" class="Symbol">(</a><a id="2478" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2478" class="Bound">n</a> <a id="2480" class="Symbol">:</a> <a id="2482" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2483" class="Symbol">)</a> <a id="2485" class="Symbol">→</a>
      <a id="2493" href="foundation-core.commuting-triangles-of-maps.html#867" class="Function">coherence-triangle-maps</a>
        <a id="2525" class="Symbol">(</a> <a id="2527" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="2550" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2068" class="Bound">A</a> <a id="2552" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2478" class="Bound">n</a><a id="2553" class="Symbol">)</a>
        <a id="2563" class="Symbol">(</a> <a id="2565" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2242" class="Bound">g</a> <a id="2567" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2478" class="Bound">n</a><a id="2568" class="Symbol">)</a>
        <a id="2578" class="Symbol">(</a> <a id="2580" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2148" class="Bound">f</a> <a id="2582" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2478" class="Bound">n</a><a id="2583" class="Symbol">)</a>

    <a id="2590" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2590" class="Function">coherence-lower-triangle-zigzag-sequential-diagram</a> <a id="2641" class="Symbol">:</a> <a id="2643" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2646" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2055" class="Bound">l2</a>
    <a id="2653" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2590" class="Function">coherence-lower-triangle-zigzag-sequential-diagram</a> <a id="2704" class="Symbol">=</a>
      <a id="2712" class="Symbol">(</a><a id="2713" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2713" class="Bound">n</a> <a id="2715" class="Symbol">:</a> <a id="2717" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2718" class="Symbol">)</a> <a id="2720" class="Symbol">→</a>
      <a id="2728" href="foundation-core.commuting-triangles-of-maps.html#867" class="Function">coherence-triangle-maps</a>
        <a id="2760" class="Symbol">(</a> <a id="2762" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="2785" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2096" class="Bound">B</a> <a id="2787" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2713" class="Bound">n</a><a id="2788" class="Symbol">)</a>
        <a id="2798" class="Symbol">(</a> <a id="2800" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2148" class="Bound">f</a> <a id="2802" class="Symbol">(</a><a id="2803" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2810" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2713" class="Bound">n</a><a id="2811" class="Symbol">))</a>
        <a id="2822" class="Symbol">(</a> <a id="2824" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2242" class="Bound">g</a> <a id="2826" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2713" class="Bound">n</a><a id="2827" class="Symbol">)</a>

  <a id="2832" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="2858" class="Symbol">:</a> <a id="2860" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2863" class="Symbol">(</a><a id="2864" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2052" class="Bound">l1</a> <a id="2867" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2869" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2055" class="Bound">l2</a><a id="2871" class="Symbol">)</a>
  <a id="2875" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="2901" class="Symbol">=</a>
    <a id="2907" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2909" class="Symbol">(</a> <a id="2911" class="Symbol">(</a><a id="2912" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2912" class="Bound">n</a> <a id="2914" class="Symbol">:</a> <a id="2916" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2917" class="Symbol">)</a> <a id="2919" class="Symbol">→</a>
        <a id="2929" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="2955" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2068" class="Bound">A</a> <a id="2957" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2912" class="Bound">n</a> <a id="2959" class="Symbol">→</a> <a id="2961" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="2987" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2096" class="Bound">B</a> <a id="2989" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2912" class="Bound">n</a><a id="2990" class="Symbol">)</a>
      <a id="2998" class="Symbol">(</a> <a id="3000" class="Symbol">λ</a> <a id="3002" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3002" class="Bound">f</a> <a id="3004" class="Symbol">→</a>
        <a id="3014" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3016" class="Symbol">(</a> <a id="3018" class="Symbol">(</a><a id="3019" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3019" class="Bound">n</a> <a id="3021" class="Symbol">:</a> <a id="3023" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="3024" class="Symbol">)</a> <a id="3026" class="Symbol">→</a>
            <a id="3040" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="3066" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2096" class="Bound">B</a> <a id="3068" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3019" class="Bound">n</a> <a id="3070" class="Symbol">→</a>
            <a id="3084" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="3110" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2068" class="Bound">A</a> <a id="3112" class="Symbol">(</a><a id="3113" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="3120" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3019" class="Bound">n</a><a id="3121" class="Symbol">))</a>
          <a id="3134" class="Symbol">(</a> <a id="3136" class="Symbol">λ</a> <a id="3138" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3138" class="Bound">g</a> <a id="3140" class="Symbol">→</a>
            <a id="3154" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2355" class="Function">coherence-upper-triangle-zigzag-sequential-diagram</a> <a id="3205" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3002" class="Bound">f</a> <a id="3207" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3138" class="Bound">g</a> <a id="3209" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
            <a id="3223" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2590" class="Function">coherence-lower-triangle-zigzag-sequential-diagram</a> <a id="3274" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3002" class="Bound">f</a> <a id="3276" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3138" class="Bound">g</a><a id="3277" class="Symbol">))</a>
</pre>
### Components of a zigzag of sequential diagrams

<pre class="Agda"><a id="3344" class="Keyword">module</a> <a id="3351" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3351" class="Module">_</a>
  <a id="3355" class="Symbol">{</a><a id="3356" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3356" class="Bound">l1</a> <a id="3359" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3359" class="Bound">l2</a> <a id="3362" class="Symbol">:</a> <a id="3364" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3369" class="Symbol">}</a> <a id="3371" class="Symbol">{</a><a id="3372" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3372" class="Bound">A</a> <a id="3374" class="Symbol">:</a> <a id="3376" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="3395" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3356" class="Bound">l1</a><a id="3397" class="Symbol">}</a> <a id="3399" class="Symbol">{</a><a id="3400" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3400" class="Bound">B</a> <a id="3402" class="Symbol">:</a> <a id="3404" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="3423" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3359" class="Bound">l2</a><a id="3425" class="Symbol">}</a>
  <a id="3429" class="Symbol">(</a><a id="3430" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3430" class="Bound">z</a> <a id="3432" class="Symbol">:</a> <a id="3434" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="3460" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3372" class="Bound">A</a> <a id="3462" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3400" class="Bound">B</a><a id="3463" class="Symbol">)</a>
  <a id="3467" class="Keyword">where</a>

  <a id="3476" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a> <a id="3506" class="Symbol">:</a>
    <a id="3512" class="Symbol">(</a><a id="3513" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3513" class="Bound">n</a> <a id="3515" class="Symbol">:</a> <a id="3517" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="3518" class="Symbol">)</a> <a id="3520" class="Symbol">→</a>
    <a id="3526" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="3552" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3372" class="Bound">A</a> <a id="3554" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3513" class="Bound">n</a> <a id="3556" class="Symbol">→</a> <a id="3558" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="3584" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3400" class="Bound">B</a> <a id="3586" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3513" class="Bound">n</a>
  <a id="3590" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a> <a id="3620" class="Symbol">=</a> <a id="3622" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3626" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3430" class="Bound">z</a>

  <a id="3631" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3631" class="Function">inv-map-zigzag-sequential-diagram</a> <a id="3665" class="Symbol">:</a>
    <a id="3671" class="Symbol">(</a><a id="3672" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3672" class="Bound">n</a> <a id="3674" class="Symbol">:</a> <a id="3676" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="3677" class="Symbol">)</a> <a id="3679" class="Symbol">→</a>
    <a id="3685" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="3711" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3400" class="Bound">B</a> <a id="3713" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3672" class="Bound">n</a> <a id="3715" class="Symbol">→</a> <a id="3717" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="3743" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3372" class="Bound">A</a> <a id="3745" class="Symbol">(</a><a id="3746" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="3753" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3672" class="Bound">n</a><a id="3754" class="Symbol">)</a>
  <a id="3758" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3631" class="Function">inv-map-zigzag-sequential-diagram</a> <a id="3792" class="Symbol">=</a> <a id="3794" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3798" class="Symbol">(</a><a id="3799" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3803" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3430" class="Bound">z</a><a id="3804" class="Symbol">)</a>

  <a id="3809" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="3850" class="Symbol">:</a>
    <a id="3856" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2355" class="Function">coherence-upper-triangle-zigzag-sequential-diagram</a> <a id="3907" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3372" class="Bound">A</a> <a id="3909" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3400" class="Bound">B</a>
      <a id="3917" class="Symbol">(</a> <a id="3919" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a><a id="3948" class="Symbol">)</a>
      <a id="3956" class="Symbol">(</a> <a id="3958" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3631" class="Function">inv-map-zigzag-sequential-diagram</a><a id="3991" class="Symbol">)</a>
  <a id="3995" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="4036" class="Symbol">=</a> <a id="4038" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4042" class="Symbol">(</a><a id="4043" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4047" class="Symbol">(</a><a id="4048" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4052" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3430" class="Bound">z</a><a id="4053" class="Symbol">))</a>

  <a id="4059" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#4059" class="Function">lower-triangle-zigzag-sequential-diagram</a> <a id="4100" class="Symbol">:</a>
    <a id="4106" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2590" class="Function">coherence-lower-triangle-zigzag-sequential-diagram</a> <a id="4157" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3372" class="Bound">A</a> <a id="4159" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3400" class="Bound">B</a>
      <a id="4167" class="Symbol">(</a> <a id="4169" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a><a id="4198" class="Symbol">)</a>
      <a id="4206" class="Symbol">(</a> <a id="4208" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3631" class="Function">inv-map-zigzag-sequential-diagram</a><a id="4241" class="Symbol">)</a>
  <a id="4245" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#4059" class="Function">lower-triangle-zigzag-sequential-diagram</a> <a id="4286" class="Symbol">=</a> <a id="4288" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4292" class="Symbol">(</a><a id="4293" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4297" class="Symbol">(</a><a id="4298" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4302" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3430" class="Bound">z</a><a id="4303" class="Symbol">))</a>
</pre>
### Half-shifts of zigzags of sequential diagrams

We can forget the first triangle of a zigzag between `(A, a)` and `(B, b)` to
get a zigzag between `(B, b)` and the
[shift](synthetic-homotopy-theory.shifts-sequential-diagrams.md) `(A[1], a[1])`

```text
       b₀        b₁
  B₀ -----> B₁ -----> B₂ -----> ⋯
   \       ∧ \       ∧
    \     /   \ g₁  /
  g₀ \   / f₁  \   / f₂
      ∨ /       ∨ /
      A₁ -----> A₂ -----> ⋯ .
           a₁
```

We call this a _half-shift_ of the original zigzag, and it provides a symmetry
between the downward-going `f` maps and upward-going `g` maps. We exploit this
symmetry in the proceeding constructions by formulating the definitions and
lemmas for the downwards directions, and then applying them to the half-shift of
a zigzag to get the constructions for the upward direction.

Repeating a half-shift twice gets us a shift of a zigzag.

<pre class="Agda"><a id="5202" class="Keyword">module</a> <a id="5209" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5209" class="Module">_</a>
  <a id="5213" class="Symbol">{</a><a id="5214" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5214" class="Bound">l1</a> <a id="5217" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5217" class="Bound">l2</a> <a id="5220" class="Symbol">:</a> <a id="5222" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5227" class="Symbol">}</a> <a id="5229" class="Symbol">{</a><a id="5230" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5230" class="Bound">A</a> <a id="5232" class="Symbol">:</a> <a id="5234" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="5253" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5214" class="Bound">l1</a><a id="5255" class="Symbol">}</a> <a id="5257" class="Symbol">{</a><a id="5258" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5258" class="Bound">B</a> <a id="5260" class="Symbol">:</a> <a id="5262" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="5281" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5217" class="Bound">l2</a><a id="5283" class="Symbol">}</a>
  <a id="5287" class="Symbol">(</a><a id="5288" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5288" class="Bound">z</a> <a id="5290" class="Symbol">:</a> <a id="5292" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="5318" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5230" class="Bound">A</a> <a id="5320" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5258" class="Bound">B</a><a id="5321" class="Symbol">)</a>
  <a id="5325" class="Keyword">where</a>

  <a id="5334" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a> <a id="5371" class="Symbol">:</a>
    <a id="5377" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="5403" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5258" class="Bound">B</a> <a id="5405" class="Symbol">(</a><a id="5406" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="5436" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5230" class="Bound">A</a><a id="5437" class="Symbol">)</a>
  <a id="5441" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5445" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a> <a id="5482" class="Symbol">=</a>
    <a id="5488" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3631" class="Function">inv-map-zigzag-sequential-diagram</a> <a id="5522" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5288" class="Bound">z</a>
  <a id="5526" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5530" class="Symbol">(</a><a id="5531" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5535" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a><a id="5571" class="Symbol">)</a> <a id="5573" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5573" class="Bound">n</a> <a id="5575" class="Symbol">=</a>
    <a id="5581" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a> <a id="5611" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5288" class="Bound">z</a> <a id="5613" class="Symbol">(</a><a id="5614" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="5621" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5573" class="Bound">n</a><a id="5622" class="Symbol">)</a>
  <a id="5626" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5630" class="Symbol">(</a><a id="5631" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5635" class="Symbol">(</a><a id="5636" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5640" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a><a id="5676" class="Symbol">))</a> <a id="5679" class="Symbol">=</a>
    <a id="5685" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#4059" class="Function">lower-triangle-zigzag-sequential-diagram</a> <a id="5726" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5288" class="Bound">z</a>
  <a id="5730" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5734" class="Symbol">(</a><a id="5735" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5739" class="Symbol">(</a><a id="5740" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5744" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a><a id="5780" class="Symbol">))</a> <a id="5783" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5783" class="Bound">n</a> <a id="5785" class="Symbol">=</a>
    <a id="5791" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="5832" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5288" class="Bound">z</a> <a id="5834" class="Symbol">(</a><a id="5835" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="5842" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5783" class="Bound">n</a><a id="5843" class="Symbol">)</a>

<a id="5846" class="Keyword">module</a> <a id="5853" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5853" class="Module">_</a>
  <a id="5857" class="Symbol">{</a><a id="5858" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5858" class="Bound">l1</a> <a id="5861" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5861" class="Bound">l2</a> <a id="5864" class="Symbol">:</a> <a id="5866" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5871" class="Symbol">}</a> <a id="5873" class="Symbol">{</a><a id="5874" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5874" class="Bound">A</a> <a id="5876" class="Symbol">:</a> <a id="5878" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="5897" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5858" class="Bound">l1</a><a id="5899" class="Symbol">}</a> <a id="5901" class="Symbol">{</a><a id="5902" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5902" class="Bound">B</a> <a id="5904" class="Symbol">:</a> <a id="5906" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="5925" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5861" class="Bound">l2</a><a id="5927" class="Symbol">}</a>
  <a id="5931" class="Symbol">(</a><a id="5932" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5932" class="Bound">z</a> <a id="5934" class="Symbol">:</a> <a id="5936" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="5962" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5874" class="Bound">A</a> <a id="5964" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5902" class="Bound">B</a><a id="5965" class="Symbol">)</a>
  <a id="5969" class="Keyword">where</a>

  <a id="5978" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5978" class="Function">shift-zigzag-sequential-diagram</a> <a id="6010" class="Symbol">:</a>
    <a id="6016" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a>
      <a id="6048" class="Symbol">(</a> <a id="6050" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="6080" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5874" class="Bound">A</a><a id="6081" class="Symbol">)</a>
      <a id="6089" class="Symbol">(</a> <a id="6091" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="6121" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5902" class="Bound">B</a><a id="6122" class="Symbol">)</a>
  <a id="6126" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5978" class="Function">shift-zigzag-sequential-diagram</a> <a id="6158" class="Symbol">=</a>
    <a id="6164" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a>
      <a id="6207" class="Symbol">(</a> <a id="6209" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a> <a id="6246" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5932" class="Bound">z</a><a id="6247" class="Symbol">)</a>
</pre>
### Morphisms of sequential diagrams induced by zigzags of sequential diagrams

We can realign a zigzag

```text
       a₀        a₁
  A₀ -----> A₁ -----> A₂ -----> ⋯
   \       ∧ \       ∧
    \     /   \ f₁  /
  f₀ \   / g₀  \   / g₁
      ∨ /       ∨ /
      B₀ -----> B₁ -----> ⋯
           b₀
```

into a [morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
`f : A → B`

```text
          a₀        a₁
     A₀ -----> A₁ -----> A₂ -----> ⋯
     |        ∧|        ∧|
  f₀ |   g₀ /  | f₁   /  | f₂
     |    /    |    / g₁ |
     ∨  /      ∨  /      ∨
     B₀ -----> B₁ -----> B₂ -----> ⋯ .
          b₀        b₁
```

Similarly, we can realign the half-shift of a zigzag to get the morphism
`g : B → A[1]`:

```text
          b₀        b₁
     B₀ -----> B₁ -----> B₂ -----> ⋯
     |        ∧|        ∧|
  g₀ |   f₁ /  | g₁   /  | g₂
     |    /    |    / f₂ |
     ∨  /      ∨  /      ∨
     A₁ -----> A₂ -----> A₃ -----> ⋯ ,
          a₁        a₂
```

which should be thought of as an inverse of `f` --- and we show that it indeed
induces an inverse in the colimit further down.

<pre class="Agda"><a id="7366" class="Keyword">module</a> <a id="7373" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7373" class="Module">_</a>
  <a id="7377" class="Symbol">{</a><a id="7378" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7378" class="Bound">l1</a> <a id="7381" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7381" class="Bound">l2</a> <a id="7384" class="Symbol">:</a> <a id="7386" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7391" class="Symbol">}</a> <a id="7393" class="Symbol">{</a><a id="7394" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7394" class="Bound">A</a> <a id="7396" class="Symbol">:</a> <a id="7398" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="7417" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7378" class="Bound">l1</a><a id="7419" class="Symbol">}</a> <a id="7421" class="Symbol">{</a><a id="7422" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7422" class="Bound">B</a> <a id="7424" class="Symbol">:</a> <a id="7426" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="7445" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7381" class="Bound">l2</a><a id="7447" class="Symbol">}</a>
  <a id="7451" class="Symbol">(</a><a id="7452" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7452" class="Bound">z</a> <a id="7454" class="Symbol">:</a> <a id="7456" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="7482" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7394" class="Bound">A</a> <a id="7484" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7422" class="Bound">B</a><a id="7485" class="Symbol">)</a>
  <a id="7489" class="Keyword">where</a>

  <a id="7498" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7498" class="Function">hom-diagram-zigzag-sequential-diagram</a> <a id="7536" class="Symbol">:</a> <a id="7538" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a> <a id="7561" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7394" class="Bound">A</a> <a id="7563" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7422" class="Bound">B</a>
  <a id="7567" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="7571" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7498" class="Function">hom-diagram-zigzag-sequential-diagram</a> <a id="7609" class="Symbol">=</a>
    <a id="7615" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a> <a id="7645" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7452" class="Bound">z</a>
  <a id="7649" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7653" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7498" class="Function">hom-diagram-zigzag-sequential-diagram</a> <a id="7691" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7691" class="Bound">n</a> <a id="7693" class="Symbol">=</a>
    <a id="7699" href="foundation.commuting-triangles-of-maps.html#7825" class="Function">horizontal-pasting-up-diagonal-coherence-triangle-maps</a>
      <a id="7760" class="Symbol">(</a> <a id="7762" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="7785" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7394" class="Bound">A</a> <a id="7787" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7691" class="Bound">n</a><a id="7788" class="Symbol">)</a>
      <a id="7796" class="Symbol">(</a> <a id="7798" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a> <a id="7828" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7452" class="Bound">z</a> <a id="7830" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7691" class="Bound">n</a><a id="7831" class="Symbol">)</a>
      <a id="7839" class="Symbol">(</a> <a id="7841" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a> <a id="7871" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7452" class="Bound">z</a> <a id="7873" class="Symbol">(</a><a id="7874" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="7881" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7691" class="Bound">n</a><a id="7882" class="Symbol">))</a>
      <a id="7891" class="Symbol">(</a> <a id="7893" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="7916" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7422" class="Bound">B</a> <a id="7918" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7691" class="Bound">n</a><a id="7919" class="Symbol">)</a>
      <a id="7927" class="Symbol">(</a> <a id="7929" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="7938" class="Symbol">(</a><a id="7939" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="7980" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7452" class="Bound">z</a> <a id="7982" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7691" class="Bound">n</a><a id="7983" class="Symbol">))</a>
      <a id="7992" class="Symbol">(</a> <a id="7994" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#4059" class="Function">lower-triangle-zigzag-sequential-diagram</a> <a id="8035" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7452" class="Bound">z</a> <a id="8037" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7691" class="Bound">n</a><a id="8038" class="Symbol">)</a>

<a id="8041" class="Keyword">module</a> <a id="8048" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8048" class="Module">_</a>
  <a id="8052" class="Symbol">{</a><a id="8053" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8053" class="Bound">l1</a> <a id="8056" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8056" class="Bound">l2</a> <a id="8059" class="Symbol">:</a> <a id="8061" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8066" class="Symbol">}</a> <a id="8068" class="Symbol">{</a><a id="8069" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8069" class="Bound">A</a> <a id="8071" class="Symbol">:</a> <a id="8073" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="8092" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8053" class="Bound">l1</a><a id="8094" class="Symbol">}</a> <a id="8096" class="Symbol">{</a><a id="8097" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8097" class="Bound">B</a> <a id="8099" class="Symbol">:</a> <a id="8101" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="8120" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8056" class="Bound">l2</a><a id="8122" class="Symbol">}</a>
  <a id="8126" class="Symbol">(</a><a id="8127" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8127" class="Bound">z</a> <a id="8129" class="Symbol">:</a> <a id="8131" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="8157" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8069" class="Bound">A</a> <a id="8159" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8097" class="Bound">B</a><a id="8160" class="Symbol">)</a>
  <a id="8164" class="Keyword">where</a>

  <a id="8173" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8173" class="Function">inv-hom-diagram-zigzag-sequential-diagram</a> <a id="8215" class="Symbol">:</a>
    <a id="8221" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a> <a id="8244" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8097" class="Bound">B</a> <a id="8246" class="Symbol">(</a><a id="8247" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="8277" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8069" class="Bound">A</a><a id="8278" class="Symbol">)</a>
  <a id="8282" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8173" class="Function">inv-hom-diagram-zigzag-sequential-diagram</a> <a id="8324" class="Symbol">=</a>
    <a id="8330" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7498" class="Function">hom-diagram-zigzag-sequential-diagram</a>
      <a id="8374" class="Symbol">(</a> <a id="8376" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a> <a id="8413" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8127" class="Bound">z</a><a id="8414" class="Symbol">)</a>
</pre>
### Zigzags of sequential diagrams unfold to the shifting morphism of sequential diagrams

After composing the morphisms induced by a zigzag, we get a morphism
`g ∘ f : A → A[1]`

```text
          a₀        a₁
     A₀ -----> A₁ -----> A₂ -----> ⋯
     |        ∧|        ∧|
  f₀ |   g₀ /  | f₁   /  | f₂
     |    /    |    / g₁ |
     ∨  / b₀   ∨  / b₁   ∨
     B₀ -----> B₁ -----> B₂ -----> ⋯
     |        ∧|        ∧|
  g₀ |   f₁ /  | g₁   /  | g₂
     |    /    |    / f₂ |
     ∨  /      ∨  /      ∨
     A₁ -----> A₂ -----> A₃ -----> ⋯ .
          a₁        a₂
```

We show that there is a
[homotopy](synthetic-homotopy-theory.morphisms-sequential-diagrams.md) between
this morphism and the
[shift inclusion morphism](synthetic-homotopy-theory.shifts-sequential-diagrams.md)
`a : A → A[1]`

```text
        a₀      a₁
    A₀ ---> A₁ ---> A₂ ---> ⋯
    |       |       |
 a₀ |       | a₁    | a₂
    ∨       ∨       ∨
    A₁ ---> A₂ ---> A₃ ---> ⋯ .
        a₁      a₂
```

**Proof:** Component-wise the homotopies `aₙ ~ gₙ ∘ fₙ` are given by the upper
triangles in the zigzag. The coherence of a homotopy requires us to show that
the compositions

```text
      aₙ
  Aₙ ----> Aₙ₊₁
            | \ fₙ₊₁
            |   ∨
       aₙ₊₁ |    Bₙ₊₁
            |   /
            ∨ ∨ gₙ₊₁
           Aₙ₊₂
```

and

```text
               aₙ
          Aₙ -----> Aₙ₊₁
        /  |        ∧|
      / fₙ |   gₙ /  | fₙ₊₁
     |     |    /    |
     |     ∨  /      ∨
  aₙ |    Bₙ -----> Bₙ₊₁
     |     |        ∧|
     |  gₙ | fₙ₊₁ /  | gₙ₊₁
       \   |    /    |
         ∨ ∨  /      ∨
          Aₙ₊₁ ---> Aₙ₊₂
               aₙ₊₁
```

are homotopic. Since the skewed square

```text
         gₙ
    Bₙ -----> Aₙ₊₁
     |         |
  gₙ |         | fₙ₊₁
     ∨         ∨
    Aₙ₊₁ ---> Bₙ₊₁
         fₙ₊₁
```

in the middle is composed of inverse triangles, it is homotopic to the
reflexivity homotopy, which makes the second diagram collapse to

```text
           aₙ
        --------
      /          \
    /              ∨
  Aₙ ----> Bₙ ----> Aₙ₊₁
    \ fₙ       gₙ  ∧ |   \ fₙ₊₁
      \          /   |     ∨
        --------     | aₙ₊₁ Bₙ₊₁
           aₙ        |     /
                     ∨   ∨ gₙ₊₁
                    Aₙ₊₂ ,
```

where the globe is again composed of inverse triangles, so the diagram collapses
to

```text
      aₙ
  Aₙ ----> Aₙ₊₁
            | \ fₙ₊₁
            |   ∨
       aₙ₊₁ |    Bₙ₊₁
            |   /
            ∨ ∨ gₙ₊₁
           Aₙ₊₂ ,
```

which is what we needed to show.

<pre class="Agda"><a id="10940" class="Keyword">module</a> <a id="10947" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10947" class="Module">_</a>
  <a id="10951" class="Symbol">{</a><a id="10952" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10952" class="Bound">l1</a> <a id="10955" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10955" class="Bound">l2</a> <a id="10958" class="Symbol">:</a> <a id="10960" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="10965" class="Symbol">}</a> <a id="10967" class="Symbol">{</a><a id="10968" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="10970" class="Symbol">:</a> <a id="10972" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="10991" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10952" class="Bound">l1</a><a id="10993" class="Symbol">}</a> <a id="10995" class="Symbol">{</a><a id="10996" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10996" class="Bound">B</a> <a id="10998" class="Symbol">:</a> <a id="11000" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="11019" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10955" class="Bound">l2</a><a id="11021" class="Symbol">}</a>
  <a id="11025" class="Symbol">(</a><a id="11026" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="11028" class="Symbol">:</a> <a id="11030" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="11056" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="11058" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10996" class="Bound">B</a><a id="11059" class="Symbol">)</a>
  <a id="11063" class="Keyword">where</a>

  <a id="11072" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11072" class="Function">htpy-hom-shift-hom-zigzag-sequential-diagram</a> <a id="11117" class="Symbol">:</a>
    <a id="11123" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#5905" class="Function">htpy-hom-sequential-diagram</a>
      <a id="11157" class="Symbol">(</a> <a id="11159" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="11189" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a><a id="11190" class="Symbol">)</a>
      <a id="11198" class="Symbol">(</a> <a id="11200" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="11234" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a><a id="11235" class="Symbol">)</a>
      <a id="11243" class="Symbol">(</a> <a id="11245" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#4579" class="Function">comp-hom-sequential-diagram</a> <a id="11273" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="11275" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10996" class="Bound">B</a>
        <a id="11285" class="Symbol">(</a> <a id="11287" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="11317" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a><a id="11318" class="Symbol">)</a>
        <a id="11328" class="Symbol">(</a> <a id="11330" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8173" class="Function">inv-hom-diagram-zigzag-sequential-diagram</a> <a id="11372" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a><a id="11373" class="Symbol">)</a>
        <a id="11383" class="Symbol">(</a> <a id="11385" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7498" class="Function">hom-diagram-zigzag-sequential-diagram</a> <a id="11423" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a><a id="11424" class="Symbol">))</a>
  <a id="11429" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="11433" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11072" class="Function">htpy-hom-shift-hom-zigzag-sequential-diagram</a> <a id="11478" class="Symbol">=</a>
    <a id="11484" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="11525" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a>
  <a id="11529" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="11533" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11072" class="Function">htpy-hom-shift-hom-zigzag-sequential-diagram</a> <a id="11578" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a> <a id="11580" class="Symbol">=</a>
    <a id="11586" href="foundation-core.commuting-squares-of-homotopies.html#14352" class="Function">inv-concat-right-homotopy-coherence-square-homotopies</a>
      <a id="11646" class="Symbol">(</a> <a id="11648" class="Symbol">(</a> <a id="11650" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="11673" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="11675" class="Symbol">(</a><a id="11676" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="11683" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="11684" class="Symbol">))</a> <a id="11687" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a>
        <a id="11698" class="Symbol">(</a> <a id="11700" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="11741" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="11743" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="11744" class="Symbol">))</a>
      <a id="11753" class="Symbol">(</a> <a id="11755" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="11764" class="Symbol">)</a>
      <a id="11772" class="Symbol">(</a> <a id="11774" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#3973" class="Function">naturality-comp-hom-sequential-diagram</a> <a id="11813" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="11815" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10996" class="Bound">B</a>
        <a id="11825" class="Symbol">(</a> <a id="11827" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="11857" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a><a id="11858" class="Symbol">)</a>
        <a id="11868" class="Symbol">(</a> <a id="11870" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8173" class="Function">inv-hom-diagram-zigzag-sequential-diagram</a> <a id="11912" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a><a id="11913" class="Symbol">)</a>
        <a id="11923" class="Symbol">(</a> <a id="11925" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7498" class="Function">hom-diagram-zigzag-sequential-diagram</a> <a id="11963" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a><a id="11964" class="Symbol">)</a>
        <a id="11974" class="Symbol">(</a> <a id="11976" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="11977" class="Symbol">))</a>
      <a id="11986" class="Symbol">(</a> <a id="11988" class="Symbol">(</a> <a id="11990" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="12031" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12033" class="Symbol">(</a><a id="12034" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="12041" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12042" class="Symbol">))</a> <a id="12045" href="foundation.whiskering-homotopies-composition.html#2725" class="Function Operator">·r</a>
        <a id="12056" class="Symbol">(</a> <a id="12058" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="12081" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="12083" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12084" class="Symbol">))</a>
      <a id="12093" class="Symbol">(</a> <a id="12095" href="foundation.commuting-squares-of-maps.html#34231" class="Function">pasting-coherence-squares-collapse-triangles</a>
        <a id="12148" class="Symbol">(</a> <a id="12150" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="12173" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="12175" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12176" class="Symbol">)</a>
        <a id="12186" class="Symbol">(</a> <a id="12188" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a> <a id="12218" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12220" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12221" class="Symbol">)</a>
        <a id="12231" class="Symbol">(</a> <a id="12233" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3476" class="Function">map-zigzag-sequential-diagram</a> <a id="12263" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12265" class="Symbol">(</a><a id="12266" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="12273" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12274" class="Symbol">))</a>
        <a id="12285" class="Symbol">(</a> <a id="12287" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="12310" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10996" class="Bound">B</a> <a id="12312" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12313" class="Symbol">)</a>
        <a id="12323" class="Symbol">(</a> <a id="12325" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3631" class="Function">inv-map-zigzag-sequential-diagram</a> <a id="12359" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12361" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12362" class="Symbol">)</a>
        <a id="12372" class="Symbol">(</a> <a id="12374" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3631" class="Function">inv-map-zigzag-sequential-diagram</a> <a id="12408" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12410" class="Symbol">(</a><a id="12411" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="12418" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12419" class="Symbol">))</a>
        <a id="12430" class="Symbol">(</a> <a id="12432" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="12455" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="12457" class="Symbol">(</a><a id="12458" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="12465" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12466" class="Symbol">))</a>
        <a id="12477" class="Symbol">(</a> <a id="12479" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="12488" class="Symbol">(</a><a id="12489" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="12530" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12532" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12533" class="Symbol">))</a>
        <a id="12544" class="Symbol">(</a> <a id="12546" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#4059" class="Function">lower-triangle-zigzag-sequential-diagram</a> <a id="12587" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12589" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12590" class="Symbol">)</a>
        <a id="12600" class="Symbol">(</a> <a id="12602" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="12611" class="Symbol">(</a><a id="12612" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#4059" class="Function">lower-triangle-zigzag-sequential-diagram</a> <a id="12653" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12655" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12656" class="Symbol">))</a>
        <a id="12667" class="Symbol">(</a> <a id="12669" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="12710" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12712" class="Symbol">(</a><a id="12713" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="12720" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12721" class="Symbol">))</a>
        <a id="12732" class="Symbol">(</a> <a id="12734" href="foundation-core.homotopies.html#5492" class="Function">left-inv-htpy</a> <a id="12748" class="Symbol">(</a><a id="12749" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#4059" class="Function">lower-triangle-zigzag-sequential-diagram</a> <a id="12790" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12792" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12793" class="Symbol">)))</a>
      <a id="12803" class="Symbol">(</a> <a id="12805" href="foundation-core.commuting-squares-of-homotopies.html#22542" class="Function">right-whisker-concat-coherence-square-homotopies</a>
        <a id="12862" class="Symbol">(</a> <a id="12864" class="Symbol">(</a> <a id="12866" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="12889" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="12891" class="Symbol">(</a><a id="12892" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="12899" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12900" class="Symbol">))</a> <a id="12903" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a>
          <a id="12916" class="Symbol">(</a> <a id="12918" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="12959" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="12961" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="12962" class="Symbol">))</a>
        <a id="12973" class="Symbol">(</a> <a id="12975" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="12984" class="Symbol">)</a>
        <a id="12994" class="Symbol">(</a> <a id="12996" class="Symbol">(</a> <a id="12998" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="13021" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="13023" class="Symbol">(</a><a id="13024" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="13031" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="13032" class="Symbol">))</a> <a id="13035" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a>
          <a id="13048" class="Symbol">(</a> <a id="13050" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="13059" class="Symbol">(</a><a id="13060" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="13101" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="13103" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="13104" class="Symbol">)))</a>
        <a id="13116" class="Symbol">(</a> <a id="13118" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="13127" class="Symbol">)</a>
        <a id="13137" class="Symbol">(</a> <a id="13139" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a>
          <a id="13158" class="Symbol">(</a> <a id="13160" href="foundation.whiskering-homotopies-composition.html#5969" class="Function">right-inv-htpy-left-whisker</a>
            <a id="13200" class="Symbol">(</a> <a id="13202" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="13225" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="13227" class="Symbol">(</a><a id="13228" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="13235" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="13236" class="Symbol">))</a>
            <a id="13251" class="Symbol">(</a> <a id="13253" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="13294" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="13296" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="13297" class="Symbol">)))</a>
        <a id="13309" class="Symbol">(</a> <a id="13311" class="Symbol">(</a> <a id="13313" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#3809" class="Function">upper-triangle-zigzag-sequential-diagram</a> <a id="13354" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11026" class="Bound">z</a> <a id="13356" class="Symbol">(</a><a id="13357" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="13364" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="13365" class="Symbol">))</a> <a id="13368" href="foundation.whiskering-homotopies-composition.html#2725" class="Function Operator">·r</a>
          <a id="13381" class="Symbol">(</a> <a id="13383" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="13406" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#10968" class="Bound">A</a> <a id="13408" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11578" class="Bound">n</a><a id="13409" class="Symbol">)))</a>
</pre>
## Properties

### Zigzags of sequential diagrams induce equivalences of sequential colimits

By
[functoriality](synthetic-homotopy-theory.functoriality-sequential-colimits.md)
of sequential colimits, the morphism `f : A → B` induced by a zigzag then
induces a map of colimits `A∞ → B∞`. We show that this induced map is an
equivalence.

**Proof:** Given a colimit `X` of `(A, a)` and a colimit `Y` of `(B, b)`, we get
a map `f∞ : X → Y`. Since `X` is also a colimit of `(A[1], a[1])`, the morphism
`g : B → A[1]` induces a map `g∞ : Y → X`. Composing the two, we get
`g∞ ∘ f∞ : X → X`. By functoriality, this map is homotopic to `(g ∘ f)∞`, and
taking a colimit preserves homotopies, so `g ∘ f ~ a` implies `(g ∘ f)∞ ~ a∞`.
In
[`shifts-sequential-diagrams`](synthetic-homotopy-theory.shifts-sequential-diagrams.md)
we show that `a∞ ~ id`, so we get a commuting triangle

```text
        id
     X ---> X
     |     ∧
  f∞ |   / g∞
     ∨ /
     Y .
```

Applying this construction to the half-shift of the zigzag, we get a commuting
triangle

```text
        id
     Y ---> Y
     |     ∧
  g∞ |   / f[1]∞
     ∨ /
     X .
```

These triangles compose to the
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
         id
     X -----> X
     |       ∧|
  f∞ |  g∞ /  | f[1]∞
     |   /    |
     ∨ /      ∨
     Y -----> Y .
         id
```

Since the horizontal maps are identities, we get that `g∞` is by definition an
equivalence, because we just presented its section `f∞` and its retraction
`f[1]∞`. Since `f∞` is a section of an equivalence, it is itself an equivalence.

Additionally we get the judgmental equalities `f∞⁻¹ ≐ g∞` and `g∞⁻¹ ≐ f∞`.

<pre class="Agda"><a id="15106" class="Keyword">module</a> <a id="15113" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15113" class="Module">_</a>
  <a id="15117" class="Symbol">{</a><a id="15118" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15118" class="Bound">l1</a> <a id="15121" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15121" class="Bound">l2</a> <a id="15124" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15124" class="Bound">l3</a> <a id="15127" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15127" class="Bound">l4</a> <a id="15130" class="Symbol">:</a> <a id="15132" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="15137" class="Symbol">}</a> <a id="15139" class="Symbol">{</a><a id="15140" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15140" class="Bound">A</a> <a id="15142" class="Symbol">:</a> <a id="15144" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="15163" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15118" class="Bound">l1</a><a id="15165" class="Symbol">}</a> <a id="15167" class="Symbol">{</a><a id="15168" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15168" class="Bound">B</a> <a id="15170" class="Symbol">:</a> <a id="15172" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="15191" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15121" class="Bound">l2</a><a id="15193" class="Symbol">}</a>
  <a id="15197" class="Symbol">{</a><a id="15198" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15198" class="Bound">X</a> <a id="15200" class="Symbol">:</a> <a id="15202" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="15205" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15124" class="Bound">l3</a><a id="15207" class="Symbol">}</a> <a id="15209" class="Symbol">{</a><a id="15210" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15210" class="Bound">c</a> <a id="15212" class="Symbol">:</a> <a id="15214" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="15240" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15140" class="Bound">A</a> <a id="15242" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15198" class="Bound">X</a><a id="15243" class="Symbol">}</a>
  <a id="15247" class="Symbol">(</a><a id="15248" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15248" class="Bound">up-c</a> <a id="15253" class="Symbol">:</a> <a id="15255" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="15293" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15210" class="Bound">c</a><a id="15294" class="Symbol">)</a>
  <a id="15298" class="Symbol">{</a><a id="15299" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15299" class="Bound">Y</a> <a id="15301" class="Symbol">:</a> <a id="15303" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="15306" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15127" class="Bound">l4</a><a id="15308" class="Symbol">}</a> <a id="15310" class="Symbol">{</a><a id="15311" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15311" class="Bound">c&#39;</a> <a id="15314" class="Symbol">:</a> <a id="15316" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="15342" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15168" class="Bound">B</a> <a id="15344" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15299" class="Bound">Y</a><a id="15345" class="Symbol">}</a>
  <a id="15349" class="Symbol">(</a><a id="15350" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15350" class="Bound">up-c&#39;</a> <a id="15356" class="Symbol">:</a> <a id="15358" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="15396" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15311" class="Bound">c&#39;</a><a id="15398" class="Symbol">)</a>
  <a id="15402" class="Symbol">(</a><a id="15403" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15403" class="Bound">z</a> <a id="15405" class="Symbol">:</a> <a id="15407" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="15433" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15140" class="Bound">A</a> <a id="15435" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15168" class="Bound">B</a><a id="15436" class="Symbol">)</a>
  <a id="15440" class="Keyword">where</a>

  <a id="15449" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a> <a id="15487" class="Symbol">:</a> <a id="15489" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15198" class="Bound">X</a> <a id="15491" class="Symbol">→</a> <a id="15493" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15299" class="Bound">Y</a>
  <a id="15497" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a> <a id="15535" class="Symbol">=</a>
    <a id="15541" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#4827" class="Function">map-sequential-colimit-hom-sequential-diagram</a>
      <a id="15593" class="Symbol">(</a> <a id="15595" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15248" class="Bound">up-c</a><a id="15599" class="Symbol">)</a>
      <a id="15607" class="Symbol">(</a> <a id="15609" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15311" class="Bound">c&#39;</a><a id="15611" class="Symbol">)</a>
      <a id="15619" class="Symbol">(</a> <a id="15621" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7498" class="Function">hom-diagram-zigzag-sequential-diagram</a> <a id="15659" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15403" class="Bound">z</a><a id="15660" class="Symbol">)</a>

  <a id="15665" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15665" class="Function">inv-map-colimit-zigzag-sequential-diagram</a> <a id="15707" class="Symbol">:</a> <a id="15709" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15299" class="Bound">Y</a> <a id="15711" class="Symbol">→</a> <a id="15713" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15198" class="Bound">X</a>
  <a id="15717" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15665" class="Function">inv-map-colimit-zigzag-sequential-diagram</a> <a id="15759" class="Symbol">=</a>
    <a id="15765" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#4827" class="Function">map-sequential-colimit-hom-sequential-diagram</a>
      <a id="15817" class="Symbol">(</a> <a id="15819" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15350" class="Bound">up-c&#39;</a><a id="15824" class="Symbol">)</a>
      <a id="15832" class="Symbol">(</a> <a id="15834" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="15871" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15210" class="Bound">c</a><a id="15872" class="Symbol">)</a>
      <a id="15880" class="Symbol">(</a> <a id="15882" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8173" class="Function">inv-hom-diagram-zigzag-sequential-diagram</a> <a id="15924" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15403" class="Bound">z</a><a id="15925" class="Symbol">)</a>

  <a id="15930" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15930" class="Function">upper-triangle-colimit-zigzag-sequential-diagram</a> <a id="15979" class="Symbol">:</a>
    <a id="15985" href="foundation-core.commuting-triangles-of-maps.html#867" class="Function">coherence-triangle-maps</a>
      <a id="16015" class="Symbol">(</a> <a id="16017" href="foundation-core.function-types.html#307" class="Function">id</a><a id="16019" class="Symbol">)</a>
      <a id="16027" class="Symbol">(</a> <a id="16029" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15665" class="Function">inv-map-colimit-zigzag-sequential-diagram</a><a id="16070" class="Symbol">)</a>
      <a id="16078" class="Symbol">(</a> <a id="16080" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a><a id="16117" class="Symbol">)</a>
  <a id="16121" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15930" class="Function">upper-triangle-colimit-zigzag-sequential-diagram</a> <a id="16170" class="Symbol">=</a>
    <a id="16176" class="Symbol">(</a> <a id="16178" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="16187" class="Symbol">(</a><a id="16188" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29961" class="Function">compute-map-colimit-hom-shift-once-sequential-diagram</a> <a id="16242" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15248" class="Bound">up-c</a><a id="16246" class="Symbol">))</a> <a id="16249" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a>
    <a id="16256" class="Symbol">(</a> <a id="16258" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#8963" class="Function">htpy-map-sequential-colimit-htpy-hom-sequential-diagram</a> <a id="16314" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15248" class="Bound">up-c</a>
      <a id="16325" class="Symbol">(</a> <a id="16327" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="16364" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15210" class="Bound">c</a><a id="16365" class="Symbol">)</a>
      <a id="16373" class="Symbol">(</a> <a id="16375" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#11072" class="Function">htpy-hom-shift-hom-zigzag-sequential-diagram</a> <a id="16420" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15403" class="Bound">z</a><a id="16421" class="Symbol">))</a> <a id="16424" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a>
    <a id="16431" class="Symbol">(</a> <a id="16433" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#16458" class="Function">preserves-comp-map-sequential-colimit-hom-sequential-diagram</a>
      <a id="16500" class="Symbol">(</a> <a id="16502" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15248" class="Bound">up-c</a><a id="16506" class="Symbol">)</a>
      <a id="16514" class="Symbol">(</a> <a id="16516" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15350" class="Bound">up-c&#39;</a><a id="16521" class="Symbol">)</a>
      <a id="16529" class="Symbol">(</a> <a id="16531" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="16568" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15210" class="Bound">c</a><a id="16569" class="Symbol">)</a>
      <a id="16577" class="Symbol">(</a> <a id="16579" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#8173" class="Function">inv-hom-diagram-zigzag-sequential-diagram</a> <a id="16621" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15403" class="Bound">z</a><a id="16622" class="Symbol">)</a>
      <a id="16630" class="Symbol">(</a> <a id="16632" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#7498" class="Function">hom-diagram-zigzag-sequential-diagram</a> <a id="16670" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15403" class="Bound">z</a><a id="16671" class="Symbol">))</a>

  <a id="16677" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16677" class="Function">is-retraction-inv-map-colimit-zigzag-sequential-diagram</a> <a id="16733" class="Symbol">:</a>
    <a id="16739" href="foundation-core.retractions.html#790" class="Function">is-retraction</a>
      <a id="16759" class="Symbol">(</a> <a id="16761" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a><a id="16798" class="Symbol">)</a>
      <a id="16806" class="Symbol">(</a> <a id="16808" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15665" class="Function">inv-map-colimit-zigzag-sequential-diagram</a><a id="16849" class="Symbol">)</a>
  <a id="16853" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16677" class="Function">is-retraction-inv-map-colimit-zigzag-sequential-diagram</a> <a id="16909" class="Symbol">=</a>
    <a id="16915" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="16924" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15930" class="Function">upper-triangle-colimit-zigzag-sequential-diagram</a>

<a id="16974" class="Keyword">module</a> <a id="16981" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16981" class="Module">_</a>
  <a id="16985" class="Symbol">{</a><a id="16986" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16986" class="Bound">l1</a> <a id="16989" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16989" class="Bound">l2</a> <a id="16992" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16992" class="Bound">l3</a> <a id="16995" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16995" class="Bound">l4</a> <a id="16998" class="Symbol">:</a> <a id="17000" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="17005" class="Symbol">}</a> <a id="17007" class="Symbol">(</a><a id="17008" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17008" class="Bound">A</a> <a id="17010" class="Symbol">:</a> <a id="17012" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="17031" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16986" class="Bound">l1</a><a id="17033" class="Symbol">)</a> <a id="17035" class="Symbol">(</a><a id="17036" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17036" class="Bound">B</a> <a id="17038" class="Symbol">:</a> <a id="17040" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="17059" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16989" class="Bound">l2</a><a id="17061" class="Symbol">)</a>
  <a id="17065" class="Symbol">{</a><a id="17066" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17066" class="Bound">X</a> <a id="17068" class="Symbol">:</a> <a id="17070" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="17073" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16992" class="Bound">l3</a><a id="17075" class="Symbol">}</a> <a id="17077" class="Symbol">{</a><a id="17078" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17078" class="Bound">c</a> <a id="17080" class="Symbol">:</a> <a id="17082" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="17108" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17008" class="Bound">A</a> <a id="17110" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17066" class="Bound">X</a><a id="17111" class="Symbol">}</a>
  <a id="17115" class="Symbol">(</a><a id="17116" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a> <a id="17121" class="Symbol">:</a> <a id="17123" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="17161" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17078" class="Bound">c</a><a id="17162" class="Symbol">)</a>
  <a id="17166" class="Symbol">{</a><a id="17167" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17167" class="Bound">Y</a> <a id="17169" class="Symbol">:</a> <a id="17171" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="17174" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16995" class="Bound">l4</a><a id="17176" class="Symbol">}</a> <a id="17178" class="Symbol">{</a><a id="17179" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17179" class="Bound">c&#39;</a> <a id="17182" class="Symbol">:</a> <a id="17184" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="17210" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17036" class="Bound">B</a> <a id="17212" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17167" class="Bound">Y</a><a id="17213" class="Symbol">}</a>
  <a id="17217" class="Symbol">(</a><a id="17218" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a> <a id="17224" class="Symbol">:</a> <a id="17226" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="17264" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17179" class="Bound">c&#39;</a><a id="17266" class="Symbol">)</a>
  <a id="17270" class="Symbol">(</a><a id="17271" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a> <a id="17273" class="Symbol">:</a> <a id="17275" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#2832" class="Function">zigzag-sequential-diagram</a> <a id="17301" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17008" class="Bound">A</a> <a id="17303" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17036" class="Bound">B</a><a id="17304" class="Symbol">)</a>
  <a id="17308" class="Keyword">where</a>

  <a id="17317" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17317" class="Function">lower-triangle-colimit-zigzag-sequential-diagram</a> <a id="17366" class="Symbol">:</a>
    <a id="17372" href="foundation-core.commuting-triangles-of-maps.html#867" class="Function">coherence-triangle-maps</a>
      <a id="17402" class="Symbol">(</a> <a id="17404" href="foundation-core.function-types.html#307" class="Function">id</a><a id="17406" class="Symbol">)</a>
      <a id="17414" class="Symbol">(</a> <a id="17416" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a>
        <a id="17462" class="Symbol">(</a> <a id="17464" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="17499" class="Number">1</a> <a id="17501" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a><a id="17505" class="Symbol">)</a>
        <a id="17515" class="Symbol">(</a> <a id="17517" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="17552" class="Number">1</a> <a id="17554" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a><a id="17559" class="Symbol">)</a>
        <a id="17569" class="Symbol">(</a> <a id="17571" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5978" class="Function">shift-zigzag-sequential-diagram</a> <a id="17603" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a><a id="17604" class="Symbol">))</a>
      <a id="17613" class="Symbol">(</a> <a id="17615" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a> <a id="17653" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a>
        <a id="17667" class="Symbol">(</a> <a id="17669" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="17704" class="Number">1</a> <a id="17706" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a><a id="17710" class="Symbol">)</a>
        <a id="17720" class="Symbol">(</a> <a id="17722" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a> <a id="17759" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a><a id="17760" class="Symbol">))</a>
  <a id="17765" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17317" class="Function">lower-triangle-colimit-zigzag-sequential-diagram</a> <a id="17814" class="Symbol">=</a>
    <a id="17820" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15930" class="Function">upper-triangle-colimit-zigzag-sequential-diagram</a>
      <a id="17875" class="Symbol">(</a> <a id="17877" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a><a id="17882" class="Symbol">)</a>
      <a id="17890" class="Symbol">(</a> <a id="17892" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="17927" class="Number">1</a> <a id="17929" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a><a id="17933" class="Symbol">)</a>
      <a id="17941" class="Symbol">(</a> <a id="17943" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a> <a id="17980" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a><a id="17981" class="Symbol">)</a>

  <a id="17986" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17986" class="Function">is-equiv-inv-map-colimit-zigzag-sequential-diagram</a> <a id="18037" class="Symbol">:</a>
    <a id="18043" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="18052" class="Symbol">(</a><a id="18053" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15665" class="Function">inv-map-colimit-zigzag-sequential-diagram</a> <a id="18095" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a> <a id="18100" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a> <a id="18106" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a><a id="18107" class="Symbol">)</a>
  <a id="18111" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="18115" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17986" class="Function">is-equiv-inv-map-colimit-zigzag-sequential-diagram</a> <a id="18166" class="Symbol">=</a>
    <a id="18172" class="Symbol">(</a> <a id="18174" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a> <a id="18212" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a> <a id="18217" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a> <a id="18223" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a><a id="18224" class="Symbol">)</a> <a id="18226" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="18232" class="Symbol">(</a> <a id="18234" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16677" class="Function">is-retraction-inv-map-colimit-zigzag-sequential-diagram</a> <a id="18290" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a> <a id="18295" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a> <a id="18301" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a><a id="18302" class="Symbol">)</a>
  <a id="18306" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="18310" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17986" class="Function">is-equiv-inv-map-colimit-zigzag-sequential-diagram</a> <a id="18361" class="Symbol">=</a>
    <a id="18367" class="Symbol">(</a> <a id="18369" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a>
      <a id="18413" class="Symbol">(</a> <a id="18415" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="18450" class="Number">1</a> <a id="18452" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a><a id="18456" class="Symbol">)</a>
      <a id="18464" class="Symbol">(</a> <a id="18466" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="18501" class="Number">1</a> <a id="18503" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a><a id="18508" class="Symbol">)</a>
      <a id="18516" class="Symbol">(</a> <a id="18518" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5978" class="Function">shift-zigzag-sequential-diagram</a> <a id="18550" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a><a id="18551" class="Symbol">))</a> <a id="18554" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="18560" class="Symbol">(</a> <a id="18562" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#16677" class="Function">is-retraction-inv-map-colimit-zigzag-sequential-diagram</a>
      <a id="18624" class="Symbol">(</a> <a id="18626" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a><a id="18631" class="Symbol">)</a>
      <a id="18639" class="Symbol">(</a> <a id="18641" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="18676" class="Number">1</a> <a id="18678" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a><a id="18682" class="Symbol">)</a>
      <a id="18690" class="Symbol">(</a> <a id="18692" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#5334" class="Function">half-shift-zigzag-sequential-diagram</a> <a id="18729" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a><a id="18730" class="Symbol">))</a>

  <a id="18736" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#18736" class="Function">inv-equiv-colimit-zigzag-sequential-diagram</a> <a id="18780" class="Symbol">:</a> <a id="18782" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17167" class="Bound">Y</a> <a id="18784" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="18786" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17066" class="Bound">X</a>
  <a id="18790" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="18794" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#18736" class="Function">inv-equiv-colimit-zigzag-sequential-diagram</a> <a id="18838" class="Symbol">=</a>
    <a id="18844" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15665" class="Function">inv-map-colimit-zigzag-sequential-diagram</a> <a id="18886" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a> <a id="18891" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a> <a id="18897" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a>
  <a id="18901" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="18905" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#18736" class="Function">inv-equiv-colimit-zigzag-sequential-diagram</a> <a id="18949" class="Symbol">=</a>
    <a id="18955" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17986" class="Function">is-equiv-inv-map-colimit-zigzag-sequential-diagram</a>

  <a id="19009" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#19009" class="Function">equiv-colimit-zigzag-sequential-diagram</a> <a id="19049" class="Symbol">:</a> <a id="19051" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17066" class="Bound">X</a> <a id="19053" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="19055" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17167" class="Bound">Y</a>
  <a id="19059" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="19063" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#19009" class="Function">equiv-colimit-zigzag-sequential-diagram</a> <a id="19103" class="Symbol">=</a>
    <a id="19109" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#15449" class="Function">map-colimit-zigzag-sequential-diagram</a> <a id="19147" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17116" class="Bound">up-c</a> <a id="19152" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17218" class="Bound">up-c&#39;</a> <a id="19158" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#17271" class="Bound">z</a>
  <a id="19162" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="19166" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#19009" class="Function">equiv-colimit-zigzag-sequential-diagram</a> <a id="19206" class="Symbol">=</a>
    <a id="19212" href="foundation-core.equivalences.html#8732" class="Function">is-equiv-map-inv-equiv</a> <a id="19235" href="synthetic-homotopy-theory.zigzags-sequential-diagrams.html#18736" class="Function">inv-equiv-colimit-zigzag-sequential-diagram</a>
</pre>