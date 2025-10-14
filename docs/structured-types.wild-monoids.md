# Wild monoids

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="structured-types.wild-monoids.html" class="Module">structured-types.wild-monoids</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="structured-types.h-spaces.html" class="Module">structured-types.h-spaces</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

A **wild monoid** is a first–order approximation to an ∞-monoid, i.e. a
∞-monoid-like structure whose laws hold at least up to the first homotopy level,
but may fail at higher levels.

A wild monoid consists of

- an underlying type `A`
- a unit, say `e : A`
- a binary operation on `A`, say `_*_`
- left and right unit laws `e * x ＝ x` and `x * e ＝ x`
- a coherence between the left and right unit laws at the unit
- an associator `(x y z : A) → (x * y) * z ＝ x * (y * z)`
- coherences between the associator and the left and right unit laws

We call such an associator **unital**. It may be described as a coherence of the
following diagram

```text
          map-associative-product
     (A × A) × A ----> A × (A × A)
             |           |
  (_*_ , id) |           | (id, _*_)
             ∨           ∨
           A × A       A × A
               \       /
          (_*_) \     / (_*_)
                 ∨   ∨
                   A
```

such that the three diagrams below cohere

```text
            associator
  (e * x) * y ===== e * (x * y)
          \\         //
     left  \\       //  left
   unit law \\     // unit law
              y * z,
```

```text
            associator
  (x * e) * y ===== x * (e * y)
          \\         //
    right  \\       //  left
   unit law \\     // unit law
              x * y,
```

and

```text
            associator
  (x * y) * e ===== x * (y * e)
          \\         //
    right  \\       //  right
   unit law \\     // unit law
              x * y
```

for all `x y : A`.

Concretely, we define wild monoids to be
[H-spaces](structured-types.h-spaces.md) equipped with a unital associator.

## Definition

### Unital associators on H-spaces

<pre class="Agda"><a id="2148" class="Keyword">module</a> <a id="2155" href="structured-types.wild-monoids.html#2155" class="Module">_</a>
  <a id="2159" class="Symbol">{</a><a id="2160" href="structured-types.wild-monoids.html#2160" class="Bound">l</a> <a id="2162" class="Symbol">:</a> <a id="2164" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2169" class="Symbol">}</a> <a id="2171" class="Symbol">(</a><a id="2172" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2174" class="Symbol">:</a> <a id="2176" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="2184" href="structured-types.wild-monoids.html#2160" class="Bound">l</a><a id="2185" class="Symbol">)</a>
  <a id="2189" class="Keyword">where</a>

  <a id="2198" href="structured-types.wild-monoids.html#2198" class="Function">associator-H-Space</a> <a id="2217" class="Symbol">:</a> <a id="2219" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2222" href="structured-types.wild-monoids.html#2160" class="Bound">l</a>
  <a id="2226" href="structured-types.wild-monoids.html#2198" class="Function">associator-H-Space</a> <a id="2245" class="Symbol">=</a>
    <a id="2251" class="Symbol">(</a><a id="2252" href="structured-types.wild-monoids.html#2252" class="Bound">x</a> <a id="2254" href="structured-types.wild-monoids.html#2254" class="Bound">y</a> <a id="2256" href="structured-types.wild-monoids.html#2256" class="Bound">z</a> <a id="2258" class="Symbol">:</a> <a id="2260" href="structured-types.h-spaces.html#2880" class="Function">type-H-Space</a> <a id="2273" href="structured-types.wild-monoids.html#2172" class="Bound">M</a><a id="2274" class="Symbol">)</a> <a id="2276" class="Symbol">→</a>
    <a id="2282" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a>
      <a id="2291" class="Symbol">(</a> <a id="2293" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="2305" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2307" class="Symbol">(</a><a id="2308" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="2320" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2322" href="structured-types.wild-monoids.html#2252" class="Bound">x</a> <a id="2324" href="structured-types.wild-monoids.html#2254" class="Bound">y</a><a id="2325" class="Symbol">)</a> <a id="2327" href="structured-types.wild-monoids.html#2256" class="Bound">z</a><a id="2328" class="Symbol">)</a>
      <a id="2336" class="Symbol">(</a> <a id="2338" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="2350" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2352" href="structured-types.wild-monoids.html#2252" class="Bound">x</a> <a id="2354" class="Symbol">(</a><a id="2355" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="2367" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2369" href="structured-types.wild-monoids.html#2254" class="Bound">y</a> <a id="2371" href="structured-types.wild-monoids.html#2256" class="Bound">z</a><a id="2372" class="Symbol">))</a>

  <a id="2378" href="structured-types.wild-monoids.html#2378" class="Function">is-unital-associator</a> <a id="2399" class="Symbol">:</a> <a id="2401" class="Symbol">(</a><a id="2402" href="structured-types.wild-monoids.html#2402" class="Bound">α</a> <a id="2404" class="Symbol">:</a> <a id="2406" href="structured-types.wild-monoids.html#2198" class="Function">associator-H-Space</a><a id="2424" class="Symbol">)</a> <a id="2426" class="Symbol">→</a> <a id="2428" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2431" href="structured-types.wild-monoids.html#2160" class="Bound">l</a>
  <a id="2435" href="structured-types.wild-monoids.html#2378" class="Function">is-unital-associator</a> <a id="2456" href="structured-types.wild-monoids.html#2456" class="Bound">α111</a> <a id="2461" class="Symbol">=</a>
    <a id="2467" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2469" class="Symbol">(</a> <a id="2471" class="Symbol">(</a><a id="2472" href="structured-types.wild-monoids.html#2472" class="Bound">y</a> <a id="2474" href="structured-types.wild-monoids.html#2474" class="Bound">z</a> <a id="2476" class="Symbol">:</a> <a id="2478" href="structured-types.h-spaces.html#2880" class="Function">type-H-Space</a> <a id="2491" href="structured-types.wild-monoids.html#2172" class="Bound">M</a><a id="2492" class="Symbol">)</a> <a id="2494" class="Symbol">→</a>
        <a id="2504" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a>
          <a id="2517" class="Symbol">(</a> <a id="2519" class="Symbol">(</a> <a id="2521" href="structured-types.wild-monoids.html#2456" class="Bound">α111</a> <a id="2526" class="Symbol">(</a><a id="2527" href="structured-types.h-spaces.html#2959" class="Function">unit-H-Space</a> <a id="2540" href="structured-types.wild-monoids.html#2172" class="Bound">M</a><a id="2541" class="Symbol">)</a> <a id="2543" href="structured-types.wild-monoids.html#2472" class="Bound">y</a> <a id="2545" href="structured-types.wild-monoids.html#2474" class="Bound">z</a><a id="2546" class="Symbol">)</a> <a id="2548" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
            <a id="2562" class="Symbol">(</a> <a id="2564" href="structured-types.h-spaces.html#3802" class="Function">left-unit-law-mul-H-Space</a> <a id="2590" href="structured-types.wild-monoids.html#2172" class="Bound">M</a>
              <a id="2606" class="Symbol">(</a> <a id="2608" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="2620" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2622" href="structured-types.wild-monoids.html#2472" class="Bound">y</a> <a id="2624" href="structured-types.wild-monoids.html#2474" class="Bound">z</a><a id="2625" class="Symbol">)))</a>
            <a id="2641" class="Symbol">(</a> <a id="2643" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
              <a id="2660" class="Symbol">(</a> <a id="2662" href="structured-types.h-spaces.html#3288" class="Function">mul-H-Space&#39;</a> <a id="2675" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2677" href="structured-types.wild-monoids.html#2474" class="Bound">z</a><a id="2678" class="Symbol">)</a>
              <a id="2694" class="Symbol">(</a> <a id="2696" href="structured-types.h-spaces.html#3802" class="Function">left-unit-law-mul-H-Space</a> <a id="2722" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2724" href="structured-types.wild-monoids.html#2472" class="Bound">y</a><a id="2725" class="Symbol">)))</a>
      <a id="2735" class="Symbol">(</a> <a id="2737" class="Symbol">λ</a> <a id="2739" href="structured-types.wild-monoids.html#2739" class="Bound">α011</a> <a id="2744" class="Symbol">→</a>
        <a id="2754" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2756" class="Symbol">(</a> <a id="2758" class="Symbol">(</a><a id="2759" href="structured-types.wild-monoids.html#2759" class="Bound">x</a> <a id="2761" href="structured-types.wild-monoids.html#2761" class="Bound">z</a> <a id="2763" class="Symbol">:</a> <a id="2765" href="structured-types.h-spaces.html#2880" class="Function">type-H-Space</a> <a id="2778" href="structured-types.wild-monoids.html#2172" class="Bound">M</a><a id="2779" class="Symbol">)</a> <a id="2781" class="Symbol">→</a>
            <a id="2795" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a>
              <a id="2812" class="Symbol">(</a> <a id="2814" class="Symbol">(</a> <a id="2816" href="structured-types.wild-monoids.html#2456" class="Bound">α111</a> <a id="2821" href="structured-types.wild-monoids.html#2759" class="Bound">x</a> <a id="2823" class="Symbol">(</a><a id="2824" href="structured-types.h-spaces.html#2959" class="Function">unit-H-Space</a> <a id="2837" href="structured-types.wild-monoids.html#2172" class="Bound">M</a><a id="2838" class="Symbol">)</a> <a id="2840" href="structured-types.wild-monoids.html#2761" class="Bound">z</a><a id="2841" class="Symbol">)</a> <a id="2843" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
                <a id="2861" class="Symbol">(</a> <a id="2863" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
                  <a id="2884" class="Symbol">(</a> <a id="2886" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="2898" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2900" href="structured-types.wild-monoids.html#2759" class="Bound">x</a><a id="2901" class="Symbol">)</a>
                  <a id="2921" class="Symbol">(</a> <a id="2923" href="structured-types.h-spaces.html#3802" class="Function">left-unit-law-mul-H-Space</a> <a id="2949" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="2951" href="structured-types.wild-monoids.html#2761" class="Bound">z</a><a id="2952" class="Symbol">)))</a>
              <a id="2970" class="Symbol">(</a> <a id="2972" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
                <a id="2991" class="Symbol">(</a> <a id="2993" href="structured-types.h-spaces.html#3288" class="Function">mul-H-Space&#39;</a> <a id="3006" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="3008" href="structured-types.wild-monoids.html#2761" class="Bound">z</a><a id="3009" class="Symbol">)</a>
                <a id="3027" class="Symbol">(</a> <a id="3029" href="structured-types.h-spaces.html#3965" class="Function">right-unit-law-mul-H-Space</a> <a id="3056" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="3058" href="structured-types.wild-monoids.html#2759" class="Bound">x</a><a id="3059" class="Symbol">)))</a>
          <a id="3073" class="Symbol">(</a> <a id="3075" class="Symbol">λ</a> <a id="3077" href="structured-types.wild-monoids.html#3077" class="Bound">α101</a> <a id="3082" class="Symbol">→</a>
            <a id="3096" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3098" class="Symbol">(</a> <a id="3100" class="Symbol">(</a><a id="3101" href="structured-types.wild-monoids.html#3101" class="Bound">x</a> <a id="3103" href="structured-types.wild-monoids.html#3103" class="Bound">y</a> <a id="3105" class="Symbol">:</a> <a id="3107" href="structured-types.h-spaces.html#2880" class="Function">type-H-Space</a> <a id="3120" href="structured-types.wild-monoids.html#2172" class="Bound">M</a><a id="3121" class="Symbol">)</a> <a id="3123" class="Symbol">→</a>
                <a id="3141" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a>
                  <a id="3162" class="Symbol">(</a> <a id="3164" class="Symbol">(</a> <a id="3166" href="structured-types.wild-monoids.html#2456" class="Bound">α111</a> <a id="3171" href="structured-types.wild-monoids.html#3101" class="Bound">x</a> <a id="3173" href="structured-types.wild-monoids.html#3103" class="Bound">y</a> <a id="3175" class="Symbol">(</a><a id="3176" href="structured-types.h-spaces.html#2959" class="Function">unit-H-Space</a> <a id="3189" href="structured-types.wild-monoids.html#2172" class="Bound">M</a><a id="3190" class="Symbol">))</a> <a id="3193" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
                    <a id="3215" class="Symbol">(</a> <a id="3217" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
                      <a id="3242" class="Symbol">(</a> <a id="3244" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="3256" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="3258" href="structured-types.wild-monoids.html#3101" class="Bound">x</a><a id="3259" class="Symbol">)</a>
                      <a id="3283" class="Symbol">(</a> <a id="3285" href="structured-types.h-spaces.html#3965" class="Function">right-unit-law-mul-H-Space</a> <a id="3312" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="3314" href="structured-types.wild-monoids.html#3103" class="Bound">y</a><a id="3315" class="Symbol">)))</a>
                  <a id="3337" class="Symbol">(</a> <a id="3339" href="structured-types.h-spaces.html#3965" class="Function">right-unit-law-mul-H-Space</a> <a id="3366" href="structured-types.wild-monoids.html#2172" class="Bound">M</a>
                    <a id="3388" class="Symbol">(</a> <a id="3390" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="3402" href="structured-types.wild-monoids.html#2172" class="Bound">M</a> <a id="3404" href="structured-types.wild-monoids.html#3101" class="Bound">x</a> <a id="3406" href="structured-types.wild-monoids.html#3103" class="Bound">y</a><a id="3407" class="Symbol">)))</a>
              <a id="3425" class="Symbol">(</a> <a id="3427" class="Symbol">λ</a> <a id="3429" href="structured-types.wild-monoids.html#3429" class="Bound">α110</a> <a id="3434" class="Symbol">→</a> <a id="3436" href="foundation.unit-type.html#950" class="Record">unit</a><a id="3440" class="Symbol">)))</a>

  <a id="3447" href="structured-types.wild-monoids.html#3447" class="Function">unital-associator</a> <a id="3465" class="Symbol">:</a> <a id="3467" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3470" href="structured-types.wild-monoids.html#2160" class="Bound">l</a>
  <a id="3474" href="structured-types.wild-monoids.html#3447" class="Function">unital-associator</a> <a id="3492" class="Symbol">=</a> <a id="3494" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3496" class="Symbol">(</a><a id="3497" href="structured-types.wild-monoids.html#2198" class="Function">associator-H-Space</a><a id="3515" class="Symbol">)</a> <a id="3517" class="Symbol">(</a><a id="3518" href="structured-types.wild-monoids.html#2378" class="Function">is-unital-associator</a><a id="3538" class="Symbol">)</a>
</pre>
### Wild monoids

<pre class="Agda"><a id="Wild-Monoid"></a><a id="3571" href="structured-types.wild-monoids.html#3571" class="Function">Wild-Monoid</a> <a id="3583" class="Symbol">:</a> <a id="3585" class="Symbol">(</a><a id="3586" href="structured-types.wild-monoids.html#3586" class="Bound">l</a> <a id="3588" class="Symbol">:</a> <a id="3590" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3595" class="Symbol">)</a> <a id="3597" class="Symbol">→</a> <a id="3599" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3602" class="Symbol">(</a><a id="3603" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3608" href="structured-types.wild-monoids.html#3586" class="Bound">l</a><a id="3609" class="Symbol">)</a>
<a id="3611" href="structured-types.wild-monoids.html#3571" class="Function">Wild-Monoid</a> <a id="3623" href="structured-types.wild-monoids.html#3623" class="Bound">l</a> <a id="3625" class="Symbol">=</a>
  <a id="3629" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3631" class="Symbol">(</a><a id="3632" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="3640" href="structured-types.wild-monoids.html#3623" class="Bound">l</a><a id="3641" class="Symbol">)</a> <a id="3643" href="structured-types.wild-monoids.html#3447" class="Function">unital-associator</a>

<a id="3662" class="Keyword">module</a> <a id="3669" href="structured-types.wild-monoids.html#3669" class="Module">_</a>
  <a id="3673" class="Symbol">{</a><a id="3674" href="structured-types.wild-monoids.html#3674" class="Bound">l</a> <a id="3676" class="Symbol">:</a> <a id="3678" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3683" class="Symbol">}</a> <a id="3685" class="Symbol">(</a><a id="3686" href="structured-types.wild-monoids.html#3686" class="Bound">M</a> <a id="3688" class="Symbol">:</a> <a id="3690" href="structured-types.wild-monoids.html#3571" class="Function">Wild-Monoid</a> <a id="3702" href="structured-types.wild-monoids.html#3674" class="Bound">l</a><a id="3703" class="Symbol">)</a>
  <a id="3707" class="Keyword">where</a>

  <a id="3716" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a> <a id="3736" class="Symbol">:</a> <a id="3738" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="3746" href="structured-types.wild-monoids.html#3674" class="Bound">l</a>
  <a id="3750" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a> <a id="3770" class="Symbol">=</a> <a id="3772" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3776" href="structured-types.wild-monoids.html#3686" class="Bound">M</a>

  <a id="3781" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a> <a id="3798" class="Symbol">:</a> <a id="3800" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3803" href="structured-types.wild-monoids.html#3674" class="Bound">l</a>
  <a id="3807" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a> <a id="3824" class="Symbol">=</a> <a id="3826" href="structured-types.h-spaces.html#2880" class="Function">type-H-Space</a> <a id="3839" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="3862" href="structured-types.wild-monoids.html#3862" class="Function">unit-Wild-Monoid</a> <a id="3879" class="Symbol">:</a> <a id="3881" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a>
  <a id="3900" href="structured-types.wild-monoids.html#3862" class="Function">unit-Wild-Monoid</a> <a id="3917" class="Symbol">=</a> <a id="3919" href="structured-types.h-spaces.html#2959" class="Function">unit-H-Space</a> <a id="3932" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="3955" href="structured-types.wild-monoids.html#3955" class="Function">pointed-type-Wild-Monoid</a> <a id="3980" class="Symbol">:</a> <a id="3982" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3995" href="structured-types.wild-monoids.html#3674" class="Bound">l</a>
  <a id="3999" href="structured-types.wild-monoids.html#3955" class="Function">pointed-type-Wild-Monoid</a> <a id="4024" class="Symbol">=</a>
    <a id="4030" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="4051" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="4074" href="structured-types.wild-monoids.html#4074" class="Function">coherent-unital-mul-Wild-Monoid</a> <a id="4106" class="Symbol">:</a>
    <a id="4112" href="structured-types.h-spaces.html#1659" class="Function">coherent-unital-mul-Pointed-Type</a> <a id="4145" href="structured-types.wild-monoids.html#3955" class="Function">pointed-type-Wild-Monoid</a>
  <a id="4172" href="structured-types.wild-monoids.html#4074" class="Function">coherent-unital-mul-Wild-Monoid</a> <a id="4204" class="Symbol">=</a>
    <a id="4210" href="structured-types.h-spaces.html#3047" class="Function">coherent-unital-mul-H-Space</a> <a id="4238" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="4261" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="4277" class="Symbol">:</a> <a id="4279" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a> <a id="4296" class="Symbol">→</a> <a id="4298" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a> <a id="4315" class="Symbol">→</a> <a id="4317" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a>
  <a id="4336" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="4352" class="Symbol">=</a> <a id="4354" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="4366" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="4389" href="structured-types.wild-monoids.html#4389" class="Function">mul-Wild-Monoid&#39;</a> <a id="4406" class="Symbol">:</a> <a id="4408" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a> <a id="4425" class="Symbol">→</a> <a id="4427" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a> <a id="4444" class="Symbol">→</a> <a id="4446" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a>
  <a id="4465" href="structured-types.wild-monoids.html#4389" class="Function">mul-Wild-Monoid&#39;</a> <a id="4482" class="Symbol">=</a> <a id="4484" href="structured-types.h-spaces.html#3288" class="Function">mul-H-Space&#39;</a> <a id="4497" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="4520" href="structured-types.wild-monoids.html#4520" class="Function">ap-mul-Wild-Monoid</a> <a id="4539" class="Symbol">:</a>
    <a id="4545" class="Symbol">{</a><a id="4546" href="structured-types.wild-monoids.html#4546" class="Bound">a</a> <a id="4548" href="structured-types.wild-monoids.html#4548" class="Bound">b</a> <a id="4550" href="structured-types.wild-monoids.html#4550" class="Bound">c</a> <a id="4552" href="structured-types.wild-monoids.html#4552" class="Bound">d</a> <a id="4554" class="Symbol">:</a> <a id="4556" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a><a id="4572" class="Symbol">}</a> <a id="4574" class="Symbol">→</a>
    <a id="4580" href="structured-types.wild-monoids.html#4546" class="Bound">a</a> <a id="4582" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4584" href="structured-types.wild-monoids.html#4548" class="Bound">b</a> <a id="4586" class="Symbol">→</a> <a id="4588" href="structured-types.wild-monoids.html#4550" class="Bound">c</a> <a id="4590" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4592" href="structured-types.wild-monoids.html#4552" class="Bound">d</a> <a id="4594" class="Symbol">→</a> <a id="4596" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="4612" href="structured-types.wild-monoids.html#4546" class="Bound">a</a> <a id="4614" href="structured-types.wild-monoids.html#4550" class="Bound">c</a> <a id="4616" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4618" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="4634" href="structured-types.wild-monoids.html#4548" class="Bound">b</a> <a id="4636" href="structured-types.wild-monoids.html#4552" class="Bound">d</a>
  <a id="4640" href="structured-types.wild-monoids.html#4520" class="Function">ap-mul-Wild-Monoid</a> <a id="4659" class="Symbol">=</a> <a id="4661" href="structured-types.h-spaces.html#3390" class="Function">ap-mul-H-Space</a> <a id="4676" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="4699" href="structured-types.wild-monoids.html#4699" class="Function">left-unit-law-mul-Wild-Monoid</a> <a id="4729" class="Symbol">:</a>
    <a id="4735" class="Symbol">(</a><a id="4736" href="structured-types.wild-monoids.html#4736" class="Bound">x</a> <a id="4738" class="Symbol">:</a> <a id="4740" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a><a id="4756" class="Symbol">)</a> <a id="4758" class="Symbol">→</a> <a id="4760" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="4776" href="structured-types.wild-monoids.html#3862" class="Function">unit-Wild-Monoid</a> <a id="4793" href="structured-types.wild-monoids.html#4736" class="Bound">x</a> <a id="4795" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4797" href="structured-types.wild-monoids.html#4736" class="Bound">x</a>
  <a id="4801" href="structured-types.wild-monoids.html#4699" class="Function">left-unit-law-mul-Wild-Monoid</a> <a id="4831" class="Symbol">=</a>
    <a id="4837" href="structured-types.h-spaces.html#3802" class="Function">left-unit-law-mul-H-Space</a> <a id="4863" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="4886" href="structured-types.wild-monoids.html#4886" class="Function">right-unit-law-mul-Wild-Monoid</a> <a id="4917" class="Symbol">:</a>
    <a id="4923" class="Symbol">(</a><a id="4924" href="structured-types.wild-monoids.html#4924" class="Bound">x</a> <a id="4926" class="Symbol">:</a> <a id="4928" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a><a id="4944" class="Symbol">)</a> <a id="4946" class="Symbol">→</a> <a id="4948" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="4964" href="structured-types.wild-monoids.html#4924" class="Bound">x</a> <a id="4966" href="structured-types.wild-monoids.html#3862" class="Function">unit-Wild-Monoid</a> <a id="4983" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4985" href="structured-types.wild-monoids.html#4924" class="Bound">x</a>
  <a id="4989" href="structured-types.wild-monoids.html#4886" class="Function">right-unit-law-mul-Wild-Monoid</a> <a id="5020" class="Symbol">=</a>
    <a id="5026" href="structured-types.h-spaces.html#3965" class="Function">right-unit-law-mul-H-Space</a> <a id="5053" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="5076" href="structured-types.wild-monoids.html#5076" class="Function">coh-unit-laws-mul-Wild-Monoid</a> <a id="5106" class="Symbol">:</a>
    <a id="5112" class="Symbol">(</a> <a id="5114" href="structured-types.wild-monoids.html#4699" class="Function">left-unit-law-mul-Wild-Monoid</a> <a id="5144" href="structured-types.wild-monoids.html#3862" class="Function">unit-Wild-Monoid</a><a id="5160" class="Symbol">)</a> <a id="5162" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="5168" class="Symbol">(</a> <a id="5170" href="structured-types.wild-monoids.html#4886" class="Function">right-unit-law-mul-Wild-Monoid</a> <a id="5201" href="structured-types.wild-monoids.html#3862" class="Function">unit-Wild-Monoid</a><a id="5217" class="Symbol">)</a>
  <a id="5221" href="structured-types.wild-monoids.html#5076" class="Function">coh-unit-laws-mul-Wild-Monoid</a> <a id="5251" class="Symbol">=</a>
    <a id="5257" href="structured-types.h-spaces.html#4136" class="Function">coh-unit-laws-mul-H-Space</a> <a id="5283" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>

  <a id="5306" href="structured-types.wild-monoids.html#5306" class="Function">unital-associator-Wild-Monoid</a> <a id="5336" class="Symbol">:</a>
    <a id="5342" href="structured-types.wild-monoids.html#3447" class="Function">unital-associator</a> <a id="5360" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>
  <a id="5382" href="structured-types.wild-monoids.html#5306" class="Function">unital-associator-Wild-Monoid</a> <a id="5412" class="Symbol">=</a> <a id="5414" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5418" href="structured-types.wild-monoids.html#3686" class="Bound">M</a>

  <a id="5423" href="structured-types.wild-monoids.html#5423" class="Function">associator-Wild-Monoid</a> <a id="5446" class="Symbol">:</a>
    <a id="5452" href="structured-types.wild-monoids.html#2198" class="Function">associator-H-Space</a> <a id="5471" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a>
  <a id="5493" href="structured-types.wild-monoids.html#5423" class="Function">associator-Wild-Monoid</a> <a id="5516" class="Symbol">=</a> <a id="5518" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5522" href="structured-types.wild-monoids.html#5306" class="Function">unital-associator-Wild-Monoid</a>

  <a id="5555" href="structured-types.wild-monoids.html#5555" class="Function">associative-mul-Wild-Monoid</a> <a id="5583" class="Symbol">:</a>
    <a id="5589" class="Symbol">(</a><a id="5590" href="structured-types.wild-monoids.html#5590" class="Bound">x</a> <a id="5592" href="structured-types.wild-monoids.html#5592" class="Bound">y</a> <a id="5594" href="structured-types.wild-monoids.html#5594" class="Bound">z</a> <a id="5596" class="Symbol">:</a> <a id="5598" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a><a id="5614" class="Symbol">)</a> <a id="5616" class="Symbol">→</a>
    <a id="5622" class="Symbol">(</a> <a id="5624" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="5640" class="Symbol">(</a><a id="5641" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="5657" href="structured-types.wild-monoids.html#5590" class="Bound">x</a> <a id="5659" href="structured-types.wild-monoids.html#5592" class="Bound">y</a><a id="5660" class="Symbol">)</a> <a id="5662" href="structured-types.wild-monoids.html#5594" class="Bound">z</a><a id="5663" class="Symbol">)</a> <a id="5665" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="5671" class="Symbol">(</a> <a id="5673" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="5689" href="structured-types.wild-monoids.html#5590" class="Bound">x</a> <a id="5691" class="Symbol">(</a><a id="5692" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="5708" href="structured-types.wild-monoids.html#5592" class="Bound">y</a> <a id="5710" href="structured-types.wild-monoids.html#5594" class="Bound">z</a><a id="5711" class="Symbol">))</a>
  <a id="5716" href="structured-types.wild-monoids.html#5555" class="Function">associative-mul-Wild-Monoid</a> <a id="5744" class="Symbol">=</a> <a id="5746" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5750" href="structured-types.wild-monoids.html#5306" class="Function">unital-associator-Wild-Monoid</a>

  <a id="5783" href="structured-types.wild-monoids.html#5783" class="Function">unit-law-110-associative-Wild-Monoid</a> <a id="5820" class="Symbol">:</a>
    <a id="5826" class="Symbol">(</a><a id="5827" href="structured-types.wild-monoids.html#5827" class="Bound">x</a> <a id="5829" href="structured-types.wild-monoids.html#5829" class="Bound">y</a> <a id="5831" class="Symbol">:</a> <a id="5833" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a><a id="5849" class="Symbol">)</a> <a id="5851" class="Symbol">→</a>
    <a id="5857" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a>
      <a id="5866" class="Symbol">(</a> <a id="5868" class="Symbol">(</a> <a id="5870" href="structured-types.wild-monoids.html#5555" class="Function">associative-mul-Wild-Monoid</a> <a id="5898" href="structured-types.wild-monoids.html#5827" class="Bound">x</a> <a id="5900" href="structured-types.wild-monoids.html#5829" class="Bound">y</a> <a id="5902" href="structured-types.wild-monoids.html#3862" class="Function">unit-Wild-Monoid</a><a id="5918" class="Symbol">)</a> <a id="5920" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
        <a id="5930" class="Symbol">(</a> <a id="5932" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="5935" class="Symbol">(</a><a id="5936" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="5952" href="structured-types.wild-monoids.html#5827" class="Bound">x</a><a id="5953" class="Symbol">)</a> <a id="5955" class="Symbol">(</a><a id="5956" href="structured-types.wild-monoids.html#4886" class="Function">right-unit-law-mul-Wild-Monoid</a> <a id="5987" href="structured-types.wild-monoids.html#5829" class="Bound">y</a><a id="5988" class="Symbol">)))</a>
      <a id="5998" class="Symbol">(</a> <a id="6000" href="structured-types.wild-monoids.html#4886" class="Function">right-unit-law-mul-Wild-Monoid</a> <a id="6031" class="Symbol">(</a><a id="6032" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="6048" href="structured-types.wild-monoids.html#5827" class="Bound">x</a> <a id="6050" href="structured-types.wild-monoids.html#5829" class="Bound">y</a><a id="6051" class="Symbol">))</a>
  <a id="6056" href="structured-types.wild-monoids.html#5783" class="Function">unit-law-110-associative-Wild-Monoid</a> <a id="6093" class="Symbol">=</a> <a id="6095" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="6099" class="Symbol">(</a><a id="6100" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="6104" class="Symbol">(</a><a id="6105" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="6109" class="Symbol">(</a><a id="6110" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="6114" class="Symbol">(</a><a id="6115" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="6119" href="structured-types.wild-monoids.html#3686" class="Bound">M</a><a id="6120" class="Symbol">))))</a>
</pre>