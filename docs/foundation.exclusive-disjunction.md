# Exclusive disjunctions

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="foundation.exclusive-disjunction.html" class="Module">foundation.exclusive-disjunction</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a>
<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="foundation.exclusive-sum.html" class="Module">foundation.exclusive-sum</a>
<a id="341" class="Keyword">open</a> <a id="346" class="Keyword">import</a> <a id="353" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="foundation.type-arithmetic-cartesian-product-types.html" class="Module">foundation.type-arithmetic-cartesian-product-types</a>
<a id="506" class="Keyword">open</a> <a id="511" class="Keyword">import</a> <a id="518" href="foundation.type-arithmetic-coproduct-types.html" class="Module">foundation.type-arithmetic-coproduct-types</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="foundation.universal-property-coproduct-types.html" class="Module">foundation.universal-property-coproduct-types</a>
<a id="619" class="Keyword">open</a> <a id="624" class="Keyword">import</a> <a id="631" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="659" class="Keyword">open</a> <a id="664" class="Keyword">import</a> <a id="671" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="698" class="Keyword">open</a> <a id="703" class="Keyword">import</a> <a id="710" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="739" class="Keyword">open</a> <a id="744" class="Keyword">import</a> <a id="751" href="foundation-core.functoriality-dependent-function-types.html" class="Module">foundation-core.functoriality-dependent-function-types</a>
<a id="806" class="Keyword">open</a> <a id="811" class="Keyword">import</a> <a id="818" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="869" class="Keyword">open</a> <a id="874" class="Keyword">import</a> <a id="881" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="912" class="Keyword">open</a> <a id="917" class="Keyword">import</a> <a id="924" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

The
{{#concept "exclusive disjunction" Disambiguation="of propositions" WDID=Q498186 WD="exclusive or" Agda=xor-Prop}}
of two [propositions](foundation-core.propositions.md) `P` and `Q` is the
proposition that precisely one of `P` and `Q` holds, and is defined as the
proposition that the [coproduct](foundation-core.coproduct-types.md) of their
underlying types is [contractible](foundation-core.contractible-types.md)

```text
  P ⊻ Q := is-contr (P + Q)
```

It necessarily follows that precisely one of the two propositions hold, and the
other does not. This is captured by the
[exclusive sum](foundation.exclusive-sum.md).

## Definitions

### The exclusive disjunction of arbitrary types

The definition of exclusive sum is sometimes generalized to arbitrary types,
which we record here for completeness.

The
{{#concept "exclusive disjunction" Disambiguation="of types" Agda=xor-type-Prop}}
of the types `A` and `B` is the proposition that their coproduct is contractible

```text
  A ⊻ B := is-contr (A + B).
```

Note that unlike the case for [disjunction](foundation.disjunction.md) and
[existential quantification](foundation.existential-quantification.md), but
analogous to the case of
[uniqueness quantification](foundation.uniqueness-quantification.md), the
exclusive disjunction of types does _not_ coincide with the exclusive
disjunction of the summands'
[propositional reflections](foundation.propositional-truncations.md):

```text
  A ⊻ B ≠ ║ A ║₋₁ ⊻ ║ B ║₋₁.
```

<pre class="Agda"><a id="2471" class="Keyword">module</a> <a id="2478" href="foundation.exclusive-disjunction.html#2478" class="Module">_</a>
  <a id="2482" class="Symbol">{</a><a id="2483" href="foundation.exclusive-disjunction.html#2483" class="Bound">l1</a> <a id="2486" href="foundation.exclusive-disjunction.html#2486" class="Bound">l2</a> <a id="2489" class="Symbol">:</a> <a id="2491" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2496" class="Symbol">}</a> <a id="2498" class="Symbol">(</a><a id="2499" href="foundation.exclusive-disjunction.html#2499" class="Bound">A</a> <a id="2501" class="Symbol">:</a> <a id="2503" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2506" href="foundation.exclusive-disjunction.html#2483" class="Bound">l1</a><a id="2508" class="Symbol">)</a> <a id="2510" class="Symbol">(</a><a id="2511" href="foundation.exclusive-disjunction.html#2511" class="Bound">B</a> <a id="2513" class="Symbol">:</a> <a id="2515" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2518" href="foundation.exclusive-disjunction.html#2486" class="Bound">l2</a><a id="2520" class="Symbol">)</a>
  <a id="2524" class="Keyword">where</a>

  <a id="2533" href="foundation.exclusive-disjunction.html#2533" class="Function">xor-type-Prop</a> <a id="2547" class="Symbol">:</a> <a id="2549" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2554" class="Symbol">(</a><a id="2555" href="foundation.exclusive-disjunction.html#2483" class="Bound">l1</a> <a id="2558" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2560" href="foundation.exclusive-disjunction.html#2486" class="Bound">l2</a><a id="2562" class="Symbol">)</a>
  <a id="2566" href="foundation.exclusive-disjunction.html#2533" class="Function">xor-type-Prop</a> <a id="2580" class="Symbol">=</a> <a id="2582" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="2596" class="Symbol">(</a><a id="2597" href="foundation.exclusive-disjunction.html#2499" class="Bound">A</a> <a id="2599" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="2601" href="foundation.exclusive-disjunction.html#2511" class="Bound">B</a><a id="2602" class="Symbol">)</a>

  <a id="2607" href="foundation.exclusive-disjunction.html#2607" class="Function">xor-type</a> <a id="2616" class="Symbol">:</a> <a id="2618" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2621" class="Symbol">(</a><a id="2622" href="foundation.exclusive-disjunction.html#2483" class="Bound">l1</a> <a id="2625" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2627" href="foundation.exclusive-disjunction.html#2486" class="Bound">l2</a><a id="2629" class="Symbol">)</a>
  <a id="2633" href="foundation.exclusive-disjunction.html#2607" class="Function">xor-type</a> <a id="2642" class="Symbol">=</a> <a id="2644" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2654" href="foundation.exclusive-disjunction.html#2533" class="Function">xor-type-Prop</a>

  <a id="2671" href="foundation.exclusive-disjunction.html#2671" class="Function">is-prop-xor-type</a> <a id="2688" class="Symbol">:</a> <a id="2690" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2698" href="foundation.exclusive-disjunction.html#2607" class="Function">xor-type</a>
  <a id="2709" href="foundation.exclusive-disjunction.html#2671" class="Function">is-prop-xor-type</a> <a id="2726" class="Symbol">=</a> <a id="2728" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2746" href="foundation.exclusive-disjunction.html#2533" class="Function">xor-type-Prop</a>
</pre>
### The exclusive disjunction

<pre class="Agda"><a id="2804" class="Keyword">module</a> <a id="2811" href="foundation.exclusive-disjunction.html#2811" class="Module">_</a>
  <a id="2815" class="Symbol">{</a><a id="2816" href="foundation.exclusive-disjunction.html#2816" class="Bound">l1</a> <a id="2819" href="foundation.exclusive-disjunction.html#2819" class="Bound">l2</a> <a id="2822" class="Symbol">:</a> <a id="2824" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2829" class="Symbol">}</a> <a id="2831" class="Symbol">(</a><a id="2832" href="foundation.exclusive-disjunction.html#2832" class="Bound">P</a> <a id="2834" class="Symbol">:</a> <a id="2836" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2841" href="foundation.exclusive-disjunction.html#2816" class="Bound">l1</a><a id="2843" class="Symbol">)</a> <a id="2845" class="Symbol">(</a><a id="2846" href="foundation.exclusive-disjunction.html#2846" class="Bound">Q</a> <a id="2848" class="Symbol">:</a> <a id="2850" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2855" href="foundation.exclusive-disjunction.html#2819" class="Bound">l2</a><a id="2857" class="Symbol">)</a>
  <a id="2861" class="Keyword">where</a>

  <a id="2870" href="foundation.exclusive-disjunction.html#2870" class="Function">xor-Prop</a> <a id="2879" class="Symbol">:</a> <a id="2881" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2886" class="Symbol">(</a><a id="2887" href="foundation.exclusive-disjunction.html#2816" class="Bound">l1</a> <a id="2890" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2892" href="foundation.exclusive-disjunction.html#2819" class="Bound">l2</a><a id="2894" class="Symbol">)</a>
  <a id="2898" href="foundation.exclusive-disjunction.html#2870" class="Function">xor-Prop</a> <a id="2907" class="Symbol">=</a> <a id="2909" href="foundation.exclusive-disjunction.html#2533" class="Function">xor-type-Prop</a> <a id="2923" class="Symbol">(</a><a id="2924" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2934" href="foundation.exclusive-disjunction.html#2832" class="Bound">P</a><a id="2935" class="Symbol">)</a> <a id="2937" class="Symbol">(</a><a id="2938" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2948" href="foundation.exclusive-disjunction.html#2846" class="Bound">Q</a><a id="2949" class="Symbol">)</a>

  <a id="2954" href="foundation.exclusive-disjunction.html#2954" class="Function">type-xor-Prop</a> <a id="2968" class="Symbol">:</a> <a id="2970" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2973" class="Symbol">(</a><a id="2974" href="foundation.exclusive-disjunction.html#2816" class="Bound">l1</a> <a id="2977" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2979" href="foundation.exclusive-disjunction.html#2819" class="Bound">l2</a><a id="2981" class="Symbol">)</a>
  <a id="2985" href="foundation.exclusive-disjunction.html#2954" class="Function">type-xor-Prop</a> <a id="2999" class="Symbol">=</a> <a id="3001" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="3011" href="foundation.exclusive-disjunction.html#2870" class="Function">xor-Prop</a>

  <a id="3023" href="foundation.exclusive-disjunction.html#3023" class="Function">is-prop-xor-Prop</a> <a id="3040" class="Symbol">:</a> <a id="3042" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3050" href="foundation.exclusive-disjunction.html#2954" class="Function">type-xor-Prop</a>
  <a id="3066" href="foundation.exclusive-disjunction.html#3023" class="Function">is-prop-xor-Prop</a> <a id="3083" class="Symbol">=</a> <a id="3085" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="3103" href="foundation.exclusive-disjunction.html#2870" class="Function">xor-Prop</a>

  <a id="3115" class="Keyword">infixr</a> <a id="3122" class="Number">10</a> <a id="3125" href="foundation.exclusive-disjunction.html#3131" class="Function Operator">_⊻_</a>
  <a id="3131" href="foundation.exclusive-disjunction.html#3131" class="Function Operator">_⊻_</a> <a id="3135" class="Symbol">:</a> <a id="3137" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3142" class="Symbol">(</a><a id="3143" href="foundation.exclusive-disjunction.html#2816" class="Bound">l1</a> <a id="3146" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3148" href="foundation.exclusive-disjunction.html#2819" class="Bound">l2</a><a id="3150" class="Symbol">)</a>
  <a id="3154" href="foundation.exclusive-disjunction.html#3131" class="Function Operator">_⊻_</a> <a id="3158" class="Symbol">=</a> <a id="3160" href="foundation.exclusive-disjunction.html#2870" class="Function">xor-Prop</a>
</pre>
**Notation.** The
[symbol used for exclusive disjunction](https://codepoints.net/U+22BB?lang=en)
`⊻` can be written with the escape sequence `\veebar`.

## Properties

### The canonical map from the exclusive disjunction into the exclusive sum

<pre class="Agda"><a id="3427" class="Keyword">module</a> <a id="3434" href="foundation.exclusive-disjunction.html#3434" class="Module">_</a>
  <a id="3438" class="Symbol">{</a><a id="3439" href="foundation.exclusive-disjunction.html#3439" class="Bound">l1</a> <a id="3442" href="foundation.exclusive-disjunction.html#3442" class="Bound">l2</a> <a id="3445" class="Symbol">:</a> <a id="3447" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3452" class="Symbol">}</a> <a id="3454" class="Symbol">{</a><a id="3455" href="foundation.exclusive-disjunction.html#3455" class="Bound">A</a> <a id="3457" class="Symbol">:</a> <a id="3459" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3462" href="foundation.exclusive-disjunction.html#3439" class="Bound">l1</a><a id="3464" class="Symbol">}</a> <a id="3466" class="Symbol">{</a><a id="3467" href="foundation.exclusive-disjunction.html#3467" class="Bound">B</a> <a id="3469" class="Symbol">:</a> <a id="3471" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3474" href="foundation.exclusive-disjunction.html#3442" class="Bound">l2</a><a id="3476" class="Symbol">}</a>
  <a id="3480" class="Keyword">where</a>

  <a id="3489" href="foundation.exclusive-disjunction.html#3489" class="Function">map-exclusive-sum-xor</a> <a id="3511" class="Symbol">:</a> <a id="3513" href="foundation.exclusive-disjunction.html#2607" class="Function">xor-type</a> <a id="3522" href="foundation.exclusive-disjunction.html#3455" class="Bound">A</a> <a id="3524" href="foundation.exclusive-disjunction.html#3467" class="Bound">B</a> <a id="3526" class="Symbol">→</a> <a id="3528" href="foundation.exclusive-sum.html#1996" class="Function">exclusive-sum</a> <a id="3542" href="foundation.exclusive-disjunction.html#3455" class="Bound">A</a> <a id="3544" href="foundation.exclusive-disjunction.html#3467" class="Bound">B</a>
  <a id="3548" href="foundation.exclusive-disjunction.html#3489" class="Function">map-exclusive-sum-xor</a> <a id="3570" class="Symbol">(</a><a id="3571" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="3575" href="foundation.exclusive-disjunction.html#3575" class="Bound">a</a> <a id="3577" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3579" href="foundation.exclusive-disjunction.html#3579" class="Bound">H</a><a id="3580" class="Symbol">)</a> <a id="3582" class="Symbol">=</a>
    <a id="3588" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="3592" class="Symbol">(</a><a id="3593" href="foundation.exclusive-disjunction.html#3575" class="Bound">a</a> <a id="3595" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3597" class="Symbol">(λ</a> <a id="3600" href="foundation.exclusive-disjunction.html#3600" class="Bound">b</a> <a id="3602" class="Symbol">→</a> <a id="3604" href="foundation.equality-coproduct-types.html#5851" class="Function">is-empty-eq-coproduct-inl-inr</a> <a id="3634" href="foundation.exclusive-disjunction.html#3575" class="Bound">a</a> <a id="3636" href="foundation.exclusive-disjunction.html#3600" class="Bound">b</a> <a id="3638" class="Symbol">(</a><a id="3639" href="foundation.exclusive-disjunction.html#3579" class="Bound">H</a> <a id="3641" class="Symbol">(</a><a id="3642" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="3646" href="foundation.exclusive-disjunction.html#3600" class="Bound">b</a><a id="3647" class="Symbol">))))</a>
  <a id="3654" href="foundation.exclusive-disjunction.html#3489" class="Function">map-exclusive-sum-xor</a> <a id="3676" class="Symbol">(</a><a id="3677" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="3681" href="foundation.exclusive-disjunction.html#3681" class="Bound">b</a> <a id="3683" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3685" href="foundation.exclusive-disjunction.html#3685" class="Bound">H</a><a id="3686" class="Symbol">)</a> <a id="3688" class="Symbol">=</a>
    <a id="3694" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="3698" class="Symbol">(</a><a id="3699" href="foundation.exclusive-disjunction.html#3681" class="Bound">b</a> <a id="3701" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3703" class="Symbol">(λ</a> <a id="3706" href="foundation.exclusive-disjunction.html#3706" class="Bound">a</a> <a id="3708" class="Symbol">→</a> <a id="3710" href="foundation.equality-coproduct-types.html#6782" class="Function">is-empty-eq-coproduct-inr-inl</a> <a id="3740" href="foundation.exclusive-disjunction.html#3681" class="Bound">b</a> <a id="3742" href="foundation.exclusive-disjunction.html#3706" class="Bound">a</a> <a id="3744" class="Symbol">(</a><a id="3745" href="foundation.exclusive-disjunction.html#3685" class="Bound">H</a> <a id="3747" class="Symbol">(</a><a id="3748" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="3752" href="foundation.exclusive-disjunction.html#3706" class="Bound">a</a><a id="3753" class="Symbol">))))</a>
</pre>
### The exclusive disjunction of two propositions is equivalent to their exclusive sum

<pre class="Agda"><a id="3859" class="Keyword">module</a> <a id="3866" href="foundation.exclusive-disjunction.html#3866" class="Module">_</a>
  <a id="3870" class="Symbol">{</a><a id="3871" href="foundation.exclusive-disjunction.html#3871" class="Bound">l1</a> <a id="3874" href="foundation.exclusive-disjunction.html#3874" class="Bound">l2</a> <a id="3877" class="Symbol">:</a> <a id="3879" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3884" class="Symbol">}</a> <a id="3886" class="Symbol">(</a><a id="3887" href="foundation.exclusive-disjunction.html#3887" class="Bound">P</a> <a id="3889" class="Symbol">:</a> <a id="3891" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3896" href="foundation.exclusive-disjunction.html#3871" class="Bound">l1</a><a id="3898" class="Symbol">)</a> <a id="3900" class="Symbol">(</a><a id="3901" href="foundation.exclusive-disjunction.html#3901" class="Bound">Q</a> <a id="3903" class="Symbol">:</a> <a id="3905" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3910" href="foundation.exclusive-disjunction.html#3874" class="Bound">l2</a><a id="3912" class="Symbol">)</a>
  <a id="3916" class="Keyword">where</a>

  <a id="3925" href="foundation.exclusive-disjunction.html#3925" class="Function">equiv-exclusive-sum-xor-Prop</a> <a id="3954" class="Symbol">:</a> <a id="3956" href="foundation.exclusive-disjunction.html#2954" class="Function">type-xor-Prop</a> <a id="3970" href="foundation.exclusive-disjunction.html#3887" class="Bound">P</a> <a id="3972" href="foundation.exclusive-disjunction.html#3901" class="Bound">Q</a> <a id="3974" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="3976" href="foundation.exclusive-sum.html#2335" class="Function">type-exclusive-sum-Prop</a> <a id="4000" href="foundation.exclusive-disjunction.html#3887" class="Bound">P</a> <a id="4002" href="foundation.exclusive-disjunction.html#3901" class="Bound">Q</a>
  <a id="4006" href="foundation.exclusive-disjunction.html#3925" class="Function">equiv-exclusive-sum-xor-Prop</a> <a id="4035" class="Symbol">=</a>
    <a id="4041" class="Symbol">(</a> <a id="4043" href="foundation.functoriality-coproduct-types.html#8707" class="Function">equiv-coproduct</a>
      <a id="4065" class="Symbol">(</a> <a id="4067" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a>
        <a id="4085" class="Symbol">(</a> <a id="4087" class="Symbol">λ</a> <a id="4089" href="foundation.exclusive-disjunction.html#4089" class="Bound">p</a> <a id="4091" class="Symbol">→</a>
          <a id="4103" class="Symbol">(</a> <a id="4105" class="Symbol">(</a> <a id="4107" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a> <a id="4128" class="Symbol">(</a><a id="4129" href="foundation.equality-coproduct-types.html#5662" class="Function">compute-eq-coproduct-inl-inr</a> <a id="4158" href="foundation.exclusive-disjunction.html#4089" class="Bound">p</a><a id="4159" class="Symbol">))</a> <a id="4162" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
            <a id="4177" class="Symbol">(</a> <a id="4179" href="foundation.type-arithmetic-cartesian-product-types.html#3602" class="Function">left-unit-law-product-is-contr</a>
              <a id="4224" class="Symbol">(</a> <a id="4226" href="foundation-core.contractible-types.html#7898" class="Function">is-contr-Π</a>
                <a id="4253" class="Symbol">(</a> <a id="4255" class="Symbol">λ</a> <a id="4257" href="foundation.exclusive-disjunction.html#4257" class="Bound">p&#39;</a> <a id="4260" class="Symbol">→</a>
                  <a id="4280" href="foundation-core.contractible-types.html#2905" class="Function">is-contr-equiv&#39;</a>
                    <a id="4316" class="Symbol">(</a> <a id="4318" href="foundation.exclusive-disjunction.html#4089" class="Bound">p</a> <a id="4320" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4322" href="foundation.exclusive-disjunction.html#4257" class="Bound">p&#39;</a><a id="4324" class="Symbol">)</a>
                    <a id="4346" class="Symbol">(</a> <a id="4348" href="foundation-core.embeddings.html#1889" class="Function">equiv-ap-emb</a> <a id="4361" href="foundation.equality-coproduct-types.html#8927" class="Function">emb-inl</a><a id="4368" class="Symbol">)</a>
                    <a id="4390" class="Symbol">(</a> <a id="4392" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="4410" href="foundation.exclusive-disjunction.html#3887" class="Bound">P</a> <a id="4412" href="foundation.exclusive-disjunction.html#4089" class="Bound">p</a> <a id="4414" href="foundation.exclusive-disjunction.html#4257" class="Bound">p&#39;</a><a id="4416" class="Symbol">)))))</a> <a id="4422" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
          <a id="4435" class="Symbol">(</a> <a id="4437" href="foundation.universal-property-coproduct-types.html#1476" class="Function">equiv-dependent-universal-property-coproduct</a> <a id="4482" class="Symbol">(</a><a id="4483" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="4487" href="foundation.exclusive-disjunction.html#4089" class="Bound">p</a> <a id="4489" href="foundation-core.identity-types.html#2713" class="Function Operator">＝_</a><a id="4491" class="Symbol">))))</a>
      <a id="4502" class="Symbol">(</a> <a id="4504" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a>
        <a id="4522" class="Symbol">(</a> <a id="4524" class="Symbol">λ</a> <a id="4526" href="foundation.exclusive-disjunction.html#4526" class="Bound">q</a> <a id="4528" class="Symbol">→</a>
          <a id="4540" class="Symbol">(</a> <a id="4542" class="Symbol">(</a> <a id="4544" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a> <a id="4565" class="Symbol">(</a><a id="4566" href="foundation.equality-coproduct-types.html#6593" class="Function">compute-eq-coproduct-inr-inl</a> <a id="4595" href="foundation.exclusive-disjunction.html#4526" class="Bound">q</a><a id="4596" class="Symbol">))</a> <a id="4599" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
            <a id="4614" class="Symbol">(</a> <a id="4616" href="foundation.type-arithmetic-cartesian-product-types.html#3251" class="Function">right-unit-law-product-is-contr</a>
              <a id="4662" class="Symbol">(</a> <a id="4664" href="foundation-core.contractible-types.html#7898" class="Function">is-contr-Π</a>
                <a id="4691" class="Symbol">(</a> <a id="4693" class="Symbol">λ</a> <a id="4695" href="foundation.exclusive-disjunction.html#4695" class="Bound">q&#39;</a> <a id="4698" class="Symbol">→</a>
                  <a id="4718" href="foundation-core.contractible-types.html#2905" class="Function">is-contr-equiv&#39;</a>
                    <a id="4754" class="Symbol">(</a> <a id="4756" href="foundation.exclusive-disjunction.html#4526" class="Bound">q</a> <a id="4758" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4760" href="foundation.exclusive-disjunction.html#4695" class="Bound">q&#39;</a><a id="4762" class="Symbol">)</a>
                    <a id="4784" class="Symbol">(</a> <a id="4786" href="foundation-core.embeddings.html#1889" class="Function">equiv-ap-emb</a> <a id="4799" href="foundation.equality-coproduct-types.html#9266" class="Function">emb-inr</a><a id="4806" class="Symbol">)</a>
                    <a id="4828" class="Symbol">(</a> <a id="4830" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="4848" href="foundation.exclusive-disjunction.html#3901" class="Bound">Q</a> <a id="4850" href="foundation.exclusive-disjunction.html#4526" class="Bound">q</a> <a id="4852" href="foundation.exclusive-disjunction.html#4695" class="Bound">q&#39;</a><a id="4854" class="Symbol">)))))</a> <a id="4860" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
          <a id="4873" class="Symbol">(</a> <a id="4875" href="foundation.universal-property-coproduct-types.html#1476" class="Function">equiv-dependent-universal-property-coproduct</a> <a id="4920" class="Symbol">(</a><a id="4921" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="4925" href="foundation.exclusive-disjunction.html#4526" class="Bound">q</a> <a id="4927" href="foundation-core.identity-types.html#2713" class="Function Operator">＝_</a><a id="4929" class="Symbol">)))))</a> <a id="4935" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
    <a id="4942" class="Symbol">(</a> <a id="4944" href="foundation.type-arithmetic-coproduct-types.html#5922" class="Function">right-distributive-Σ-coproduct</a>
      <a id="4981" class="Symbol">(</a> <a id="4983" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="4993" href="foundation.exclusive-disjunction.html#3887" class="Bound">P</a><a id="4994" class="Symbol">)</a>
      <a id="5002" class="Symbol">(</a> <a id="5004" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="5014" href="foundation.exclusive-disjunction.html#3901" class="Bound">Q</a><a id="5015" class="Symbol">)</a>
      <a id="5023" class="Symbol">(</a> <a id="5025" class="Symbol">λ</a> <a id="5027" href="foundation.exclusive-disjunction.html#5027" class="Bound">x</a> <a id="5029" class="Symbol">→</a> <a id="5031" class="Symbol">(</a><a id="5032" href="foundation.exclusive-disjunction.html#5032" class="Bound">y</a> <a id="5034" class="Symbol">:</a> <a id="5036" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="5046" href="foundation.exclusive-disjunction.html#3887" class="Bound">P</a> <a id="5048" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="5050" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="5060" href="foundation.exclusive-disjunction.html#3901" class="Bound">Q</a><a id="5061" class="Symbol">)</a> <a id="5063" class="Symbol">→</a> <a id="5065" href="foundation.exclusive-disjunction.html#5027" class="Bound">x</a> <a id="5067" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="5069" href="foundation.exclusive-disjunction.html#5032" class="Bound">y</a><a id="5070" class="Symbol">))</a>
</pre>
## See also

- The indexed counterpart to exclusive disjunction is
  [unique existence](foundation.uniqueness-quantification.md).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [exclusive disjunction](https://ncatlab.org/nlab/show/exclusive+disjunction)
  at $n$Lab
- [Exclusive disjunction](https://simple.wikipedia.org/wiki/Exclusive_disjunction)
  at Wikipedia
