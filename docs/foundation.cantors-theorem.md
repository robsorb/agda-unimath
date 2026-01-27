# Cantor's theorem

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="foundation.cantors-theorem.html" class="Module">foundation.cantors-theorem</a> <a id="63" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="119" class="Keyword">open</a> <a id="124" class="Keyword">import</a> <a id="131" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.decidable-propositions.html" class="Module">foundation.decidable-propositions</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="foundation.double-negation-stable-propositions.html" class="Module">foundation.double-negation-stable-propositions</a>
<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="416" class="Keyword">open</a> <a id="421" class="Keyword">import</a> <a id="428" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="460" class="Keyword">open</a> <a id="465" class="Keyword">import</a> <a id="472" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="492" class="Keyword">open</a> <a id="497" class="Keyword">import</a> <a id="504" href="foundation.powersets.html" class="Module">foundation.powersets</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="564" class="Keyword">open</a> <a id="569" class="Keyword">import</a> <a id="576" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="604" class="Keyword">open</a> <a id="609" class="Keyword">import</a> <a id="616" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>

<a id="648" class="Keyword">open</a> <a id="653" class="Keyword">import</a> <a id="660" href="logic.de-morgan-propositions.html" class="Module">logic.de-morgan-propositions</a>
<a id="689" class="Keyword">open</a> <a id="694" class="Keyword">import</a> <a id="701" href="logic.de-morgan-subtypes.html" class="Module">logic.de-morgan-subtypes</a>
<a id="726" class="Keyword">open</a> <a id="731" class="Keyword">import</a> <a id="738" href="logic.double-negation-dense-maps.html" class="Module">logic.double-negation-dense-maps</a>
<a id="771" class="Keyword">open</a> <a id="776" class="Keyword">import</a> <a id="783" href="logic.double-negation-stable-subtypes.html" class="Module">logic.double-negation-stable-subtypes</a>
</pre>
</details>

## Idea

{{#concept "Cantor's theorem" Agda=theorem-Cantor WD="Cantor's theorem" WDID=Q474881}}
shows that there is [no](foundation-core.negation.md)
[surjective map](foundation.surjective-maps.md) from a type onto its
[powerset](foundation.powersets.md).

```text
  ¬ (A ↠ 𝒫(A))
```

In fact, no map `A → PA` into a
[complement](foundation.complements-subtypes.md)-closed
[subset](foundation-core.subtypes.md) `PA` of the powerset may be
[double negation dense](logic.double-negation-dense-maps.md).

## Theorem

**Proof.** The proof is an instance of an argument _by diagonalization_. Given a
function `f : A → 𝒫(A)` we may define an element of the powerset `𝒫(A)` that `f`
cannot possibly hit. This subtype is defined by

```text
  B := {x ∈ A | x ∉ f(x)}
```

which is given formally by the predicate `x ↦ ¬ (f x x)`. If this subtype were
to be hit by `f`, that would mean there is a `ξ ∈ A` such that `f(ξ) = B`. This
would have to be a fixed point of the negation operation, since

```text
  f(ξ)(ξ) = B(ξ) = ¬ (f(ξ)(ξ)),
```

but negation has no fixed points.

Cantor's theorem is the [63rd](literature.100-theorems.md#63) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

<pre class="Agda"><a id="2112" class="Keyword">module</a> <a id="2119" href="foundation.cantors-theorem.html#2119" class="Module">_</a>
  <a id="2123" class="Symbol">{</a><a id="2124" href="foundation.cantors-theorem.html#2124" class="Bound">l1</a> <a id="2127" href="foundation.cantors-theorem.html#2127" class="Bound">l2</a> <a id="2130" class="Symbol">:</a> <a id="2132" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2137" class="Symbol">}</a> <a id="2139" class="Symbol">{</a><a id="2140" href="foundation.cantors-theorem.html#2140" class="Bound">X</a> <a id="2142" class="Symbol">:</a> <a id="2144" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2147" href="foundation.cantors-theorem.html#2124" class="Bound">l1</a><a id="2149" class="Symbol">}</a> <a id="2151" class="Symbol">(</a><a id="2152" href="foundation.cantors-theorem.html#2152" class="Bound">f</a> <a id="2154" class="Symbol">:</a> <a id="2156" href="foundation.cantors-theorem.html#2140" class="Bound">X</a> <a id="2158" class="Symbol">→</a> <a id="2160" href="foundation.powersets.html#1718" class="Function">powerset</a> <a id="2169" href="foundation.cantors-theorem.html#2127" class="Bound">l2</a> <a id="2172" href="foundation.cantors-theorem.html#2140" class="Bound">X</a><a id="2173" class="Symbol">)</a>
  <a id="2177" class="Keyword">where</a>

  <a id="2186" href="foundation.cantors-theorem.html#2186" class="Function">subtype-theorem-Cantor</a> <a id="2209" class="Symbol">:</a> <a id="2211" href="foundation.powersets.html#1718" class="Function">powerset</a> <a id="2220" href="foundation.cantors-theorem.html#2127" class="Bound">l2</a> <a id="2223" href="foundation.cantors-theorem.html#2140" class="Bound">X</a>
  <a id="2227" href="foundation.cantors-theorem.html#2186" class="Function">subtype-theorem-Cantor</a> <a id="2250" href="foundation.cantors-theorem.html#2250" class="Bound">x</a> <a id="2252" class="Symbol">=</a> <a id="2254" href="foundation.negation.html#981" class="Function">neg-Prop</a> <a id="2263" class="Symbol">(</a><a id="2264" href="foundation.cantors-theorem.html#2152" class="Bound">f</a> <a id="2266" href="foundation.cantors-theorem.html#2250" class="Bound">x</a> <a id="2268" href="foundation.cantors-theorem.html#2250" class="Bound">x</a><a id="2269" class="Symbol">)</a>

  <a id="2274" class="Keyword">abstract</a>
    <a id="2287" href="foundation.cantors-theorem.html#2287" class="Function">not-in-image-subtype-theorem-Cantor</a> <a id="2323" class="Symbol">:</a> <a id="2325" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2327" class="Symbol">(</a><a id="2328" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="2334" href="foundation.cantors-theorem.html#2152" class="Bound">f</a> <a id="2336" href="foundation.cantors-theorem.html#2186" class="Function">subtype-theorem-Cantor</a><a id="2358" class="Symbol">)</a>
    <a id="2364" href="foundation.cantors-theorem.html#2287" class="Function">not-in-image-subtype-theorem-Cantor</a> <a id="2400" class="Symbol">(</a><a id="2401" href="foundation.cantors-theorem.html#2401" class="Bound">ξ</a> <a id="2403" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2405" href="foundation.cantors-theorem.html#2405" class="Bound">α</a><a id="2406" class="Symbol">)</a> <a id="2408" class="Symbol">=</a>
      <a id="2416" href="foundation.negation.html#2237" class="Function">no-fixed-points-neg-Prop</a> <a id="2441" class="Symbol">(</a><a id="2442" href="foundation.cantors-theorem.html#2152" class="Bound">f</a> <a id="2444" href="foundation.cantors-theorem.html#2401" class="Bound">ξ</a> <a id="2446" href="foundation.cantors-theorem.html#2401" class="Bound">ξ</a><a id="2447" class="Symbol">)</a> <a id="2449" class="Symbol">(</a><a id="2450" href="foundation.logical-equivalences.html#6668" class="Function">iff-eq</a> <a id="2457" class="Symbol">(</a><a id="2458" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a> <a id="2466" href="foundation.cantors-theorem.html#2405" class="Bound">α</a> <a id="2468" href="foundation.cantors-theorem.html#2401" class="Bound">ξ</a><a id="2469" class="Symbol">))</a>

    <a id="2477" href="foundation.cantors-theorem.html#2477" class="Function">theorem-double-negation-dense-Cantor</a> <a id="2514" class="Symbol">:</a> <a id="2516" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2518" class="Symbol">(</a><a id="2519" href="logic.double-negation-dense-maps.html#2867" class="Function">is-double-negation-dense-map</a> <a id="2548" href="foundation.cantors-theorem.html#2152" class="Bound">f</a><a id="2549" class="Symbol">)</a>
    <a id="2555" href="foundation.cantors-theorem.html#2477" class="Function">theorem-double-negation-dense-Cantor</a> <a id="2592" href="foundation.cantors-theorem.html#2592" class="Bound">H</a> <a id="2594" class="Symbol">=</a>
      <a id="2602" href="foundation.cantors-theorem.html#2592" class="Bound">H</a> <a id="2604" href="foundation.cantors-theorem.html#2186" class="Function">subtype-theorem-Cantor</a> <a id="2627" href="foundation.cantors-theorem.html#2287" class="Function">not-in-image-subtype-theorem-Cantor</a>

    <a id="2668" href="foundation.cantors-theorem.html#2668" class="Function">theorem-Cantor</a> <a id="2683" class="Symbol">:</a> <a id="2685" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2687" class="Symbol">(</a><a id="2688" href="foundation.surjective-maps.html#2524" class="Function">is-surjective</a> <a id="2702" href="foundation.cantors-theorem.html#2152" class="Bound">f</a><a id="2703" class="Symbol">)</a>
    <a id="2709" href="foundation.cantors-theorem.html#2668" class="Function">theorem-Cantor</a> <a id="2724" class="Symbol">=</a>
      <a id="2732" href="foundation-core.negation.html#643" class="Function">map-neg</a>
        <a id="2748" class="Symbol">(</a> <a id="2750" href="logic.double-negation-dense-maps.html#5107" class="Function">is-double-negation-dense-map-is-surjective</a><a id="2792" class="Symbol">)</a>
        <a id="2802" class="Symbol">(</a> <a id="2804" href="foundation.cantors-theorem.html#2477" class="Function">theorem-double-negation-dense-Cantor</a><a id="2840" class="Symbol">)</a>
</pre>
## Alternative statements

### Cantor's theorem for the set of decidable subtypes

**Statement.** There is no surjective map from a type `X` to its set of
decidable subtypes `𝒫ᵈ(X)`.

<pre class="Agda"><a id="3039" class="Keyword">module</a> <a id="3046" href="foundation.cantors-theorem.html#3046" class="Module">_</a>
  <a id="3050" class="Symbol">{</a><a id="3051" href="foundation.cantors-theorem.html#3051" class="Bound">l1</a> <a id="3054" href="foundation.cantors-theorem.html#3054" class="Bound">l2</a> <a id="3057" class="Symbol">:</a> <a id="3059" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3064" class="Symbol">}</a> <a id="3066" class="Symbol">{</a><a id="3067" href="foundation.cantors-theorem.html#3067" class="Bound">X</a> <a id="3069" class="Symbol">:</a> <a id="3071" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3074" href="foundation.cantors-theorem.html#3051" class="Bound">l1</a><a id="3076" class="Symbol">}</a> <a id="3078" class="Symbol">(</a><a id="3079" href="foundation.cantors-theorem.html#3079" class="Bound">f</a> <a id="3081" class="Symbol">:</a> <a id="3083" href="foundation.cantors-theorem.html#3067" class="Bound">X</a> <a id="3085" class="Symbol">→</a> <a id="3087" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="3105" href="foundation.cantors-theorem.html#3054" class="Bound">l2</a> <a id="3108" href="foundation.cantors-theorem.html#3067" class="Bound">X</a><a id="3109" class="Symbol">)</a>
  <a id="3113" class="Keyword">where</a>

  <a id="3122" href="foundation.cantors-theorem.html#3122" class="Function">map-theorem-decidable-Cantor</a> <a id="3151" class="Symbol">:</a> <a id="3153" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="3171" href="foundation.cantors-theorem.html#3054" class="Bound">l2</a> <a id="3174" href="foundation.cantors-theorem.html#3067" class="Bound">X</a>
  <a id="3178" href="foundation.cantors-theorem.html#3122" class="Function">map-theorem-decidable-Cantor</a> <a id="3207" href="foundation.cantors-theorem.html#3207" class="Bound">x</a> <a id="3209" class="Symbol">=</a> <a id="3211" href="foundation-core.decidable-propositions.html#7409" class="Function">neg-Decidable-Prop</a> <a id="3230" class="Symbol">(</a><a id="3231" href="foundation.cantors-theorem.html#3079" class="Bound">f</a> <a id="3233" href="foundation.cantors-theorem.html#3207" class="Bound">x</a> <a id="3235" href="foundation.cantors-theorem.html#3207" class="Bound">x</a><a id="3236" class="Symbol">)</a>

  <a id="3241" class="Keyword">abstract</a>
    <a id="3254" href="foundation.cantors-theorem.html#3254" class="Function">not-in-image-map-theorem-decidable-Cantor</a> <a id="3296" class="Symbol">:</a>
      <a id="3304" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="3306" class="Symbol">(</a><a id="3307" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="3313" href="foundation.cantors-theorem.html#3079" class="Bound">f</a> <a id="3315" href="foundation.cantors-theorem.html#3122" class="Function">map-theorem-decidable-Cantor</a><a id="3343" class="Symbol">)</a>
    <a id="3349" href="foundation.cantors-theorem.html#3254" class="Function">not-in-image-map-theorem-decidable-Cantor</a> <a id="3391" class="Symbol">(</a><a id="3392" href="foundation.cantors-theorem.html#3392" class="Bound">x</a> <a id="3394" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3396" href="foundation.cantors-theorem.html#3396" class="Bound">α</a><a id="3397" class="Symbol">)</a> <a id="3399" class="Symbol">=</a>
      <a id="3407" href="foundation.decidable-propositions.html#10739" class="Function">no-fixed-points-neg-Decidable-Prop</a>
        <a id="3450" class="Symbol">(</a> <a id="3452" href="foundation.cantors-theorem.html#3079" class="Bound">f</a> <a id="3454" href="foundation.cantors-theorem.html#3392" class="Bound">x</a> <a id="3456" href="foundation.cantors-theorem.html#3392" class="Bound">x</a><a id="3457" class="Symbol">)</a>
        <a id="3467" class="Symbol">(</a> <a id="3469" href="foundation.logical-equivalences.html#6668" class="Function">iff-eq</a> <a id="3476" class="Symbol">(</a><a id="3477" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="3480" href="foundation-core.decidable-propositions.html#2656" class="Function">prop-Decidable-Prop</a> <a id="3500" class="Symbol">(</a><a id="3501" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a> <a id="3509" href="foundation.cantors-theorem.html#3396" class="Bound">α</a> <a id="3511" href="foundation.cantors-theorem.html#3392" class="Bound">x</a><a id="3512" class="Symbol">)))</a>

    <a id="3521" href="foundation.cantors-theorem.html#3521" class="Function">theorem-double-negation-dense-decidable-Cantor</a> <a id="3568" class="Symbol">:</a>
      <a id="3576" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="3578" class="Symbol">(</a><a id="3579" href="logic.double-negation-dense-maps.html#2867" class="Function">is-double-negation-dense-map</a> <a id="3608" href="foundation.cantors-theorem.html#3079" class="Bound">f</a><a id="3609" class="Symbol">)</a>
    <a id="3615" href="foundation.cantors-theorem.html#3521" class="Function">theorem-double-negation-dense-decidable-Cantor</a> <a id="3662" href="foundation.cantors-theorem.html#3662" class="Bound">H</a> <a id="3664" class="Symbol">=</a>
      <a id="3672" href="foundation.cantors-theorem.html#3662" class="Bound">H</a> <a id="3674" href="foundation.cantors-theorem.html#3122" class="Function">map-theorem-decidable-Cantor</a> <a id="3703" href="foundation.cantors-theorem.html#3254" class="Function">not-in-image-map-theorem-decidable-Cantor</a>

    <a id="3750" href="foundation.cantors-theorem.html#3750" class="Function">theorem-decidable-Cantor</a> <a id="3775" class="Symbol">:</a>
      <a id="3783" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="3785" class="Symbol">(</a><a id="3786" href="foundation.surjective-maps.html#2524" class="Function">is-surjective</a> <a id="3800" href="foundation.cantors-theorem.html#3079" class="Bound">f</a><a id="3801" class="Symbol">)</a>
    <a id="3807" href="foundation.cantors-theorem.html#3750" class="Function">theorem-decidable-Cantor</a> <a id="3832" class="Symbol">=</a>
      <a id="3840" href="foundation-core.negation.html#643" class="Function">map-neg</a>
        <a id="3856" class="Symbol">(</a> <a id="3858" href="logic.double-negation-dense-maps.html#5107" class="Function">is-double-negation-dense-map-is-surjective</a><a id="3900" class="Symbol">)</a>
        <a id="3910" class="Symbol">(</a> <a id="3912" href="foundation.cantors-theorem.html#3521" class="Function">theorem-double-negation-dense-decidable-Cantor</a><a id="3958" class="Symbol">)</a>
</pre>
### Cantor's theorem for the set of double negation stable subtypes

**Statement.** There is no surjective map from a type `X` to its set of double
negation stable subtypes `𝒫^¬¬(X)`.

<pre class="Agda"><a id="4158" class="Keyword">module</a> <a id="4165" href="foundation.cantors-theorem.html#4165" class="Module">_</a>
  <a id="4169" class="Symbol">{</a><a id="4170" href="foundation.cantors-theorem.html#4170" class="Bound">l1</a> <a id="4173" href="foundation.cantors-theorem.html#4173" class="Bound">l2</a> <a id="4176" class="Symbol">:</a> <a id="4178" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4183" class="Symbol">}</a> <a id="4185" class="Symbol">{</a><a id="4186" href="foundation.cantors-theorem.html#4186" class="Bound">X</a> <a id="4188" class="Symbol">:</a> <a id="4190" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4193" href="foundation.cantors-theorem.html#4170" class="Bound">l1</a><a id="4195" class="Symbol">}</a> <a id="4197" class="Symbol">(</a><a id="4198" href="foundation.cantors-theorem.html#4198" class="Bound">f</a> <a id="4200" class="Symbol">:</a> <a id="4202" href="foundation.cantors-theorem.html#4186" class="Bound">X</a> <a id="4204" class="Symbol">→</a> <a id="4206" href="logic.double-negation-stable-subtypes.html#2451" class="Function">double-negation-stable-subtype</a> <a id="4237" href="foundation.cantors-theorem.html#4173" class="Bound">l2</a> <a id="4240" href="foundation.cantors-theorem.html#4186" class="Bound">X</a><a id="4241" class="Symbol">)</a>
  <a id="4245" class="Keyword">where</a>

  <a id="4254" href="foundation.cantors-theorem.html#4254" class="Function">map-theorem-double-negation-stable-Cantor</a> <a id="4296" class="Symbol">:</a>
    <a id="4302" href="logic.double-negation-stable-subtypes.html#2451" class="Function">double-negation-stable-subtype</a> <a id="4333" href="foundation.cantors-theorem.html#4173" class="Bound">l2</a> <a id="4336" href="foundation.cantors-theorem.html#4186" class="Bound">X</a>
  <a id="4340" href="foundation.cantors-theorem.html#4254" class="Function">map-theorem-double-negation-stable-Cantor</a> <a id="4382" href="foundation.cantors-theorem.html#4382" class="Bound">x</a> <a id="4384" class="Symbol">=</a>
    <a id="4390" href="foundation.double-negation-stable-propositions.html#8649" class="Function">neg-Double-Negation-Stable-Prop</a> <a id="4422" class="Symbol">(</a><a id="4423" href="foundation.cantors-theorem.html#4198" class="Bound">f</a> <a id="4425" href="foundation.cantors-theorem.html#4382" class="Bound">x</a> <a id="4427" href="foundation.cantors-theorem.html#4382" class="Bound">x</a><a id="4428" class="Symbol">)</a>

  <a id="4433" class="Keyword">abstract</a>
    <a id="4446" href="foundation.cantors-theorem.html#4446" class="Function">not-in-image-map-theorem-double-negation-stable-Cantor</a> <a id="4501" class="Symbol">:</a>
      <a id="4509" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="4511" class="Symbol">(</a><a id="4512" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="4518" href="foundation.cantors-theorem.html#4198" class="Bound">f</a> <a id="4520" href="foundation.cantors-theorem.html#4254" class="Function">map-theorem-double-negation-stable-Cantor</a><a id="4561" class="Symbol">)</a>
    <a id="4567" href="foundation.cantors-theorem.html#4446" class="Function">not-in-image-map-theorem-double-negation-stable-Cantor</a> <a id="4622" class="Symbol">(</a><a id="4623" href="foundation.cantors-theorem.html#4623" class="Bound">x</a> <a id="4625" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4627" href="foundation.cantors-theorem.html#4627" class="Bound">α</a><a id="4628" class="Symbol">)</a> <a id="4630" class="Symbol">=</a>
      <a id="4638" href="foundation.double-negation-stable-propositions.html#13340" class="Function">no-fixed-points-neg-Double-Negation-Stable-Prop</a>
        <a id="4694" class="Symbol">(</a> <a id="4696" href="foundation.cantors-theorem.html#4198" class="Bound">f</a> <a id="4698" href="foundation.cantors-theorem.html#4623" class="Bound">x</a> <a id="4700" href="foundation.cantors-theorem.html#4623" class="Bound">x</a><a id="4701" class="Symbol">)</a>
        <a id="4711" class="Symbol">(</a> <a id="4713" href="foundation.logical-equivalences.html#6668" class="Function">iff-eq</a> <a id="4720" class="Symbol">(</a><a id="4721" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4724" href="foundation.double-negation-stable-propositions.html#3666" class="Function">prop-Double-Negation-Stable-Prop</a> <a id="4757" class="Symbol">(</a><a id="4758" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a> <a id="4766" href="foundation.cantors-theorem.html#4627" class="Bound">α</a> <a id="4768" href="foundation.cantors-theorem.html#4623" class="Bound">x</a><a id="4769" class="Symbol">)))</a>

    <a id="4778" href="foundation.cantors-theorem.html#4778" class="Function">theorem-double-negation-dense-double-negation-stable-Cantor</a> <a id="4838" class="Symbol">:</a>
      <a id="4846" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="4848" class="Symbol">(</a><a id="4849" href="logic.double-negation-dense-maps.html#2867" class="Function">is-double-negation-dense-map</a> <a id="4878" href="foundation.cantors-theorem.html#4198" class="Bound">f</a><a id="4879" class="Symbol">)</a>
    <a id="4885" href="foundation.cantors-theorem.html#4778" class="Function">theorem-double-negation-dense-double-negation-stable-Cantor</a> <a id="4945" href="foundation.cantors-theorem.html#4945" class="Bound">H</a> <a id="4947" class="Symbol">=</a>
      <a id="4955" href="foundation.cantors-theorem.html#4945" class="Bound">H</a> <a id="4957" href="foundation.cantors-theorem.html#4254" class="Function">map-theorem-double-negation-stable-Cantor</a>
        <a id="5007" href="foundation.cantors-theorem.html#4446" class="Function">not-in-image-map-theorem-double-negation-stable-Cantor</a>

    <a id="5067" href="foundation.cantors-theorem.html#5067" class="Function">theorem-double-negation-stable-Cantor</a> <a id="5105" class="Symbol">:</a>
      <a id="5113" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="5115" class="Symbol">(</a><a id="5116" href="foundation.surjective-maps.html#2524" class="Function">is-surjective</a> <a id="5130" href="foundation.cantors-theorem.html#4198" class="Bound">f</a><a id="5131" class="Symbol">)</a>
    <a id="5137" href="foundation.cantors-theorem.html#5067" class="Function">theorem-double-negation-stable-Cantor</a> <a id="5175" class="Symbol">=</a>
      <a id="5183" href="foundation-core.negation.html#643" class="Function">map-neg</a>
        <a id="5199" href="logic.double-negation-dense-maps.html#5107" class="Function">is-double-negation-dense-map-is-surjective</a>
        <a id="5250" href="foundation.cantors-theorem.html#4778" class="Function">theorem-double-negation-dense-double-negation-stable-Cantor</a>
</pre>
### Cantor's theorem for the set of De Morgan subtypes

**Statement.** There is no surjective map from a type `X` to its set of De
Morgan subtypes `𝒫ᵈᵐ(X)`.

<pre class="Agda"><a id="5481" class="Keyword">module</a> <a id="5488" href="foundation.cantors-theorem.html#5488" class="Module">_</a>
  <a id="5492" class="Symbol">{</a><a id="5493" href="foundation.cantors-theorem.html#5493" class="Bound">l1</a> <a id="5496" href="foundation.cantors-theorem.html#5496" class="Bound">l2</a> <a id="5499" class="Symbol">:</a> <a id="5501" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5506" class="Symbol">}</a> <a id="5508" class="Symbol">{</a><a id="5509" href="foundation.cantors-theorem.html#5509" class="Bound">X</a> <a id="5511" class="Symbol">:</a> <a id="5513" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5516" href="foundation.cantors-theorem.html#5493" class="Bound">l1</a><a id="5518" class="Symbol">}</a> <a id="5520" class="Symbol">(</a><a id="5521" href="foundation.cantors-theorem.html#5521" class="Bound">f</a> <a id="5523" class="Symbol">:</a> <a id="5525" href="foundation.cantors-theorem.html#5509" class="Bound">X</a> <a id="5527" class="Symbol">→</a> <a id="5529" href="logic.de-morgan-subtypes.html#2054" class="Function">de-morgan-subtype</a> <a id="5547" href="foundation.cantors-theorem.html#5496" class="Bound">l2</a> <a id="5550" href="foundation.cantors-theorem.html#5509" class="Bound">X</a><a id="5551" class="Symbol">)</a>
  <a id="5555" class="Keyword">where</a>

  <a id="5564" href="foundation.cantors-theorem.html#5564" class="Function">map-theorem-de-morgan-Cantor</a> <a id="5593" class="Symbol">:</a> <a id="5595" href="logic.de-morgan-subtypes.html#2054" class="Function">de-morgan-subtype</a> <a id="5613" href="foundation.cantors-theorem.html#5496" class="Bound">l2</a> <a id="5616" href="foundation.cantors-theorem.html#5509" class="Bound">X</a>
  <a id="5620" href="foundation.cantors-theorem.html#5564" class="Function">map-theorem-de-morgan-Cantor</a> <a id="5649" href="foundation.cantors-theorem.html#5649" class="Bound">x</a> <a id="5651" class="Symbol">=</a> <a id="5653" href="logic.de-morgan-propositions.html#8639" class="Function">neg-De-Morgan-Prop</a> <a id="5672" class="Symbol">(</a><a id="5673" href="foundation.cantors-theorem.html#5521" class="Bound">f</a> <a id="5675" href="foundation.cantors-theorem.html#5649" class="Bound">x</a> <a id="5677" href="foundation.cantors-theorem.html#5649" class="Bound">x</a><a id="5678" class="Symbol">)</a>

  <a id="5683" class="Keyword">abstract</a>
    <a id="5696" href="foundation.cantors-theorem.html#5696" class="Function">not-in-image-map-theorem-de-morgan-Cantor</a> <a id="5738" class="Symbol">:</a>
      <a id="5746" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="5748" class="Symbol">(</a><a id="5749" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="5755" href="foundation.cantors-theorem.html#5521" class="Bound">f</a> <a id="5757" href="foundation.cantors-theorem.html#5564" class="Function">map-theorem-de-morgan-Cantor</a><a id="5785" class="Symbol">)</a>
    <a id="5791" href="foundation.cantors-theorem.html#5696" class="Function">not-in-image-map-theorem-de-morgan-Cantor</a> <a id="5833" class="Symbol">(</a><a id="5834" href="foundation.cantors-theorem.html#5834" class="Bound">x</a> <a id="5836" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5838" href="foundation.cantors-theorem.html#5838" class="Bound">α</a><a id="5839" class="Symbol">)</a> <a id="5841" class="Symbol">=</a>
      <a id="5849" href="logic.de-morgan-propositions.html#10091" class="Function">no-fixed-points-neg-De-Morgan-Prop</a>
        <a id="5892" class="Symbol">(</a> <a id="5894" href="foundation.cantors-theorem.html#5521" class="Bound">f</a> <a id="5896" href="foundation.cantors-theorem.html#5834" class="Bound">x</a> <a id="5898" href="foundation.cantors-theorem.html#5834" class="Bound">x</a><a id="5899" class="Symbol">)</a>
        <a id="5909" class="Symbol">(</a> <a id="5911" href="foundation.logical-equivalences.html#6668" class="Function">iff-eq</a> <a id="5918" class="Symbol">(</a><a id="5919" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="5922" href="logic.de-morgan-propositions.html#3833" class="Function">prop-De-Morgan-Prop</a> <a id="5942" class="Symbol">(</a><a id="5943" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a> <a id="5951" href="foundation.cantors-theorem.html#5838" class="Bound">α</a> <a id="5953" href="foundation.cantors-theorem.html#5834" class="Bound">x</a><a id="5954" class="Symbol">)))</a>

    <a id="5963" href="foundation.cantors-theorem.html#5963" class="Function">theorem-double-negation-dense-de-morgan-Cantor</a> <a id="6010" class="Symbol">:</a>
      <a id="6018" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="6020" class="Symbol">(</a><a id="6021" href="logic.double-negation-dense-maps.html#2867" class="Function">is-double-negation-dense-map</a> <a id="6050" href="foundation.cantors-theorem.html#5521" class="Bound">f</a><a id="6051" class="Symbol">)</a>
    <a id="6057" href="foundation.cantors-theorem.html#5963" class="Function">theorem-double-negation-dense-de-morgan-Cantor</a> <a id="6104" href="foundation.cantors-theorem.html#6104" class="Bound">H</a> <a id="6106" class="Symbol">=</a>
      <a id="6114" href="foundation.cantors-theorem.html#6104" class="Bound">H</a> <a id="6116" href="foundation.cantors-theorem.html#5564" class="Function">map-theorem-de-morgan-Cantor</a> <a id="6145" href="foundation.cantors-theorem.html#5696" class="Function">not-in-image-map-theorem-de-morgan-Cantor</a>

    <a id="6192" href="foundation.cantors-theorem.html#6192" class="Function">theorem-de-morgan-Cantor</a> <a id="6217" class="Symbol">:</a>
      <a id="6225" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="6227" class="Symbol">(</a><a id="6228" href="foundation.surjective-maps.html#2524" class="Function">is-surjective</a> <a id="6242" href="foundation.cantors-theorem.html#5521" class="Bound">f</a><a id="6243" class="Symbol">)</a>
    <a id="6249" href="foundation.cantors-theorem.html#6192" class="Function">theorem-de-morgan-Cantor</a> <a id="6274" class="Symbol">=</a>
      <a id="6282" href="foundation-core.negation.html#643" class="Function">map-neg</a>
        <a id="6298" href="logic.double-negation-dense-maps.html#5107" class="Function">is-double-negation-dense-map-is-surjective</a>
        <a id="6349" href="foundation.cantors-theorem.html#5963" class="Function">theorem-double-negation-dense-de-morgan-Cantor</a>
</pre>
## References

A proof of Cantor's theorem first appeared in {{#cite Cantor1890/91}} where it
was considered in the context of [infinite sets](set-theory.infinite-sets.md).

{{#bibliography}} {{#reference Cantor1890/91}}

## See also

- Cantor's theorem generalizes
  [Cantor's diagonal argument](set-theory.cantors-diagonal-argument.md), which
  shows that the [set](foundation-core.sets.md) of
  [infinite sequences](lists.sequences.md) on a set with at least two distinct
  elements is [uncountable](set-theory.uncountable-sets.md).
- Cantor's theorem is generalized by
  [Lawvere's fixed point theorem](foundation.lawveres-fixed-point-theorem.md).

## External links

- [Cantor's theorem](https://ncatlab.org/nlab/show/Cantor%27s+theorem) at $n$Lab
- [Cantor's theorem](https://en.wikipedia.org/wiki/Cantor%27s_theorem) at
  Wikipedia
- [Cantor's theorem](https://www.britannica.com/science/Cantors-theorem) at
  Britannica
