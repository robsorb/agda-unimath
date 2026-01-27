# The strong preunivalence axiom

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="foundation.strong-preunivalence.html" class="Module">foundation.strong-preunivalence</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.dependent-identifications.html" class="Module">foundation.dependent-identifications</a>
<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="362" class="Keyword">open</a> <a id="367" class="Keyword">import</a> <a id="374" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="420" class="Keyword">open</a> <a id="425" class="Keyword">import</a> <a id="432" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="458" class="Keyword">open</a> <a id="463" class="Keyword">import</a> <a id="470" href="foundation.preunivalence.html" class="Module">foundation.preunivalence</a>
<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="foundation.propositional-maps.html" class="Module">foundation.propositional-maps</a>
<a id="537" class="Keyword">open</a> <a id="542" class="Keyword">import</a> <a id="549" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="573" class="Keyword">open</a> <a id="578" class="Keyword">import</a> <a id="585" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="601" class="Keyword">open</a> <a id="606" class="Keyword">import</a> <a id="613" href="foundation.small-types.html" class="Module">foundation.small-types</a>
<a id="636" class="Keyword">open</a> <a id="641" class="Keyword">import</a> <a id="648" href="foundation.structured-equality-duality.html" class="Module">foundation.structured-equality-duality</a>
<a id="687" class="Keyword">open</a> <a id="692" class="Keyword">import</a> <a id="699" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="721" class="Keyword">open</a> <a id="726" class="Keyword">import</a> <a id="733" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="761" class="Keyword">open</a> <a id="766" class="Keyword">import</a> <a id="773" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

{{#concept "The strong preunivalence axiom" Agda=strong-preunivalence-axiom}} is
a common generalization of the [univalence axiom](foundation.univalence.md) and
[axiom K](foundation-core.sets.md). It asserts that for any type `X : 𝒰` and any
other universe `𝒱`, the [smallness predicate](foundation-core.small-types.md)
`is-small 𝒱 X ≐ Σ (Y : 𝒱), (X ≃ Y)` is a [set](foundation-core.sets.md).

The strong preunivalence axiom is a strengthening of
[the preunivalence axiom](foundation.preunivalence.md) in the following way. If
we restrict to `𝒱 ≐ 𝒰`,
[subuniverse equality duality](foundation.structured-equality-duality.md) says
that, for every `X : 𝒰`, `Σ (Y : 𝒰), (X ≃ Y)` is a set if and only if every
binary family of maps

```text
  (Z Y : 𝒰) → (Z ＝ Y) → (X ≃ Y)
```

is a binary family of [embeddings](foundation-core.embeddings.md). The
preunivalence axiom asserts that the particular (unary) family of maps
`(Y : 𝒰) → (X ＝ Y) → (X ≃ Y)` defined by identity induction by
`refl ↦ id-equiv` is a family of embeddings.

While the strong preunivalence axiom is a strengthening of the preunivalence
axiom, it is still a common generalization of the
[univalence axiom](foundation.univalence.md) and
[axiom K](foundation-core.sets.md): if we assume the univalence axiom then
`is-small 𝒱 X` is a proposition, and if we assume axiom K then every type is a
set.

## Definitions

<pre class="Agda"><a id="instance-strong-preunivalence"></a><a id="2215" href="foundation.strong-preunivalence.html#2215" class="Function">instance-strong-preunivalence</a> <a id="2245" class="Symbol">:</a>
  <a id="2249" class="Symbol">{</a><a id="2250" href="foundation.strong-preunivalence.html#2250" class="Bound">l1</a> <a id="2253" class="Symbol">:</a> <a id="2255" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2260" class="Symbol">}</a> <a id="2262" class="Symbol">(</a><a id="2263" href="foundation.strong-preunivalence.html#2263" class="Bound">l2</a> <a id="2266" class="Symbol">:</a> <a id="2268" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2273" class="Symbol">)</a> <a id="2275" class="Symbol">(</a><a id="2276" href="foundation.strong-preunivalence.html#2276" class="Bound">X</a> <a id="2278" class="Symbol">:</a> <a id="2280" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2283" href="foundation.strong-preunivalence.html#2250" class="Bound">l1</a><a id="2285" class="Symbol">)</a> <a id="2287" class="Symbol">→</a> <a id="2289" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2292" class="Symbol">(</a><a id="2293" href="foundation.strong-preunivalence.html#2250" class="Bound">l1</a> <a id="2296" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2298" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2303" href="foundation.strong-preunivalence.html#2263" class="Bound">l2</a><a id="2305" class="Symbol">)</a>
<a id="2307" href="foundation.strong-preunivalence.html#2215" class="Function">instance-strong-preunivalence</a> <a id="2337" href="foundation.strong-preunivalence.html#2337" class="Bound">l2</a> <a id="2340" href="foundation.strong-preunivalence.html#2340" class="Bound">X</a> <a id="2342" class="Symbol">=</a> <a id="2344" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="2351" class="Symbol">(</a><a id="2352" href="foundation-core.small-types.html#1494" class="Function">is-small</a> <a id="2361" href="foundation.strong-preunivalence.html#2337" class="Bound">l2</a> <a id="2364" href="foundation.strong-preunivalence.html#2340" class="Bound">X</a><a id="2365" class="Symbol">)</a>

<a id="strong-preunivalence-axiom-Level"></a><a id="2368" href="foundation.strong-preunivalence.html#2368" class="Function">strong-preunivalence-axiom-Level</a> <a id="2401" class="Symbol">:</a> <a id="2403" class="Symbol">(</a><a id="2404" href="foundation.strong-preunivalence.html#2404" class="Bound">l1</a> <a id="2407" href="foundation.strong-preunivalence.html#2407" class="Bound">l2</a> <a id="2410" class="Symbol">:</a> <a id="2412" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2417" class="Symbol">)</a> <a id="2419" class="Symbol">→</a> <a id="2421" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2424" class="Symbol">(</a><a id="2425" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2430" href="foundation.strong-preunivalence.html#2404" class="Bound">l1</a> <a id="2433" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2435" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2440" href="foundation.strong-preunivalence.html#2407" class="Bound">l2</a><a id="2442" class="Symbol">)</a>
<a id="2444" href="foundation.strong-preunivalence.html#2368" class="Function">strong-preunivalence-axiom-Level</a> <a id="2477" href="foundation.strong-preunivalence.html#2477" class="Bound">l1</a> <a id="2480" href="foundation.strong-preunivalence.html#2480" class="Bound">l2</a> <a id="2483" class="Symbol">=</a>
  <a id="2487" class="Symbol">(</a><a id="2488" href="foundation.strong-preunivalence.html#2488" class="Bound">X</a> <a id="2490" class="Symbol">:</a> <a id="2492" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2495" href="foundation.strong-preunivalence.html#2477" class="Bound">l1</a><a id="2497" class="Symbol">)</a> <a id="2499" class="Symbol">→</a> <a id="2501" href="foundation.strong-preunivalence.html#2215" class="Function">instance-strong-preunivalence</a> <a id="2531" href="foundation.strong-preunivalence.html#2480" class="Bound">l2</a> <a id="2534" href="foundation.strong-preunivalence.html#2488" class="Bound">X</a>

<a id="strong-preunivalence-axiom"></a><a id="2537" href="foundation.strong-preunivalence.html#2537" class="Function">strong-preunivalence-axiom</a> <a id="2564" class="Symbol">:</a> <a id="2566" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
<a id="2570" href="foundation.strong-preunivalence.html#2537" class="Function">strong-preunivalence-axiom</a> <a id="2597" class="Symbol">=</a>
  <a id="2601" class="Symbol">{</a><a id="2602" href="foundation.strong-preunivalence.html#2602" class="Bound">l1</a> <a id="2605" href="foundation.strong-preunivalence.html#2605" class="Bound">l2</a> <a id="2608" class="Symbol">:</a> <a id="2610" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2615" class="Symbol">}</a> <a id="2617" class="Symbol">→</a> <a id="2619" href="foundation.strong-preunivalence.html#2368" class="Function">strong-preunivalence-axiom-Level</a> <a id="2652" href="foundation.strong-preunivalence.html#2602" class="Bound">l1</a> <a id="2655" href="foundation.strong-preunivalence.html#2605" class="Bound">l2</a>
</pre>
## Properties

### The strong preunivalence axiom strengthens the preunivalence axiom

<pre class="Agda"><a id="based-preunivalence-instance-strong-preunivalence"></a><a id="2758" href="foundation.strong-preunivalence.html#2758" class="Function">based-preunivalence-instance-strong-preunivalence</a> <a id="2808" class="Symbol">:</a>
  <a id="2812" class="Symbol">{</a><a id="2813" href="foundation.strong-preunivalence.html#2813" class="Bound">l</a> <a id="2815" class="Symbol">:</a> <a id="2817" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2822" class="Symbol">}</a> <a id="2824" class="Symbol">(</a><a id="2825" href="foundation.strong-preunivalence.html#2825" class="Bound">X</a> <a id="2827" class="Symbol">:</a> <a id="2829" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2832" href="foundation.strong-preunivalence.html#2813" class="Bound">l</a><a id="2833" class="Symbol">)</a> <a id="2835" class="Symbol">→</a>
  <a id="2839" href="foundation.strong-preunivalence.html#2215" class="Function">instance-strong-preunivalence</a> <a id="2869" href="foundation.strong-preunivalence.html#2813" class="Bound">l</a> <a id="2871" href="foundation.strong-preunivalence.html#2825" class="Bound">X</a> <a id="2873" class="Symbol">→</a> <a id="2875" href="foundation.preunivalence.html#945" class="Function">based-preunivalence-axiom</a> <a id="2901" href="foundation.strong-preunivalence.html#2825" class="Bound">X</a>
<a id="2903" href="foundation.strong-preunivalence.html#2758" class="Function">based-preunivalence-instance-strong-preunivalence</a> <a id="2953" href="foundation.strong-preunivalence.html#2953" class="Bound">X</a> <a id="2955" href="foundation.strong-preunivalence.html#2955" class="Bound">L</a> <a id="2957" href="foundation.strong-preunivalence.html#2957" class="Bound">Y</a> <a id="2959" class="Symbol">=</a>
  <a id="2963" href="foundation-core.propositional-maps.html#2081" class="Function">is-emb-is-prop-map</a>
    <a id="2986" class="Symbol">(</a> <a id="2988" href="foundation.structured-equality-duality.html#2414" class="Function">backward-implication-structured-equality-duality</a>
      <a id="3043" class="Symbol">(</a> <a id="3045" href="foundation-core.propositions.html#4365" class="Function">is-prop-equiv&#39;</a><a id="3059" class="Symbol">)</a>
      <a id="3067" class="Symbol">(</a> <a id="3069" href="foundation.strong-preunivalence.html#2955" class="Bound">L</a><a id="3070" class="Symbol">)</a>
      <a id="3078" class="Symbol">(</a> <a id="3080" href="foundation.strong-preunivalence.html#2953" class="Bound">X</a><a id="3081" class="Symbol">)</a>
      <a id="3089" class="Symbol">(</a> <a id="3091" class="Symbol">λ</a> <a id="3093" href="foundation.strong-preunivalence.html#3093" class="Bound">_</a> <a id="3095" class="Symbol">→</a> <a id="3097" href="foundation-core.univalence.html#1454" class="Function">equiv-eq</a><a id="3105" class="Symbol">)</a>
      <a id="3113" class="Symbol">(</a> <a id="3115" href="foundation.strong-preunivalence.html#2957" class="Bound">Y</a><a id="3116" class="Symbol">))</a>

<a id="preunivalence-axiom-strong-preunivalence-axiom"></a><a id="3120" href="foundation.strong-preunivalence.html#3120" class="Function">preunivalence-axiom-strong-preunivalence-axiom</a> <a id="3167" class="Symbol">:</a>
  <a id="3171" href="foundation.strong-preunivalence.html#2537" class="Function">strong-preunivalence-axiom</a> <a id="3198" class="Symbol">→</a> <a id="3200" href="foundation.preunivalence.html#1212" class="Function">preunivalence-axiom</a>
<a id="3220" href="foundation.strong-preunivalence.html#3120" class="Function">preunivalence-axiom-strong-preunivalence-axiom</a> <a id="3267" href="foundation.strong-preunivalence.html#3267" class="Bound">L</a> <a id="3269" href="foundation.strong-preunivalence.html#3269" class="Bound">X</a> <a id="3271" class="Symbol">=</a>
  <a id="3275" href="foundation.strong-preunivalence.html#2758" class="Function">based-preunivalence-instance-strong-preunivalence</a> <a id="3325" href="foundation.strong-preunivalence.html#3269" class="Bound">X</a> <a id="3327" class="Symbol">(</a><a id="3328" href="foundation.strong-preunivalence.html#3267" class="Bound">L</a> <a id="3330" href="foundation.strong-preunivalence.html#3269" class="Bound">X</a><a id="3331" class="Symbol">)</a>
</pre>
### The strong preunivalence axiom generalizes axiom K

To show that preunivalence generalizes axiom K, we assume axiom K for types of
equivalences and for the universe itself.

<pre class="Agda"><a id="instance-strong-preunivalence-instance-axiom-K"></a><a id="3524" href="foundation.strong-preunivalence.html#3524" class="Function">instance-strong-preunivalence-instance-axiom-K</a> <a id="3571" class="Symbol">:</a>
  <a id="3575" class="Symbol">{</a><a id="3576" href="foundation.strong-preunivalence.html#3576" class="Bound">l1</a> <a id="3579" class="Symbol">:</a> <a id="3581" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3586" class="Symbol">}</a> <a id="3588" class="Symbol">(</a><a id="3589" href="foundation.strong-preunivalence.html#3589" class="Bound">l2</a> <a id="3592" class="Symbol">:</a> <a id="3594" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3599" class="Symbol">)</a> <a id="3601" class="Symbol">(</a><a id="3602" href="foundation.strong-preunivalence.html#3602" class="Bound">A</a> <a id="3604" class="Symbol">:</a> <a id="3606" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3609" href="foundation.strong-preunivalence.html#3576" class="Bound">l1</a><a id="3611" class="Symbol">)</a> <a id="3613" class="Symbol">→</a>
  <a id="3617" href="foundation-core.sets.html#1320" class="Function">instance-axiom-K</a> <a id="3634" class="Symbol">(</a><a id="3635" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3638" href="foundation.strong-preunivalence.html#3589" class="Bound">l2</a><a id="3640" class="Symbol">)</a> <a id="3642" class="Symbol">→</a>
  <a id="3646" class="Symbol">((</a><a id="3648" href="foundation.strong-preunivalence.html#3648" class="Bound">B</a> <a id="3650" class="Symbol">:</a> <a id="3652" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3655" href="foundation.strong-preunivalence.html#3589" class="Bound">l2</a><a id="3657" class="Symbol">)</a> <a id="3659" class="Symbol">→</a> <a id="3661" href="foundation-core.sets.html#1320" class="Function">instance-axiom-K</a> <a id="3678" class="Symbol">(</a><a id="3679" href="foundation.strong-preunivalence.html#3602" class="Bound">A</a> <a id="3681" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="3683" href="foundation.strong-preunivalence.html#3648" class="Bound">B</a><a id="3684" class="Symbol">))</a> <a id="3687" class="Symbol">→</a>
  <a id="3691" href="foundation.strong-preunivalence.html#2215" class="Function">instance-strong-preunivalence</a> <a id="3721" href="foundation.strong-preunivalence.html#3589" class="Bound">l2</a> <a id="3724" href="foundation.strong-preunivalence.html#3602" class="Bound">A</a>
<a id="3726" href="foundation.strong-preunivalence.html#3524" class="Function">instance-strong-preunivalence-instance-axiom-K</a> <a id="3773" href="foundation.strong-preunivalence.html#3773" class="Bound">l2</a> <a id="3776" href="foundation.strong-preunivalence.html#3776" class="Bound">A</a> <a id="3778" href="foundation.strong-preunivalence.html#3778" class="Bound">K-Type</a> <a id="3785" href="foundation.strong-preunivalence.html#3785" class="Bound">K-A≃B</a> <a id="3791" class="Symbol">=</a>
  <a id="3795" href="foundation.sets.html#1498" class="Function">is-set-Σ</a> <a id="3804" class="Symbol">(</a><a id="3805" href="foundation-core.sets.html#1791" class="Function">is-set-axiom-K</a> <a id="3820" href="foundation.strong-preunivalence.html#3778" class="Bound">K-Type</a><a id="3826" class="Symbol">)</a> <a id="3828" class="Symbol">(</a><a id="3829" href="foundation-core.sets.html#1791" class="Function">is-set-axiom-K</a> <a id="3844" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3846" href="foundation.strong-preunivalence.html#3785" class="Bound">K-A≃B</a><a id="3851" class="Symbol">)</a>

<a id="strong-preunivalence-axiom-axiom-K"></a><a id="3854" href="foundation.strong-preunivalence.html#3854" class="Function">strong-preunivalence-axiom-axiom-K</a> <a id="3889" class="Symbol">:</a> <a id="3891" href="foundation-core.sets.html#1511" class="Function">axiom-K</a> <a id="3899" class="Symbol">→</a> <a id="3901" href="foundation.strong-preunivalence.html#2537" class="Function">strong-preunivalence-axiom</a>
<a id="3928" href="foundation.strong-preunivalence.html#3854" class="Function">strong-preunivalence-axiom-axiom-K</a> <a id="3963" href="foundation.strong-preunivalence.html#3963" class="Bound">K</a> <a id="3965" class="Symbol">{</a><a id="3966" href="foundation.strong-preunivalence.html#3966" class="Bound">l1</a><a id="3968" class="Symbol">}</a> <a id="3970" class="Symbol">{</a><a id="3971" href="foundation.strong-preunivalence.html#3971" class="Bound">l2</a><a id="3973" class="Symbol">}</a> <a id="3975" href="foundation.strong-preunivalence.html#3975" class="Bound">A</a> <a id="3977" class="Symbol">=</a>
  <a id="3981" href="foundation.strong-preunivalence.html#3524" class="Function">instance-strong-preunivalence-instance-axiom-K</a> <a id="4028" href="foundation.strong-preunivalence.html#3971" class="Bound">l2</a> <a id="4031" href="foundation.strong-preunivalence.html#3975" class="Bound">A</a>
    <a id="4037" class="Symbol">(</a> <a id="4039" href="foundation.strong-preunivalence.html#3963" class="Bound">K</a> <a id="4041" class="Symbol">(</a><a id="4042" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4045" href="foundation.strong-preunivalence.html#3971" class="Bound">l2</a><a id="4047" class="Symbol">))</a>
    <a id="4054" class="Symbol">(</a> <a id="4056" class="Symbol">λ</a> <a id="4058" href="foundation.strong-preunivalence.html#4058" class="Bound">B</a> <a id="4060" class="Symbol">→</a> <a id="4062" href="foundation.strong-preunivalence.html#3963" class="Bound">K</a> <a id="4064" class="Symbol">(</a><a id="4065" href="foundation.strong-preunivalence.html#3975" class="Bound">A</a> <a id="4067" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="4069" href="foundation.strong-preunivalence.html#4058" class="Bound">B</a><a id="4070" class="Symbol">))</a>
</pre>
### The strong preunivalence axiom generalizes the univalence axiom

<pre class="Agda"><a id="strong-preunivalence-axiom-univalence-axiom"></a><a id="4155" href="foundation.strong-preunivalence.html#4155" class="Function">strong-preunivalence-axiom-univalence-axiom</a> <a id="4199" class="Symbol">:</a>
  <a id="4203" href="foundation-core.univalence.html#2382" class="Function">univalence-axiom</a> <a id="4220" class="Symbol">→</a> <a id="4222" href="foundation.strong-preunivalence.html#2537" class="Function">strong-preunivalence-axiom</a>
<a id="4249" href="foundation.strong-preunivalence.html#4155" class="Function">strong-preunivalence-axiom-univalence-axiom</a> <a id="4293" href="foundation.strong-preunivalence.html#4293" class="Bound">UA</a> <a id="4296" class="Symbol">{</a><a id="4297" href="foundation.strong-preunivalence.html#4297" class="Bound">l1</a><a id="4299" class="Symbol">}</a> <a id="4301" class="Symbol">{</a><a id="4302" href="foundation.strong-preunivalence.html#4302" class="Bound">l2</a><a id="4304" class="Symbol">}</a> <a id="4306" href="foundation.strong-preunivalence.html#4306" class="Bound">A</a> <a id="4308" class="Symbol">=</a>
  <a id="4312" href="foundation-core.sets.html#4158" class="Function">is-set-is-prop</a>
  <a id="4329" class="Symbol">(</a> <a id="4331" href="foundation-core.propositions.html#3025" class="Function">is-prop-is-proof-irrelevant</a>
    <a id="4363" class="Symbol">(</a> <a id="4365" class="Symbol">λ</a> <a id="4367" class="Symbol">(</a><a id="4368" href="foundation.strong-preunivalence.html#4368" class="Bound">X</a> <a id="4370" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4372" href="foundation.strong-preunivalence.html#4372" class="Bound">e</a><a id="4373" class="Symbol">)</a> <a id="4375" class="Symbol">→</a>
      <a id="4383" href="foundation-core.contractible-types.html#2905" class="Function">is-contr-equiv&#39;</a>
        <a id="4407" class="Symbol">(</a> <a id="4409" href="foundation-core.small-types.html#1494" class="Function">is-small</a> <a id="4418" href="foundation.strong-preunivalence.html#4302" class="Bound">l2</a> <a id="4421" href="foundation.strong-preunivalence.html#4368" class="Bound">X</a><a id="4422" class="Symbol">)</a>
        <a id="4432" class="Symbol">(</a> <a id="4434" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a> <a id="4444" class="Symbol">(</a><a id="4445" href="foundation.equivalences.html#18625" class="Function">equiv-precomp-equiv</a> <a id="4465" href="foundation.strong-preunivalence.html#4372" class="Bound">e</a><a id="4466" class="Symbol">))</a>
        <a id="4477" class="Symbol">(</a> <a id="4479" href="foundation-core.univalence.html#2589" class="Function">is-torsorial-equiv-based-univalence</a> <a id="4515" href="foundation.strong-preunivalence.html#4368" class="Bound">X</a> <a id="4517" class="Symbol">(</a><a id="4518" href="foundation.strong-preunivalence.html#4293" class="Bound">UA</a> <a id="4521" href="foundation.strong-preunivalence.html#4368" class="Bound">X</a><a id="4522" class="Symbol">))))</a>
</pre>
### Strong preunivalence holds in univalent foundations

<pre class="Agda"><a id="strong-preunivalence"></a><a id="4597" href="foundation.strong-preunivalence.html#4597" class="Function">strong-preunivalence</a> <a id="4618" class="Symbol">:</a> <a id="4620" href="foundation.strong-preunivalence.html#2537" class="Function">strong-preunivalence-axiom</a>
<a id="4647" href="foundation.strong-preunivalence.html#4597" class="Function">strong-preunivalence</a> <a id="4668" class="Symbol">=</a> <a id="4670" href="foundation.strong-preunivalence.html#4155" class="Function">strong-preunivalence-axiom-univalence-axiom</a> <a id="4714" href="foundation.univalence.html#2111" class="Function">univalence</a>
</pre>
### The preunivalence axiom implies the strong preunivalence axiom

This argument is due to [Evan Cavallo](https://ecavallo.net/). Note that it
depends on the function extensionality axiom in order to compute the equality
type of `is-small`.

<pre class="Agda"><a id="strong-preunivalence-axiom-preunivalence-axiom-Level"></a><a id="4981" href="foundation.strong-preunivalence.html#4981" class="Function">strong-preunivalence-axiom-preunivalence-axiom-Level</a> <a id="5034" class="Symbol">:</a>
  <a id="5038" class="Symbol">{</a><a id="5039" href="foundation.strong-preunivalence.html#5039" class="Bound">l1</a> <a id="5042" href="foundation.strong-preunivalence.html#5042" class="Bound">l2</a> <a id="5045" class="Symbol">:</a> <a id="5047" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5052" class="Symbol">}</a> <a id="5054" class="Symbol">→</a>
  <a id="5058" href="foundation.preunivalence.html#1085" class="Function">preunivalence-axiom-Level</a> <a id="5084" href="foundation.strong-preunivalence.html#5039" class="Bound">l1</a> <a id="5087" class="Symbol">→</a> <a id="5089" href="foundation.strong-preunivalence.html#2368" class="Function">strong-preunivalence-axiom-Level</a> <a id="5122" href="foundation.strong-preunivalence.html#5042" class="Bound">l2</a> <a id="5125" href="foundation.strong-preunivalence.html#5039" class="Bound">l1</a>
<a id="5128" href="foundation.strong-preunivalence.html#4981" class="Function">strong-preunivalence-axiom-preunivalence-axiom-Level</a> <a id="5181" href="foundation.strong-preunivalence.html#5181" class="Bound">pua</a> <a id="5185" href="foundation.strong-preunivalence.html#5185" class="Bound">X</a> <a id="5187" class="Symbol">(</a><a id="5188" href="foundation.strong-preunivalence.html#5188" class="Bound">Y</a> <a id="5190" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5192" href="foundation.strong-preunivalence.html#5192" class="Bound">α</a><a id="5193" class="Symbol">)</a> <a id="5195" class="Symbol">(</a><a id="5196" href="foundation.strong-preunivalence.html#5196" class="Bound">Y&#39;</a> <a id="5199" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5201" href="foundation.strong-preunivalence.html#5201" class="Bound">α&#39;</a><a id="5203" class="Symbol">)</a> <a id="5205" class="Symbol">=</a>
  <a id="5209" href="foundation-core.propositions.html#4010" class="Function">is-prop-equiv</a>
    <a id="5227" class="Symbol">(</a> <a id="5229" href="foundation-core.small-types.html#5986" class="Function">compute-eq-is-small</a> <a id="5249" class="Symbol">(</a><a id="5250" href="foundation.strong-preunivalence.html#5188" class="Bound">Y</a> <a id="5252" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5254" href="foundation.strong-preunivalence.html#5192" class="Bound">α</a><a id="5255" class="Symbol">)</a> <a id="5257" class="Symbol">(</a><a id="5258" href="foundation.strong-preunivalence.html#5196" class="Bound">Y&#39;</a> <a id="5261" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5263" href="foundation.strong-preunivalence.html#5201" class="Bound">α&#39;</a><a id="5265" class="Symbol">))</a>
    <a id="5272" class="Symbol">(</a> <a id="5274" href="foundation-core.propositional-maps.html#2396" class="Function">is-prop-map-is-emb</a> <a id="5293" class="Symbol">(</a><a id="5294" href="foundation.strong-preunivalence.html#5181" class="Bound">pua</a> <a id="5298" href="foundation.strong-preunivalence.html#5188" class="Bound">Y</a> <a id="5300" href="foundation.strong-preunivalence.html#5196" class="Bound">Y&#39;</a><a id="5302" class="Symbol">)</a> <a id="5304" class="Symbol">(</a><a id="5305" href="foundation.strong-preunivalence.html#5201" class="Bound">α&#39;</a> <a id="5308" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a> <a id="5311" href="foundation-core.equivalences.html#8859" class="Function">inv-equiv</a> <a id="5321" href="foundation.strong-preunivalence.html#5192" class="Bound">α</a><a id="5322" class="Symbol">))</a>
</pre>
See
[`UF.PreUnivalence`](https://martinescardo.github.io/TypeTopology/UF.PreUnivalence.html)
at TypeTopology for Cavallo's original formalizations.

## See also

- [Strongly preunivalent categories](category-theory.strongly-preunivalent-categories.md)
