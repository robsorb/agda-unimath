# Crisp function types

<pre class="Agda"><a id="33" class="Symbol">{-#</a> <a id="37" class="Keyword">OPTIONS</a> <a id="45" class="Pragma">--cohesion</a> <a id="56" class="Pragma">--flat-split</a> <a id="69" class="Symbol">#-}</a>

<a id="74" class="Keyword">module</a> <a id="81" href="modal-type-theory.crisp-function-types.html" class="Module">modal-type-theory.crisp-function-types</a> <a id="120" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="341" class="Keyword">open</a> <a id="346" class="Keyword">import</a> <a id="353" href="foundation.postcomposition-functions.html" class="Module">foundation.postcomposition-functions</a>
<a id="390" class="Keyword">open</a> <a id="395" class="Keyword">import</a> <a id="402" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="425" class="Keyword">open</a> <a id="430" class="Keyword">import</a> <a id="437" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="457" class="Keyword">open</a> <a id="462" class="Keyword">import</a> <a id="469" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="modal-type-theory.action-on-identifications-flat-modality.html" class="Module">modal-type-theory.action-on-identifications-flat-modality</a>
<a id="567" class="Keyword">open</a> <a id="572" class="Keyword">import</a> <a id="579" href="modal-type-theory.crisp-dependent-function-types.html" class="Module">modal-type-theory.crisp-dependent-function-types</a>
<a id="628" class="Keyword">open</a> <a id="633" class="Keyword">import</a> <a id="640" href="modal-type-theory.flat-modality.html" class="Module">modal-type-theory.flat-modality</a>
<a id="672" class="Keyword">open</a> <a id="677" class="Keyword">import</a> <a id="684" href="modal-type-theory.functoriality-flat-modality.html" class="Module">modal-type-theory.functoriality-flat-modality</a>
</pre>
</details>

## Idea

We say a [function type](foundation-core.function-types.md) is
{{#concept "crisp" Disambiguation="function type"}} if it is formed in a
[crisp context](modal-type-theory.crisp-types.md).

A function `f` from `A` to `B` may be assumed to be a
{{#concept "crisp function" Disambiguation="of crisp types"}} given that its
domain and codomain are crisp. By this we mean it is a crisp element of its
type, written `@♭ f : A → B`. We may also assume that a function is
{{#concept "defined on crisp elements" Disambiguation="function on a crisp type"}}
if its definition assumes that the elements of its domain are crisp, written
`f : @♭ A → B`. Being crisp, and being defined on crisp elements are independent
properties. A function may be crisp and defined on cohesive elements, and it may
be cohesive but defined on crisp elements. Indeed, all configurations are
possible when both `A` and `B` are crisp:

|                              |  Crisp function | Cohesive function |
| ---------------------------: | --------------: | ----------------: |
|    Defined on crisp elements | `@♭ (@♭ A → B)` |        `@♭ A → B` |
| Defined on cohesive elements |    `@♭ (A → B)` |           `A → B` |

Note, since assuming that a hypothesis is crisp is _less_ general, assuming that
a hypothesis assumes that a hypothesis is crisp is _more_ general. Hence
assuming the function is cohesive and defined on crisp elements `f : @♭ A → B`
is the _weakest_ assumption one can make given that `A` is crisp, while assuming
it is crisp and defined on cohesive elements `@♭ f : A → B` is the strongest,
given that `B` is also crisp.

## Properties

### Flat distributes in one direction over function types

<pre class="Agda"><a id="2448" class="Keyword">module</a> <a id="2455" href="modal-type-theory.crisp-function-types.html#2455" class="Module">_</a>
  <a id="2459" class="Symbol">{@</a>♭ <a id="2463" href="modal-type-theory.crisp-function-types.html#2463" class="Bound">l1</a> <a id="2466" href="modal-type-theory.crisp-function-types.html#2466" class="Bound">l2</a> <a id="2469" class="Symbol">:</a> <a id="2471" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2476" class="Symbol">}</a> <a id="2478" class="Symbol">{@</a>♭ <a id="2482" href="modal-type-theory.crisp-function-types.html#2482" class="Bound">A</a> <a id="2484" class="Symbol">:</a> <a id="2486" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2489" href="modal-type-theory.crisp-function-types.html#2463" class="Bound">l1</a><a id="2491" class="Symbol">}</a> <a id="2493" class="Symbol">{@</a>♭ <a id="2497" href="modal-type-theory.crisp-function-types.html#2497" class="Bound">B</a> <a id="2499" class="Symbol">:</a> <a id="2501" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2504" href="modal-type-theory.crisp-function-types.html#2466" class="Bound">l2</a><a id="2506" class="Symbol">}</a>
  <a id="2510" class="Keyword">where</a>

  <a id="2519" href="modal-type-theory.crisp-function-types.html#2519" class="Function">map-distributive-flat-crisp-function-types</a> <a id="2562" class="Symbol">:</a> <a id="2564" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="2566" class="Symbol">(@</a>♭ <a id="2570" href="modal-type-theory.crisp-function-types.html#2482" class="Bound">A</a> <a id="2572" class="Symbol">→</a> <a id="2574" href="modal-type-theory.crisp-function-types.html#2497" class="Bound">B</a><a id="2575" class="Symbol">)</a> <a id="2577" class="Symbol">→</a> <a id="2579" class="Symbol">(@</a>♭ <a id="2583" href="modal-type-theory.crisp-function-types.html#2482" class="Bound">A</a> <a id="2585" class="Symbol">→</a> <a id="2587" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="2589" href="modal-type-theory.crisp-function-types.html#2497" class="Bound">B</a><a id="2590" class="Symbol">)</a>
  <a id="2594" href="modal-type-theory.crisp-function-types.html#2519" class="Function">map-distributive-flat-crisp-function-types</a> <a id="2637" class="Symbol">=</a> <a id="2639" href="modal-type-theory.crisp-dependent-function-types.html#2659" class="Function">map-distributive-flat-crisp-Π</a>

  <a id="2672" href="modal-type-theory.crisp-function-types.html#2672" class="Function">map-distributive-flat-function-types</a> <a id="2709" class="Symbol">:</a> <a id="2711" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="2713" class="Symbol">(</a><a id="2714" href="modal-type-theory.crisp-function-types.html#2482" class="Bound">A</a> <a id="2716" class="Symbol">→</a> <a id="2718" href="modal-type-theory.crisp-function-types.html#2497" class="Bound">B</a><a id="2719" class="Symbol">)</a> <a id="2721" class="Symbol">→</a> <a id="2723" class="Symbol">(</a><a id="2724" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="2726" href="modal-type-theory.crisp-function-types.html#2482" class="Bound">A</a> <a id="2728" class="Symbol">→</a> <a id="2730" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="2732" href="modal-type-theory.crisp-function-types.html#2497" class="Bound">B</a><a id="2733" class="Symbol">)</a>
  <a id="2737" href="modal-type-theory.crisp-function-types.html#2672" class="Function">map-distributive-flat-function-types</a> <a id="2774" href="modal-type-theory.crisp-function-types.html#2774" class="Bound">f</a> <a id="2776" class="Symbol">(</a><a id="2777" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="2788" href="modal-type-theory.crisp-function-types.html#2788" class="Bound">x</a><a id="2789" class="Symbol">)</a> <a id="2791" class="Symbol">=</a>
    <a id="2797" href="modal-type-theory.crisp-dependent-function-types.html#2881" class="Function">map-distributive-flat-Π</a> <a id="2821" href="modal-type-theory.crisp-function-types.html#2774" class="Bound">f</a> <a id="2823" class="Symbol">(</a><a id="2824" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="2835" href="modal-type-theory.crisp-function-types.html#2788" class="Bound">x</a><a id="2836" class="Symbol">)</a>
</pre>
### Postcomposition by the flat counit induces an equivalence `♭ (♭ A → ♭ B) ≃ ♭ (♭ A → B)`

This is Theorem 6.14 in {{#cite Shu18}}.

<pre class="Agda"><a id="2986" class="Keyword">module</a> <a id="2993" href="modal-type-theory.crisp-function-types.html#2993" class="Module">_</a>
  <a id="2997" class="Symbol">{@</a>♭ <a id="3001" href="modal-type-theory.crisp-function-types.html#3001" class="Bound">l1</a> <a id="3004" href="modal-type-theory.crisp-function-types.html#3004" class="Bound">l2</a> <a id="3007" class="Symbol">:</a> <a id="3009" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3014" class="Symbol">}</a> <a id="3016" class="Symbol">{@</a>♭ <a id="3020" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a> <a id="3022" class="Symbol">:</a> <a id="3024" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3027" href="modal-type-theory.crisp-function-types.html#3001" class="Bound">l1</a><a id="3029" class="Symbol">}</a> <a id="3031" class="Symbol">{@</a>♭ <a id="3035" href="modal-type-theory.crisp-function-types.html#3035" class="Bound">B</a> <a id="3037" class="Symbol">:</a> <a id="3039" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3042" href="modal-type-theory.crisp-function-types.html#3004" class="Bound">l2</a><a id="3044" class="Symbol">}</a>
  <a id="3048" class="Keyword">where</a>

  <a id="3057" href="modal-type-theory.crisp-function-types.html#3057" class="Function">map-inv-action-flat-map-postcomp-counit-flat</a> <a id="3102" class="Symbol">:</a> <a id="3104" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="3106" class="Symbol">(</a><a id="3107" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="3109" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a> <a id="3111" class="Symbol">→</a> <a id="3113" href="modal-type-theory.crisp-function-types.html#3035" class="Bound">B</a><a id="3114" class="Symbol">)</a> <a id="3116" class="Symbol">→</a> <a id="3118" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="3120" class="Symbol">(</a><a id="3121" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="3123" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a> <a id="3125" class="Symbol">→</a> <a id="3127" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="3129" href="modal-type-theory.crisp-function-types.html#3035" class="Bound">B</a><a id="3130" class="Symbol">)</a>
  <a id="3134" href="modal-type-theory.crisp-function-types.html#3057" class="Function">map-inv-action-flat-map-postcomp-counit-flat</a> <a id="3179" class="Symbol">(</a><a id="3180" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3191" href="modal-type-theory.crisp-function-types.html#3191" class="Bound">f</a><a id="3192" class="Symbol">)</a> <a id="3194" class="Symbol">=</a>
    <a id="3200" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3211" class="Symbol">(λ</a> <a id="3214" class="Keyword">where</a> <a id="3220" class="Symbol">(</a><a id="3221" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3232" href="modal-type-theory.crisp-function-types.html#3232" class="Bound">y</a><a id="3233" class="Symbol">)</a> <a id="3235" class="Symbol">→</a> <a id="3237" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3248" class="Symbol">(</a><a id="3249" href="modal-type-theory.crisp-function-types.html#3191" class="Bound">f</a> <a id="3251" class="Symbol">(</a><a id="3252" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3263" href="modal-type-theory.crisp-function-types.html#3232" class="Bound">y</a><a id="3264" class="Symbol">)))</a>

  <a id="3271" href="modal-type-theory.crisp-function-types.html#3271" class="Function">is-section-map-inv-action-flat-map-postcomp-counit-flat</a> <a id="3327" class="Symbol">:</a>
    <a id="3333" href="foundation-core.sections.html#1194" class="Function">is-section</a>
      <a id="3350" class="Symbol">(</a> <a id="3352" href="modal-type-theory.functoriality-flat-modality.html#2329" class="Function">action-flat-map</a> <a id="3368" class="Symbol">(</a><a id="3369" href="foundation-core.postcomposition-functions.html#551" class="Function">postcomp</a> <a id="3378" class="Symbol">(</a><a id="3379" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="3381" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a><a id="3382" class="Symbol">)</a> <a id="3384" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a><a id="3395" class="Symbol">))</a>
      <a id="3404" class="Symbol">(</a> <a id="3406" href="modal-type-theory.crisp-function-types.html#3057" class="Function">map-inv-action-flat-map-postcomp-counit-flat</a><a id="3450" class="Symbol">)</a>
  <a id="3454" href="modal-type-theory.crisp-function-types.html#3271" class="Function">is-section-map-inv-action-flat-map-postcomp-counit-flat</a> <a id="3510" class="Symbol">(</a><a id="3511" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3522" href="modal-type-theory.crisp-function-types.html#3522" class="Bound">f</a><a id="3523" class="Symbol">)</a> <a id="3525" class="Symbol">=</a>
    <a id="3531" href="modal-type-theory.action-on-identifications-flat-modality.html#892" class="Function">ap-flat</a> <a id="3539" class="Symbol">(</a><a id="3540" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a> <a id="3548" class="Symbol">(λ</a> <a id="3551" class="Keyword">where</a> <a id="3557" class="Symbol">(</a><a id="3558" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3569" class="Symbol">_)</a> <a id="3572" class="Symbol">→</a> <a id="3574" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="3578" class="Symbol">))</a>

  <a id="3584" href="modal-type-theory.crisp-function-types.html#3584" class="Function">is-retraction-map-inv-action-flat-map-postcomp-counit-flat</a> <a id="3643" class="Symbol">:</a>
    <a id="3649" href="foundation-core.retractions.html#790" class="Function">is-retraction</a>
      <a id="3669" class="Symbol">(</a> <a id="3671" href="modal-type-theory.functoriality-flat-modality.html#2329" class="Function">action-flat-map</a> <a id="3687" class="Symbol">(</a><a id="3688" href="foundation-core.postcomposition-functions.html#551" class="Function">postcomp</a> <a id="3697" class="Symbol">(</a><a id="3698" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="3700" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a><a id="3701" class="Symbol">)</a> <a id="3703" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a><a id="3714" class="Symbol">))</a>
      <a id="3723" class="Symbol">(</a> <a id="3725" href="modal-type-theory.crisp-function-types.html#3057" class="Function">map-inv-action-flat-map-postcomp-counit-flat</a><a id="3769" class="Symbol">)</a>
  <a id="3773" href="modal-type-theory.crisp-function-types.html#3584" class="Function">is-retraction-map-inv-action-flat-map-postcomp-counit-flat</a> <a id="3832" class="Symbol">(</a><a id="3833" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3844" href="modal-type-theory.crisp-function-types.html#3844" class="Bound">f</a><a id="3845" class="Symbol">)</a> <a id="3847" class="Symbol">=</a>
    <a id="3853" href="modal-type-theory.action-on-identifications-flat-modality.html#892" class="Function">ap-flat</a>
      <a id="3867" class="Symbol">(</a> <a id="3869" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a>
        <a id="3885" class="Symbol">(</a> <a id="3887" class="Symbol">λ</a> <a id="3889" class="Keyword">where</a>
          <a id="3905" class="Symbol">(</a><a id="3906" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3917" href="modal-type-theory.crisp-function-types.html#3917" class="Bound">x</a><a id="3918" class="Symbol">)</a> <a id="3920" class="Symbol">→</a> <a id="3922" href="modal-type-theory.flat-modality.html#1867" class="Function">is-crisp-retraction-intro-flat</a> <a id="3953" class="Symbol">(</a><a id="3954" href="modal-type-theory.crisp-function-types.html#3844" class="Bound">f</a> <a id="3956" class="Symbol">(</a><a id="3957" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="3968" href="modal-type-theory.crisp-function-types.html#3917" class="Bound">x</a><a id="3969" class="Symbol">))))</a>

  <a id="3977" href="modal-type-theory.crisp-function-types.html#3977" class="Function">is-equiv-action-flat-map-postcomp-counit-flat</a> <a id="4023" class="Symbol">:</a>
    <a id="4029" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="4038" class="Symbol">(</a><a id="4039" href="modal-type-theory.functoriality-flat-modality.html#2329" class="Function">action-flat-map</a> <a id="4055" class="Symbol">(</a><a id="4056" href="foundation-core.postcomposition-functions.html#551" class="Function">postcomp</a> <a id="4065" class="Symbol">(</a><a id="4066" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="4068" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a><a id="4069" class="Symbol">)</a> <a id="4071" class="Symbol">(</a><a id="4072" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a> <a id="4084" class="Symbol">{</a><a id="4085" class="Argument">A</a> <a id="4087" class="Symbol">=</a> <a id="4089" href="modal-type-theory.crisp-function-types.html#3035" class="Bound">B</a><a id="4090" class="Symbol">})))</a>
  <a id="4097" href="modal-type-theory.crisp-function-types.html#3977" class="Function">is-equiv-action-flat-map-postcomp-counit-flat</a> <a id="4143" class="Symbol">=</a>
    <a id="4149" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
      <a id="4178" class="Symbol">(</a> <a id="4180" href="modal-type-theory.crisp-function-types.html#3057" class="Function">map-inv-action-flat-map-postcomp-counit-flat</a><a id="4224" class="Symbol">)</a>
      <a id="4232" class="Symbol">(</a> <a id="4234" href="modal-type-theory.crisp-function-types.html#3271" class="Function">is-section-map-inv-action-flat-map-postcomp-counit-flat</a><a id="4289" class="Symbol">)</a>
      <a id="4297" class="Symbol">(</a> <a id="4299" href="modal-type-theory.crisp-function-types.html#3584" class="Function">is-retraction-map-inv-action-flat-map-postcomp-counit-flat</a><a id="4357" class="Symbol">)</a>

  <a id="4362" href="modal-type-theory.crisp-function-types.html#4362" class="Function">equiv-action-flat-map-postcomp-counit-flat</a> <a id="4405" class="Symbol">:</a> <a id="4407" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="4409" class="Symbol">(</a><a id="4410" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="4412" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a> <a id="4414" class="Symbol">→</a> <a id="4416" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="4418" href="modal-type-theory.crisp-function-types.html#3035" class="Bound">B</a><a id="4419" class="Symbol">)</a> <a id="4421" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="4423" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="4425" class="Symbol">(</a><a id="4426" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="4428" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a> <a id="4430" class="Symbol">→</a> <a id="4432" href="modal-type-theory.crisp-function-types.html#3035" class="Bound">B</a><a id="4433" class="Symbol">)</a>
  <a id="4437" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4441" href="modal-type-theory.crisp-function-types.html#4362" class="Function">equiv-action-flat-map-postcomp-counit-flat</a> <a id="4484" class="Symbol">=</a>
    <a id="4490" href="modal-type-theory.functoriality-flat-modality.html#2329" class="Function">action-flat-map</a> <a id="4506" class="Symbol">(</a><a id="4507" href="foundation-core.postcomposition-functions.html#551" class="Function">postcomp</a> <a id="4516" class="Symbol">(</a><a id="4517" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="4519" href="modal-type-theory.crisp-function-types.html#3020" class="Bound">A</a><a id="4520" class="Symbol">)</a> <a id="4522" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a><a id="4533" class="Symbol">)</a>
  <a id="4537" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4541" href="modal-type-theory.crisp-function-types.html#4362" class="Function">equiv-action-flat-map-postcomp-counit-flat</a> <a id="4584" class="Symbol">=</a>
    <a id="4590" href="modal-type-theory.crisp-function-types.html#3977" class="Function">is-equiv-action-flat-map-postcomp-counit-flat</a>
</pre>
## See also

- [Flat discrete crisp types](modal-type-theory.flat-discrete-crisp-types.md)
  for crisp types that are flat modal.

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
