# Idempotent maps

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="foundation.idempotent-maps.html" class="Module">foundation.idempotent-maps</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.homotopy-algebra.html" class="Module">foundation.homotopy-algebra</a>
<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="422" class="Keyword">open</a> <a id="427" class="Keyword">import</a> <a id="434" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>
<a id="462" class="Keyword">open</a> <a id="467" class="Keyword">import</a> <a id="474" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
</pre>
</details>

## Idea

An {{#concept "idempotent map" Disambiguation="of types" Agda=is-idempotent}} is
a map `f : A → A` [equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md)

```text
  f ∘ f ~ f.
```

While this definition corresponds to the classical concept of an idempotent map
in [set](foundation-core.sets.md)-level mathematics, a homotopy `I : f ∘ f ~ f`
may fail to be coherent with itself in Homotopy Type Theory. For instance, one
may ask for a second-order coherence

```text
  J : f ·r I ~ I ·l f
```

giving the definition of a
[quasicoherently idempotent map](foundation.quasicoherently-idempotent-maps.md).

The situation may be compared against that of
[invertible maps](foundation-core.invertible-maps.md) vs.
[coherently invertible maps](foundation-core.coherently-invertible-maps.md).
Recall that an _invertible map_ is a map `f : A → B` equipped with a converse
map `g : B → A` and homotopies `S : f ∘ g ~ id` and `R : g ∘ f ~ id` witnessing
that `g` is an _inverse_ of `f`, while a _coherently invertible map_ has an
additional coherence `f ·r R ~ S ·l f`.

It is true that every invertible map is coherently invertible, but no such
construction preserves both of the homotopies `S` and `R`. Likewise, every
quasicoherently idempotent map is also coherently idempotent, although again the
coherence `J` is replaced as part of this construction. On the other hand, in
contrast to invertible maps, not every idempotent map can be made to be fully
coherent or even quasicoherent. For a counterexample see Section 4 of
{{#cite Shu17}}.

**Terminology.** Our definition of an _idempotent map_ corresponds to the
definition of a _preidempotent map_ in {{#reference Shu17}} and
{{#reference Shu14SplittingIdempotents}}, while their definition of an
_idempotent map_ corresponds in our terminology to a _coherently idempotent
map_.

## Definitions

### The structure on a map of idempotence

<pre class="Agda"><a id="is-idempotent"></a><a id="2443" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="2457" class="Symbol">:</a> <a id="2459" class="Symbol">{</a><a id="2460" href="foundation.idempotent-maps.html#2460" class="Bound">l</a> <a id="2462" class="Symbol">:</a> <a id="2464" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2469" class="Symbol">}</a> <a id="2471" class="Symbol">{</a><a id="2472" href="foundation.idempotent-maps.html#2472" class="Bound">A</a> <a id="2474" class="Symbol">:</a> <a id="2476" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2479" href="foundation.idempotent-maps.html#2460" class="Bound">l</a><a id="2480" class="Symbol">}</a> <a id="2482" class="Symbol">→</a> <a id="2484" class="Symbol">(</a><a id="2485" href="foundation.idempotent-maps.html#2472" class="Bound">A</a> <a id="2487" class="Symbol">→</a> <a id="2489" href="foundation.idempotent-maps.html#2472" class="Bound">A</a><a id="2490" class="Symbol">)</a> <a id="2492" class="Symbol">→</a> <a id="2494" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2497" href="foundation.idempotent-maps.html#2460" class="Bound">l</a>
<a id="2499" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="2513" href="foundation.idempotent-maps.html#2513" class="Bound">f</a> <a id="2515" class="Symbol">=</a> <a id="2517" href="foundation.idempotent-maps.html#2513" class="Bound">f</a> <a id="2519" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2521" href="foundation.idempotent-maps.html#2513" class="Bound">f</a> <a id="2523" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="2525" href="foundation.idempotent-maps.html#2513" class="Bound">f</a>
</pre>
### The type of idempotent maps on a type

<pre class="Agda"><a id="idempotent-map"></a><a id="2583" href="foundation.idempotent-maps.html#2583" class="Function">idempotent-map</a> <a id="2598" class="Symbol">:</a> <a id="2600" class="Symbol">{</a><a id="2601" href="foundation.idempotent-maps.html#2601" class="Bound">l</a> <a id="2603" class="Symbol">:</a> <a id="2605" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2610" class="Symbol">}</a> <a id="2612" class="Symbol">(</a><a id="2613" href="foundation.idempotent-maps.html#2613" class="Bound">A</a> <a id="2615" class="Symbol">:</a> <a id="2617" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2620" href="foundation.idempotent-maps.html#2601" class="Bound">l</a><a id="2621" class="Symbol">)</a> <a id="2623" class="Symbol">→</a> <a id="2625" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2628" href="foundation.idempotent-maps.html#2601" class="Bound">l</a>
<a id="2630" href="foundation.idempotent-maps.html#2583" class="Function">idempotent-map</a> <a id="2645" href="foundation.idempotent-maps.html#2645" class="Bound">A</a> <a id="2647" class="Symbol">=</a> <a id="2649" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2651" class="Symbol">(</a><a id="2652" href="foundation.idempotent-maps.html#2645" class="Bound">A</a> <a id="2654" class="Symbol">→</a> <a id="2656" href="foundation.idempotent-maps.html#2645" class="Bound">A</a><a id="2657" class="Symbol">)</a> <a id="2659" class="Symbol">(</a><a id="2660" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a><a id="2673" class="Symbol">)</a>

<a id="2676" class="Keyword">module</a> <a id="2683" href="foundation.idempotent-maps.html#2683" class="Module">_</a>
  <a id="2687" class="Symbol">{</a><a id="2688" href="foundation.idempotent-maps.html#2688" class="Bound">l</a> <a id="2690" class="Symbol">:</a> <a id="2692" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2697" class="Symbol">}</a> <a id="2699" class="Symbol">{</a><a id="2700" href="foundation.idempotent-maps.html#2700" class="Bound">A</a> <a id="2702" class="Symbol">:</a> <a id="2704" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2707" href="foundation.idempotent-maps.html#2688" class="Bound">l</a><a id="2708" class="Symbol">}</a> <a id="2710" class="Symbol">(</a><a id="2711" href="foundation.idempotent-maps.html#2711" class="Bound">f</a> <a id="2713" class="Symbol">:</a> <a id="2715" href="foundation.idempotent-maps.html#2583" class="Function">idempotent-map</a> <a id="2730" href="foundation.idempotent-maps.html#2700" class="Bound">A</a><a id="2731" class="Symbol">)</a>
  <a id="2735" class="Keyword">where</a>

  <a id="2744" href="foundation.idempotent-maps.html#2744" class="Function">map-idempotent-map</a> <a id="2763" class="Symbol">:</a> <a id="2765" href="foundation.idempotent-maps.html#2700" class="Bound">A</a> <a id="2767" class="Symbol">→</a> <a id="2769" href="foundation.idempotent-maps.html#2700" class="Bound">A</a>
  <a id="2773" href="foundation.idempotent-maps.html#2744" class="Function">map-idempotent-map</a> <a id="2792" class="Symbol">=</a> <a id="2794" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2798" href="foundation.idempotent-maps.html#2711" class="Bound">f</a>

  <a id="2803" href="foundation.idempotent-maps.html#2803" class="Function">is-idempotent-idempotent-map</a> <a id="2832" class="Symbol">:</a>
    <a id="2838" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="2852" href="foundation.idempotent-maps.html#2744" class="Function">map-idempotent-map</a>
  <a id="2873" href="foundation.idempotent-maps.html#2803" class="Function">is-idempotent-idempotent-map</a> <a id="2902" class="Symbol">=</a> <a id="2904" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2908" href="foundation.idempotent-maps.html#2711" class="Bound">f</a>
</pre>
## Properties

### Being an idempotent operation on a set is a property

<pre class="Agda"><a id="2996" class="Keyword">module</a> <a id="3003" href="foundation.idempotent-maps.html#3003" class="Module">_</a>
  <a id="3007" class="Symbol">{</a><a id="3008" href="foundation.idempotent-maps.html#3008" class="Bound">l</a> <a id="3010" class="Symbol">:</a> <a id="3012" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3017" class="Symbol">}</a> <a id="3019" class="Symbol">{</a><a id="3020" href="foundation.idempotent-maps.html#3020" class="Bound">A</a> <a id="3022" class="Symbol">:</a> <a id="3024" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3027" href="foundation.idempotent-maps.html#3008" class="Bound">l</a><a id="3028" class="Symbol">}</a> <a id="3030" class="Symbol">(</a><a id="3031" href="foundation.idempotent-maps.html#3031" class="Bound">is-set-A</a> <a id="3040" class="Symbol">:</a> <a id="3042" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="3049" href="foundation.idempotent-maps.html#3020" class="Bound">A</a><a id="3050" class="Symbol">)</a> <a id="3052" class="Symbol">(</a><a id="3053" href="foundation.idempotent-maps.html#3053" class="Bound">f</a> <a id="3055" class="Symbol">:</a> <a id="3057" href="foundation.idempotent-maps.html#3020" class="Bound">A</a> <a id="3059" class="Symbol">→</a> <a id="3061" href="foundation.idempotent-maps.html#3020" class="Bound">A</a><a id="3062" class="Symbol">)</a>
  <a id="3066" class="Keyword">where</a>

  <a id="3075" href="foundation.idempotent-maps.html#3075" class="Function">is-prop-is-idempotent-is-set</a> <a id="3104" class="Symbol">:</a> <a id="3106" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3114" class="Symbol">(</a><a id="3115" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="3129" href="foundation.idempotent-maps.html#3053" class="Bound">f</a><a id="3130" class="Symbol">)</a>
  <a id="3134" href="foundation.idempotent-maps.html#3075" class="Function">is-prop-is-idempotent-is-set</a> <a id="3163" class="Symbol">=</a>
    <a id="3169" href="foundation-core.propositions.html#6443" class="Function">is-prop-Π</a> <a id="3179" class="Symbol">(λ</a> <a id="3182" href="foundation.idempotent-maps.html#3182" class="Bound">x</a> <a id="3184" class="Symbol">→</a> <a id="3186" href="foundation.idempotent-maps.html#3031" class="Bound">is-set-A</a> <a id="3195" class="Symbol">(</a><a id="3196" href="foundation.idempotent-maps.html#3053" class="Bound">f</a> <a id="3198" class="Symbol">(</a><a id="3199" href="foundation.idempotent-maps.html#3053" class="Bound">f</a> <a id="3201" href="foundation.idempotent-maps.html#3182" class="Bound">x</a><a id="3202" class="Symbol">))</a> <a id="3205" class="Symbol">(</a><a id="3206" href="foundation.idempotent-maps.html#3053" class="Bound">f</a> <a id="3208" href="foundation.idempotent-maps.html#3182" class="Bound">x</a><a id="3209" class="Symbol">))</a>

  <a id="3215" href="foundation.idempotent-maps.html#3215" class="Function">is-idempotent-is-set-Prop</a> <a id="3241" class="Symbol">:</a> <a id="3243" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3248" href="foundation.idempotent-maps.html#3008" class="Bound">l</a>
  <a id="3252" href="foundation.idempotent-maps.html#3215" class="Function">is-idempotent-is-set-Prop</a> <a id="3278" class="Symbol">=</a>
    <a id="3284" class="Symbol">(</a> <a id="3286" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="3300" href="foundation.idempotent-maps.html#3053" class="Bound">f</a> <a id="3302" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3304" href="foundation.idempotent-maps.html#3075" class="Function">is-prop-is-idempotent-is-set</a><a id="3332" class="Symbol">)</a>

<a id="3335" class="Keyword">module</a> <a id="3342" href="foundation.idempotent-maps.html#3342" class="Module">_</a>
  <a id="3346" class="Symbol">{</a><a id="3347" href="foundation.idempotent-maps.html#3347" class="Bound">l</a> <a id="3349" class="Symbol">:</a> <a id="3351" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3356" class="Symbol">}</a> <a id="3358" class="Symbol">(</a><a id="3359" href="foundation.idempotent-maps.html#3359" class="Bound">A</a> <a id="3361" class="Symbol">:</a> <a id="3363" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="3367" href="foundation.idempotent-maps.html#3347" class="Bound">l</a><a id="3368" class="Symbol">)</a> <a id="3370" class="Symbol">(</a><a id="3371" href="foundation.idempotent-maps.html#3371" class="Bound">f</a> <a id="3373" class="Symbol">:</a> <a id="3375" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="3384" href="foundation.idempotent-maps.html#3359" class="Bound">A</a> <a id="3386" class="Symbol">→</a> <a id="3388" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="3397" href="foundation.idempotent-maps.html#3359" class="Bound">A</a><a id="3398" class="Symbol">)</a>
  <a id="3402" class="Keyword">where</a>

  <a id="3411" href="foundation.idempotent-maps.html#3411" class="Function">is-prop-is-idempotent-Set</a> <a id="3437" class="Symbol">:</a> <a id="3439" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3447" class="Symbol">(</a><a id="3448" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="3462" href="foundation.idempotent-maps.html#3371" class="Bound">f</a><a id="3463" class="Symbol">)</a>
  <a id="3467" href="foundation.idempotent-maps.html#3411" class="Function">is-prop-is-idempotent-Set</a> <a id="3493" class="Symbol">=</a>
    <a id="3499" href="foundation.idempotent-maps.html#3075" class="Function">is-prop-is-idempotent-is-set</a> <a id="3528" class="Symbol">(</a><a id="3529" href="foundation-core.sets.html#1076" class="Function">is-set-type-Set</a> <a id="3545" href="foundation.idempotent-maps.html#3359" class="Bound">A</a><a id="3546" class="Symbol">)</a> <a id="3548" href="foundation.idempotent-maps.html#3371" class="Bound">f</a>

  <a id="3553" href="foundation.idempotent-maps.html#3553" class="Function">is-idempotent-prop-Set</a> <a id="3576" class="Symbol">:</a> <a id="3578" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3583" href="foundation.idempotent-maps.html#3347" class="Bound">l</a>
  <a id="3587" href="foundation.idempotent-maps.html#3553" class="Function">is-idempotent-prop-Set</a> <a id="3610" class="Symbol">=</a>
    <a id="3616" class="Symbol">(</a> <a id="3618" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="3632" href="foundation.idempotent-maps.html#3371" class="Bound">f</a> <a id="3634" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3636" href="foundation.idempotent-maps.html#3411" class="Function">is-prop-is-idempotent-Set</a><a id="3661" class="Symbol">)</a>
</pre>
### If `i` and `r` is an inclusion-retraction pair, then `i ∘ r` is idempotent

<pre class="Agda"><a id="3756" class="Keyword">module</a> <a id="3763" href="foundation.idempotent-maps.html#3763" class="Module">_</a>
  <a id="3767" class="Symbol">{</a><a id="3768" href="foundation.idempotent-maps.html#3768" class="Bound">l1</a> <a id="3771" href="foundation.idempotent-maps.html#3771" class="Bound">l2</a> <a id="3774" class="Symbol">:</a> <a id="3776" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3781" class="Symbol">}</a> <a id="3783" class="Symbol">{</a><a id="3784" href="foundation.idempotent-maps.html#3784" class="Bound">A</a> <a id="3786" class="Symbol">:</a> <a id="3788" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3791" href="foundation.idempotent-maps.html#3768" class="Bound">l1</a><a id="3793" class="Symbol">}</a> <a id="3795" class="Symbol">{</a><a id="3796" href="foundation.idempotent-maps.html#3796" class="Bound">B</a> <a id="3798" class="Symbol">:</a> <a id="3800" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3803" href="foundation.idempotent-maps.html#3771" class="Bound">l2</a><a id="3805" class="Symbol">}</a>
  <a id="3809" class="Symbol">(</a><a id="3810" href="foundation.idempotent-maps.html#3810" class="Bound">i</a> <a id="3812" class="Symbol">:</a> <a id="3814" href="foundation.idempotent-maps.html#3796" class="Bound">B</a> <a id="3816" class="Symbol">→</a> <a id="3818" href="foundation.idempotent-maps.html#3784" class="Bound">A</a><a id="3819" class="Symbol">)</a> <a id="3821" class="Symbol">(</a><a id="3822" href="foundation.idempotent-maps.html#3822" class="Bound">r</a> <a id="3824" class="Symbol">:</a> <a id="3826" href="foundation.idempotent-maps.html#3784" class="Bound">A</a> <a id="3828" class="Symbol">→</a> <a id="3830" href="foundation.idempotent-maps.html#3796" class="Bound">B</a><a id="3831" class="Symbol">)</a> <a id="3833" class="Symbol">(</a><a id="3834" href="foundation.idempotent-maps.html#3834" class="Bound">H</a> <a id="3836" class="Symbol">:</a> <a id="3838" href="foundation-core.retractions.html#790" class="Function">is-retraction</a> <a id="3852" href="foundation.idempotent-maps.html#3810" class="Bound">i</a> <a id="3854" href="foundation.idempotent-maps.html#3822" class="Bound">r</a><a id="3855" class="Symbol">)</a>
  <a id="3859" class="Keyword">where</a>

  <a id="3868" href="foundation.idempotent-maps.html#3868" class="Function">is-idempotent-inclusion-retraction</a> <a id="3903" class="Symbol">:</a> <a id="3905" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="3919" class="Symbol">(</a><a id="3920" href="foundation.idempotent-maps.html#3810" class="Bound">i</a> <a id="3922" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3924" href="foundation.idempotent-maps.html#3822" class="Bound">r</a><a id="3925" class="Symbol">)</a>
  <a id="3929" href="foundation.idempotent-maps.html#3868" class="Function">is-idempotent-inclusion-retraction</a> <a id="3964" class="Symbol">=</a> <a id="3966" href="foundation.idempotent-maps.html#3810" class="Bound">i</a> <a id="3968" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a> <a id="3971" href="foundation.idempotent-maps.html#3834" class="Bound">H</a> <a id="3973" href="foundation.whiskering-homotopies-composition.html#2725" class="Function Operator">·r</a> <a id="3976" href="foundation.idempotent-maps.html#3822" class="Bound">r</a>
</pre>
### Idempotence is preserved by homotopies

If a map `g` is homotopic to an idempotent map `f`, then `g` is also idempotent.

<pre class="Agda"><a id="4117" class="Keyword">module</a> <a id="4124" href="foundation.idempotent-maps.html#4124" class="Module">_</a>
  <a id="4128" class="Symbol">{</a><a id="4129" href="foundation.idempotent-maps.html#4129" class="Bound">l</a> <a id="4131" class="Symbol">:</a> <a id="4133" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4138" class="Symbol">}</a> <a id="4140" class="Symbol">{</a><a id="4141" href="foundation.idempotent-maps.html#4141" class="Bound">A</a> <a id="4143" class="Symbol">:</a> <a id="4145" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4148" href="foundation.idempotent-maps.html#4129" class="Bound">l</a><a id="4149" class="Symbol">}</a> <a id="4151" class="Symbol">{</a><a id="4152" href="foundation.idempotent-maps.html#4152" class="Bound">f</a> <a id="4154" href="foundation.idempotent-maps.html#4154" class="Bound">g</a> <a id="4156" class="Symbol">:</a> <a id="4158" href="foundation.idempotent-maps.html#4141" class="Bound">A</a> <a id="4160" class="Symbol">→</a> <a id="4162" href="foundation.idempotent-maps.html#4141" class="Bound">A</a><a id="4163" class="Symbol">}</a> <a id="4165" class="Symbol">(</a><a id="4166" href="foundation.idempotent-maps.html#4166" class="Bound">F</a> <a id="4168" class="Symbol">:</a> <a id="4170" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="4184" href="foundation.idempotent-maps.html#4152" class="Bound">f</a><a id="4185" class="Symbol">)</a>
  <a id="4189" class="Keyword">where</a>

  <a id="4198" href="foundation.idempotent-maps.html#4198" class="Function">is-idempotent-htpy</a> <a id="4217" class="Symbol">:</a> <a id="4219" href="foundation.idempotent-maps.html#4154" class="Bound">g</a> <a id="4221" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="4223" href="foundation.idempotent-maps.html#4152" class="Bound">f</a> <a id="4225" class="Symbol">→</a> <a id="4227" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="4241" href="foundation.idempotent-maps.html#4154" class="Bound">g</a>
  <a id="4245" href="foundation.idempotent-maps.html#4198" class="Function">is-idempotent-htpy</a> <a id="4264" href="foundation.idempotent-maps.html#4264" class="Bound">H</a> <a id="4266" class="Symbol">=</a>
    <a id="4272" href="foundation.homotopy-algebra.html#861" class="Function">horizontal-concat-htpy</a> <a id="4295" href="foundation.idempotent-maps.html#4264" class="Bound">H</a> <a id="4297" href="foundation.idempotent-maps.html#4264" class="Bound">H</a> <a id="4299" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="4302" href="foundation.idempotent-maps.html#4166" class="Bound">F</a> <a id="4304" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="4307" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="4316" href="foundation.idempotent-maps.html#4264" class="Bound">H</a>

  <a id="4321" href="foundation.idempotent-maps.html#4321" class="Function">is-idempotent-inv-htpy</a> <a id="4344" class="Symbol">:</a> <a id="4346" href="foundation.idempotent-maps.html#4152" class="Bound">f</a> <a id="4348" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="4350" href="foundation.idempotent-maps.html#4154" class="Bound">g</a> <a id="4352" class="Symbol">→</a> <a id="4354" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="4368" href="foundation.idempotent-maps.html#4154" class="Bound">g</a>
  <a id="4372" href="foundation.idempotent-maps.html#4321" class="Function">is-idempotent-inv-htpy</a> <a id="4395" href="foundation.idempotent-maps.html#4395" class="Bound">H</a> <a id="4397" class="Symbol">=</a>
    <a id="4403" href="foundation.homotopy-algebra.html#861" class="Function">horizontal-concat-htpy</a> <a id="4426" class="Symbol">(</a><a id="4427" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="4436" href="foundation.idempotent-maps.html#4395" class="Bound">H</a><a id="4437" class="Symbol">)</a> <a id="4439" class="Symbol">(</a><a id="4440" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a> <a id="4449" href="foundation.idempotent-maps.html#4395" class="Bound">H</a><a id="4450" class="Symbol">)</a> <a id="4452" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="4455" href="foundation.idempotent-maps.html#4166" class="Bound">F</a> <a id="4457" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="4460" href="foundation.idempotent-maps.html#4395" class="Bound">H</a>
</pre>
## See also

- [Quasicoherently idempotent maps](foundation.quasicoherently-idempotent-maps.md)
- [Split idempotent maps](foundation.split-idempotent-maps.md)

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
