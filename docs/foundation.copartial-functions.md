# Copartial functions

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="foundation.copartial-functions.html" class="Module">foundation.copartial-functions</a> <a id="70" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="126" class="Keyword">open</a> <a id="131" class="Keyword">import</a> <a id="138" href="foundation.copartial-elements.html" class="Module">foundation.copartial-elements</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.partial-functions.html" class="Module">foundation.partial-functions</a>
<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A {{#concept "copartial function" Agda=copartial-function}} from `A` to `B` is a
map from `A` into the type of
[copartial elements](foundation.copartial-elements.md) of `B`. I.e., a copartial
function is a map

```text
  A → Σ (Q : Prop), B * Q
```

where `- * Q` is the
[closed modality](orthogonal-factorization-systems.closed-modalities.md), which
is defined by the [join operation](synthetic-homotopy-theory.joins-of-types.md).

Evaluation of a copartial function `f` at `a : A` is said to be
{{#concept "denied" Disambiguation="copartial function" Agda=is-denied-copartial-function}}
if evaluation of the copartial element `f a` of `B` is denied.

A copartial function is [equivalently](foundation-core.equivalences.md)
described as a [morphism of arrows](foundation.morphisms-arrows.md)

```text
     A     B   1
     |     |   |
  id |  ⇒  | □ | T
     ∨     ∨   ∨
     A     1  Prop
```

where `□` is the
[pushout-product](synthetic-homotopy-theory.pushout-products.md). Indeed, the
domain of the pushout-product `B □ T` is the type of copartial elements of `B`.

{{#concept "Composition" Disambiguation="copartial functions"}} of copartial
functions can be defined by

```text
                     copartial-element (copartial-element C)
                            ∧                 |
   map-copartial-element g /                  | join-copartial-element
                          /                   ∨
  A ----> copartial-element B       copartial-element C
      f
```

In this diagram, the map going up is defined by functoriality of the operation

```text
  X ↦ Σ (Q : Prop), X * Q
```

The map going down is defined by the join operation on copartial elements, i.e.,
the pushout-product algebra structure of the map `T : 1 → Prop`. The main idea
behind composition of copartial functions is that a composite of copartial
function is denied on the union of the subtypes where each factor is denied.
Indeed, if `f` is denied at `a` or `map-copartial-element g` is denied at the
copartial element `f a` of `B`, then the composite of copartial functions
`g ∘ f` should be denied at `a`.

**Note:** The topic of copartial functions was not known to us in the
literature, and our formalization on this topic should be considered
experimental.

## Definitions

### Copartial dependent functions

<pre class="Agda"><a id="copartial-dependent-function"></a><a id="2623" href="foundation.copartial-functions.html#2623" class="Function">copartial-dependent-function</a> <a id="2652" class="Symbol">:</a>
  <a id="2656" class="Symbol">{</a><a id="2657" href="foundation.copartial-functions.html#2657" class="Bound">l1</a> <a id="2660" href="foundation.copartial-functions.html#2660" class="Bound">l2</a> <a id="2663" class="Symbol">:</a> <a id="2665" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2670" class="Symbol">}</a> <a id="2672" class="Symbol">(</a><a id="2673" href="foundation.copartial-functions.html#2673" class="Bound">l3</a> <a id="2676" class="Symbol">:</a> <a id="2678" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2683" class="Symbol">)</a> <a id="2685" class="Symbol">(</a><a id="2686" href="foundation.copartial-functions.html#2686" class="Bound">A</a> <a id="2688" class="Symbol">:</a> <a id="2690" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2693" href="foundation.copartial-functions.html#2657" class="Bound">l1</a><a id="2695" class="Symbol">)</a> <a id="2697" class="Symbol">→</a> <a id="2699" class="Symbol">(</a><a id="2700" href="foundation.copartial-functions.html#2686" class="Bound">A</a> <a id="2702" class="Symbol">→</a> <a id="2704" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2707" href="foundation.copartial-functions.html#2660" class="Bound">l2</a><a id="2709" class="Symbol">)</a> <a id="2711" class="Symbol">→</a>
  <a id="2715" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2718" class="Symbol">(</a><a id="2719" href="foundation.copartial-functions.html#2657" class="Bound">l1</a> <a id="2722" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2724" href="foundation.copartial-functions.html#2660" class="Bound">l2</a> <a id="2727" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2729" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2734" href="foundation.copartial-functions.html#2673" class="Bound">l3</a><a id="2736" class="Symbol">)</a>
<a id="2738" href="foundation.copartial-functions.html#2623" class="Function">copartial-dependent-function</a> <a id="2767" href="foundation.copartial-functions.html#2767" class="Bound">l3</a> <a id="2770" href="foundation.copartial-functions.html#2770" class="Bound">A</a> <a id="2772" href="foundation.copartial-functions.html#2772" class="Bound">B</a> <a id="2774" class="Symbol">=</a> <a id="2776" class="Symbol">(</a><a id="2777" href="foundation.copartial-functions.html#2777" class="Bound">x</a> <a id="2779" class="Symbol">:</a> <a id="2781" href="foundation.copartial-functions.html#2770" class="Bound">A</a><a id="2782" class="Symbol">)</a> <a id="2784" class="Symbol">→</a> <a id="2786" href="foundation.copartial-elements.html#3625" class="Function">copartial-element</a> <a id="2804" href="foundation.copartial-functions.html#2767" class="Bound">l3</a> <a id="2807" class="Symbol">(</a><a id="2808" href="foundation.copartial-functions.html#2772" class="Bound">B</a> <a id="2810" href="foundation.copartial-functions.html#2777" class="Bound">x</a><a id="2811" class="Symbol">)</a>
</pre>
### Copartial functions

<pre class="Agda"><a id="copartial-function"></a><a id="2851" href="foundation.copartial-functions.html#2851" class="Function">copartial-function</a> <a id="2870" class="Symbol">:</a>
  <a id="2874" class="Symbol">{</a><a id="2875" href="foundation.copartial-functions.html#2875" class="Bound">l1</a> <a id="2878" href="foundation.copartial-functions.html#2878" class="Bound">l2</a> <a id="2881" class="Symbol">:</a> <a id="2883" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2888" class="Symbol">}</a> <a id="2890" class="Symbol">(</a><a id="2891" href="foundation.copartial-functions.html#2891" class="Bound">l3</a> <a id="2894" class="Symbol">:</a> <a id="2896" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2901" class="Symbol">)</a> <a id="2903" class="Symbol">→</a> <a id="2905" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2908" href="foundation.copartial-functions.html#2875" class="Bound">l1</a> <a id="2911" class="Symbol">→</a> <a id="2913" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2916" href="foundation.copartial-functions.html#2878" class="Bound">l2</a> <a id="2919" class="Symbol">→</a> <a id="2921" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2924" class="Symbol">(</a><a id="2925" href="foundation.copartial-functions.html#2875" class="Bound">l1</a> <a id="2928" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2930" href="foundation.copartial-functions.html#2878" class="Bound">l2</a> <a id="2933" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2935" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2940" href="foundation.copartial-functions.html#2891" class="Bound">l3</a><a id="2942" class="Symbol">)</a>
<a id="2944" href="foundation.copartial-functions.html#2851" class="Function">copartial-function</a> <a id="2963" href="foundation.copartial-functions.html#2963" class="Bound">l3</a> <a id="2966" href="foundation.copartial-functions.html#2966" class="Bound">A</a> <a id="2968" href="foundation.copartial-functions.html#2968" class="Bound">B</a> <a id="2970" class="Symbol">=</a> <a id="2972" href="foundation.copartial-functions.html#2623" class="Function">copartial-dependent-function</a> <a id="3001" href="foundation.copartial-functions.html#2963" class="Bound">l3</a> <a id="3004" href="foundation.copartial-functions.html#2966" class="Bound">A</a> <a id="3006" class="Symbol">(λ</a> <a id="3009" href="foundation.copartial-functions.html#3009" class="Bound">_</a> <a id="3011" class="Symbol">→</a> <a id="3013" href="foundation.copartial-functions.html#2968" class="Bound">B</a><a id="3014" class="Symbol">)</a>
</pre>
### Denied values of copartial dependent functions

<pre class="Agda"><a id="3081" class="Keyword">module</a> <a id="3088" href="foundation.copartial-functions.html#3088" class="Module">_</a>
  <a id="3092" class="Symbol">{</a><a id="3093" href="foundation.copartial-functions.html#3093" class="Bound">l1</a> <a id="3096" href="foundation.copartial-functions.html#3096" class="Bound">l2</a> <a id="3099" href="foundation.copartial-functions.html#3099" class="Bound">l3</a> <a id="3102" class="Symbol">:</a> <a id="3104" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3109" class="Symbol">}</a> <a id="3111" class="Symbol">{</a><a id="3112" href="foundation.copartial-functions.html#3112" class="Bound">A</a> <a id="3114" class="Symbol">:</a> <a id="3116" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3119" href="foundation.copartial-functions.html#3093" class="Bound">l1</a><a id="3121" class="Symbol">}</a> <a id="3123" class="Symbol">{</a><a id="3124" href="foundation.copartial-functions.html#3124" class="Bound">B</a> <a id="3126" class="Symbol">:</a> <a id="3128" href="foundation.copartial-functions.html#3112" class="Bound">A</a> <a id="3130" class="Symbol">→</a> <a id="3132" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3135" href="foundation.copartial-functions.html#3096" class="Bound">l2</a><a id="3137" class="Symbol">}</a>
  <a id="3141" class="Symbol">(</a><a id="3142" href="foundation.copartial-functions.html#3142" class="Bound">f</a> <a id="3144" class="Symbol">:</a> <a id="3146" href="foundation.copartial-functions.html#2623" class="Function">copartial-dependent-function</a> <a id="3175" href="foundation.copartial-functions.html#3099" class="Bound">l3</a> <a id="3178" href="foundation.copartial-functions.html#3112" class="Bound">A</a> <a id="3180" href="foundation.copartial-functions.html#3124" class="Bound">B</a><a id="3181" class="Symbol">)</a> <a id="3183" class="Symbol">(</a><a id="3184" href="foundation.copartial-functions.html#3184" class="Bound">a</a> <a id="3186" class="Symbol">:</a> <a id="3188" href="foundation.copartial-functions.html#3112" class="Bound">A</a><a id="3189" class="Symbol">)</a>
  <a id="3193" class="Keyword">where</a>

  <a id="3202" href="foundation.copartial-functions.html#3202" class="Function">is-denied-prop-copartial-dependent-function</a> <a id="3246" class="Symbol">:</a> <a id="3248" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3253" href="foundation.copartial-functions.html#3099" class="Bound">l3</a>
  <a id="3258" href="foundation.copartial-functions.html#3202" class="Function">is-denied-prop-copartial-dependent-function</a> <a id="3302" class="Symbol">=</a>
    <a id="3308" href="foundation.copartial-elements.html#3855" class="Function">is-denied-prop-copartial-element</a> <a id="3341" class="Symbol">(</a><a id="3342" href="foundation.copartial-functions.html#3142" class="Bound">f</a> <a id="3344" href="foundation.copartial-functions.html#3184" class="Bound">a</a><a id="3345" class="Symbol">)</a>

  <a id="3350" href="foundation.copartial-functions.html#3350" class="Function">is-denied-copartial-dependent-function</a> <a id="3389" class="Symbol">:</a> <a id="3391" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3394" href="foundation.copartial-functions.html#3099" class="Bound">l3</a>
  <a id="3399" href="foundation.copartial-functions.html#3350" class="Function">is-denied-copartial-dependent-function</a> <a id="3438" class="Symbol">=</a> <a id="3440" href="foundation.copartial-elements.html#3944" class="Function">is-denied-copartial-element</a> <a id="3468" class="Symbol">(</a><a id="3469" href="foundation.copartial-functions.html#3142" class="Bound">f</a> <a id="3471" href="foundation.copartial-functions.html#3184" class="Bound">a</a><a id="3472" class="Symbol">)</a>
</pre>
### Denied values of copartial functions

<pre class="Agda"><a id="3529" class="Keyword">module</a> <a id="3536" href="foundation.copartial-functions.html#3536" class="Module">_</a>
  <a id="3540" class="Symbol">{</a><a id="3541" href="foundation.copartial-functions.html#3541" class="Bound">l1</a> <a id="3544" href="foundation.copartial-functions.html#3544" class="Bound">l2</a> <a id="3547" href="foundation.copartial-functions.html#3547" class="Bound">l3</a> <a id="3550" class="Symbol">:</a> <a id="3552" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3557" class="Symbol">}</a> <a id="3559" class="Symbol">{</a><a id="3560" href="foundation.copartial-functions.html#3560" class="Bound">A</a> <a id="3562" class="Symbol">:</a> <a id="3564" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3567" href="foundation.copartial-functions.html#3541" class="Bound">l1</a><a id="3569" class="Symbol">}</a> <a id="3571" class="Symbol">{</a><a id="3572" href="foundation.copartial-functions.html#3572" class="Bound">B</a> <a id="3574" class="Symbol">:</a> <a id="3576" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3579" href="foundation.copartial-functions.html#3544" class="Bound">l2</a><a id="3581" class="Symbol">}</a> <a id="3583" class="Symbol">(</a><a id="3584" href="foundation.copartial-functions.html#3584" class="Bound">f</a> <a id="3586" class="Symbol">:</a> <a id="3588" href="foundation.copartial-functions.html#2851" class="Function">copartial-function</a> <a id="3607" href="foundation.copartial-functions.html#3547" class="Bound">l3</a> <a id="3610" href="foundation.copartial-functions.html#3560" class="Bound">A</a> <a id="3612" href="foundation.copartial-functions.html#3572" class="Bound">B</a><a id="3613" class="Symbol">)</a>
  <a id="3617" class="Symbol">(</a><a id="3618" href="foundation.copartial-functions.html#3618" class="Bound">a</a> <a id="3620" class="Symbol">:</a> <a id="3622" href="foundation.copartial-functions.html#3560" class="Bound">A</a><a id="3623" class="Symbol">)</a>
  <a id="3627" class="Keyword">where</a>

  <a id="3636" href="foundation.copartial-functions.html#3636" class="Function">is-denied-prop-copartial-function</a> <a id="3670" class="Symbol">:</a> <a id="3672" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3677" href="foundation.copartial-functions.html#3547" class="Bound">l3</a>
  <a id="3682" href="foundation.copartial-functions.html#3636" class="Function">is-denied-prop-copartial-function</a> <a id="3716" class="Symbol">=</a>
    <a id="3722" href="foundation.copartial-functions.html#3202" class="Function">is-denied-prop-copartial-dependent-function</a> <a id="3766" href="foundation.copartial-functions.html#3584" class="Bound">f</a> <a id="3768" href="foundation.copartial-functions.html#3618" class="Bound">a</a>

  <a id="3773" href="foundation.copartial-functions.html#3773" class="Function">is-denied-copartial-function</a> <a id="3802" class="Symbol">:</a> <a id="3804" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3807" href="foundation.copartial-functions.html#3547" class="Bound">l3</a>
  <a id="3812" href="foundation.copartial-functions.html#3773" class="Function">is-denied-copartial-function</a> <a id="3841" class="Symbol">=</a>
    <a id="3847" href="foundation.copartial-functions.html#3350" class="Function">is-denied-copartial-dependent-function</a> <a id="3886" href="foundation.copartial-functions.html#3584" class="Bound">f</a> <a id="3888" href="foundation.copartial-functions.html#3618" class="Bound">a</a>
</pre>
### Copartial dependent functions obtained from dependent functions

<pre class="Agda"><a id="3972" class="Keyword">module</a> <a id="3979" href="foundation.copartial-functions.html#3979" class="Module">_</a>
  <a id="3983" class="Symbol">{</a><a id="3984" href="foundation.copartial-functions.html#3984" class="Bound">l1</a> <a id="3987" href="foundation.copartial-functions.html#3987" class="Bound">l2</a> <a id="3990" class="Symbol">:</a> <a id="3992" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3997" class="Symbol">}</a> <a id="3999" class="Symbol">{</a><a id="4000" href="foundation.copartial-functions.html#4000" class="Bound">A</a> <a id="4002" class="Symbol">:</a> <a id="4004" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4007" href="foundation.copartial-functions.html#3984" class="Bound">l1</a><a id="4009" class="Symbol">}</a> <a id="4011" class="Symbol">{</a><a id="4012" href="foundation.copartial-functions.html#4012" class="Bound">B</a> <a id="4014" class="Symbol">:</a> <a id="4016" href="foundation.copartial-functions.html#4000" class="Bound">A</a> <a id="4018" class="Symbol">→</a> <a id="4020" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4023" href="foundation.copartial-functions.html#3987" class="Bound">l2</a><a id="4025" class="Symbol">}</a> <a id="4027" class="Symbol">(</a><a id="4028" href="foundation.copartial-functions.html#4028" class="Bound">f</a> <a id="4030" class="Symbol">:</a> <a id="4032" class="Symbol">(</a><a id="4033" href="foundation.copartial-functions.html#4033" class="Bound">x</a> <a id="4035" class="Symbol">:</a> <a id="4037" href="foundation.copartial-functions.html#4000" class="Bound">A</a><a id="4038" class="Symbol">)</a> <a id="4040" class="Symbol">→</a> <a id="4042" href="foundation.copartial-functions.html#4012" class="Bound">B</a> <a id="4044" href="foundation.copartial-functions.html#4033" class="Bound">x</a><a id="4045" class="Symbol">)</a>
  <a id="4049" class="Keyword">where</a>

  <a id="4058" href="foundation.copartial-functions.html#4058" class="Function">copartial-dependent-function-dependent-function</a> <a id="4106" class="Symbol">:</a>
    <a id="4112" href="foundation.copartial-functions.html#2623" class="Function">copartial-dependent-function</a> <a id="4141" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="4147" href="foundation.copartial-functions.html#4000" class="Bound">A</a> <a id="4149" href="foundation.copartial-functions.html#4012" class="Bound">B</a>
  <a id="4153" href="foundation.copartial-functions.html#4058" class="Function">copartial-dependent-function-dependent-function</a> <a id="4201" href="foundation.copartial-functions.html#4201" class="Bound">a</a> <a id="4203" class="Symbol">=</a>
    <a id="4209" href="foundation.copartial-elements.html#4499" class="Function">unit-copartial-element</a> <a id="4232" class="Symbol">(</a><a id="4233" href="foundation.copartial-functions.html#4028" class="Bound">f</a> <a id="4235" href="foundation.copartial-functions.html#4201" class="Bound">a</a><a id="4236" class="Symbol">)</a>
</pre>
### Copartial functions obtained from functions

<pre class="Agda"><a id="4300" class="Keyword">module</a> <a id="4307" href="foundation.copartial-functions.html#4307" class="Module">_</a>
  <a id="4311" class="Symbol">{</a><a id="4312" href="foundation.copartial-functions.html#4312" class="Bound">l1</a> <a id="4315" href="foundation.copartial-functions.html#4315" class="Bound">l2</a> <a id="4318" class="Symbol">:</a> <a id="4320" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4325" class="Symbol">}</a> <a id="4327" class="Symbol">{</a><a id="4328" href="foundation.copartial-functions.html#4328" class="Bound">A</a> <a id="4330" class="Symbol">:</a> <a id="4332" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4335" href="foundation.copartial-functions.html#4312" class="Bound">l1</a><a id="4337" class="Symbol">}</a> <a id="4339" class="Symbol">{</a><a id="4340" href="foundation.copartial-functions.html#4340" class="Bound">B</a> <a id="4342" class="Symbol">:</a> <a id="4344" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4347" href="foundation.copartial-functions.html#4315" class="Bound">l2</a><a id="4349" class="Symbol">}</a> <a id="4351" class="Symbol">(</a><a id="4352" href="foundation.copartial-functions.html#4352" class="Bound">f</a> <a id="4354" class="Symbol">:</a> <a id="4356" href="foundation.copartial-functions.html#4328" class="Bound">A</a> <a id="4358" class="Symbol">→</a> <a id="4360" href="foundation.copartial-functions.html#4340" class="Bound">B</a><a id="4361" class="Symbol">)</a>
  <a id="4365" class="Keyword">where</a>

  <a id="4374" href="foundation.copartial-functions.html#4374" class="Function">copartial-function-function</a> <a id="4402" class="Symbol">:</a> <a id="4404" href="foundation.copartial-functions.html#2851" class="Function">copartial-function</a> <a id="4423" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="4429" href="foundation.copartial-functions.html#4328" class="Bound">A</a> <a id="4431" href="foundation.copartial-functions.html#4340" class="Bound">B</a>
  <a id="4435" href="foundation.copartial-functions.html#4374" class="Function">copartial-function-function</a> <a id="4463" class="Symbol">=</a>
    <a id="4469" href="foundation.copartial-functions.html#4058" class="Function">copartial-dependent-function-dependent-function</a> <a id="4517" href="foundation.copartial-functions.html#4352" class="Bound">f</a>
</pre>
## Properties

### The underlying partial dependent function of a copartial dependent function

<pre class="Agda"><a id="4628" class="Keyword">module</a> <a id="4635" href="foundation.copartial-functions.html#4635" class="Module">_</a>
  <a id="4639" class="Symbol">{</a><a id="4640" href="foundation.copartial-functions.html#4640" class="Bound">l1</a> <a id="4643" href="foundation.copartial-functions.html#4643" class="Bound">l2</a> <a id="4646" href="foundation.copartial-functions.html#4646" class="Bound">l3</a> <a id="4649" class="Symbol">:</a> <a id="4651" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4656" class="Symbol">}</a> <a id="4658" class="Symbol">{</a><a id="4659" href="foundation.copartial-functions.html#4659" class="Bound">A</a> <a id="4661" class="Symbol">:</a> <a id="4663" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4666" href="foundation.copartial-functions.html#4640" class="Bound">l1</a><a id="4668" class="Symbol">}</a> <a id="4670" class="Symbol">{</a><a id="4671" href="foundation.copartial-functions.html#4671" class="Bound">B</a> <a id="4673" class="Symbol">:</a> <a id="4675" href="foundation.copartial-functions.html#4659" class="Bound">A</a> <a id="4677" class="Symbol">→</a> <a id="4679" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4682" href="foundation.copartial-functions.html#4643" class="Bound">l2</a><a id="4684" class="Symbol">}</a>
  <a id="4688" class="Symbol">(</a><a id="4689" href="foundation.copartial-functions.html#4689" class="Bound">f</a> <a id="4691" class="Symbol">:</a> <a id="4693" href="foundation.copartial-functions.html#2623" class="Function">copartial-dependent-function</a> <a id="4722" href="foundation.copartial-functions.html#4646" class="Bound">l3</a> <a id="4725" href="foundation.copartial-functions.html#4659" class="Bound">A</a> <a id="4727" href="foundation.copartial-functions.html#4671" class="Bound">B</a><a id="4728" class="Symbol">)</a>
  <a id="4732" class="Keyword">where</a>

  <a id="4741" href="foundation.copartial-functions.html#4741" class="Function">partial-dependent-function-copartial-dependent-function</a> <a id="4797" class="Symbol">:</a>
    <a id="4803" href="foundation.partial-functions.html#1208" class="Function">partial-dependent-function</a> <a id="4830" href="foundation.copartial-functions.html#4646" class="Bound">l3</a> <a id="4833" href="foundation.copartial-functions.html#4659" class="Bound">A</a> <a id="4835" href="foundation.copartial-functions.html#4671" class="Bound">B</a>
  <a id="4839" href="foundation.copartial-functions.html#4741" class="Function">partial-dependent-function-copartial-dependent-function</a> <a id="4895" href="foundation.copartial-functions.html#4895" class="Bound">a</a> <a id="4897" class="Symbol">=</a>
    <a id="4903" href="foundation.copartial-elements.html#5405" class="Function">partial-element-copartial-element</a> <a id="4937" class="Symbol">(</a><a id="4938" href="foundation.copartial-functions.html#4689" class="Bound">f</a> <a id="4940" href="foundation.copartial-functions.html#4895" class="Bound">a</a><a id="4941" class="Symbol">)</a>
</pre>
### The underlying partial function of a copartial function

<pre class="Agda"><a id="5017" class="Keyword">module</a> <a id="5024" href="foundation.copartial-functions.html#5024" class="Module">_</a>
  <a id="5028" class="Symbol">{</a><a id="5029" href="foundation.copartial-functions.html#5029" class="Bound">l1</a> <a id="5032" href="foundation.copartial-functions.html#5032" class="Bound">l2</a> <a id="5035" href="foundation.copartial-functions.html#5035" class="Bound">l3</a> <a id="5038" class="Symbol">:</a> <a id="5040" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5045" class="Symbol">}</a> <a id="5047" class="Symbol">{</a><a id="5048" href="foundation.copartial-functions.html#5048" class="Bound">A</a> <a id="5050" class="Symbol">:</a> <a id="5052" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5055" href="foundation.copartial-functions.html#5029" class="Bound">l1</a><a id="5057" class="Symbol">}</a> <a id="5059" class="Symbol">{</a><a id="5060" href="foundation.copartial-functions.html#5060" class="Bound">B</a> <a id="5062" class="Symbol">:</a> <a id="5064" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5067" href="foundation.copartial-functions.html#5032" class="Bound">l2</a><a id="5069" class="Symbol">}</a> <a id="5071" class="Symbol">(</a><a id="5072" href="foundation.copartial-functions.html#5072" class="Bound">f</a> <a id="5074" class="Symbol">:</a> <a id="5076" href="foundation.copartial-functions.html#2851" class="Function">copartial-function</a> <a id="5095" href="foundation.copartial-functions.html#5035" class="Bound">l3</a> <a id="5098" href="foundation.copartial-functions.html#5048" class="Bound">A</a> <a id="5100" href="foundation.copartial-functions.html#5060" class="Bound">B</a><a id="5101" class="Symbol">)</a>
  <a id="5105" class="Keyword">where</a>

  <a id="5114" href="foundation.copartial-functions.html#5114" class="Function">partial-function-copartial-function</a> <a id="5150" class="Symbol">:</a> <a id="5152" href="foundation.partial-functions.html#1432" class="Function">partial-function</a> <a id="5169" href="foundation.copartial-functions.html#5035" class="Bound">l3</a> <a id="5172" href="foundation.copartial-functions.html#5048" class="Bound">A</a> <a id="5174" href="foundation.copartial-functions.html#5060" class="Bound">B</a>
  <a id="5178" href="foundation.copartial-functions.html#5114" class="Function">partial-function-copartial-function</a> <a id="5214" href="foundation.copartial-functions.html#5214" class="Bound">a</a> <a id="5216" class="Symbol">=</a>
    <a id="5222" href="foundation.copartial-elements.html#5405" class="Function">partial-element-copartial-element</a> <a id="5256" class="Symbol">(</a><a id="5257" href="foundation.copartial-functions.html#5072" class="Bound">f</a> <a id="5259" href="foundation.copartial-functions.html#5214" class="Bound">a</a><a id="5260" class="Symbol">)</a>
</pre>
## See also

- [Partial functions](foundation.partial-functions.md)
