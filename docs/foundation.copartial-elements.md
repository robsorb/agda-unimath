# Copartial elements

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="foundation.copartial-elements.html" class="Module">foundation.copartial-elements</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="foundation.partial-elements.html" class="Module">foundation.partial-elements</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>

<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="orthogonal-factorization-systems.closed-modalities.html" class="Module">orthogonal-factorization-systems.closed-modalities</a>

<a id="421" class="Keyword">open</a> <a id="426" class="Keyword">import</a> <a id="433" href="synthetic-homotopy-theory.joins-of-types.html" class="Module">synthetic-homotopy-theory.joins-of-types</a>
</pre>
</details>

## Idea

A {{#concept "copartial element" Agda=copartial-element}} of a type `A` is an
element of type

```text
  Σ (Q : Prop), A * Q
```

where the type `A * Q` is the
[join](synthetic-homotopy-theory.joins-of-types.md) of `Q` and `A`. We say that
evaluation of a copartial element `(Q , u)` is
{{#concept "denied" Disambiguation="copartial element" Agda=is-denied-copartial-element}}
if the proposition `Q` holds.

In order to compare copartial elements with
[partial elements](foundation.partial-elements.md), note that we have the
following [pullback](foundation.pullbacks.md) squares

```text
  A -----> Σ (Q : Prop), A * Q        1 -----> Σ (P : Prop), (P → A)
  | ⌟              |                  | ⌟              |
  |                |                  |                |
  ∨                ∨                  ∨                ∨
  1 -----------> Prop                 1 -----------> Prop
          F                                   F

  1 -----> Σ (Q : Prop), A * Q        A -----> Σ (P : Prop), (P → A)
  | ⌟              |                  | ⌟              |
  |                |                  |                |
  ∨                ∨                  ∨                ∨
  1 -----------> Prop                 1 -----------> Prop
          T                                   T
```

Note that we make use of the
[closed modalities](orthogonal-factorization-systems.closed-modalities.md)
`A ↦ A * Q` in the formulation of copartial element, whereas the formulation of
partial elements makes use of the
[open modalities](orthogonal-factorization-systems.open-modalities.md). The
concepts of partial and copartial elements are dual in that sense.

Alternatively, the type of copartial elements of a type `A` can be defined as
the [pushout-product](synthetic-homotopy-theory.pushout-products.md)

```text
    A   1
    |   |
  ! | □ | T
    ∨   ∨
    1  Prop
```

This point of view is useful in order to establish that copartial elements of
copartial elements induce copartial elements. Indeed, note that
`(A □ T) □ T ＝ A □ (T □ T)` by associativity of the pushout product, and that
`T` is a pushout-product algebra in the sense that

```text
                                         P Q x ↦ (P * Q , x)
    1     1       Σ (P Q : Prop), P * Q ---------------------> 1
    |     |               |                                    |
  T |  □  | T   =   T □ T |                                    |
    ∨     ∨               ∨                                    ∨
  Prop   Prop           Prop² ------------------------------> Prop
                                       P Q ↦ P * Q
```

By this [morphism of arrows](foundation.morphisms-arrows.md) it follows that
there is a morphism of arrows

```text
  join-copartial-element : (A □ T) □ T → A □ T,
```

i.e., that copartial copartial elements induce copartial elements. These
considerations allow us to compose
[copartial functions](foundation.copartial-functions.md).

**Note:** The topic of copartial functions was not known to us in the
literature, and our formalization on this topic should be considered
experimental.

## Definition

### Copartial elements

<pre class="Agda"><a id="copartial-element"></a><a id="3625" href="foundation.copartial-elements.html#3625" class="Function">copartial-element</a> <a id="3643" class="Symbol">:</a> <a id="3645" class="Symbol">{</a><a id="3646" href="foundation.copartial-elements.html#3646" class="Bound">l1</a> <a id="3649" class="Symbol">:</a> <a id="3651" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3656" class="Symbol">}</a> <a id="3658" class="Symbol">(</a><a id="3659" href="foundation.copartial-elements.html#3659" class="Bound">l2</a> <a id="3662" class="Symbol">:</a> <a id="3664" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3669" class="Symbol">)</a> <a id="3671" class="Symbol">→</a> <a id="3673" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3676" href="foundation.copartial-elements.html#3646" class="Bound">l1</a> <a id="3679" class="Symbol">→</a> <a id="3681" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3684" class="Symbol">(</a><a id="3685" href="foundation.copartial-elements.html#3646" class="Bound">l1</a> <a id="3688" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3690" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3695" href="foundation.copartial-elements.html#3659" class="Bound">l2</a><a id="3697" class="Symbol">)</a>
<a id="3699" href="foundation.copartial-elements.html#3625" class="Function">copartial-element</a> <a id="3717" href="foundation.copartial-elements.html#3717" class="Bound">l2</a> <a id="3720" href="foundation.copartial-elements.html#3720" class="Bound">A</a> <a id="3722" class="Symbol">=</a>
  <a id="3726" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3728" class="Symbol">(</a><a id="3729" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3734" href="foundation.copartial-elements.html#3717" class="Bound">l2</a><a id="3736" class="Symbol">)</a> <a id="3738" class="Symbol">(λ</a> <a id="3741" href="foundation.copartial-elements.html#3741" class="Bound">Q</a> <a id="3743" class="Symbol">→</a> <a id="3745" href="orthogonal-factorization-systems.closed-modalities.html#1199" class="Function">operator-closed-modality</a> <a id="3770" href="foundation.copartial-elements.html#3741" class="Bound">Q</a> <a id="3772" href="foundation.copartial-elements.html#3720" class="Bound">A</a><a id="3773" class="Symbol">)</a>

<a id="3776" class="Keyword">module</a> <a id="3783" href="foundation.copartial-elements.html#3783" class="Module">_</a>
  <a id="3787" class="Symbol">{</a><a id="3788" href="foundation.copartial-elements.html#3788" class="Bound">l1</a> <a id="3791" href="foundation.copartial-elements.html#3791" class="Bound">l2</a> <a id="3794" class="Symbol">:</a> <a id="3796" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3801" class="Symbol">}</a> <a id="3803" class="Symbol">{</a><a id="3804" href="foundation.copartial-elements.html#3804" class="Bound">A</a> <a id="3806" class="Symbol">:</a> <a id="3808" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3811" href="foundation.copartial-elements.html#3788" class="Bound">l1</a><a id="3813" class="Symbol">}</a> <a id="3815" class="Symbol">(</a><a id="3816" href="foundation.copartial-elements.html#3816" class="Bound">a</a> <a id="3818" class="Symbol">:</a> <a id="3820" href="foundation.copartial-elements.html#3625" class="Function">copartial-element</a> <a id="3838" href="foundation.copartial-elements.html#3791" class="Bound">l2</a> <a id="3841" href="foundation.copartial-elements.html#3804" class="Bound">A</a><a id="3842" class="Symbol">)</a>
  <a id="3846" class="Keyword">where</a>

  <a id="3855" href="foundation.copartial-elements.html#3855" class="Function">is-denied-prop-copartial-element</a> <a id="3888" class="Symbol">:</a> <a id="3890" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3895" href="foundation.copartial-elements.html#3791" class="Bound">l2</a>
  <a id="3900" href="foundation.copartial-elements.html#3855" class="Function">is-denied-prop-copartial-element</a> <a id="3933" class="Symbol">=</a> <a id="3935" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3939" href="foundation.copartial-elements.html#3816" class="Bound">a</a>

  <a id="3944" href="foundation.copartial-elements.html#3944" class="Function">is-denied-copartial-element</a> <a id="3972" class="Symbol">:</a> <a id="3974" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3977" href="foundation.copartial-elements.html#3791" class="Bound">l2</a>
  <a id="3982" href="foundation.copartial-elements.html#3944" class="Function">is-denied-copartial-element</a> <a id="4010" class="Symbol">=</a>
    <a id="4016" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="4026" href="foundation.copartial-elements.html#3855" class="Function">is-denied-prop-copartial-element</a>

  <a id="4062" href="foundation.copartial-elements.html#4062" class="Function">value-copartial-element</a> <a id="4086" class="Symbol">:</a>
    <a id="4092" href="orthogonal-factorization-systems.closed-modalities.html#1199" class="Function">operator-closed-modality</a> <a id="4117" href="foundation.copartial-elements.html#3855" class="Function">is-denied-prop-copartial-element</a> <a id="4150" href="foundation.copartial-elements.html#3804" class="Bound">A</a>
  <a id="4154" href="foundation.copartial-elements.html#4062" class="Function">value-copartial-element</a> <a id="4178" class="Symbol">=</a> <a id="4180" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4184" href="foundation.copartial-elements.html#3816" class="Bound">a</a>
</pre>
### The unit of the copartial element operator

<pre class="Agda"><a id="4247" class="Keyword">module</a> <a id="4254" href="foundation.copartial-elements.html#4254" class="Module">_</a>
  <a id="4258" class="Symbol">{</a><a id="4259" href="foundation.copartial-elements.html#4259" class="Bound">l1</a> <a id="4262" class="Symbol">:</a> <a id="4264" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4269" class="Symbol">}</a> <a id="4271" class="Symbol">{</a><a id="4272" href="foundation.copartial-elements.html#4272" class="Bound">A</a> <a id="4274" class="Symbol">:</a> <a id="4276" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4279" href="foundation.copartial-elements.html#4259" class="Bound">l1</a><a id="4281" class="Symbol">}</a> <a id="4283" class="Symbol">(</a><a id="4284" href="foundation.copartial-elements.html#4284" class="Bound">a</a> <a id="4286" class="Symbol">:</a> <a id="4288" href="foundation.copartial-elements.html#4272" class="Bound">A</a><a id="4289" class="Symbol">)</a>
  <a id="4293" class="Keyword">where</a>

  <a id="4302" href="foundation.copartial-elements.html#4302" class="Function">is-denied-prop-unit-copartial-element</a> <a id="4340" class="Symbol">:</a> <a id="4342" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4347" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="4355" href="foundation.copartial-elements.html#4302" class="Function">is-denied-prop-unit-copartial-element</a> <a id="4393" class="Symbol">=</a> <a id="4395" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a>

  <a id="4409" href="foundation.copartial-elements.html#4409" class="Function">is-denied-unit-copartial-element</a> <a id="4442" class="Symbol">:</a> <a id="4444" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4447" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="4455" href="foundation.copartial-elements.html#4409" class="Function">is-denied-unit-copartial-element</a> <a id="4488" class="Symbol">=</a> <a id="4490" href="foundation-core.empty-types.html#801" class="Datatype">empty</a>

  <a id="4499" href="foundation.copartial-elements.html#4499" class="Function">unit-copartial-element</a> <a id="4522" class="Symbol">:</a> <a id="4524" href="foundation.copartial-elements.html#3625" class="Function">copartial-element</a> <a id="4542" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="4548" href="foundation.copartial-elements.html#4272" class="Bound">A</a>
  <a id="4552" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4556" href="foundation.copartial-elements.html#4499" class="Function">unit-copartial-element</a> <a id="4579" class="Symbol">=</a> <a id="4581" href="foundation.copartial-elements.html#4302" class="Function">is-denied-prop-unit-copartial-element</a>
  <a id="4621" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4625" href="foundation.copartial-elements.html#4499" class="Function">unit-copartial-element</a> <a id="4648" class="Symbol">=</a> <a id="4650" href="orthogonal-factorization-systems.closed-modalities.html#1336" class="Function">unit-closed-modality</a> <a id="4671" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a> <a id="4682" href="foundation.copartial-elements.html#4284" class="Bound">a</a>
</pre>
## Properties

### Forgetful map from copartial elements to partial elements

<pre class="Agda"><a id="4775" class="Keyword">module</a> <a id="4782" href="foundation.copartial-elements.html#4782" class="Module">_</a>
  <a id="4786" class="Symbol">{</a><a id="4787" href="foundation.copartial-elements.html#4787" class="Bound">l1</a> <a id="4790" href="foundation.copartial-elements.html#4790" class="Bound">l2</a> <a id="4793" class="Symbol">:</a> <a id="4795" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4800" class="Symbol">}</a> <a id="4802" class="Symbol">{</a><a id="4803" href="foundation.copartial-elements.html#4803" class="Bound">A</a> <a id="4805" class="Symbol">:</a> <a id="4807" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4810" href="foundation.copartial-elements.html#4787" class="Bound">l1</a><a id="4812" class="Symbol">}</a> <a id="4814" class="Symbol">(</a><a id="4815" href="foundation.copartial-elements.html#4815" class="Bound">a</a> <a id="4817" class="Symbol">:</a> <a id="4819" href="foundation.copartial-elements.html#3625" class="Function">copartial-element</a> <a id="4837" href="foundation.copartial-elements.html#4790" class="Bound">l2</a> <a id="4840" href="foundation.copartial-elements.html#4803" class="Bound">A</a><a id="4841" class="Symbol">)</a>
  <a id="4845" class="Keyword">where</a>

  <a id="4854" href="foundation.copartial-elements.html#4854" class="Function">is-defined-prop-partial-element-copartial-element</a> <a id="4904" class="Symbol">:</a> <a id="4906" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4911" href="foundation.copartial-elements.html#4790" class="Bound">l2</a>
  <a id="4916" href="foundation.copartial-elements.html#4854" class="Function">is-defined-prop-partial-element-copartial-element</a> <a id="4966" class="Symbol">=</a>
    <a id="4972" href="foundation.negation.html#981" class="Function">neg-Prop</a> <a id="4981" class="Symbol">(</a><a id="4982" href="foundation.copartial-elements.html#3855" class="Function">is-denied-prop-copartial-element</a> <a id="5015" href="foundation.copartial-elements.html#4815" class="Bound">a</a><a id="5016" class="Symbol">)</a>

  <a id="5021" href="foundation.copartial-elements.html#5021" class="Function">is-defined-partial-element-copartial-element</a> <a id="5066" class="Symbol">:</a> <a id="5068" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5071" href="foundation.copartial-elements.html#4790" class="Bound">l2</a>
  <a id="5076" href="foundation.copartial-elements.html#5021" class="Function">is-defined-partial-element-copartial-element</a> <a id="5121" class="Symbol">=</a>
    <a id="5127" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="5137" href="foundation.copartial-elements.html#4854" class="Function">is-defined-prop-partial-element-copartial-element</a>

  <a id="5190" href="foundation.copartial-elements.html#5190" class="Function">value-partial-element-copartial-element</a> <a id="5230" class="Symbol">:</a>
    <a id="5236" href="foundation.copartial-elements.html#5021" class="Function">is-defined-partial-element-copartial-element</a> <a id="5281" class="Symbol">→</a> <a id="5283" href="foundation.copartial-elements.html#4803" class="Bound">A</a>
  <a id="5287" href="foundation.copartial-elements.html#5190" class="Function">value-partial-element-copartial-element</a> <a id="5327" href="foundation.copartial-elements.html#5327" class="Bound">f</a> <a id="5329" class="Symbol">=</a>
    <a id="5335" href="synthetic-homotopy-theory.joins-of-types.html#6537" class="Function">map-inv-right-unit-law-join-is-empty</a> <a id="5372" href="foundation.copartial-elements.html#5327" class="Bound">f</a> <a id="5374" class="Symbol">(</a><a id="5375" href="foundation.copartial-elements.html#4062" class="Function">value-copartial-element</a> <a id="5399" href="foundation.copartial-elements.html#4815" class="Bound">a</a><a id="5400" class="Symbol">)</a>

  <a id="5405" href="foundation.copartial-elements.html#5405" class="Function">partial-element-copartial-element</a> <a id="5439" class="Symbol">:</a> <a id="5441" href="foundation.partial-elements.html#1254" class="Function">partial-element</a> <a id="5457" href="foundation.copartial-elements.html#4790" class="Bound">l2</a> <a id="5460" href="foundation.copartial-elements.html#4803" class="Bound">A</a>
  <a id="5464" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5468" href="foundation.copartial-elements.html#5405" class="Function">partial-element-copartial-element</a> <a id="5502" class="Symbol">=</a>
    <a id="5508" href="foundation.copartial-elements.html#4854" class="Function">is-defined-prop-partial-element-copartial-element</a>
  <a id="5560" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5564" href="foundation.copartial-elements.html#5405" class="Function">partial-element-copartial-element</a> <a id="5598" class="Symbol">=</a>
    <a id="5604" href="foundation.copartial-elements.html#5190" class="Function">value-partial-element-copartial-element</a>
</pre>