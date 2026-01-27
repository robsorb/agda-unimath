# Deloopable types

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="higher-group-theory.deloopable-types.html" class="Module">higher-group-theory.deloopable-types</a> <a id="73" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="129" class="Keyword">open</a> <a id="134" class="Keyword">import</a> <a id="141" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.small-types.html" class="Module">foundation.small-types</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="higher-group-theory.equivalences-higher-groups.html" class="Module">higher-group-theory.equivalences-higher-groups</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>
<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="higher-group-theory.small-higher-groups.html" class="Module">higher-group-theory.small-higher-groups</a>

<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="structured-types.pointed-equivalences.html" class="Module">structured-types.pointed-equivalences</a>
<a id="492" class="Keyword">open</a> <a id="497" class="Keyword">import</a> <a id="504" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="structured-types.small-pointed-types.html" class="Module">structured-types.small-pointed-types</a>
</pre>
</details>

## Idea

Consider a [pointed type](structured-types.pointed-types.md) `X` and a pointed
[connected](foundation.0-connected-types.md) type `Y`. We say that `Y` is a
{{#concept "delooping" Disambiguation="pointed type" Agda=is-delooping}} of `X`
if we have a [pointed equivalence](structured-types.pointed-equivalences.md)

```text
  X ≃∗ Ω Y.
```

Recall that a pointed connected type is an
[∞-group](higher-group-theory.higher-groups.md). An ∞-group `G` is therefore a
delooping of `X` if its underlying pointed type is pointed equivalent to `X`. A
{{#concept "delooping" Disambiguation="pointed type" Agda=delooping}} of `X`
therefore consist of an ∞-group `G` and a pointed equivalence

```text
  X ≃∗ type-∞-Group G
```

In other words, the type of deloopings of `X` is defined to be

```text
  delooping X := Σ (Y : ∞-Group), X ≃∗ Ω Y.
```

### Relation to higher group structures

A delooping of a pointed type `X` is, in quite a literal way, an
{{#concept "∞-group structure" Agda=delooping}} on `X`. In other words, the type
`delooping X` is the type of ∞-group structures on `X`. Indeed, the type of all
pointed types equipped with deloopings is
[equivalent](foundation-core.equivalences.md) to the type of ∞-groups, by
extensionality of the type of pointed types.

Being deloopable is therefore a [structure](foundation.structure.md), and
usually not a [property](foundation-core.propositions.md). If there are multiple
distinct ways to equip a pointed type `X` with the structure of an ∞-group, or
even with the structure of a [group](group-theory.groups.md), then the type of
deloopings of `X` will not be a proposition. For instance, the
[standard `4`-element type](univalent-combinatorics.standard-finite-types.md)
`Fin 4` is deloopable in multiple distinct ways, by equipping it with the
[cyclic group structure](group-theory.cyclic-groups.md) of `ℤ₄` or by equipping
it with the group structure of `ℤ₂ × ℤ₂`.

### Universe levels in the definition of being deloopable

Note that there is a small question about universe levels in the definition of
being a deloopable type. We say that a type is deloopable in a universe `𝒰` if
there is an ∞-group `Y` in the universe `𝒰` that is a delooping of `X`. However,
by the [type theoretic replacement principle](foundation.replacement.md) it
follows that any delooping of `X` is always [small](foundation.small-types.md)
with respect to the universe of `X` itself. Therefore we simply say that `X` is
deloopable, i.e., without reference to any universes, if `X` is deloopable in
its own universe.

## Definitions

### The predicate of being a delooping

<pre class="Agda"><a id="3220" class="Keyword">module</a> <a id="3227" href="higher-group-theory.deloopable-types.html#3227" class="Module">_</a>
  <a id="3231" class="Symbol">{</a><a id="3232" href="higher-group-theory.deloopable-types.html#3232" class="Bound">l1</a> <a id="3235" href="higher-group-theory.deloopable-types.html#3235" class="Bound">l2</a> <a id="3238" class="Symbol">:</a> <a id="3240" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3245" class="Symbol">}</a> <a id="3247" class="Symbol">(</a><a id="3248" href="higher-group-theory.deloopable-types.html#3248" class="Bound">X</a> <a id="3250" class="Symbol">:</a> <a id="3252" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3265" href="higher-group-theory.deloopable-types.html#3232" class="Bound">l1</a><a id="3267" class="Symbol">)</a>
  <a id="3271" class="Keyword">where</a>

  <a id="3280" href="higher-group-theory.deloopable-types.html#3280" class="Function">is-delooping</a> <a id="3293" class="Symbol">:</a> <a id="3295" class="Symbol">(</a><a id="3296" href="higher-group-theory.deloopable-types.html#3296" class="Bound">G</a> <a id="3298" class="Symbol">:</a> <a id="3300" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="3308" href="higher-group-theory.deloopable-types.html#3235" class="Bound">l2</a><a id="3310" class="Symbol">)</a> <a id="3312" class="Symbol">→</a> <a id="3314" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3317" class="Symbol">(</a><a id="3318" href="higher-group-theory.deloopable-types.html#3232" class="Bound">l1</a> <a id="3321" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3323" href="higher-group-theory.deloopable-types.html#3235" class="Bound">l2</a><a id="3325" class="Symbol">)</a>
  <a id="3329" href="higher-group-theory.deloopable-types.html#3280" class="Function">is-delooping</a> <a id="3342" href="higher-group-theory.deloopable-types.html#3342" class="Bound">G</a> <a id="3344" class="Symbol">=</a> <a id="3346" href="higher-group-theory.deloopable-types.html#3248" class="Bound">X</a> <a id="3348" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="3351" href="higher-group-theory.higher-groups.html#2979" class="Function">pointed-type-∞-Group</a> <a id="3372" href="higher-group-theory.deloopable-types.html#3342" class="Bound">G</a>
</pre>
### The type of deloopings of a pointed type, in a given universe

<pre class="Agda"><a id="3454" class="Keyword">module</a> <a id="3461" href="higher-group-theory.deloopable-types.html#3461" class="Module">_</a>
  <a id="3465" class="Symbol">{</a><a id="3466" href="higher-group-theory.deloopable-types.html#3466" class="Bound">l1</a> <a id="3469" class="Symbol">:</a> <a id="3471" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3476" class="Symbol">}</a> <a id="3478" class="Symbol">(</a><a id="3479" href="higher-group-theory.deloopable-types.html#3479" class="Bound">X</a> <a id="3481" class="Symbol">:</a> <a id="3483" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3496" href="higher-group-theory.deloopable-types.html#3466" class="Bound">l1</a><a id="3498" class="Symbol">)</a>
  <a id="3502" class="Keyword">where</a>

  <a id="3511" href="higher-group-theory.deloopable-types.html#3511" class="Function">delooping-Level</a> <a id="3527" class="Symbol">:</a> <a id="3529" class="Symbol">(</a><a id="3530" href="higher-group-theory.deloopable-types.html#3530" class="Bound">l</a> <a id="3532" class="Symbol">:</a> <a id="3534" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3539" class="Symbol">)</a> <a id="3541" class="Symbol">→</a> <a id="3543" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3546" class="Symbol">(</a><a id="3547" href="higher-group-theory.deloopable-types.html#3466" class="Bound">l1</a> <a id="3550" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3552" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3557" href="higher-group-theory.deloopable-types.html#3530" class="Bound">l</a><a id="3558" class="Symbol">)</a>
  <a id="3562" href="higher-group-theory.deloopable-types.html#3511" class="Function">delooping-Level</a> <a id="3578" href="higher-group-theory.deloopable-types.html#3578" class="Bound">l</a> <a id="3580" class="Symbol">=</a> <a id="3582" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3584" class="Symbol">(</a><a id="3585" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="3593" href="higher-group-theory.deloopable-types.html#3578" class="Bound">l</a><a id="3594" class="Symbol">)</a> <a id="3596" class="Symbol">(</a><a id="3597" href="higher-group-theory.deloopable-types.html#3280" class="Function">is-delooping</a> <a id="3610" href="higher-group-theory.deloopable-types.html#3479" class="Bound">X</a><a id="3611" class="Symbol">)</a>

  <a id="3616" class="Keyword">module</a> <a id="3623" href="higher-group-theory.deloopable-types.html#3623" class="Module">_</a>
    <a id="3629" class="Symbol">{</a><a id="3630" href="higher-group-theory.deloopable-types.html#3630" class="Bound">l</a> <a id="3632" class="Symbol">:</a> <a id="3634" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3639" class="Symbol">}</a> <a id="3641" class="Symbol">(</a><a id="3642" href="higher-group-theory.deloopable-types.html#3642" class="Bound">Y</a> <a id="3644" class="Symbol">:</a> <a id="3646" href="higher-group-theory.deloopable-types.html#3511" class="Function">delooping-Level</a> <a id="3662" href="higher-group-theory.deloopable-types.html#3630" class="Bound">l</a><a id="3663" class="Symbol">)</a>
    <a id="3669" class="Keyword">where</a>

    <a id="3680" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a> <a id="3704" class="Symbol">:</a> <a id="3706" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="3714" href="higher-group-theory.deloopable-types.html#3630" class="Bound">l</a>
    <a id="3720" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a> <a id="3744" class="Symbol">=</a> <a id="3746" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3750" href="higher-group-theory.deloopable-types.html#3642" class="Bound">Y</a>

    <a id="3757" href="higher-group-theory.deloopable-types.html#3757" class="Function">classifying-pointed-type-∞-group-delooping-Level</a> <a id="3806" class="Symbol">:</a> <a id="3808" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3821" href="higher-group-theory.deloopable-types.html#3630" class="Bound">l</a>
    <a id="3827" href="higher-group-theory.deloopable-types.html#3757" class="Function">classifying-pointed-type-∞-group-delooping-Level</a> <a id="3876" class="Symbol">=</a>
      <a id="3884" href="higher-group-theory.higher-groups.html#1156" class="Function">classifying-pointed-type-∞-Group</a> <a id="3917" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a>

    <a id="3946" href="higher-group-theory.deloopable-types.html#3946" class="Function">classifying-type-∞-group-delooping-Level</a> <a id="3987" class="Symbol">:</a> <a id="3989" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3992" href="higher-group-theory.deloopable-types.html#3630" class="Bound">l</a>
    <a id="3998" href="higher-group-theory.deloopable-types.html#3946" class="Function">classifying-type-∞-group-delooping-Level</a> <a id="4039" class="Symbol">=</a>
      <a id="4047" href="higher-group-theory.higher-groups.html#1252" class="Function">classifying-type-∞-Group</a> <a id="4072" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a>

    <a id="4101" href="higher-group-theory.deloopable-types.html#4101" class="Function">is-delooping-delooping-Level</a> <a id="4130" class="Symbol">:</a> <a id="4132" href="higher-group-theory.deloopable-types.html#3280" class="Function">is-delooping</a> <a id="4145" href="higher-group-theory.deloopable-types.html#3479" class="Bound">X</a> <a id="4147" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a>
    <a id="4175" href="higher-group-theory.deloopable-types.html#4101" class="Function">is-delooping-delooping-Level</a> <a id="4204" class="Symbol">=</a> <a id="4206" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4210" href="higher-group-theory.deloopable-types.html#3642" class="Bound">Y</a>

    <a id="4217" href="higher-group-theory.deloopable-types.html#4217" class="Function">equiv-is-delooping-delooping-Level</a> <a id="4252" class="Symbol">:</a>
      <a id="4260" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="4278" href="higher-group-theory.deloopable-types.html#3479" class="Bound">X</a> <a id="4280" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="4282" href="higher-group-theory.higher-groups.html#3080" class="Function">type-∞-Group</a> <a id="4295" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a>
    <a id="4323" href="higher-group-theory.deloopable-types.html#4217" class="Function">equiv-is-delooping-delooping-Level</a> <a id="4358" class="Symbol">=</a>
      <a id="4366" href="structured-types.pointed-equivalences.html#7408" class="Function">equiv-pointed-equiv</a> <a id="4386" href="higher-group-theory.deloopable-types.html#4101" class="Function">is-delooping-delooping-Level</a>
</pre>
### The type of deloopings of a pointed type

<pre class="Agda"><a id="4474" class="Keyword">module</a> <a id="4481" href="higher-group-theory.deloopable-types.html#4481" class="Module">_</a>
  <a id="4485" class="Symbol">{</a><a id="4486" href="higher-group-theory.deloopable-types.html#4486" class="Bound">l1</a> <a id="4489" class="Symbol">:</a> <a id="4491" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4496" class="Symbol">}</a> <a id="4498" class="Symbol">(</a><a id="4499" href="higher-group-theory.deloopable-types.html#4499" class="Bound">X</a> <a id="4501" class="Symbol">:</a> <a id="4503" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4516" href="higher-group-theory.deloopable-types.html#4486" class="Bound">l1</a><a id="4518" class="Symbol">)</a>
  <a id="4522" class="Keyword">where</a>

  <a id="4531" href="higher-group-theory.deloopable-types.html#4531" class="Function">delooping</a> <a id="4541" class="Symbol">:</a> <a id="4543" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4546" class="Symbol">(</a><a id="4547" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="4552" href="higher-group-theory.deloopable-types.html#4486" class="Bound">l1</a><a id="4554" class="Symbol">)</a>
  <a id="4558" href="higher-group-theory.deloopable-types.html#4531" class="Function">delooping</a> <a id="4568" class="Symbol">=</a> <a id="4570" href="higher-group-theory.deloopable-types.html#3511" class="Function">delooping-Level</a> <a id="4586" href="higher-group-theory.deloopable-types.html#4499" class="Bound">X</a> <a id="4588" href="higher-group-theory.deloopable-types.html#4486" class="Bound">l1</a>
</pre>
## Properties

### The delooping of a pointed type in a universe `𝒰` is a `𝒰`-small ∞-group

<pre class="Agda"><a id="4697" class="Keyword">module</a> <a id="4704" href="higher-group-theory.deloopable-types.html#4704" class="Module">_</a>
  <a id="4708" class="Symbol">{</a><a id="4709" href="higher-group-theory.deloopable-types.html#4709" class="Bound">l1</a> <a id="4712" href="higher-group-theory.deloopable-types.html#4712" class="Bound">l2</a> <a id="4715" class="Symbol">:</a> <a id="4717" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4722" class="Symbol">}</a> <a id="4724" class="Symbol">(</a><a id="4725" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a> <a id="4727" class="Symbol">:</a> <a id="4729" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4742" href="higher-group-theory.deloopable-types.html#4709" class="Bound">l1</a><a id="4744" class="Symbol">)</a> <a id="4746" class="Symbol">(</a><a id="4747" href="higher-group-theory.deloopable-types.html#4747" class="Bound">H</a> <a id="4749" class="Symbol">:</a> <a id="4751" href="higher-group-theory.deloopable-types.html#3511" class="Function">delooping-Level</a> <a id="4767" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a> <a id="4769" href="higher-group-theory.deloopable-types.html#4712" class="Bound">l2</a><a id="4771" class="Symbol">)</a>
  <a id="4775" class="Keyword">where</a>

  <a id="4784" class="Keyword">abstract</a>
    <a id="4797" href="higher-group-theory.deloopable-types.html#4797" class="Function">is-small-∞-group-delooping-Level</a> <a id="4830" class="Symbol">:</a>
      <a id="4838" href="higher-group-theory.small-higher-groups.html#2224" class="Function">is-small-∞-Group</a> <a id="4855" href="higher-group-theory.deloopable-types.html#4709" class="Bound">l1</a> <a id="4858" class="Symbol">(</a><a id="4859" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a> <a id="4883" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a> <a id="4885" href="higher-group-theory.deloopable-types.html#4747" class="Bound">H</a><a id="4886" class="Symbol">)</a>
    <a id="4892" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4896" href="higher-group-theory.deloopable-types.html#4797" class="Function">is-small-∞-group-delooping-Level</a> <a id="4929" class="Symbol">=</a> <a id="4931" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="4949" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a>
    <a id="4955" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4959" href="higher-group-theory.deloopable-types.html#4797" class="Function">is-small-∞-group-delooping-Level</a> <a id="4992" class="Symbol">=</a>
      <a id="5000" href="foundation-core.equivalences.html#8859" class="Function">inv-equiv</a> <a id="5010" class="Symbol">(</a><a id="5011" href="higher-group-theory.deloopable-types.html#4217" class="Function">equiv-is-delooping-delooping-Level</a> <a id="5046" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a> <a id="5048" href="higher-group-theory.deloopable-types.html#4747" class="Bound">H</a><a id="5049" class="Symbol">)</a>

  <a id="5054" class="Keyword">abstract</a>
    <a id="5067" href="higher-group-theory.deloopable-types.html#5067" class="Function">is-small-classifying-type-∞-group-delooping-Level</a> <a id="5117" class="Symbol">:</a>
      <a id="5125" href="foundation-core.small-types.html#1494" class="Function">is-small</a> <a id="5134" href="higher-group-theory.deloopable-types.html#4709" class="Bound">l1</a> <a id="5137" class="Symbol">(</a><a id="5138" href="higher-group-theory.deloopable-types.html#3946" class="Function">classifying-type-∞-group-delooping-Level</a> <a id="5179" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a> <a id="5181" href="higher-group-theory.deloopable-types.html#4747" class="Bound">H</a><a id="5182" class="Symbol">)</a>
    <a id="5188" href="higher-group-theory.deloopable-types.html#5067" class="Function">is-small-classifying-type-∞-group-delooping-Level</a> <a id="5238" class="Symbol">=</a>
      <a id="5246" href="higher-group-theory.small-higher-groups.html#5735" class="Function">is-small-classifying-type-is-small-∞-Group</a>
        <a id="5297" class="Symbol">(</a> <a id="5299" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a> <a id="5323" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a> <a id="5325" href="higher-group-theory.deloopable-types.html#4747" class="Bound">H</a><a id="5326" class="Symbol">)</a>
        <a id="5336" class="Symbol">(</a> <a id="5338" href="higher-group-theory.deloopable-types.html#4797" class="Function">is-small-∞-group-delooping-Level</a><a id="5370" class="Symbol">)</a>

  <a id="5375" class="Keyword">abstract</a>
    <a id="5388" href="higher-group-theory.deloopable-types.html#5388" class="Function">is-pointed-small-classifying-pointed-type-∞-group-delooping-Level</a> <a id="5454" class="Symbol">:</a>
      <a id="5462" href="structured-types.small-pointed-types.html#2112" class="Function">is-pointed-small-Pointed-Type</a> <a id="5492" href="higher-group-theory.deloopable-types.html#4709" class="Bound">l1</a>
        <a id="5503" class="Symbol">(</a> <a id="5505" href="higher-group-theory.deloopable-types.html#3757" class="Function">classifying-pointed-type-∞-group-delooping-Level</a> <a id="5554" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a> <a id="5556" href="higher-group-theory.deloopable-types.html#4747" class="Bound">H</a><a id="5557" class="Symbol">)</a>
    <a id="5563" href="higher-group-theory.deloopable-types.html#5388" class="Function">is-pointed-small-classifying-pointed-type-∞-group-delooping-Level</a> <a id="5629" class="Symbol">=</a>
      <a id="5637" href="structured-types.small-pointed-types.html#4034" class="Function">is-pointed-small-is-small-Pointed-Type</a>
        <a id="5684" class="Symbol">(</a> <a id="5686" href="higher-group-theory.deloopable-types.html#3757" class="Function">classifying-pointed-type-∞-group-delooping-Level</a> <a id="5735" href="higher-group-theory.deloopable-types.html#4725" class="Bound">X</a> <a id="5737" href="higher-group-theory.deloopable-types.html#4747" class="Bound">H</a><a id="5738" class="Symbol">)</a>
        <a id="5748" class="Symbol">(</a> <a id="5750" href="higher-group-theory.deloopable-types.html#5067" class="Function">is-small-classifying-type-∞-group-delooping-Level</a><a id="5799" class="Symbol">)</a>
</pre>
### If a pointed type in universe `𝒰 l1` is deloopable in any universe, then it is deloopable in `𝒰 l1`

Suppose `X` is a pointed type of universe level `l1`, which is deloopable in
universe level `l2`. Then there is an ∞-group `H` of universe level `l2`
equipped with a pointed equivalence

```text
  X ≃∗ type-∞-Group H.
```

This implies that the ∞-group `H` is `l1`-small, because its underlying type is
equivalent to the underlying type of `X`. Hence there is an ∞-group `K` equipped
with an
[equivalence of ∞-groups](higher-group-theory.equivalences-higher-groups.md)

```text
  H ≃ K.
```

<pre class="Agda"><a id="6411" class="Keyword">module</a> <a id="6418" href="higher-group-theory.deloopable-types.html#6418" class="Module">_</a>
  <a id="6422" class="Symbol">{</a><a id="6423" href="higher-group-theory.deloopable-types.html#6423" class="Bound">l1</a> <a id="6426" href="higher-group-theory.deloopable-types.html#6426" class="Bound">l2</a> <a id="6429" class="Symbol">:</a> <a id="6431" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6436" class="Symbol">}</a> <a id="6438" class="Symbol">(</a><a id="6439" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="6441" class="Symbol">:</a> <a id="6443" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6456" href="higher-group-theory.deloopable-types.html#6423" class="Bound">l1</a><a id="6458" class="Symbol">)</a> <a id="6460" class="Symbol">(</a><a id="6461" href="higher-group-theory.deloopable-types.html#6461" class="Bound">H</a> <a id="6463" class="Symbol">:</a> <a id="6465" href="higher-group-theory.deloopable-types.html#3511" class="Function">delooping-Level</a> <a id="6481" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="6483" href="higher-group-theory.deloopable-types.html#6426" class="Bound">l2</a><a id="6485" class="Symbol">)</a>
  <a id="6489" class="Keyword">where</a>

  <a id="6498" href="higher-group-theory.deloopable-types.html#6498" class="Function">∞-group-delooping-delooping-level</a> <a id="6532" class="Symbol">:</a> <a id="6534" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="6542" href="higher-group-theory.deloopable-types.html#6423" class="Bound">l1</a>
  <a id="6547" href="higher-group-theory.deloopable-types.html#6498" class="Function">∞-group-delooping-delooping-level</a> <a id="6581" class="Symbol">=</a>
    <a id="6587" href="higher-group-theory.small-higher-groups.html#7917" class="Function">∞-group-is-small-∞-Group</a>
      <a id="6618" class="Symbol">(</a> <a id="6620" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a> <a id="6644" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="6646" href="higher-group-theory.deloopable-types.html#6461" class="Bound">H</a><a id="6647" class="Symbol">)</a>
      <a id="6655" class="Symbol">(</a> <a id="6657" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="6675" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="6677" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
        <a id="6687" href="structured-types.pointed-equivalences.html#12444" class="Function">equiv-inv-pointed-equiv</a> <a id="6711" class="Symbol">(</a><a id="6712" href="higher-group-theory.deloopable-types.html#4101" class="Function">is-delooping-delooping-Level</a> <a id="6741" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="6743" href="higher-group-theory.deloopable-types.html#6461" class="Bound">H</a><a id="6744" class="Symbol">))</a>

  <a id="6750" href="higher-group-theory.deloopable-types.html#6750" class="Function">is-delooping-delooping-delooping-Level</a> <a id="6789" class="Symbol">:</a>
    <a id="6795" href="higher-group-theory.deloopable-types.html#3280" class="Function">is-delooping</a> <a id="6808" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="6810" href="higher-group-theory.deloopable-types.html#6498" class="Function">∞-group-delooping-delooping-level</a>
  <a id="6846" href="higher-group-theory.deloopable-types.html#6750" class="Function">is-delooping-delooping-delooping-Level</a> <a id="6885" class="Symbol">=</a>
    <a id="6891" href="structured-types.pointed-equivalences.html#11710" class="Function">comp-pointed-equiv</a>
      <a id="6916" class="Symbol">(</a> <a id="6918" href="higher-group-theory.equivalences-higher-groups.html#1397" class="Function">pointed-equiv-equiv-∞-Group</a>
        <a id="6954" class="Symbol">(</a> <a id="6956" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a> <a id="6980" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="6982" href="higher-group-theory.deloopable-types.html#6461" class="Bound">H</a><a id="6983" class="Symbol">)</a>
        <a id="6993" class="Symbol">(</a> <a id="6995" href="higher-group-theory.deloopable-types.html#6498" class="Function">∞-group-delooping-delooping-level</a><a id="7028" class="Symbol">)</a>
        <a id="7038" class="Symbol">(</a> <a id="7040" href="higher-group-theory.small-higher-groups.html#8495" class="Function">equiv-∞-group-is-small-∞-Group</a>
          <a id="7081" class="Symbol">(</a> <a id="7083" href="higher-group-theory.deloopable-types.html#3680" class="Function">∞-group-delooping-Level</a> <a id="7107" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="7109" href="higher-group-theory.deloopable-types.html#6461" class="Bound">H</a><a id="7110" class="Symbol">)</a>
          <a id="7122" class="Symbol">(</a> <a id="7124" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="7142" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="7144" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
            <a id="7158" href="structured-types.pointed-equivalences.html#12444" class="Function">equiv-inv-pointed-equiv</a> <a id="7182" class="Symbol">(</a><a id="7183" href="higher-group-theory.deloopable-types.html#4101" class="Function">is-delooping-delooping-Level</a> <a id="7212" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="7214" href="higher-group-theory.deloopable-types.html#6461" class="Bound">H</a><a id="7215" class="Symbol">))))</a>
      <a id="7226" class="Symbol">(</a> <a id="7228" href="higher-group-theory.deloopable-types.html#4101" class="Function">is-delooping-delooping-Level</a> <a id="7257" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a> <a id="7259" href="higher-group-theory.deloopable-types.html#6461" class="Bound">H</a><a id="7260" class="Symbol">)</a>

  <a id="7265" href="higher-group-theory.deloopable-types.html#7265" class="Function">delooping-delooping-Level</a> <a id="7291" class="Symbol">:</a> <a id="7293" href="higher-group-theory.deloopable-types.html#4531" class="Function">delooping</a> <a id="7303" href="higher-group-theory.deloopable-types.html#6439" class="Bound">X</a>
  <a id="7307" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="7311" href="higher-group-theory.deloopable-types.html#7265" class="Function">delooping-delooping-Level</a> <a id="7337" class="Symbol">=</a> <a id="7339" href="higher-group-theory.deloopable-types.html#6498" class="Function">∞-group-delooping-delooping-level</a>
  <a id="7375" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7379" href="higher-group-theory.deloopable-types.html#7265" class="Function">delooping-delooping-Level</a> <a id="7405" class="Symbol">=</a> <a id="7407" href="higher-group-theory.deloopable-types.html#6750" class="Function">is-delooping-delooping-delooping-Level</a>
</pre>
## See also

- [Deloopable H-spaces](higher-group-theory.deloopable-h-spaces.md)
- [Deloopable groups](higher-group-theory.deloopable-groups.md)
