# Eilenberg-Mac Lane spaces

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="higher-group-theory.eilenberg-mac-lane-spaces.html" class="Module">higher-group-theory.eilenberg-mac-lane-spaces</a> <a id="91" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="147" class="Keyword">open</a> <a id="152" class="Keyword">import</a> <a id="159" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="foundation.0-connected-types.html" class="Module">foundation.0-connected-types</a>
<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation.truncated-types.html" class="Module">foundation.truncated-types</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="group-theory.abelian-groups.html" class="Module">group-theory.abelian-groups</a>
<a id="488" class="Keyword">open</a> <a id="493" class="Keyword">import</a> <a id="500" href="group-theory.groups.html" class="Module">group-theory.groups</a>

<a id="521" class="Keyword">open</a> <a id="526" class="Keyword">import</a> <a id="533" href="structured-types.equivalences-h-spaces.html" class="Module">structured-types.equivalences-h-spaces</a>
<a id="572" class="Keyword">open</a> <a id="577" class="Keyword">import</a> <a id="584" href="structured-types.pointed-equivalences.html" class="Module">structured-types.pointed-equivalences</a>
<a id="622" class="Keyword">open</a> <a id="627" class="Keyword">import</a> <a id="634" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="666" class="Keyword">open</a> <a id="671" class="Keyword">import</a> <a id="678" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a>
<a id="725" class="Keyword">open</a> <a id="730" class="Keyword">import</a> <a id="737" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
</pre>
</details>

## Idea

There are many ways to say what an _Eilenberg-Mac Lane space_ is. The basic idea
is that a [pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md) type `X` is an Eilenberg-Mac Lane
space if only one of its homotopy groups `π n X` is
[nontrivial](group-theory.nontrivial-groups.md). However, recall that the
condition of being [`n`-truncated](foundation-core.truncated-types.md) is
slightly stronger than the condition that the homotopy groups `π i X` are
[trivial](group-theory.trivial-groups.md) for all `i > n`. Indeed, unlike in the
setting of topological spaces or simplicial sets, univalent type theory allows
for the possibility of ∞-connected types, i.e., types of which all homotopy
groups are trivial. In order to avoid examples of Eilenberg-Mac Lane spaces
possibly involving nontrivial ∞-connected types, we will slightly strengthen the
definition of Eilenberg-Mac Lane spaces. We say that a pointed type `X`is an
{{#concept "Eilenberg-Mac Lane space"}} if`X`is`n-1`-connected and
`n`-truncated. Under this definition there is an
[equivalence](category-theory.equivalences-of-categories.md) between the
[category of groups](group-theory.category-of-groups.md), resp. the
[category of abelian groups](group-theory.category-of-abelian-groups.md), and
the category of Eilenberg-Mac Lane spaces of dimension `1`, resp. `n ≥ 2`.

Consider a [group](group-theory.groups.md) `G` and a
[natural number](elementary-number-theory.natural-numbers.md) `n ≥ 1`. A pointed
type `X` is said to be an Eilenberg-Mac Lane space of type `K G n` if `X` is
[`(n-1)`-connected](foundation.connected-types.md) and
[`n`-truncated](foundation-core.truncated-types.md), and moreover the `n`-th
homotopy group `π n X` is [isomorphic](group-theory.isomorphisms-groups.md) to
`G`.

There is also a recursive definition of what it means for a pointed type `X` to
be an $n$-th
{{#concept "Eilenberg-Mac Lane space" Agda=is-eilenberg-mac-lane-space-Group}}:

- We say that `X` is a **first Eilenberg-Mac Lane space** if `X` is
  `0`-connected and there is a
  [pointed equivalence](structured-types.pointed-equivalences.md)

  ```text
    Ω X ≃ G
  ```

  that maps concatenation in the
  [loop space](synthetic-homotopy-theory.loop-spaces.md) `Ω X` to the group
  operation on `G`.

- We say that `X` is an `(n+1)`-st Eilenberg-Mac Lane space if `X` is
  `0`-connected and `Ω X` is an `n`-th Eilenberg-Mac Lane space.

## Definitions

### Eilenberg-Mac Lane spaces

We introduce the most general notion of an (unspecified) Eilenberg-Mac Lane
space to be a pointed `n`-connected `(n+1)`-truncated type. Eilenberg-Mac Lane
spaces in this definition aren't equipped with a group isomorphism from their
nontrivial homotopy group to a given group `G`, so in this sense they are
"unspecified".

<pre class="Agda"><a id="3612" class="Keyword">module</a> <a id="3619" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3619" class="Module">_</a>
  <a id="3623" class="Symbol">{</a><a id="3624" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3624" class="Bound">l1</a> <a id="3627" class="Symbol">:</a> <a id="3629" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3634" class="Symbol">}</a> <a id="3636" class="Symbol">(</a><a id="3637" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3637" class="Bound">k</a> <a id="3639" class="Symbol">:</a> <a id="3641" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="3642" class="Symbol">)</a> <a id="3644" class="Symbol">(</a><a id="3645" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3645" class="Bound">X</a> <a id="3647" class="Symbol">:</a> <a id="3649" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3662" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3624" class="Bound">l1</a><a id="3664" class="Symbol">)</a>
  <a id="3668" class="Keyword">where</a>

  <a id="3677" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3677" class="Function">is-eilenberg-mac-lane-space-𝕋</a> <a id="3707" class="Symbol">:</a> <a id="3709" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3712" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3624" class="Bound">l1</a>
  <a id="3717" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3677" class="Function">is-eilenberg-mac-lane-space-𝕋</a> <a id="3747" class="Symbol">=</a>
    <a id="3753" href="foundation.connected-types.html#1379" class="Function">is-connected</a> <a id="3766" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3637" class="Bound">k</a> <a id="3768" class="Symbol">(</a><a id="3769" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="3787" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3645" class="Bound">X</a><a id="3788" class="Symbol">)</a> <a id="3790" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
    <a id="3796" href="foundation-core.truncated-types.html#1305" class="Function">is-trunc</a> <a id="3805" class="Symbol">(</a><a id="3806" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="3813" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3637" class="Bound">k</a><a id="3814" class="Symbol">)</a> <a id="3816" class="Symbol">(</a><a id="3817" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="3835" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3645" class="Bound">X</a><a id="3836" class="Symbol">)</a>

<a id="3839" class="Keyword">module</a> <a id="3846" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3846" class="Module">_</a>
  <a id="3850" class="Symbol">{</a><a id="3851" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3851" class="Bound">l1</a> <a id="3854" class="Symbol">:</a> <a id="3856" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3861" class="Symbol">}</a> <a id="3863" class="Symbol">(</a><a id="3864" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3864" class="Bound">n</a> <a id="3866" class="Symbol">:</a> <a id="3868" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="3869" class="Symbol">)</a> <a id="3871" class="Symbol">(</a><a id="3872" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3872" class="Bound">X</a> <a id="3874" class="Symbol">:</a> <a id="3876" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3889" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3851" class="Bound">l1</a><a id="3891" class="Symbol">)</a>
  <a id="3895" class="Keyword">where</a>

  <a id="3904" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3904" class="Function">is-eilenberg-mac-lane-space</a> <a id="3932" class="Symbol">:</a> <a id="3934" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3937" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3851" class="Bound">l1</a>
  <a id="3942" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3904" class="Function">is-eilenberg-mac-lane-space</a> <a id="3970" class="Symbol">=</a>
    <a id="3976" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3677" class="Function">is-eilenberg-mac-lane-space-𝕋</a>
      <a id="4012" class="Symbol">(</a> <a id="4014" href="foundation.truncation-levels.html#692" class="Function">truncation-level-minus-one-ℕ</a> <a id="4043" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3864" class="Bound">n</a><a id="4044" class="Symbol">)</a>
      <a id="4052" class="Symbol">(</a> <a id="4054" href="higher-group-theory.eilenberg-mac-lane-spaces.html#3872" class="Bound">X</a><a id="4055" class="Symbol">)</a>
</pre>
### Eilenberg-Mac Lane spaces specified by groups

<pre class="Agda"><a id="4121" class="Keyword">module</a> <a id="4128" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4128" class="Module">_</a>
  <a id="4132" class="Symbol">{</a><a id="4133" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4133" class="Bound">l1</a> <a id="4136" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4136" class="Bound">l2</a> <a id="4139" class="Symbol">:</a> <a id="4141" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4146" class="Symbol">}</a> <a id="4148" class="Symbol">(</a><a id="4149" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4149" class="Bound">G</a> <a id="4151" class="Symbol">:</a> <a id="4153" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="4159" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4133" class="Bound">l1</a><a id="4161" class="Symbol">)</a>
  <a id="4165" class="Keyword">where</a>

  <a id="4174" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4174" class="Function">is-eilenberg-mac-lane-space-Group</a> <a id="4208" class="Symbol">:</a>
    <a id="4214" class="Symbol">(</a><a id="4215" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4215" class="Bound">n</a> <a id="4217" class="Symbol">:</a> <a id="4219" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="4220" class="Symbol">)</a> <a id="4222" class="Symbol">(</a><a id="4223" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4223" class="Bound">X</a> <a id="4225" class="Symbol">:</a> <a id="4227" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4240" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4136" class="Bound">l2</a><a id="4242" class="Symbol">)</a> <a id="4244" class="Symbol">→</a> <a id="4246" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4249" class="Symbol">(</a><a id="4250" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4133" class="Bound">l1</a> <a id="4253" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4255" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4136" class="Bound">l2</a><a id="4257" class="Symbol">)</a>
  <a id="4261" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4174" class="Function">is-eilenberg-mac-lane-space-Group</a> <a id="4295" class="Number">0</a> <a id="4297" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4297" class="Bound">X</a> <a id="4299" class="Symbol">=</a>
    <a id="4305" href="group-theory.groups.html#4857" class="Function">pointed-type-Group</a> <a id="4324" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4149" class="Bound">G</a> <a id="4326" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="4329" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4297" class="Bound">X</a>
  <a id="4333" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4174" class="Function">is-eilenberg-mac-lane-space-Group</a> <a id="4367" class="Symbol">(</a><a id="4368" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="4375" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4375" class="Bound">n</a><a id="4376" class="Symbol">)</a> <a id="4378" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4378" class="Bound">X</a> <a id="4380" class="Symbol">=</a>
    <a id="4386" href="foundation.connected-types.html#1379" class="Function">is-connected</a> <a id="4399" class="Symbol">(</a><a id="4400" href="foundation.truncation-levels.html#799" class="Function">truncation-level-ℕ</a> <a id="4419" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4375" class="Bound">n</a><a id="4420" class="Symbol">)</a> <a id="4422" class="Symbol">(</a><a id="4423" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="4441" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4378" class="Bound">X</a><a id="4442" class="Symbol">)</a> <a id="4444" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
    <a id="4450" href="structured-types.equivalences-h-spaces.html#7149" class="Function">equiv-H-Space</a> <a id="4464" class="Symbol">(</a><a id="4465" href="group-theory.groups.html#4972" class="Function">h-space-Group</a> <a id="4479" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4149" class="Bound">G</a><a id="4480" class="Symbol">)</a> <a id="4482" class="Symbol">(</a><a id="4483" href="synthetic-homotopy-theory.loop-spaces.html#1879" class="Function">Ω-H-Space</a> <a id="4493" class="Symbol">(</a><a id="4494" href="synthetic-homotopy-theory.iterated-loop-spaces.html#841" class="Function">iterated-loop-space</a> <a id="4514" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4375" class="Bound">n</a> <a id="4516" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4378" class="Bound">X</a><a id="4517" class="Symbol">))</a>
</pre>
### Eilenberg-Mac Lane spaces specified by abelian groups

<pre class="Agda"><a id="4592" class="Keyword">module</a> <a id="4599" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4599" class="Module">_</a>
  <a id="4603" class="Symbol">{</a><a id="4604" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4604" class="Bound">l1</a> <a id="4607" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4607" class="Bound">l2</a> <a id="4610" class="Symbol">:</a> <a id="4612" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4617" class="Symbol">}</a> <a id="4619" class="Symbol">(</a><a id="4620" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4620" class="Bound">A</a> <a id="4622" class="Symbol">:</a> <a id="4624" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="4627" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4604" class="Bound">l1</a><a id="4629" class="Symbol">)</a>
  <a id="4633" class="Keyword">where</a>

  <a id="4642" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4642" class="Function">is-eilenberg-mac-lane-space-Ab</a> <a id="4673" class="Symbol">:</a>
    <a id="4679" class="Symbol">(</a><a id="4680" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4680" class="Bound">n</a> <a id="4682" class="Symbol">:</a> <a id="4684" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="4685" class="Symbol">)</a> <a id="4687" class="Symbol">(</a><a id="4688" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4688" class="Bound">X</a> <a id="4690" class="Symbol">:</a> <a id="4692" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4705" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4607" class="Bound">l2</a><a id="4707" class="Symbol">)</a> <a id="4709" class="Symbol">→</a> <a id="4711" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4714" class="Symbol">(</a><a id="4715" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4604" class="Bound">l1</a> <a id="4718" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4720" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4607" class="Bound">l2</a><a id="4722" class="Symbol">)</a>
  <a id="4726" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4642" class="Function">is-eilenberg-mac-lane-space-Ab</a> <a id="4757" class="Symbol">=</a>
    <a id="4763" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4174" class="Function">is-eilenberg-mac-lane-space-Group</a> <a id="4797" class="Symbol">(</a><a id="4798" href="group-theory.abelian-groups.html#2643" class="Function">group-Ab</a> <a id="4807" href="higher-group-theory.eilenberg-mac-lane-spaces.html#4620" class="Bound">A</a><a id="4808" class="Symbol">)</a>
</pre>