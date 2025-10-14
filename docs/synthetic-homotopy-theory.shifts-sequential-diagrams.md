# Shifts of sequential diagrams

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.shifts-sequential-diagrams</a> <a id="102" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.commuting-triangles-of-maps.html" class="Module">foundation.commuting-triangles-of-maps</a>
<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="385" class="Keyword">open</a> <a id="390" class="Keyword">import</a> <a id="397" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="423" class="Keyword">open</a> <a id="428" class="Keyword">import</a> <a id="435" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="457" class="Keyword">open</a> <a id="462" class="Keyword">import</a> <a id="469" href="foundation.homotopy-algebra.html" class="Module">foundation.homotopy-algebra</a>
<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="570" class="Keyword">open</a> <a id="575" class="Keyword">import</a> <a id="582" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="602" class="Keyword">open</a> <a id="607" class="Keyword">import</a> <a id="614" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="641" class="Keyword">open</a> <a id="646" class="Keyword">import</a> <a id="653" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>
<a id="698" class="Keyword">open</a> <a id="703" class="Keyword">import</a> <a id="710" href="foundation.whiskering-homotopies-concatenation.html" class="Module">foundation.whiskering-homotopies-concatenation</a>

<a id="758" class="Keyword">open</a> <a id="763" class="Keyword">import</a> <a id="770" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.cocones-under-sequential-diagrams</a>
<a id="830" class="Keyword">open</a> <a id="835" class="Keyword">import</a> <a id="842" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html" class="Module">synthetic-homotopy-theory.functoriality-sequential-colimits</a>
<a id="902" class="Keyword">open</a> <a id="907" class="Keyword">import</a> <a id="914" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.morphisms-sequential-diagrams</a>
<a id="970" class="Keyword">open</a> <a id="975" class="Keyword">import</a> <a id="982" href="synthetic-homotopy-theory.sequential-colimits.html" class="Module">synthetic-homotopy-theory.sequential-colimits</a>
<a id="1028" class="Keyword">open</a> <a id="1033" class="Keyword">import</a> <a id="1040" href="synthetic-homotopy-theory.sequential-diagrams.html" class="Module">synthetic-homotopy-theory.sequential-diagrams</a>
<a id="1086" class="Keyword">open</a> <a id="1091" class="Keyword">import</a> <a id="1098" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html" class="Module">synthetic-homotopy-theory.universal-property-sequential-colimits</a>
</pre>
</details>

## Idea

A
{{#concept "shift" Disambiguation="sequential diagram" Agda=shift-sequential-diagram}}
of a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md) is a
sequential diagram consisting of the types and maps shifted by one. It is also
denoted `A[1]`. This shifting can be iterated for any
[natural number](elementary-number-theory.natural-numbers.md) `k`; then the
resulting sequential diagram is denoted `A[k]`.

Similarly, a
{{#concept "shift" Disambiguation="morphism of sequential diagrams" Agda=shift-hom-sequential-diagram}}
of a
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
is a morphism from the shifted domain into the shifted codomain. In symbols,
given a morphism `f : A → B`, we have `f[k] : A[k] → B[k]`.

We also define shifts of
[cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) and
[homotopies of cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md),
which can additionally be unshifted.

Importantly the type of cocones under a sequential diagram is
[equivalent](foundation-core.equivalences.md) to the type of cocones under its
shift, which implies that the
[sequential colimit](synthetic-homotopy-theory.sequential-colimits.md) of a
shifted sequential diagram is equivalent to the colimit of the original diagram.

## Definitions

_Implementation note_: the constructions are defined by first defining a shift
by one, and then recursively shifting by one according to the argument. An
alternative would be to shift all data using
[addition](elementary-number-theory.addition-natural-numbers.md) on the natural
numbers.

However, addition computes only on one side, so we have a choice to make: given
a shift `k`, do we define the `n`-th level of the shifted structure to be the
`n+k`-th or `k+n`-th level of the original?

The former runs into issues already when defining the shifted sequence, since
`aₙ₊ₖ : Aₙ₊ₖ → A₍ₙ₊₁₎₊ₖ`, but we need a map of type `Aₙ₊ₖ → A₍ₙ₊ₖ₎₊₁`, which
forces us to introduce a
[transport](foundation-core.transport-along-identifications.md).

On the other hand, the latter requires transport when proving anything by
induction on `k` and doesn't satisfy the judgmental equality `A[0] ≐ A`, because
`A₍ₖ₊₁₎₊ₙ` is not `A₍ₖ₊ₙ₎₊₁` and `A₀₊ₙ` is not `Aₙ`, and it requires more
infrastructure for working with horizontal compositions in sequential colimit to
be formalized in terms of addition.

To contrast, defining the operations by induction does satisfy `A[0] ≐ A`, it
computes when proving properties by induction, which is the expected primary
use-case, and no further infrastructure is necessary.

### Shifts of sequential diagrams

Given a sequential diagram `A`

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯ ,
```

we can forget the first type and map to get the diagram

```text
     a₁      a₂
 A₁ ---> A₂ ---> ⋯ ,
```

which we call `A[1]`. Inductively, we define `A[k + 1] ≐ A[k][1]`.

<pre class="Agda"><a id="4157" class="Keyword">module</a> <a id="4164" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4164" class="Module">_</a>
  <a id="4168" class="Symbol">{</a><a id="4169" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4169" class="Bound">l1</a> <a id="4172" class="Symbol">:</a> <a id="4174" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4179" class="Symbol">}</a> <a id="4181" class="Symbol">(</a><a id="4182" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4182" class="Bound">A</a> <a id="4184" class="Symbol">:</a> <a id="4186" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="4205" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4169" class="Bound">l1</a><a id="4207" class="Symbol">)</a>
  <a id="4211" class="Keyword">where</a>

  <a id="4220" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="4250" class="Symbol">:</a> <a id="4252" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="4271" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4169" class="Bound">l1</a>
  <a id="4276" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4280" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="4310" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4310" class="Bound">n</a> <a id="4312" class="Symbol">=</a> <a id="4314" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="4340" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4182" class="Bound">A</a> <a id="4342" class="Symbol">(</a><a id="4343" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="4350" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4310" class="Bound">n</a><a id="4351" class="Symbol">)</a>
  <a id="4355" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4359" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="4389" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4389" class="Bound">n</a> <a id="4391" class="Symbol">=</a> <a id="4393" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="4416" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4182" class="Bound">A</a> <a id="4418" class="Symbol">(</a><a id="4419" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="4426" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4389" class="Bound">n</a><a id="4427" class="Symbol">)</a>

<a id="4430" class="Keyword">module</a> <a id="4437" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4437" class="Module">_</a>
  <a id="4441" class="Symbol">{</a><a id="4442" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4442" class="Bound">l1</a> <a id="4445" class="Symbol">:</a> <a id="4447" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4452" class="Symbol">}</a>
  <a id="4456" class="Keyword">where</a>

  <a id="4465" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="4490" class="Symbol">:</a> <a id="4492" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="4494" class="Symbol">→</a> <a id="4496" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="4515" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4442" class="Bound">l1</a> <a id="4518" class="Symbol">→</a> <a id="4520" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="4539" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4442" class="Bound">l1</a>
  <a id="4544" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="4569" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="4576" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4576" class="Bound">A</a> <a id="4578" class="Symbol">=</a> <a id="4580" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4576" class="Bound">A</a>
  <a id="4584" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="4609" class="Symbol">(</a><a id="4610" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="4617" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4617" class="Bound">k</a><a id="4618" class="Symbol">)</a> <a id="4620" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4620" class="Bound">A</a> <a id="4622" class="Symbol">=</a>
    <a id="4628" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="4658" class="Symbol">(</a><a id="4659" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="4684" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4617" class="Bound">k</a> <a id="4686" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4620" class="Bound">A</a><a id="4687" class="Symbol">)</a>
</pre>
### Shifts of morphisms of sequential diagrams

Given a morphism of sequential diagrams `f : A → B`

```text
        a₀      a₁
    A₀ ---> A₁ ---> A₂ ---> ⋯
    |       |       |
 f₀ |       | f₁    | f₂
    ∨       ∨       ∨
    B₀ ---> B₁ ---> B₂ ---> ⋯ ,
        b₀      b₁
```

we can drop the first square to get the morphism

```text
        a₁
    A₁ ---> A₂ ---> ⋯
    |       |
 f₁ |       | f₂
    ∨       ∨
    B₁ ---> B₂ ---> ⋯ ,
        b₁
```

which we call `f[1] : A[1] → B[1]`. Inductively, we define `f[k + 1] ≐ f[k][1]`.

<pre class="Agda"><a id="5243" class="Keyword">module</a> <a id="5250" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5250" class="Module">_</a>
  <a id="5254" class="Symbol">{</a><a id="5255" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5255" class="Bound">l1</a> <a id="5258" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5258" class="Bound">l2</a> <a id="5261" class="Symbol">:</a> <a id="5263" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5268" class="Symbol">}</a> <a id="5270" class="Symbol">{</a><a id="5271" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5271" class="Bound">A</a> <a id="5273" class="Symbol">:</a> <a id="5275" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="5294" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5255" class="Bound">l1</a><a id="5296" class="Symbol">}</a> <a id="5298" class="Symbol">(</a><a id="5299" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5299" class="Bound">B</a> <a id="5301" class="Symbol">:</a> <a id="5303" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="5322" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5258" class="Bound">l2</a><a id="5324" class="Symbol">)</a>
  <a id="5328" class="Symbol">(</a><a id="5329" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5329" class="Bound">f</a> <a id="5331" class="Symbol">:</a> <a id="5333" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a> <a id="5356" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5271" class="Bound">A</a> <a id="5358" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5299" class="Bound">B</a><a id="5359" class="Symbol">)</a>
  <a id="5363" class="Keyword">where</a>

  <a id="5372" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5372" class="Function">shift-once-hom-sequential-diagram</a> <a id="5406" class="Symbol">:</a>
    <a id="5412" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a>
      <a id="5441" class="Symbol">(</a> <a id="5443" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="5473" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5271" class="Bound">A</a><a id="5474" class="Symbol">)</a>
      <a id="5482" class="Symbol">(</a> <a id="5484" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="5514" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5299" class="Bound">B</a><a id="5515" class="Symbol">)</a>
  <a id="5519" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5523" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5372" class="Function">shift-once-hom-sequential-diagram</a> <a id="5557" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5557" class="Bound">n</a> <a id="5559" class="Symbol">=</a>
    <a id="5565" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#2693" class="Function">map-hom-sequential-diagram</a> <a id="5592" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5299" class="Bound">B</a> <a id="5594" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5329" class="Bound">f</a> <a id="5596" class="Symbol">(</a><a id="5597" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="5604" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5557" class="Bound">n</a><a id="5605" class="Symbol">)</a>
  <a id="5609" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5613" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5372" class="Function">shift-once-hom-sequential-diagram</a> <a id="5647" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5647" class="Bound">n</a> <a id="5649" class="Symbol">=</a>
    <a id="5655" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#2839" class="Function">naturality-map-hom-sequential-diagram</a> <a id="5693" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5299" class="Bound">B</a> <a id="5695" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5329" class="Bound">f</a> <a id="5697" class="Symbol">(</a><a id="5698" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="5705" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5647" class="Bound">n</a><a id="5706" class="Symbol">)</a>

<a id="5709" class="Keyword">module</a> <a id="5716" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5716" class="Module">_</a>
  <a id="5720" class="Symbol">{</a><a id="5721" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5721" class="Bound">l1</a> <a id="5724" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5724" class="Bound">l2</a> <a id="5727" class="Symbol">:</a> <a id="5729" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5734" class="Symbol">}</a> <a id="5736" class="Symbol">{</a><a id="5737" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5737" class="Bound">A</a> <a id="5739" class="Symbol">:</a> <a id="5741" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="5760" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5721" class="Bound">l1</a><a id="5762" class="Symbol">}</a> <a id="5764" class="Symbol">(</a><a id="5765" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5765" class="Bound">B</a> <a id="5767" class="Symbol">:</a> <a id="5769" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="5788" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5724" class="Bound">l2</a><a id="5790" class="Symbol">)</a>
  <a id="5794" class="Keyword">where</a>

  <a id="5803" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5803" class="Function">shift-hom-sequential-diagram</a> <a id="5832" class="Symbol">:</a>
    <a id="5838" class="Symbol">(</a><a id="5839" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5839" class="Bound">k</a> <a id="5841" class="Symbol">:</a> <a id="5843" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="5844" class="Symbol">)</a> <a id="5846" class="Symbol">→</a>
    <a id="5852" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a> <a id="5875" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5737" class="Bound">A</a> <a id="5877" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5765" class="Bound">B</a> <a id="5879" class="Symbol">→</a>
    <a id="5885" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a>
      <a id="5914" class="Symbol">(</a> <a id="5916" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="5941" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5839" class="Bound">k</a> <a id="5943" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5737" class="Bound">A</a><a id="5944" class="Symbol">)</a>
      <a id="5952" class="Symbol">(</a> <a id="5954" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="5979" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5839" class="Bound">k</a> <a id="5981" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5765" class="Bound">B</a><a id="5982" class="Symbol">)</a>
  <a id="5986" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5803" class="Function">shift-hom-sequential-diagram</a> <a id="6015" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="6022" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6022" class="Bound">f</a> <a id="6024" class="Symbol">=</a> <a id="6026" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6022" class="Bound">f</a>
  <a id="6030" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5803" class="Function">shift-hom-sequential-diagram</a> <a id="6059" class="Symbol">(</a><a id="6060" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="6067" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6067" class="Bound">k</a><a id="6068" class="Symbol">)</a> <a id="6070" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6070" class="Bound">f</a> <a id="6072" class="Symbol">=</a>
    <a id="6078" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5372" class="Function">shift-once-hom-sequential-diagram</a>
      <a id="6118" class="Symbol">(</a> <a id="6120" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="6145" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6067" class="Bound">k</a> <a id="6147" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5765" class="Bound">B</a><a id="6148" class="Symbol">)</a>
      <a id="6156" class="Symbol">(</a> <a id="6158" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#5803" class="Function">shift-hom-sequential-diagram</a> <a id="6187" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6067" class="Bound">k</a> <a id="6189" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6070" class="Bound">f</a><a id="6190" class="Symbol">)</a>
</pre>
### Shifts of cocones under sequential diagrams

Given a cocone `c`

```text
      a₀      a₁
  A₀ ---> A₁ ---> A₂ ---> ⋯
   \      |      /
    \     |     /
  i₀ \    | i₁ / i₂
      \   |   /
       ∨  ∨  ∨
          X
```

under `A`, we may forget the first inclusion and homotopy to get the cocone

```text
         a₁
     A₁ ---> A₂ ---> ⋯
     |      /
     |     /
  i₁ |    / i₂
     |   /
     ∨  ∨
     X
```

under `A[1]`. We denote this cocone `c[1]`. Inductively, we define
`c[k + 1] ≐ c[k][1]`.

<pre class="Agda"><a id="6717" class="Keyword">module</a> <a id="6724" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6724" class="Module">_</a>
  <a id="6728" class="Symbol">{</a><a id="6729" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6729" class="Bound">l1</a> <a id="6732" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6732" class="Bound">l2</a> <a id="6735" class="Symbol">:</a> <a id="6737" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6742" class="Symbol">}</a> <a id="6744" class="Symbol">{</a><a id="6745" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6745" class="Bound">A</a> <a id="6747" class="Symbol">:</a> <a id="6749" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="6768" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6729" class="Bound">l1</a><a id="6770" class="Symbol">}</a>
  <a id="6774" class="Symbol">{</a><a id="6775" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6775" class="Bound">X</a> <a id="6777" class="Symbol">:</a> <a id="6779" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6782" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6732" class="Bound">l2</a><a id="6784" class="Symbol">}</a> <a id="6786" class="Symbol">(</a><a id="6787" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6787" class="Bound">c</a> <a id="6789" class="Symbol">:</a> <a id="6791" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="6817" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6745" class="Bound">A</a> <a id="6819" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6775" class="Bound">X</a><a id="6820" class="Symbol">)</a>
  <a id="6824" class="Keyword">where</a>

  <a id="6833" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="6870" class="Symbol">:</a>
    <a id="6876" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="6902" class="Symbol">(</a><a id="6903" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="6933" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6745" class="Bound">A</a><a id="6934" class="Symbol">)</a> <a id="6936" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6775" class="Bound">X</a>
  <a id="6940" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="6944" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="6981" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6981" class="Bound">n</a> <a id="6983" class="Symbol">=</a>
    <a id="6989" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2233" class="Function">map-cocone-sequential-diagram</a> <a id="7019" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6787" class="Bound">c</a> <a id="7021" class="Symbol">(</a><a id="7022" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="7029" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6981" class="Bound">n</a><a id="7030" class="Symbol">)</a>
  <a id="7034" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7038" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="7075" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7075" class="Bound">n</a> <a id="7077" class="Symbol">=</a>
    <a id="7083" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2352" class="Function">coherence-cocone-sequential-diagram</a> <a id="7119" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6787" class="Bound">c</a> <a id="7121" class="Symbol">(</a><a id="7122" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="7129" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7075" class="Bound">n</a><a id="7130" class="Symbol">)</a>

<a id="7133" class="Keyword">module</a> <a id="7140" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7140" class="Module">_</a>
  <a id="7144" class="Symbol">{</a><a id="7145" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7145" class="Bound">l1</a> <a id="7148" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7148" class="Bound">l2</a> <a id="7151" class="Symbol">:</a> <a id="7153" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7158" class="Symbol">}</a> <a id="7160" class="Symbol">{</a><a id="7161" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7161" class="Bound">A</a> <a id="7163" class="Symbol">:</a> <a id="7165" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="7184" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7145" class="Bound">l1</a><a id="7186" class="Symbol">}</a>
  <a id="7190" class="Symbol">{</a><a id="7191" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7191" class="Bound">X</a> <a id="7193" class="Symbol">:</a> <a id="7195" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="7198" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7148" class="Bound">l2</a><a id="7200" class="Symbol">}</a>
  <a id="7204" class="Keyword">where</a>

  <a id="7213" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="7245" class="Symbol">:</a>
    <a id="7251" class="Symbol">(</a><a id="7252" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7252" class="Bound">k</a> <a id="7254" class="Symbol">:</a> <a id="7256" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="7257" class="Symbol">)</a> <a id="7259" class="Symbol">→</a>
    <a id="7265" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="7291" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7161" class="Bound">A</a> <a id="7293" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7191" class="Bound">X</a> <a id="7295" class="Symbol">→</a>
    <a id="7301" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="7327" class="Symbol">(</a><a id="7328" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="7353" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7252" class="Bound">k</a> <a id="7355" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7161" class="Bound">A</a><a id="7356" class="Symbol">)</a> <a id="7358" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7191" class="Bound">X</a>
  <a id="7362" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="7394" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="7401" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7401" class="Bound">c</a> <a id="7403" class="Symbol">=</a>
    <a id="7409" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7401" class="Bound">c</a>
  <a id="7413" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="7445" class="Symbol">(</a><a id="7446" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="7453" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7453" class="Bound">k</a><a id="7454" class="Symbol">)</a> <a id="7456" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7456" class="Bound">c</a> <a id="7458" class="Symbol">=</a>
    <a id="7464" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a>
      <a id="7507" class="Symbol">(</a> <a id="7509" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="7541" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7453" class="Bound">k</a> <a id="7543" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7456" class="Bound">c</a><a id="7544" class="Symbol">)</a>
</pre>
### Unshifts of cocones under sequential diagrams

Conversely, given a cocone `c`

```text
         a₁
     A₁ ---> A₂ ---> ⋯
     |      /
     |     /
  i₁ |    / i₂
     |   /
     ∨  ∨
     X
```

under `A[1]`, we may prepend a map

```text
           a₀      a₁
       A₀ ---> A₁ ---> A₂ ---> ⋯
        \      |      /
         \     |     /
  i₁ ∘ a₀ \    | i₁ / i₂
           \   |   /
            ∨  ∨  ∨
               X
```

which commutes by reflexivity, giving us a cocone under `A`, which we call
`c[-1]`.

Notice that by restricting the type of `c` to be the cocones under an already
shifted diagram, we ensure that unshifting cannot get out of bounds of the
original diagram.

Inductively, we define `c[-(k + 1)] ≐ c[-1][-k]`. One might expect that
following the pattern of shifts, this should be `c[-k][-1]`, but recall that we
only know how to unshift a cocone under `A[n]` by `n`; since this `c` is under
`A[k][1]`, we first need to unshift by 1 to get `c[-1]` under `A[k]`, and only
then we can unshift by `k` to get `c[-1][-k]` under `A`.

<pre class="Agda"><a id="8619" class="Keyword">module</a> <a id="8626" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8626" class="Module">_</a>
  <a id="8630" class="Symbol">{</a><a id="8631" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8631" class="Bound">l1</a> <a id="8634" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8634" class="Bound">l2</a> <a id="8637" class="Symbol">:</a> <a id="8639" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8644" class="Symbol">}</a> <a id="8646" class="Symbol">(</a><a id="8647" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8647" class="Bound">A</a> <a id="8649" class="Symbol">:</a> <a id="8651" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="8670" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8631" class="Bound">l1</a><a id="8672" class="Symbol">)</a>
  <a id="8676" class="Symbol">{</a><a id="8677" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8677" class="Bound">X</a> <a id="8679" class="Symbol">:</a> <a id="8681" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="8684" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8634" class="Bound">l2</a><a id="8686" class="Symbol">}</a>
  <a id="8690" class="Symbol">(</a><a id="8691" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8691" class="Bound">c</a> <a id="8693" class="Symbol">:</a> <a id="8695" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="8721" class="Symbol">(</a><a id="8722" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="8752" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8647" class="Bound">A</a><a id="8753" class="Symbol">)</a> <a id="8755" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8677" class="Bound">X</a><a id="8756" class="Symbol">)</a>
  <a id="8760" class="Keyword">where</a>

  <a id="8769" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="8808" class="Symbol">:</a>
    <a id="8814" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="8840" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8647" class="Bound">A</a> <a id="8842" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8677" class="Bound">X</a>
  <a id="8846" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8850" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="8889" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="8896" class="Symbol">=</a>
    <a id="8902" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2233" class="Function">map-cocone-sequential-diagram</a> <a id="8932" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8691" class="Bound">c</a> <a id="8934" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="8941" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="8943" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="8966" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8647" class="Bound">A</a> <a id="8968" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a>
  <a id="8977" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8981" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="9020" class="Symbol">(</a><a id="9021" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="9028" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9028" class="Bound">n</a><a id="9029" class="Symbol">)</a> <a id="9031" class="Symbol">=</a>
    <a id="9037" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2233" class="Function">map-cocone-sequential-diagram</a> <a id="9067" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8691" class="Bound">c</a> <a id="9069" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9028" class="Bound">n</a>
  <a id="9073" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="9077" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="9116" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="9123" class="Symbol">=</a>
    <a id="9129" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="9141" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="9145" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="9184" class="Symbol">(</a><a id="9185" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="9192" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9192" class="Bound">n</a><a id="9193" class="Symbol">)</a> <a id="9195" class="Symbol">=</a>
    <a id="9201" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2352" class="Function">coherence-cocone-sequential-diagram</a> <a id="9237" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8691" class="Bound">c</a> <a id="9239" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9192" class="Bound">n</a>

<a id="9242" class="Keyword">module</a> <a id="9249" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9249" class="Module">_</a>
  <a id="9253" class="Symbol">{</a><a id="9254" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9254" class="Bound">l1</a> <a id="9257" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9257" class="Bound">l2</a> <a id="9260" class="Symbol">:</a> <a id="9262" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9267" class="Symbol">}</a> <a id="9269" class="Symbol">(</a><a id="9270" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9270" class="Bound">A</a> <a id="9272" class="Symbol">:</a> <a id="9274" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="9293" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9254" class="Bound">l1</a><a id="9295" class="Symbol">)</a>
  <a id="9299" class="Symbol">{</a><a id="9300" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9300" class="Bound">X</a> <a id="9302" class="Symbol">:</a> <a id="9304" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="9307" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9257" class="Bound">l2</a><a id="9309" class="Symbol">}</a>
  <a id="9313" class="Keyword">where</a>

  <a id="9322" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="9356" class="Symbol">:</a>
    <a id="9362" class="Symbol">(</a><a id="9363" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9363" class="Bound">k</a> <a id="9365" class="Symbol">:</a> <a id="9367" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="9368" class="Symbol">)</a> <a id="9370" class="Symbol">→</a>
    <a id="9376" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="9402" class="Symbol">(</a><a id="9403" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="9428" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9363" class="Bound">k</a> <a id="9430" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9270" class="Bound">A</a><a id="9431" class="Symbol">)</a> <a id="9433" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9300" class="Bound">X</a> <a id="9435" class="Symbol">→</a>
    <a id="9441" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="9467" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9270" class="Bound">A</a> <a id="9469" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9300" class="Bound">X</a>
  <a id="9473" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="9507" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="9514" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9514" class="Bound">c</a> <a id="9516" class="Symbol">=</a>
    <a id="9522" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9514" class="Bound">c</a>
  <a id="9526" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="9560" class="Symbol">(</a><a id="9561" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="9568" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9568" class="Bound">k</a><a id="9569" class="Symbol">)</a> <a id="9571" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9571" class="Bound">c</a> <a id="9573" class="Symbol">=</a>
    <a id="9579" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="9613" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9568" class="Bound">k</a>
      <a id="9621" class="Symbol">(</a> <a id="9623" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a>
        <a id="9670" class="Symbol">(</a> <a id="9672" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="9697" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9568" class="Bound">k</a> <a id="9699" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9270" class="Bound">A</a><a id="9700" class="Symbol">)</a>
        <a id="9710" class="Symbol">(</a> <a id="9712" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9571" class="Bound">c</a><a id="9713" class="Symbol">))</a>
</pre>
### Shifts of homotopies of cocones under sequential diagrams

Given cocones `c` and `c'` under `A`

```text
     a₀      a₁                   a₀      a₁
 A₀ ---> A₁ ---> A₂ ---> ⋯    A₀ ---> A₁ ---> A₂ ---> ⋯
  \      |      /              \      |      /
   \     | i₁  /                \     | i'₁ /
 i₀ \    |    / i₂     ~     i'₀ \    |    / i'₂
     \   |   /                    \   |   /
      ∨  ∨  ∨                      ∨  ∨  ∨
         X                            X
```

and a homotopy `H : c ~ c'` between them, we can again forget the first homotopy
of maps and coherence to get the homotopy `H[1] : c[1] ~ c'[1]`. Inductively, we
define `H[k + 1] ≐ H[k][1]`.

<pre class="Agda"><a id="10405" class="Keyword">module</a> <a id="10412" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10412" class="Module">_</a>
  <a id="10416" class="Symbol">{</a><a id="10417" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10417" class="Bound">l1</a> <a id="10420" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10420" class="Bound">l2</a> <a id="10423" class="Symbol">:</a> <a id="10425" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="10430" class="Symbol">}</a> <a id="10432" class="Symbol">{</a><a id="10433" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10433" class="Bound">A</a> <a id="10435" class="Symbol">:</a> <a id="10437" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="10456" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10417" class="Bound">l1</a><a id="10458" class="Symbol">}</a> <a id="10460" class="Symbol">{</a><a id="10461" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10461" class="Bound">X</a> <a id="10463" class="Symbol">:</a> <a id="10465" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="10468" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10420" class="Bound">l2</a><a id="10470" class="Symbol">}</a>
  <a id="10474" class="Symbol">{</a><a id="10475" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10475" class="Bound">c</a> <a id="10477" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10477" class="Bound">c&#39;</a> <a id="10480" class="Symbol">:</a> <a id="10482" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="10508" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10433" class="Bound">A</a> <a id="10510" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10461" class="Bound">X</a><a id="10511" class="Symbol">}</a>
  <a id="10515" class="Symbol">(</a><a id="10516" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10516" class="Bound">H</a> <a id="10518" class="Symbol">:</a> <a id="10520" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a> <a id="10551" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10475" class="Bound">c</a> <a id="10553" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10477" class="Bound">c&#39;</a><a id="10555" class="Symbol">)</a>
  <a id="10559" class="Keyword">where</a>

  <a id="10568" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10568" class="Function">shift-once-htpy-cocone-sequential-diagram</a> <a id="10610" class="Symbol">:</a>
    <a id="10616" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="10653" class="Symbol">(</a> <a id="10655" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="10692" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10475" class="Bound">c</a><a id="10693" class="Symbol">)</a>
      <a id="10701" class="Symbol">(</a> <a id="10703" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="10740" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10477" class="Bound">c&#39;</a><a id="10742" class="Symbol">)</a>
  <a id="10746" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="10750" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10568" class="Function">shift-once-htpy-cocone-sequential-diagram</a> <a id="10792" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10792" class="Bound">n</a> <a id="10794" class="Symbol">=</a>
    <a id="10800" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#4466" class="Function">htpy-htpy-cocone-sequential-diagram</a> <a id="10836" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10516" class="Bound">H</a> <a id="10838" class="Symbol">(</a><a id="10839" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="10846" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10792" class="Bound">n</a><a id="10847" class="Symbol">)</a>
  <a id="10851" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="10855" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10568" class="Function">shift-once-htpy-cocone-sequential-diagram</a> <a id="10897" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10897" class="Bound">n</a> <a id="10899" class="Symbol">=</a>
    <a id="10905" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#4653" class="Function">coherence-htpy-htpy-cocone-sequential-diagram</a>
      <a id="10957" class="Symbol">(</a> <a id="10959" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10516" class="Bound">H</a><a id="10960" class="Symbol">)</a>
      <a id="10968" class="Symbol">(</a> <a id="10970" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="10977" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10897" class="Bound">n</a><a id="10978" class="Symbol">)</a>

<a id="10981" class="Keyword">module</a> <a id="10988" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10988" class="Module">_</a>
  <a id="10992" class="Symbol">{</a><a id="10993" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10993" class="Bound">l1</a> <a id="10996" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10996" class="Bound">l2</a> <a id="10999" class="Symbol">:</a> <a id="11001" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="11006" class="Symbol">}</a> <a id="11008" class="Symbol">{</a><a id="11009" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11009" class="Bound">A</a> <a id="11011" class="Symbol">:</a> <a id="11013" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="11032" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10993" class="Bound">l1</a><a id="11034" class="Symbol">}</a> <a id="11036" class="Symbol">{</a><a id="11037" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11037" class="Bound">X</a> <a id="11039" class="Symbol">:</a> <a id="11041" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="11044" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10996" class="Bound">l2</a><a id="11046" class="Symbol">}</a>
  <a id="11050" class="Symbol">{</a><a id="11051" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11051" class="Bound">c</a> <a id="11053" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11053" class="Bound">c&#39;</a> <a id="11056" class="Symbol">:</a> <a id="11058" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="11084" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11009" class="Bound">A</a> <a id="11086" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11037" class="Bound">X</a><a id="11087" class="Symbol">}</a>
  <a id="11091" class="Keyword">where</a>

  <a id="11100" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11100" class="Function">shift-htpy-cocone-sequential-diagram</a> <a id="11137" class="Symbol">:</a>
    <a id="11143" class="Symbol">(</a><a id="11144" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11144" class="Bound">k</a> <a id="11146" class="Symbol">:</a> <a id="11148" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="11149" class="Symbol">)</a> <a id="11151" class="Symbol">→</a>
    <a id="11157" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a> <a id="11188" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11051" class="Bound">c</a> <a id="11190" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11053" class="Bound">c&#39;</a> <a id="11193" class="Symbol">→</a>
    <a id="11199" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="11236" class="Symbol">(</a> <a id="11238" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="11270" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11144" class="Bound">k</a> <a id="11272" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11051" class="Bound">c</a><a id="11273" class="Symbol">)</a>
      <a id="11281" class="Symbol">(</a> <a id="11283" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="11315" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11144" class="Bound">k</a> <a id="11317" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11053" class="Bound">c&#39;</a><a id="11319" class="Symbol">)</a>
  <a id="11323" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11100" class="Function">shift-htpy-cocone-sequential-diagram</a> <a id="11360" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="11367" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11367" class="Bound">H</a> <a id="11369" class="Symbol">=</a>
    <a id="11375" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11367" class="Bound">H</a>
  <a id="11379" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11100" class="Function">shift-htpy-cocone-sequential-diagram</a> <a id="11416" class="Symbol">(</a><a id="11417" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="11424" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11424" class="Bound">k</a><a id="11425" class="Symbol">)</a> <a id="11427" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11427" class="Bound">H</a> <a id="11429" class="Symbol">=</a>
    <a id="11435" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10568" class="Function">shift-once-htpy-cocone-sequential-diagram</a>
      <a id="11483" class="Symbol">(</a> <a id="11485" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11100" class="Function">shift-htpy-cocone-sequential-diagram</a> <a id="11522" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11424" class="Bound">k</a> <a id="11524" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#11427" class="Bound">H</a><a id="11525" class="Symbol">)</a>
</pre>
### Unshifts of homotopies of cocones under sequential diagrams

Similarly to unshifting cocones, we can recover the first homotopy and coherence
to unshift a homotopy of cocones. Given two cocones `c`, `c'` under `A[1]`

```text
         a₁                     a₁
     A₁ ---> A₂ ---> ⋯      A₁ ---> A₂ ---> ⋯
     |      /               |      /
     |     /                |     /
  i₁ |    / i₂     ~    i'₁ |    / i'₂
     |   /                  |   /
     ∨  ∨                   ∨  ∨
     X                      X
```

and a homotopy `H : c ~ c'`, we need to show that `i₁ ∘ a₀ ~ i'₁ ∘ a₀`. This can
be obtained by whiskering `H₀ ·r a₀`, which makes the coherence trivial.

Inductively, we define `H[-(k + 1)] ≐ H[-1][-k]`.

<pre class="Agda"><a id="12271" class="Keyword">module</a> <a id="12278" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12278" class="Module">_</a>
  <a id="12282" class="Symbol">{</a><a id="12283" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12283" class="Bound">l1</a> <a id="12286" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12286" class="Bound">l2</a> <a id="12289" class="Symbol">:</a> <a id="12291" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="12296" class="Symbol">}</a> <a id="12298" class="Symbol">{</a><a id="12299" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12299" class="Bound">A</a> <a id="12301" class="Symbol">:</a> <a id="12303" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="12322" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12283" class="Bound">l1</a><a id="12324" class="Symbol">}</a> <a id="12326" class="Symbol">{</a><a id="12327" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12327" class="Bound">X</a> <a id="12329" class="Symbol">:</a> <a id="12331" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="12334" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12286" class="Bound">l2</a><a id="12336" class="Symbol">}</a>
  <a id="12340" class="Symbol">{</a><a id="12341" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12341" class="Bound">c</a> <a id="12343" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12343" class="Bound">c&#39;</a> <a id="12346" class="Symbol">:</a> <a id="12348" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="12374" class="Symbol">(</a><a id="12375" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="12405" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12299" class="Bound">A</a><a id="12406" class="Symbol">)</a> <a id="12408" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12327" class="Bound">X</a><a id="12409" class="Symbol">}</a>
  <a id="12413" class="Symbol">(</a><a id="12414" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12414" class="Bound">H</a> <a id="12416" class="Symbol">:</a> <a id="12418" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a> <a id="12449" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12341" class="Bound">c</a> <a id="12451" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12343" class="Bound">c&#39;</a><a id="12453" class="Symbol">)</a>
  <a id="12457" class="Keyword">where</a>

  <a id="12466" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12466" class="Function">unshift-once-htpy-cocone-sequential-diagram</a> <a id="12510" class="Symbol">:</a>
    <a id="12516" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="12553" class="Symbol">(</a> <a id="12555" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="12594" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12299" class="Bound">A</a> <a id="12596" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12341" class="Bound">c</a><a id="12597" class="Symbol">)</a>
      <a id="12605" class="Symbol">(</a> <a id="12607" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="12646" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12299" class="Bound">A</a> <a id="12648" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12343" class="Bound">c&#39;</a><a id="12650" class="Symbol">)</a>
  <a id="12654" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="12658" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12466" class="Function">unshift-once-htpy-cocone-sequential-diagram</a> <a id="12702" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="12709" class="Symbol">=</a>
    <a id="12715" class="Symbol">(</a> <a id="12717" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#4466" class="Function">htpy-htpy-cocone-sequential-diagram</a> <a id="12753" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12414" class="Bound">H</a> <a id="12755" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="12761" class="Symbol">)</a> <a id="12763" href="foundation.whiskering-homotopies-composition.html#2725" class="Function Operator">·r</a>
    <a id="12770" class="Symbol">(</a> <a id="12772" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="12795" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12299" class="Bound">A</a> <a id="12797" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="12803" class="Symbol">)</a>
  <a id="12807" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="12811" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12466" class="Function">unshift-once-htpy-cocone-sequential-diagram</a> <a id="12855" class="Symbol">(</a><a id="12856" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="12863" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12863" class="Bound">n</a><a id="12864" class="Symbol">)</a> <a id="12866" class="Symbol">=</a>
    <a id="12872" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#4466" class="Function">htpy-htpy-cocone-sequential-diagram</a> <a id="12908" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12414" class="Bound">H</a> <a id="12910" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12863" class="Bound">n</a>
  <a id="12914" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="12918" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12466" class="Function">unshift-once-htpy-cocone-sequential-diagram</a> <a id="12962" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="12969" class="Symbol">=</a>
    <a id="12975" href="foundation-core.homotopies.html#5244" class="Function">inv-htpy-right-unit-htpy</a>
  <a id="13002" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="13006" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12466" class="Function">unshift-once-htpy-cocone-sequential-diagram</a> <a id="13050" class="Symbol">(</a><a id="13051" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="13058" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13058" class="Bound">n</a><a id="13059" class="Symbol">)</a> <a id="13061" class="Symbol">=</a>
    <a id="13067" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#4653" class="Function">coherence-htpy-htpy-cocone-sequential-diagram</a> <a id="13113" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12414" class="Bound">H</a> <a id="13115" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13058" class="Bound">n</a>

<a id="13118" class="Keyword">module</a> <a id="13125" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13125" class="Module">_</a>
  <a id="13129" class="Symbol">{</a><a id="13130" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13130" class="Bound">l1</a> <a id="13133" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13133" class="Bound">l2</a> <a id="13136" class="Symbol">:</a> <a id="13138" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="13143" class="Symbol">}</a> <a id="13145" class="Symbol">{</a><a id="13146" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13146" class="Bound">A</a> <a id="13148" class="Symbol">:</a> <a id="13150" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="13169" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13130" class="Bound">l1</a><a id="13171" class="Symbol">}</a> <a id="13173" class="Symbol">{</a><a id="13174" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13174" class="Bound">X</a> <a id="13176" class="Symbol">:</a> <a id="13178" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="13181" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13133" class="Bound">l2</a><a id="13183" class="Symbol">}</a>
  <a id="13187" class="Keyword">where</a>

  <a id="13196" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13196" class="Function">unshift-htpy-cocone-sequential-diagram</a> <a id="13235" class="Symbol">:</a>
    <a id="13241" class="Symbol">(</a><a id="13242" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13242" class="Bound">k</a> <a id="13244" class="Symbol">:</a> <a id="13246" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="13247" class="Symbol">)</a> <a id="13249" class="Symbol">→</a>
    <a id="13255" class="Symbol">{</a><a id="13256" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13256" class="Bound">c</a> <a id="13258" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13258" class="Bound">c&#39;</a> <a id="13261" class="Symbol">:</a> <a id="13263" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="13289" class="Symbol">(</a><a id="13290" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="13315" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13242" class="Bound">k</a> <a id="13317" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13146" class="Bound">A</a><a id="13318" class="Symbol">)</a> <a id="13320" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13174" class="Bound">X</a><a id="13321" class="Symbol">}</a> <a id="13323" class="Symbol">→</a>
    <a id="13329" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a> <a id="13360" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13256" class="Bound">c</a> <a id="13362" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13258" class="Bound">c&#39;</a> <a id="13365" class="Symbol">→</a>
    <a id="13371" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="13408" class="Symbol">(</a> <a id="13410" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="13444" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13146" class="Bound">A</a> <a id="13446" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13242" class="Bound">k</a> <a id="13448" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13256" class="Bound">c</a><a id="13449" class="Symbol">)</a>
      <a id="13457" class="Symbol">(</a> <a id="13459" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="13493" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13146" class="Bound">A</a> <a id="13495" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13242" class="Bound">k</a> <a id="13497" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13258" class="Bound">c&#39;</a><a id="13499" class="Symbol">)</a>
  <a id="13503" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13196" class="Function">unshift-htpy-cocone-sequential-diagram</a> <a id="13542" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="13549" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13549" class="Bound">H</a> <a id="13551" class="Symbol">=</a>
    <a id="13557" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13549" class="Bound">H</a>
  <a id="13561" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13196" class="Function">unshift-htpy-cocone-sequential-diagram</a> <a id="13600" class="Symbol">(</a><a id="13601" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="13608" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13608" class="Bound">k</a><a id="13609" class="Symbol">)</a> <a id="13611" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13611" class="Bound">H</a> <a id="13613" class="Symbol">=</a>
    <a id="13619" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13196" class="Function">unshift-htpy-cocone-sequential-diagram</a> <a id="13658" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13608" class="Bound">k</a>
      <a id="13666" class="Symbol">(</a><a id="13667" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#12466" class="Function">unshift-once-htpy-cocone-sequential-diagram</a> <a id="13711" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13611" class="Bound">H</a><a id="13712" class="Symbol">)</a>
</pre>
### Morphisms from sequential diagrams into their shifts

The morphism is obtained by observing that the squares in the diagram

```text
        a₀      a₁
    A₀ ---> A₁ ---> A₂ ---> ⋯
    |       |       |
 a₀ |       | a₁    | a₂
    ∨       ∨       ∨
    A₁ ---> A₂ ---> A₃ ---> ⋯
        a₁      a₂
```

commute by reflexivity.

<pre class="Agda"><a id="14061" class="Keyword">module</a> <a id="14068" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14068" class="Module">_</a>
  <a id="14072" class="Symbol">{</a><a id="14073" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14073" class="Bound">l1</a> <a id="14076" class="Symbol">:</a> <a id="14078" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="14083" class="Symbol">}</a> <a id="14085" class="Symbol">(</a><a id="14086" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14086" class="Bound">A</a> <a id="14088" class="Symbol">:</a> <a id="14090" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="14109" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14073" class="Bound">l1</a><a id="14111" class="Symbol">)</a>
  <a id="14115" class="Keyword">where</a>

  <a id="14124" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="14158" class="Symbol">:</a>
    <a id="14164" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a>
      <a id="14193" class="Symbol">(</a> <a id="14195" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14086" class="Bound">A</a><a id="14196" class="Symbol">)</a>
      <a id="14204" class="Symbol">(</a> <a id="14206" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="14236" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14086" class="Bound">A</a><a id="14237" class="Symbol">)</a>
  <a id="14241" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="14245" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="14279" class="Symbol">=</a> <a id="14281" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="14304" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14086" class="Bound">A</a>
  <a id="14308" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="14312" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="14346" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14346" class="Bound">n</a> <a id="14348" class="Symbol">=</a> <a id="14350" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>

<a id="14361" class="Keyword">module</a> <a id="14368" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14368" class="Module">_</a>
  <a id="14372" class="Symbol">{</a><a id="14373" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14373" class="Bound">l1</a> <a id="14376" class="Symbol">:</a> <a id="14378" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="14383" class="Symbol">}</a> <a id="14385" class="Symbol">(</a><a id="14386" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14386" class="Bound">A</a> <a id="14388" class="Symbol">:</a> <a id="14390" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="14409" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14373" class="Bound">l1</a><a id="14411" class="Symbol">)</a>
  <a id="14415" class="Keyword">where</a>

  <a id="14424" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14424" class="Function">hom-shift-sequential-diagram</a> <a id="14453" class="Symbol">:</a>
    <a id="14459" class="Symbol">(</a><a id="14460" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14460" class="Bound">k</a> <a id="14462" class="Symbol">:</a> <a id="14464" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="14465" class="Symbol">)</a> <a id="14467" class="Symbol">→</a>
    <a id="14473" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a>
      <a id="14502" class="Symbol">(</a> <a id="14504" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14386" class="Bound">A</a><a id="14505" class="Symbol">)</a>
      <a id="14513" class="Symbol">(</a> <a id="14515" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="14540" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14460" class="Bound">k</a> <a id="14542" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14386" class="Bound">A</a><a id="14543" class="Symbol">)</a>
  <a id="14547" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14424" class="Function">hom-shift-sequential-diagram</a> <a id="14576" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="14583" class="Symbol">=</a> <a id="14585" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#3242" class="Function">id-hom-sequential-diagram</a> <a id="14611" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14386" class="Bound">A</a>
  <a id="14615" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14424" class="Function">hom-shift-sequential-diagram</a> <a id="14644" class="Symbol">(</a><a id="14645" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="14652" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14652" class="Bound">k</a><a id="14653" class="Symbol">)</a> <a id="14655" class="Symbol">=</a>
    <a id="14661" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#4579" class="Function">comp-hom-sequential-diagram</a>
      <a id="14695" class="Symbol">(</a> <a id="14697" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14386" class="Bound">A</a><a id="14698" class="Symbol">)</a>
      <a id="14706" class="Symbol">(</a> <a id="14708" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="14733" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14652" class="Bound">k</a> <a id="14735" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14386" class="Bound">A</a><a id="14736" class="Symbol">)</a>
      <a id="14744" class="Symbol">(</a> <a id="14746" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="14771" class="Symbol">(</a><a id="14772" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="14779" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14652" class="Bound">k</a><a id="14780" class="Symbol">)</a> <a id="14782" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14386" class="Bound">A</a><a id="14783" class="Symbol">)</a>
      <a id="14791" class="Symbol">(</a> <a id="14793" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a>
        <a id="14835" class="Symbol">(</a> <a id="14837" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="14862" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14652" class="Bound">k</a> <a id="14864" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14386" class="Bound">A</a><a id="14865" class="Symbol">))</a>
      <a id="14874" class="Symbol">(</a> <a id="14876" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14424" class="Function">hom-shift-sequential-diagram</a> <a id="14905" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14652" class="Bound">k</a><a id="14906" class="Symbol">)</a>
</pre>
## Properties

### The type of cocones under a sequential diagram is equivalent to the type of cocones under its shift

This is shown by proving that shifting and unshifting of cocones are mutually
inverse operations.

To show that `shift ∘ unshift ~ id` is trivial, since the first step synthesizes
some data for the first level, which the second step promptly forgets.

In the inductive step, we need to show `c[-(k + 1)][k + 1] ~ c`. The left-hand
side computes to `c[-1][-k][k][1]`, which is homotopic to `c[-1][1]` by shifting
the homotopy given by the inductive hypothesis, and that computes to `c`.

<pre class="Agda"><a id="15528" class="Keyword">module</a> <a id="15535" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15535" class="Module">_</a>
  <a id="15539" class="Symbol">{</a><a id="15540" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15540" class="Bound">l1</a> <a id="15543" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15543" class="Bound">l2</a> <a id="15546" class="Symbol">:</a> <a id="15548" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="15553" class="Symbol">}</a> <a id="15555" class="Symbol">{</a><a id="15556" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15556" class="Bound">A</a> <a id="15558" class="Symbol">:</a> <a id="15560" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="15579" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15540" class="Bound">l1</a><a id="15581" class="Symbol">}</a>
  <a id="15585" class="Symbol">{</a><a id="15586" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15586" class="Bound">X</a> <a id="15588" class="Symbol">:</a> <a id="15590" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="15593" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15543" class="Bound">l2</a><a id="15595" class="Symbol">}</a>
  <a id="15599" class="Keyword">where</a>

  <a id="15608" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15608" class="Function">htpy-is-section-unshift-once-cocone-sequential-diagram</a> <a id="15663" class="Symbol">:</a>
    <a id="15669" class="Symbol">(</a><a id="15670" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15670" class="Bound">c</a> <a id="15672" class="Symbol">:</a> <a id="15674" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="15700" class="Symbol">(</a><a id="15701" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="15731" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15556" class="Bound">A</a><a id="15732" class="Symbol">)</a> <a id="15734" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15586" class="Bound">X</a><a id="15735" class="Symbol">)</a> <a id="15737" class="Symbol">→</a>
    <a id="15743" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="15780" class="Symbol">(</a> <a id="15782" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a>
        <a id="15827" class="Symbol">(</a> <a id="15829" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="15868" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15556" class="Bound">A</a> <a id="15870" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15670" class="Bound">c</a><a id="15871" class="Symbol">))</a>
      <a id="15880" class="Symbol">(</a> <a id="15882" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15670" class="Bound">c</a><a id="15883" class="Symbol">)</a>
  <a id="15887" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15608" class="Function">htpy-is-section-unshift-once-cocone-sequential-diagram</a> <a id="15942" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15942" class="Bound">c</a> <a id="15944" class="Symbol">=</a>
    <a id="15950" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#10116" class="Function">refl-htpy-cocone-sequential-diagram</a> <a id="15986" class="Symbol">(</a><a id="15987" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="16017" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15556" class="Bound">A</a><a id="16018" class="Symbol">)</a> <a id="16020" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#15942" class="Bound">c</a>

<a id="16023" class="Keyword">module</a> <a id="16030" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16030" class="Module">_</a>
  <a id="16034" class="Symbol">{</a><a id="16035" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16035" class="Bound">l1</a> <a id="16038" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16038" class="Bound">l2</a> <a id="16041" class="Symbol">:</a> <a id="16043" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="16048" class="Symbol">}</a> <a id="16050" class="Symbol">{</a><a id="16051" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16051" class="Bound">A</a> <a id="16053" class="Symbol">:</a> <a id="16055" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="16074" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16035" class="Bound">l1</a><a id="16076" class="Symbol">}</a>
  <a id="16080" class="Symbol">{</a><a id="16081" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16081" class="Bound">X</a> <a id="16083" class="Symbol">:</a> <a id="16085" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="16088" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16038" class="Bound">l2</a><a id="16090" class="Symbol">}</a>
  <a id="16094" class="Keyword">where</a>

  <a id="16103" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16103" class="Function">htpy-is-section-unshift-cocone-sequential-diagram</a> <a id="16153" class="Symbol">:</a>
    <a id="16159" class="Symbol">(</a><a id="16160" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16160" class="Bound">k</a> <a id="16162" class="Symbol">:</a> <a id="16164" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="16165" class="Symbol">)</a> <a id="16167" class="Symbol">→</a>
    <a id="16173" class="Symbol">(</a><a id="16174" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16174" class="Bound">c</a> <a id="16176" class="Symbol">:</a> <a id="16178" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="16204" class="Symbol">(</a><a id="16205" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="16230" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16160" class="Bound">k</a> <a id="16232" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16051" class="Bound">A</a><a id="16233" class="Symbol">)</a> <a id="16235" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16081" class="Bound">X</a><a id="16236" class="Symbol">)</a> <a id="16238" class="Symbol">→</a>
    <a id="16244" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="16281" class="Symbol">(</a> <a id="16283" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="16315" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16160" class="Bound">k</a>
        <a id="16325" class="Symbol">(</a> <a id="16327" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="16361" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16051" class="Bound">A</a> <a id="16363" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16160" class="Bound">k</a> <a id="16365" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16174" class="Bound">c</a><a id="16366" class="Symbol">))</a>
      <a id="16375" class="Symbol">(</a> <a id="16377" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16174" class="Bound">c</a><a id="16378" class="Symbol">)</a>
  <a id="16382" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16103" class="Function">htpy-is-section-unshift-cocone-sequential-diagram</a> <a id="16432" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="16439" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16439" class="Bound">c</a> <a id="16441" class="Symbol">=</a>
    <a id="16447" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#10116" class="Function">refl-htpy-cocone-sequential-diagram</a> <a id="16483" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16051" class="Bound">A</a> <a id="16485" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16439" class="Bound">c</a>
  <a id="16489" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16103" class="Function">htpy-is-section-unshift-cocone-sequential-diagram</a> <a id="16539" class="Symbol">(</a><a id="16540" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="16547" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16547" class="Bound">k</a><a id="16548" class="Symbol">)</a> <a id="16550" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16550" class="Bound">c</a> <a id="16552" class="Symbol">=</a>
    <a id="16558" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#10568" class="Function">shift-once-htpy-cocone-sequential-diagram</a>
      <a id="16606" class="Symbol">(</a> <a id="16608" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16103" class="Function">htpy-is-section-unshift-cocone-sequential-diagram</a> <a id="16658" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16547" class="Bound">k</a>
        <a id="16668" class="Symbol">(</a> <a id="16670" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a>
          <a id="16719" class="Symbol">(</a> <a id="16721" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="16746" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16547" class="Bound">k</a> <a id="16748" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16051" class="Bound">A</a><a id="16749" class="Symbol">)</a>
          <a id="16761" class="Symbol">(</a> <a id="16763" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16550" class="Bound">c</a><a id="16764" class="Symbol">)))</a>

  <a id="16771" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16771" class="Function">is-section-unshift-cocone-sequential-diagram</a> <a id="16816" class="Symbol">:</a>
    <a id="16822" class="Symbol">(</a><a id="16823" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16823" class="Bound">k</a> <a id="16825" class="Symbol">:</a> <a id="16827" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="16828" class="Symbol">)</a> <a id="16830" class="Symbol">→</a>
    <a id="16836" href="foundation-core.sections.html#1194" class="Function">is-section</a>
      <a id="16853" class="Symbol">(</a> <a id="16855" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="16887" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16823" class="Bound">k</a><a id="16888" class="Symbol">)</a>
      <a id="16896" class="Symbol">(</a> <a id="16898" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="16932" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16051" class="Bound">A</a> <a id="16934" class="Symbol">{</a><a id="16935" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16081" class="Bound">X</a><a id="16936" class="Symbol">}</a> <a id="16938" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16823" class="Bound">k</a><a id="16939" class="Symbol">)</a>
  <a id="16943" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16771" class="Function">is-section-unshift-cocone-sequential-diagram</a> <a id="16988" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16988" class="Bound">k</a> <a id="16990" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16990" class="Bound">c</a> <a id="16992" class="Symbol">=</a>
    <a id="16998" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#11659" class="Function">eq-htpy-cocone-sequential-diagram</a>
      <a id="17038" class="Symbol">(</a> <a id="17040" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="17065" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16988" class="Bound">k</a> <a id="17067" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16051" class="Bound">A</a><a id="17068" class="Symbol">)</a>
      <a id="17076" class="Symbol">(</a> <a id="17078" class="Symbol">_)</a>
      <a id="17087" class="Symbol">(</a> <a id="17089" class="Symbol">_)</a>
      <a id="17098" class="Symbol">(</a> <a id="17100" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16103" class="Function">htpy-is-section-unshift-cocone-sequential-diagram</a> <a id="17150" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16988" class="Bound">k</a> <a id="17152" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16990" class="Bound">c</a><a id="17153" class="Symbol">)</a>
</pre>
For the other direction, we need to show that the synthesized data, namely the
map `i₁ ∘ a₀ : A₀ → X` and the reflexive homotopy, is consistent with the
original data `i₀ : A₀ → X` and the homotopy `H₀ : i₀ ~ i₁ ∘ a₀`. It is more
convenient to show the inverse homotopy `id ~ unshift ∘ shift`, because `H₀`
gives us exactly the right homotopy for the first level, so the rest of the
coherences are also trivial.

In the inductive step, we need to show
`c ~ c[k + 1][-(k + 1)] ≐ c[k][1][-1][-k]`. This follows from the inductive
hypothesis, which states that `c ~ c[k][-k]`, and which we compose with the
homotopy `c[k] ~ c[k][1][-1]` unshifted by `k`.

<pre class="Agda"><a id="17821" class="Keyword">module</a> <a id="17828" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17828" class="Module">_</a>
  <a id="17832" class="Symbol">{</a><a id="17833" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17833" class="Bound">l1</a> <a id="17836" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17836" class="Bound">l2</a> <a id="17839" class="Symbol">:</a> <a id="17841" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="17846" class="Symbol">}</a> <a id="17848" class="Symbol">{</a><a id="17849" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17849" class="Bound">A</a> <a id="17851" class="Symbol">:</a> <a id="17853" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="17872" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17833" class="Bound">l1</a><a id="17874" class="Symbol">}</a>
  <a id="17878" class="Symbol">{</a><a id="17879" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17879" class="Bound">X</a> <a id="17881" class="Symbol">:</a> <a id="17883" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="17886" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17836" class="Bound">l2</a><a id="17888" class="Symbol">}</a>
  <a id="17892" class="Keyword">where</a>

  <a id="17901" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17901" class="Function">inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram</a> <a id="17963" class="Symbol">:</a>
    <a id="17969" class="Symbol">(</a><a id="17970" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17970" class="Bound">c</a> <a id="17972" class="Symbol">:</a> <a id="17974" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="18000" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17849" class="Bound">A</a> <a id="18002" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17879" class="Bound">X</a><a id="18003" class="Symbol">)</a> <a id="18005" class="Symbol">→</a>
    <a id="18011" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="18048" class="Symbol">(</a> <a id="18050" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17970" class="Bound">c</a><a id="18051" class="Symbol">)</a>
      <a id="18059" class="Symbol">(</a> <a id="18061" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="18100" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17849" class="Bound">A</a>
        <a id="18110" class="Symbol">(</a> <a id="18112" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="18149" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17970" class="Bound">c</a><a id="18150" class="Symbol">))</a>
  <a id="18155" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="18159" class="Symbol">(</a><a id="18160" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17901" class="Function">inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram</a> <a id="18222" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18222" class="Bound">c</a><a id="18223" class="Symbol">)</a>
    <a id="18229" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="18236" class="Symbol">=</a>
    <a id="18242" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2352" class="Function">coherence-cocone-sequential-diagram</a> <a id="18278" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18222" class="Bound">c</a> <a id="18280" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a>
  <a id="18289" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="18293" class="Symbol">(</a><a id="18294" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17901" class="Function">inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram</a> <a id="18356" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18356" class="Bound">c</a><a id="18357" class="Symbol">)</a>
    <a id="18363" class="Symbol">(</a><a id="18364" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="18371" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18371" class="Bound">n</a><a id="18372" class="Symbol">)</a> <a id="18374" class="Symbol">=</a>
    <a id="18380" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="18392" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="18396" class="Symbol">(</a><a id="18397" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17901" class="Function">inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram</a> <a id="18459" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18459" class="Bound">c</a><a id="18460" class="Symbol">)</a>
    <a id="18466" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="18473" class="Symbol">=</a>
    <a id="18479" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="18491" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="18495" class="Symbol">(</a><a id="18496" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17901" class="Function">inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram</a> <a id="18558" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18558" class="Bound">c</a><a id="18559" class="Symbol">)</a>
    <a id="18565" class="Symbol">(</a><a id="18566" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="18573" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18573" class="Bound">n</a><a id="18574" class="Symbol">)</a> <a id="18576" class="Symbol">=</a>
    <a id="18582" href="foundation-core.homotopies.html#5171" class="Function">right-unit-htpy</a>

<a id="18599" class="Keyword">module</a> <a id="18606" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18606" class="Module">_</a>
  <a id="18610" class="Symbol">{</a><a id="18611" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18611" class="Bound">l1</a> <a id="18614" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18614" class="Bound">l2</a> <a id="18617" class="Symbol">:</a> <a id="18619" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="18624" class="Symbol">}</a> <a id="18626" class="Symbol">{</a><a id="18627" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18627" class="Bound">A</a> <a id="18629" class="Symbol">:</a> <a id="18631" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="18650" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18611" class="Bound">l1</a><a id="18652" class="Symbol">}</a>
  <a id="18656" class="Symbol">{</a><a id="18657" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18657" class="Bound">X</a> <a id="18659" class="Symbol">:</a> <a id="18661" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="18664" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18614" class="Bound">l2</a><a id="18666" class="Symbol">}</a>
  <a id="18670" class="Keyword">where</a>

  <a id="18679" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18679" class="Function">inv-htpy-is-retraction-unshift-cocone-sequential-diagram</a> <a id="18736" class="Symbol">:</a>
    <a id="18742" class="Symbol">(</a><a id="18743" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18743" class="Bound">k</a> <a id="18745" class="Symbol">:</a> <a id="18747" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="18748" class="Symbol">)</a> <a id="18750" class="Symbol">→</a>
    <a id="18756" class="Symbol">(</a><a id="18757" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18757" class="Bound">c</a> <a id="18759" class="Symbol">:</a> <a id="18761" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="18787" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18627" class="Bound">A</a> <a id="18789" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18657" class="Bound">X</a><a id="18790" class="Symbol">)</a> <a id="18792" class="Symbol">→</a>
    <a id="18798" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="18835" class="Symbol">(</a> <a id="18837" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18757" class="Bound">c</a><a id="18838" class="Symbol">)</a>
      <a id="18846" class="Symbol">(</a> <a id="18848" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="18882" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18627" class="Bound">A</a> <a id="18884" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18743" class="Bound">k</a>
        <a id="18894" class="Symbol">(</a> <a id="18896" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="18928" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18743" class="Bound">k</a> <a id="18930" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18757" class="Bound">c</a><a id="18931" class="Symbol">))</a>
  <a id="18936" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18679" class="Function">inv-htpy-is-retraction-unshift-cocone-sequential-diagram</a> <a id="18993" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="19000" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19000" class="Bound">c</a> <a id="19002" class="Symbol">=</a>
    <a id="19008" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#10116" class="Function">refl-htpy-cocone-sequential-diagram</a> <a id="19044" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18627" class="Bound">A</a> <a id="19046" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19000" class="Bound">c</a>
  <a id="19050" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18679" class="Function">inv-htpy-is-retraction-unshift-cocone-sequential-diagram</a> <a id="19107" class="Symbol">(</a><a id="19108" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="19115" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19115" class="Bound">k</a><a id="19116" class="Symbol">)</a> <a id="19118" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19118" class="Bound">c</a> <a id="19120" class="Symbol">=</a>
    <a id="19126" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#5962" class="Function">concat-htpy-cocone-sequential-diagram</a>
      <a id="19170" class="Symbol">(</a> <a id="19172" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18679" class="Function">inv-htpy-is-retraction-unshift-cocone-sequential-diagram</a> <a id="19229" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19115" class="Bound">k</a> <a id="19231" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19118" class="Bound">c</a><a id="19232" class="Symbol">)</a>
      <a id="19240" class="Symbol">(</a> <a id="19242" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#13196" class="Function">unshift-htpy-cocone-sequential-diagram</a> <a id="19281" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19115" class="Bound">k</a>
        <a id="19291" class="Symbol">(</a> <a id="19293" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17901" class="Function">inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram</a>
          <a id="19365" class="Symbol">(</a> <a id="19367" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="19399" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19115" class="Bound">k</a> <a id="19401" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19118" class="Bound">c</a><a id="19402" class="Symbol">)))</a>

  <a id="19409" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19409" class="Function">is-retraction-unshift-cocone-sequential-diagram</a> <a id="19457" class="Symbol">:</a>
    <a id="19463" class="Symbol">(</a><a id="19464" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19464" class="Bound">k</a> <a id="19466" class="Symbol">:</a> <a id="19468" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="19469" class="Symbol">)</a> <a id="19471" class="Symbol">→</a>
    <a id="19477" href="foundation-core.retractions.html#790" class="Function">is-retraction</a>
      <a id="19497" class="Symbol">(</a> <a id="19499" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="19531" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19464" class="Bound">k</a><a id="19532" class="Symbol">)</a>
      <a id="19540" class="Symbol">(</a> <a id="19542" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="19576" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18627" class="Bound">A</a> <a id="19578" class="Symbol">{</a><a id="19579" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18657" class="Bound">X</a><a id="19580" class="Symbol">}</a> <a id="19582" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19464" class="Bound">k</a><a id="19583" class="Symbol">)</a>
  <a id="19587" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19409" class="Function">is-retraction-unshift-cocone-sequential-diagram</a> <a id="19635" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19635" class="Bound">k</a> <a id="19637" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19637" class="Bound">c</a> <a id="19639" class="Symbol">=</a>
    <a id="19645" href="foundation-core.identity-types.html#6358" class="Function">inv</a>
      <a id="19655" class="Symbol">(</a> <a id="19657" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#11659" class="Function">eq-htpy-cocone-sequential-diagram</a> <a id="19691" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18627" class="Bound">A</a> <a id="19693" class="Symbol">_</a> <a id="19695" class="Symbol">_</a>
        <a id="19705" class="Symbol">(</a> <a id="19707" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#18679" class="Function">inv-htpy-is-retraction-unshift-cocone-sequential-diagram</a> <a id="19764" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19635" class="Bound">k</a> <a id="19766" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19637" class="Bound">c</a><a id="19767" class="Symbol">))</a>

<a id="19771" class="Keyword">module</a> <a id="19778" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19778" class="Module">_</a>
  <a id="19782" class="Symbol">{</a><a id="19783" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19783" class="Bound">l1</a> <a id="19786" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19786" class="Bound">l2</a> <a id="19789" class="Symbol">:</a> <a id="19791" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="19796" class="Symbol">}</a> <a id="19798" class="Symbol">{</a><a id="19799" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19799" class="Bound">A</a> <a id="19801" class="Symbol">:</a> <a id="19803" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="19822" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19783" class="Bound">l1</a><a id="19824" class="Symbol">}</a>
  <a id="19828" class="Symbol">{</a><a id="19829" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19829" class="Bound">X</a> <a id="19831" class="Symbol">:</a> <a id="19833" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="19836" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19786" class="Bound">l2</a><a id="19838" class="Symbol">}</a>
  <a id="19842" class="Keyword">where</a>

  <a id="19851" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19851" class="Function">is-equiv-shift-cocone-sequential-diagram</a> <a id="19892" class="Symbol">:</a>
    <a id="19898" class="Symbol">(</a><a id="19899" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19899" class="Bound">k</a> <a id="19901" class="Symbol">:</a> <a id="19903" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="19904" class="Symbol">)</a> <a id="19906" class="Symbol">→</a>
    <a id="19912" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="19921" class="Symbol">(</a><a id="19922" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="19954" class="Symbol">{</a><a id="19955" class="Argument">X</a> <a id="19957" class="Symbol">=</a> <a id="19959" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19829" class="Bound">X</a><a id="19960" class="Symbol">}</a> <a id="19962" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19899" class="Bound">k</a><a id="19963" class="Symbol">)</a>
  <a id="19967" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19851" class="Function">is-equiv-shift-cocone-sequential-diagram</a> <a id="20008" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20008" class="Bound">k</a> <a id="20010" class="Symbol">=</a>
    <a id="20016" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
      <a id="20045" class="Symbol">(</a> <a id="20047" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#9322" class="Function">unshift-cocone-sequential-diagram</a> <a id="20081" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19799" class="Bound">A</a> <a id="20083" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20008" class="Bound">k</a><a id="20084" class="Symbol">)</a>
      <a id="20092" class="Symbol">(</a> <a id="20094" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#16771" class="Function">is-section-unshift-cocone-sequential-diagram</a> <a id="20139" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20008" class="Bound">k</a><a id="20140" class="Symbol">)</a>
      <a id="20148" class="Symbol">(</a> <a id="20150" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19409" class="Function">is-retraction-unshift-cocone-sequential-diagram</a> <a id="20198" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20008" class="Bound">k</a><a id="20199" class="Symbol">)</a>

  <a id="20204" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20204" class="Function">equiv-shift-cocone-sequential-diagram</a> <a id="20242" class="Symbol">:</a>
    <a id="20248" class="Symbol">(</a><a id="20249" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20249" class="Bound">k</a> <a id="20251" class="Symbol">:</a> <a id="20253" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="20254" class="Symbol">)</a> <a id="20256" class="Symbol">→</a>
    <a id="20262" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="20288" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19799" class="Bound">A</a> <a id="20290" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19829" class="Bound">X</a> <a id="20292" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="20298" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="20324" class="Symbol">(</a><a id="20325" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="20350" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20249" class="Bound">k</a> <a id="20352" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19799" class="Bound">A</a><a id="20353" class="Symbol">)</a> <a id="20355" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19829" class="Bound">X</a>
  <a id="20359" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="20363" class="Symbol">(</a><a id="20364" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20204" class="Function">equiv-shift-cocone-sequential-diagram</a> <a id="20402" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20402" class="Bound">k</a><a id="20403" class="Symbol">)</a> <a id="20405" class="Symbol">=</a>
    <a id="20411" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="20443" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20402" class="Bound">k</a>
  <a id="20447" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="20451" class="Symbol">(</a><a id="20452" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20204" class="Function">equiv-shift-cocone-sequential-diagram</a> <a id="20490" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20490" class="Bound">k</a><a id="20491" class="Symbol">)</a> <a id="20493" class="Symbol">=</a>
    <a id="20499" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19851" class="Function">is-equiv-shift-cocone-sequential-diagram</a> <a id="20540" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#20490" class="Bound">k</a>
</pre>
### The sequential colimit of a sequential diagram is also the sequential colimit of its shift

Given a sequential colimit

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯ --> X,
```

there is a commuting triangle

```text
              cocone-map
      X → Y ------------> cocone A Y
            \           /
  cocone-map  \       /
                ∨   ∨
             cocone A[1] Y.
```

Inductively, we compose this triangle in the following way

```text
              cocone-map
      X → Y ------------> cocone A Y
            \⟍             |
             \ ⟍           |
              \  ⟍         |
               \   ⟍       ∨
                \    > cocone A[k] Y
     cocone-map  \       /
                  \     /
                   \   /
                    ∨ ∨
             cocone A[k + 1] Y,
```

where the top triangle is the inductive hypothesis, and the bottom triangle is
the step instantiated at `A[k]`.

This gives us the commuting triangle

```text
              cocone-map
      X → Y ------------> cocone A Y
            \     ≃     /
  cocone-map  \       / ≃
                ∨   ∨
             cocone A[k] Y,
```

where the top map is an equivalence by the universal property of the cocone on
`X`, and the right map is an equivalence by a theorem shown above, which implies
that the left map is an equivalence, which exactly says that `X` is the
sequential colimit of `A[k]`.

<pre class="Agda"><a id="21969" class="Keyword">module</a> <a id="21976" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#21976" class="Module">_</a>
  <a id="21980" class="Symbol">{</a><a id="21981" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#21981" class="Bound">l1</a> <a id="21984" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#21984" class="Bound">l2</a> <a id="21987" class="Symbol">:</a> <a id="21989" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="21994" class="Symbol">}</a> <a id="21996" class="Symbol">{</a><a id="21997" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#21997" class="Bound">A</a> <a id="21999" class="Symbol">:</a> <a id="22001" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="22020" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#21981" class="Bound">l1</a><a id="22022" class="Symbol">}</a>
  <a id="22026" class="Symbol">{</a><a id="22027" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22027" class="Bound">X</a> <a id="22029" class="Symbol">:</a> <a id="22031" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="22034" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#21984" class="Bound">l2</a><a id="22036" class="Symbol">}</a> <a id="22038" class="Symbol">(</a><a id="22039" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22039" class="Bound">c</a> <a id="22041" class="Symbol">:</a> <a id="22043" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="22069" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#21997" class="Bound">A</a> <a id="22071" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22027" class="Bound">X</a><a id="22072" class="Symbol">)</a>
  <a id="22076" class="Keyword">where</a>

  <a id="22085" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22085" class="Function">triangle-cocone-map-shift-once-cocone-sequential-diagram</a> <a id="22142" class="Symbol">:</a>
    <a id="22148" class="Symbol">{</a><a id="22149" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22149" class="Bound">l</a> <a id="22151" class="Symbol">:</a> <a id="22153" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="22158" class="Symbol">}</a> <a id="22160" class="Symbol">(</a><a id="22161" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22161" class="Bound">Y</a> <a id="22163" class="Symbol">:</a> <a id="22165" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="22168" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22149" class="Bound">l</a><a id="22169" class="Symbol">)</a> <a id="22171" class="Symbol">→</a>
    <a id="22177" href="foundation-core.commuting-triangles-of-maps.html#867" class="Function">coherence-triangle-maps</a>
      <a id="22207" class="Symbol">(</a> <a id="22209" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#7170" class="Function">cocone-map-sequential-diagram</a>
        <a id="22247" class="Symbol">(</a> <a id="22249" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="22286" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22039" class="Bound">c</a><a id="22287" class="Symbol">)</a>
        <a id="22297" class="Symbol">{</a> <a id="22299" class="Argument">Y</a> <a id="22301" class="Symbol">=</a> <a id="22303" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22161" class="Bound">Y</a><a id="22304" class="Symbol">})</a>
      <a id="22313" class="Symbol">(</a> <a id="22315" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a><a id="22351" class="Symbol">)</a>
      <a id="22359" class="Symbol">(</a> <a id="22361" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#7170" class="Function">cocone-map-sequential-diagram</a> <a id="22391" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22039" class="Bound">c</a><a id="22392" class="Symbol">)</a>
  <a id="22396" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22085" class="Function">triangle-cocone-map-shift-once-cocone-sequential-diagram</a> <a id="22453" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22453" class="Bound">Y</a> <a id="22455" class="Symbol">=</a> <a id="22457" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>

<a id="22468" class="Keyword">module</a> <a id="22475" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22475" class="Module">_</a>
  <a id="22479" class="Symbol">{</a><a id="22480" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22480" class="Bound">l1</a> <a id="22483" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22483" class="Bound">l2</a> <a id="22486" class="Symbol">:</a> <a id="22488" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="22493" class="Symbol">}</a> <a id="22495" class="Symbol">{</a><a id="22496" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22496" class="Bound">A</a> <a id="22498" class="Symbol">:</a> <a id="22500" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="22519" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22480" class="Bound">l1</a><a id="22521" class="Symbol">}</a>
  <a id="22525" class="Symbol">{</a><a id="22526" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22526" class="Bound">X</a> <a id="22528" class="Symbol">:</a> <a id="22530" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="22533" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22483" class="Bound">l2</a><a id="22535" class="Symbol">}</a> <a id="22537" class="Symbol">(</a><a id="22538" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22538" class="Bound">c</a> <a id="22540" class="Symbol">:</a> <a id="22542" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="22568" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22496" class="Bound">A</a> <a id="22570" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22526" class="Bound">X</a><a id="22571" class="Symbol">)</a>
  <a id="22575" class="Keyword">where</a>

  <a id="22584" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22584" class="Function">triangle-cocone-map-shift-cocone-sequential-diagram</a> <a id="22636" class="Symbol">:</a>
    <a id="22642" class="Symbol">(</a><a id="22643" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22643" class="Bound">k</a> <a id="22645" class="Symbol">:</a> <a id="22647" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="22648" class="Symbol">)</a> <a id="22650" class="Symbol">→</a>
    <a id="22656" class="Symbol">{</a><a id="22657" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22657" class="Bound">l</a> <a id="22659" class="Symbol">:</a> <a id="22661" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="22666" class="Symbol">}</a> <a id="22668" class="Symbol">(</a><a id="22669" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22669" class="Bound">Y</a> <a id="22671" class="Symbol">:</a> <a id="22673" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="22676" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22657" class="Bound">l</a><a id="22677" class="Symbol">)</a> <a id="22679" class="Symbol">→</a>
    <a id="22685" href="foundation-core.commuting-triangles-of-maps.html#867" class="Function">coherence-triangle-maps</a>
      <a id="22715" class="Symbol">(</a> <a id="22717" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#7170" class="Function">cocone-map-sequential-diagram</a>
        <a id="22755" class="Symbol">(</a> <a id="22757" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="22789" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22643" class="Bound">k</a> <a id="22791" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22538" class="Bound">c</a><a id="22792" class="Symbol">))</a>
      <a id="22801" class="Symbol">(</a> <a id="22803" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="22835" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22643" class="Bound">k</a><a id="22836" class="Symbol">)</a>
      <a id="22844" class="Symbol">(</a> <a id="22846" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#7170" class="Function">cocone-map-sequential-diagram</a> <a id="22876" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22538" class="Bound">c</a><a id="22877" class="Symbol">)</a>
  <a id="22881" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22584" class="Function">triangle-cocone-map-shift-cocone-sequential-diagram</a> <a id="22933" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="22940" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22940" class="Bound">Y</a> <a id="22942" class="Symbol">=</a>
    <a id="22948" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="22960" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22584" class="Function">triangle-cocone-map-shift-cocone-sequential-diagram</a> <a id="23012" class="Symbol">(</a><a id="23013" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="23020" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23020" class="Bound">k</a><a id="23021" class="Symbol">)</a> <a id="23023" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23023" class="Bound">Y</a> <a id="23025" class="Symbol">=</a>
    <a id="23031" class="Symbol">(</a> <a id="23033" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22085" class="Function">triangle-cocone-map-shift-once-cocone-sequential-diagram</a>
      <a id="23096" class="Symbol">(</a> <a id="23098" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="23130" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23020" class="Bound">k</a> <a id="23132" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22538" class="Bound">c</a><a id="23133" class="Symbol">)</a>
      <a id="23141" class="Symbol">(</a> <a id="23143" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23023" class="Bound">Y</a><a id="23144" class="Symbol">))</a> <a id="23147" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a>
    <a id="23154" class="Symbol">(</a> <a id="23156" class="Symbol">(</a> <a id="23158" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a><a id="23194" class="Symbol">)</a> <a id="23196" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a>
      <a id="23205" class="Symbol">(</a> <a id="23207" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22584" class="Function">triangle-cocone-map-shift-cocone-sequential-diagram</a> <a id="23259" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23020" class="Bound">k</a> <a id="23261" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23023" class="Bound">Y</a><a id="23262" class="Symbol">))</a>

<a id="23266" class="Keyword">module</a> <a id="23273" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23273" class="Module">_</a>
  <a id="23277" class="Symbol">{</a><a id="23278" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23278" class="Bound">l1</a> <a id="23281" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23281" class="Bound">l2</a> <a id="23284" class="Symbol">:</a> <a id="23286" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="23291" class="Symbol">}</a> <a id="23293" class="Symbol">{</a><a id="23294" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23294" class="Bound">A</a> <a id="23296" class="Symbol">:</a> <a id="23298" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="23317" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23278" class="Bound">l1</a><a id="23319" class="Symbol">}</a>
  <a id="23323" class="Symbol">{</a><a id="23324" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23324" class="Bound">X</a> <a id="23326" class="Symbol">:</a> <a id="23328" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="23331" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23281" class="Bound">l2</a><a id="23333" class="Symbol">}</a> <a id="23335" class="Symbol">{</a><a id="23336" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23336" class="Bound">c</a> <a id="23338" class="Symbol">:</a> <a id="23340" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="23366" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23294" class="Bound">A</a> <a id="23368" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23324" class="Bound">X</a><a id="23369" class="Symbol">}</a>
  <a id="23373" class="Keyword">where</a>

  <a id="23382" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="23417" class="Symbol">:</a>
    <a id="23423" class="Symbol">(</a><a id="23424" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23424" class="Bound">k</a> <a id="23426" class="Symbol">:</a> <a id="23428" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="23429" class="Symbol">)</a> <a id="23431" class="Symbol">→</a>
    <a id="23437" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="23475" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23336" class="Bound">c</a> <a id="23477" class="Symbol">→</a>
    <a id="23483" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="23521" class="Symbol">(</a><a id="23522" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="23554" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23424" class="Bound">k</a> <a id="23556" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23336" class="Bound">c</a><a id="23557" class="Symbol">)</a>
  <a id="23561" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="23596" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23596" class="Bound">k</a> <a id="23598" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23598" class="Bound">up-c</a> <a id="23603" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23603" class="Bound">Y</a> <a id="23605" class="Symbol">=</a>
    <a id="23611" href="foundation-core.equivalences.html#10197" class="Function">is-equiv-left-map-triangle</a>
      <a id="23644" class="Symbol">(</a> <a id="23646" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#7170" class="Function">cocone-map-sequential-diagram</a>
        <a id="23684" class="Symbol">(</a> <a id="23686" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="23718" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23596" class="Bound">k</a> <a id="23720" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23336" class="Bound">c</a><a id="23721" class="Symbol">))</a>
      <a id="23730" class="Symbol">(</a> <a id="23732" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="23764" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23596" class="Bound">k</a><a id="23765" class="Symbol">)</a>
      <a id="23773" class="Symbol">(</a> <a id="23775" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#7170" class="Function">cocone-map-sequential-diagram</a> <a id="23805" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23336" class="Bound">c</a><a id="23806" class="Symbol">)</a>
      <a id="23814" class="Symbol">(</a> <a id="23816" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#22584" class="Function">triangle-cocone-map-shift-cocone-sequential-diagram</a> <a id="23868" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23336" class="Bound">c</a> <a id="23870" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23596" class="Bound">k</a> <a id="23872" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23603" class="Bound">Y</a><a id="23873" class="Symbol">)</a>
      <a id="23881" class="Symbol">(</a> <a id="23883" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23598" class="Bound">up-c</a> <a id="23888" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23603" class="Bound">Y</a><a id="23889" class="Symbol">)</a>
      <a id="23897" class="Symbol">(</a> <a id="23899" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#19851" class="Function">is-equiv-shift-cocone-sequential-diagram</a> <a id="23940" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23596" class="Bound">k</a><a id="23941" class="Symbol">)</a>
</pre>
We instantiate this theorem for the standard sequential colimits, giving us
`A[k]∞ ≃ A∞`.

<pre class="Agda"><a id="24047" class="Keyword">module</a> <a id="24054" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24054" class="Module">_</a>
  <a id="24058" class="Symbol">{</a><a id="24059" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24059" class="Bound">l1</a> <a id="24062" class="Symbol">:</a> <a id="24064" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="24069" class="Symbol">}</a> <a id="24071" class="Symbol">(</a><a id="24072" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24072" class="Bound">A</a> <a id="24074" class="Symbol">:</a> <a id="24076" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="24095" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24059" class="Bound">l1</a><a id="24097" class="Symbol">)</a>
  <a id="24101" class="Keyword">where</a>

  <a id="24110" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24110" class="Function">compute-sequential-colimit-shift-sequential-diagram</a> <a id="24162" class="Symbol">:</a>
    <a id="24168" class="Symbol">(</a><a id="24169" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24169" class="Bound">k</a> <a id="24171" class="Symbol">:</a> <a id="24173" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="24174" class="Symbol">)</a> <a id="24176" class="Symbol">→</a>
    <a id="24182" href="synthetic-homotopy-theory.sequential-colimits.html#4019" class="Function">standard-sequential-colimit</a> <a id="24210" class="Symbol">(</a><a id="24211" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="24236" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24169" class="Bound">k</a> <a id="24238" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24072" class="Bound">A</a><a id="24239" class="Symbol">)</a> <a id="24241" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="24247" href="synthetic-homotopy-theory.sequential-colimits.html#4019" class="Function">standard-sequential-colimit</a> <a id="24275" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24072" class="Bound">A</a>
  <a id="24279" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="24283" class="Symbol">(</a><a id="24284" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24110" class="Function">compute-sequential-colimit-shift-sequential-diagram</a> <a id="24336" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24336" class="Bound">k</a><a id="24337" class="Symbol">)</a> <a id="24339" class="Symbol">=</a>
    <a id="24345" href="synthetic-homotopy-theory.sequential-colimits.html#6449" class="Function">cogap-standard-sequential-colimit</a>
      <a id="24385" class="Symbol">(</a> <a id="24387" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a>
        <a id="24427" class="Symbol">(</a> <a id="24429" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24336" class="Bound">k</a><a id="24430" class="Symbol">)</a>
        <a id="24440" class="Symbol">(</a> <a id="24442" href="synthetic-homotopy-theory.sequential-colimits.html#4193" class="Function">cocone-standard-sequential-colimit</a> <a id="24477" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24072" class="Bound">A</a><a id="24478" class="Symbol">))</a>
  <a id="24483" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="24487" class="Symbol">(</a><a id="24488" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24110" class="Function">compute-sequential-colimit-shift-sequential-diagram</a> <a id="24540" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24540" class="Bound">k</a><a id="24541" class="Symbol">)</a> <a id="24543" class="Symbol">=</a>
    <a id="24549" href="synthetic-homotopy-theory.sequential-colimits.html#11167" class="Function">is-sequential-colimit-universal-property</a> <a id="24590" class="Symbol">_</a>
      <a id="24598" class="Symbol">(</a> <a id="24600" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="24635" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24540" class="Bound">k</a> <a id="24637" href="synthetic-homotopy-theory.sequential-colimits.html#4928" class="Function">up-standard-sequential-colimit</a><a id="24667" class="Symbol">)</a>
</pre>
### Unshifting cocones under sequential diagrams is homotopic to precomposing them with shift inclusion morphisms

Given a cocone `c`

```text
         a₁
     A₁ ---> A₂ ---> ⋯
     |      /
     |     /
  i₁ |    / i₂
     |   /
     ∨  ∨
     X
```

under `A[1]`, we have two way of turning it into a cocone under `A` --- we can
unshift it, which gives the cocone

```text
           a₀      a₁
       A₀ ---> A₁ ---> A₂ ---> ⋯
        \      |      /
         \     |     /
  i₁ ∘ a₀ \    | i₁ / i₂
           \   |   /
            ∨  ∨  ∨
               X ,
```

or we can prepend the inclusion morphism
`hom-shift-sequential-diagram : A → A[1]` to get

```text
         a₀
     A₀ ---> A₁ ---> ⋯
     |       |
  a₀ |       | a₁
     ∨   a₁  ∨
     A₁ ---> A₂ ---> ⋯
     |      /
     |     /
  i₁ |    / i₂
     |   /
     ∨  ∨
     X .
```

We show that these two cocones are homotopic.

<pre class="Agda"><a id="25579" class="Keyword">module</a> <a id="25586" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25586" class="Module">_</a>
  <a id="25590" class="Symbol">{</a><a id="25591" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25591" class="Bound">l1</a> <a id="25594" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25594" class="Bound">l2</a> <a id="25597" class="Symbol">:</a> <a id="25599" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="25604" class="Symbol">}</a> <a id="25606" class="Symbol">{</a><a id="25607" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25607" class="Bound">A</a> <a id="25609" class="Symbol">:</a> <a id="25611" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="25630" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25591" class="Bound">l1</a><a id="25632" class="Symbol">}</a>
  <a id="25636" class="Symbol">{</a><a id="25637" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25637" class="Bound">X</a> <a id="25639" class="Symbol">:</a> <a id="25641" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="25644" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25594" class="Bound">l2</a><a id="25646" class="Symbol">}</a>
  <a id="25650" class="Symbol">(</a><a id="25651" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25651" class="Bound">c</a> <a id="25653" class="Symbol">:</a> <a id="25655" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="25681" class="Symbol">(</a><a id="25682" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4220" class="Function">shift-once-sequential-diagram</a> <a id="25712" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25607" class="Bound">A</a><a id="25713" class="Symbol">)</a> <a id="25715" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25637" class="Bound">X</a><a id="25716" class="Symbol">)</a>
  <a id="25720" class="Keyword">where</a>

  <a id="25729" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25729" class="Function">htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram</a> <a id="25796" class="Symbol">:</a>
    <a id="25802" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="25839" class="Symbol">(</a> <a id="25841" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#8769" class="Function">unshift-once-cocone-sequential-diagram</a> <a id="25880" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25607" class="Bound">A</a> <a id="25882" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25651" class="Bound">c</a><a id="25883" class="Symbol">)</a>
      <a id="25891" class="Symbol">(</a> <a id="25893" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#3080" class="Function">map-cocone-hom-sequential-diagram</a>
        <a id="25935" class="Symbol">(</a> <a id="25937" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="25971" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25607" class="Bound">A</a><a id="25972" class="Symbol">)</a>
        <a id="25982" class="Symbol">(</a> <a id="25984" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25651" class="Bound">c</a><a id="25985" class="Symbol">))</a>
  <a id="25990" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="25994" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25729" class="Function">htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram</a>
    <a id="26065" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="26072" class="Symbol">=</a> <a id="26074" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="26086" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="26090" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25729" class="Function">htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram</a>
    <a id="26161" class="Symbol">(</a><a id="26162" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="26169" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#26169" class="Bound">n</a><a id="26170" class="Symbol">)</a> <a id="26172" class="Symbol">=</a> <a id="26174" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2352" class="Function">coherence-cocone-sequential-diagram</a> <a id="26210" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25651" class="Bound">c</a> <a id="26212" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#26169" class="Bound">n</a>
  <a id="26216" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="26220" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25729" class="Function">htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram</a>
    <a id="26291" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="26298" class="Symbol">=</a> <a id="26300" href="foundation-core.homotopies.html#5244" class="Function">inv-htpy-right-unit-htpy</a>
  <a id="26327" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="26331" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25729" class="Function">htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram</a>
    <a id="26402" class="Symbol">(</a><a id="26403" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="26410" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#26410" class="Bound">n</a><a id="26411" class="Symbol">)</a> <a id="26413" class="Symbol">=</a>
    <a id="26419" href="foundation-core.whiskering-homotopies-concatenation.html#1554" class="Function">left-whisker-concat-htpy</a>
      <a id="26450" class="Symbol">(</a> <a id="26452" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2352" class="Function">coherence-cocone-sequential-diagram</a> <a id="26488" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25651" class="Bound">c</a> <a id="26490" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#26410" class="Bound">n</a><a id="26491" class="Symbol">)</a>
      <a id="26499" class="Symbol">(</a> <a id="26501" href="foundation-core.homotopies.html#5244" class="Function">inv-htpy-right-unit-htpy</a><a id="26525" class="Symbol">)</a>
</pre>
As a corollary, taking a cocone `c` under `A`, shifting it and prepending the
shift inclusion morphism results in a cocone homotopic to `c`, i.e.,

```text
         a₀      a₁
     A₀ ---> A₁ ---> A₂ ---> ⋯
     |       |       |                     a₀      a₁
  a₀ |       | a₁    | a₂              A₀ ---> A₁ ---> A₂ ---> ⋯
     ∨   a₁  ∨   a₂  ∨                  \      |      /
     A₁ ---> A₂ ---> A₃ ---> ⋯    ~      \     | i₁  /
      \      |      /                  i₀ \    |    / i₂
       \     |     /                       \   |   /
     i₁ \    | i₂ / i₃                      ∨  ∨  ∨
         \   |   /                             X .
          ∨  ∨  ∨
             X
```

**Proof:** We first use the above lemma, which says that the left cocone is
homotopic to `c[1][-1]`, and then we use the fact that unshifting is a
retraction.

<pre class="Agda"><a id="27388" class="Keyword">module</a> <a id="27395" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27395" class="Module">_</a>
  <a id="27399" class="Symbol">{</a><a id="27400" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27400" class="Bound">l1</a> <a id="27403" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27403" class="Bound">l2</a> <a id="27406" class="Symbol">:</a> <a id="27408" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="27413" class="Symbol">}</a> <a id="27415" class="Symbol">{</a><a id="27416" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27416" class="Bound">A</a> <a id="27418" class="Symbol">:</a> <a id="27420" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="27439" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27400" class="Bound">l1</a><a id="27441" class="Symbol">}</a>
  <a id="27445" class="Symbol">{</a><a id="27446" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27446" class="Bound">X</a> <a id="27448" class="Symbol">:</a> <a id="27450" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="27453" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27403" class="Bound">l2</a><a id="27455" class="Symbol">}</a> <a id="27457" class="Symbol">(</a><a id="27458" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27458" class="Bound">c</a> <a id="27460" class="Symbol">:</a> <a id="27462" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="27488" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27416" class="Bound">A</a> <a id="27490" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27446" class="Bound">X</a><a id="27491" class="Symbol">)</a>
  <a id="27495" class="Keyword">where</a>

  <a id="27504" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27504" class="Function">inv-compute-map-cocone-hom-shift-sequential-diagram</a> <a id="27556" class="Symbol">:</a>
    <a id="27562" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="27599" class="Symbol">(</a> <a id="27601" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27458" class="Bound">c</a><a id="27602" class="Symbol">)</a>
      <a id="27610" class="Symbol">(</a> <a id="27612" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#3080" class="Function">map-cocone-hom-sequential-diagram</a>
        <a id="27654" class="Symbol">(</a> <a id="27656" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="27690" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27416" class="Bound">A</a><a id="27691" class="Symbol">)</a>
        <a id="27701" class="Symbol">(</a> <a id="27703" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="27740" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27458" class="Bound">c</a><a id="27741" class="Symbol">))</a>
  <a id="27746" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27504" class="Function">inv-compute-map-cocone-hom-shift-sequential-diagram</a> <a id="27798" class="Symbol">=</a>
    <a id="27804" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#5962" class="Function">concat-htpy-cocone-sequential-diagram</a>
      <a id="27848" class="Symbol">(</a> <a id="27850" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#17901" class="Function">inv-htpy-is-retraction-unshift-once-cocone-sequential-diagram</a> <a id="27912" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27458" class="Bound">c</a><a id="27913" class="Symbol">)</a>
      <a id="27921" class="Symbol">(</a> <a id="27923" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#25729" class="Function">htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagram</a>
        <a id="27998" class="Symbol">(</a> <a id="28000" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="28037" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27458" class="Bound">c</a><a id="28038" class="Symbol">))</a>

  <a id="28044" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#28044" class="Function">compute-map-cocone-hom-shift-sequential-diagram</a> <a id="28092" class="Symbol">:</a>
    <a id="28098" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#3971" class="Function">htpy-cocone-sequential-diagram</a>
      <a id="28135" class="Symbol">(</a> <a id="28137" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#3080" class="Function">map-cocone-hom-sequential-diagram</a>
        <a id="28179" class="Symbol">(</a> <a id="28181" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="28215" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27416" class="Bound">A</a><a id="28216" class="Symbol">)</a>
        <a id="28226" class="Symbol">(</a> <a id="28228" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="28265" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27458" class="Bound">c</a><a id="28266" class="Symbol">))</a>
      <a id="28275" class="Symbol">(</a> <a id="28277" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27458" class="Bound">c</a><a id="28278" class="Symbol">)</a>
  <a id="28282" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#28044" class="Function">compute-map-cocone-hom-shift-sequential-diagram</a> <a id="28330" class="Symbol">=</a>
    <a id="28336" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#5091" class="Function">inv-htpy-cocone-sequential-diagram</a>
      <a id="28377" class="Symbol">(</a> <a id="28379" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#27504" class="Function">inv-compute-map-cocone-hom-shift-sequential-diagram</a><a id="28430" class="Symbol">)</a>
</pre>
### Inclusion morphisms of shifting sequential diagrams induce the identity map on sequential colimits

Given a sequential diagram `(A, a)` with a colimit `X`, then we know that for
every natural number `k`

- `X` is also a sequential colimit of `A[k]` and
- there is a morphism `A → A[k]`, inducing a map between colimits.

Together they give a map `X → X`, which we show here to be the identity map.

**Proof:** By induction on `k`; for the base case, observe that `A → A[0]` is
the identity morphism, which gets sent to the identity map by functoriality of
sequential colimits.

For the inductive case, observe that the inclusion morphism `A → A[k + 1]` is
defined as the composition `A → A[k] → A[k + 1]`, so by functoriality the
induced map is the composition of the maps induced by `A → A[k]` and
`A[k] → A[k + 1]`. The first induced map is the identity map by the inductive
hypothesis. The second induced map is defined to be the map obtained by the
universal property of `X` as a colimit of `A[k]` from the cocone `c[k + 1]`
precomposed by the inclusion `A[k] → A[k + 1]`. We have seen above that this
precomposition results in a cocone homotopic to `c[k]`, so the map induced by
`A[k] → A[k + 1]` is homotopic to the one induced by `c[k]`. But `c[k]` is the
cocone of the sequential colimit of `A[k]`, so it also induces the identity map.

<pre class="Agda"><a id="29794" class="Keyword">module</a> <a id="29801" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29801" class="Module">_</a>
  <a id="29805" class="Symbol">{</a><a id="29806" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29806" class="Bound">l1</a> <a id="29809" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29809" class="Bound">l2</a> <a id="29812" class="Symbol">:</a> <a id="29814" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="29819" class="Symbol">}</a> <a id="29821" class="Symbol">{</a><a id="29822" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29822" class="Bound">A</a> <a id="29824" class="Symbol">:</a> <a id="29826" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="29845" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29806" class="Bound">l1</a><a id="29847" class="Symbol">}</a>
  <a id="29851" class="Symbol">{</a><a id="29852" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29852" class="Bound">X</a> <a id="29854" class="Symbol">:</a> <a id="29856" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="29859" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29809" class="Bound">l2</a><a id="29861" class="Symbol">}</a> <a id="29863" class="Symbol">{</a><a id="29864" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29864" class="Bound">c</a> <a id="29866" class="Symbol">:</a> <a id="29868" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="29894" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29822" class="Bound">A</a> <a id="29896" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29852" class="Bound">X</a><a id="29897" class="Symbol">}</a>
  <a id="29901" class="Symbol">(</a><a id="29902" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29902" class="Bound">up-c</a> <a id="29907" class="Symbol">:</a> <a id="29909" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="29947" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29864" class="Bound">c</a><a id="29948" class="Symbol">)</a>
  <a id="29952" class="Keyword">where</a>

  <a id="29961" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29961" class="Function">compute-map-colimit-hom-shift-once-sequential-diagram</a> <a id="30015" class="Symbol">:</a>
    <a id="30021" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#4827" class="Function">map-sequential-colimit-hom-sequential-diagram</a>
      <a id="30073" class="Symbol">(</a> <a id="30075" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29902" class="Bound">up-c</a><a id="30079" class="Symbol">)</a>
      <a id="30087" class="Symbol">(</a> <a id="30089" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#6833" class="Function">shift-once-cocone-sequential-diagram</a> <a id="30126" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29864" class="Bound">c</a><a id="30127" class="Symbol">)</a>
      <a id="30135" class="Symbol">(</a> <a id="30137" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="30171" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29822" class="Bound">A</a><a id="30172" class="Symbol">)</a> <a id="30174" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="30180" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="30185" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29961" class="Function">compute-map-colimit-hom-shift-once-sequential-diagram</a> <a id="30239" class="Symbol">=</a>
    <a id="30245" class="Symbol">(</a> <a id="30247" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#6225" class="Function">htpy-map-universal-property-htpy-cocone-sequential-diagram</a>
      <a id="30312" class="Symbol">(</a> <a id="30314" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29902" class="Bound">up-c</a><a id="30318" class="Symbol">)</a>
      <a id="30326" class="Symbol">(</a> <a id="30328" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#28044" class="Function">compute-map-cocone-hom-shift-sequential-diagram</a> <a id="30376" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29864" class="Bound">c</a><a id="30377" class="Symbol">))</a> <a id="30380" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a>
    <a id="30387" class="Symbol">(</a> <a id="30389" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#5319" class="Function">compute-map-universal-property-sequential-colimit-id</a> <a id="30442" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29902" class="Bound">up-c</a><a id="30446" class="Symbol">)</a>

<a id="30449" class="Keyword">module</a> <a id="30456" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30456" class="Module">_</a>
  <a id="30460" class="Symbol">{</a><a id="30461" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30461" class="Bound">l1</a> <a id="30464" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30464" class="Bound">l2</a> <a id="30467" class="Symbol">:</a> <a id="30469" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="30474" class="Symbol">}</a> <a id="30476" class="Symbol">{</a><a id="30477" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30477" class="Bound">A</a> <a id="30479" class="Symbol">:</a> <a id="30481" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="30500" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30461" class="Bound">l1</a><a id="30502" class="Symbol">}</a>
  <a id="30506" class="Symbol">{</a><a id="30507" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30507" class="Bound">X</a> <a id="30509" class="Symbol">:</a> <a id="30511" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="30514" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30464" class="Bound">l2</a><a id="30516" class="Symbol">}</a> <a id="30518" class="Symbol">{</a><a id="30519" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30519" class="Bound">c</a> <a id="30521" class="Symbol">:</a> <a id="30523" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="30549" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30477" class="Bound">A</a> <a id="30551" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30507" class="Bound">X</a><a id="30552" class="Symbol">}</a>
  <a id="30556" class="Symbol">(</a><a id="30557" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30557" class="Bound">up-c</a> <a id="30562" class="Symbol">:</a> <a id="30564" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="30602" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30519" class="Bound">c</a><a id="30603" class="Symbol">)</a>
  <a id="30607" class="Keyword">where</a>

  <a id="30616" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30616" class="Function">compute-map-colimit-hom-shift-sequential-diagram</a> <a id="30665" class="Symbol">:</a>
    <a id="30671" class="Symbol">(</a><a id="30672" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30672" class="Bound">k</a> <a id="30674" class="Symbol">:</a> <a id="30676" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="30677" class="Symbol">)</a> <a id="30679" class="Symbol">→</a>
    <a id="30685" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#4827" class="Function">map-sequential-colimit-hom-sequential-diagram</a>
      <a id="30737" class="Symbol">(</a> <a id="30739" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30557" class="Bound">up-c</a><a id="30743" class="Symbol">)</a>
      <a id="30751" class="Symbol">(</a> <a id="30753" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="30785" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30672" class="Bound">k</a> <a id="30787" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30519" class="Bound">c</a><a id="30788" class="Symbol">)</a>
      <a id="30796" class="Symbol">(</a> <a id="30798" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14424" class="Function">hom-shift-sequential-diagram</a> <a id="30827" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30477" class="Bound">A</a> <a id="30829" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30672" class="Bound">k</a><a id="30830" class="Symbol">)</a> <a id="30832" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="30838" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="30843" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30616" class="Function">compute-map-colimit-hom-shift-sequential-diagram</a> <a id="30892" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="30899" class="Symbol">=</a>
    <a id="30905" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#10359" class="Function">preserves-id-map-sequential-colimit-hom-sequential-diagram</a> <a id="30964" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30557" class="Bound">up-c</a>
  <a id="30971" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30616" class="Function">compute-map-colimit-hom-shift-sequential-diagram</a> <a id="31020" class="Symbol">(</a><a id="31021" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="31028" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#31028" class="Bound">k</a><a id="31029" class="Symbol">)</a> <a id="31031" class="Symbol">=</a>
    <a id="31037" class="Symbol">(</a> <a id="31039" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#16458" class="Function">preserves-comp-map-sequential-colimit-hom-sequential-diagram</a>
      <a id="31106" class="Symbol">(</a> <a id="31108" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30557" class="Bound">up-c</a><a id="31112" class="Symbol">)</a>
      <a id="31120" class="Symbol">(</a> <a id="31122" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="31157" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#31028" class="Bound">k</a> <a id="31159" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30557" class="Bound">up-c</a><a id="31163" class="Symbol">)</a>
      <a id="31171" class="Symbol">(</a> <a id="31173" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#7213" class="Function">shift-cocone-sequential-diagram</a> <a id="31205" class="Symbol">(</a><a id="31206" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="31213" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#31028" class="Bound">k</a><a id="31214" class="Symbol">)</a> <a id="31216" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30519" class="Bound">c</a><a id="31217" class="Symbol">)</a>
      <a id="31225" class="Symbol">(</a> <a id="31227" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14124" class="Function">hom-shift-once-sequential-diagram</a> <a id="31261" class="Symbol">(</a><a id="31262" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#4465" class="Function">shift-sequential-diagram</a> <a id="31287" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#31028" class="Bound">k</a> <a id="31289" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30477" class="Bound">A</a><a id="31290" class="Symbol">))</a>
      <a id="31299" class="Symbol">(</a> <a id="31301" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#14424" class="Function">hom-shift-sequential-diagram</a> <a id="31330" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30477" class="Bound">A</a> <a id="31332" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#31028" class="Bound">k</a><a id="31333" class="Symbol">))</a> <a id="31336" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a>
    <a id="31343" class="Symbol">(</a> <a id="31345" href="foundation.homotopy-algebra.html#861" class="Function">horizontal-concat-htpy</a>
      <a id="31374" class="Symbol">(</a> <a id="31376" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#29961" class="Function">compute-map-colimit-hom-shift-once-sequential-diagram</a>
        <a id="31438" class="Symbol">(</a> <a id="31440" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#23382" class="Function">up-shift-cocone-sequential-diagram</a> <a id="31475" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#31028" class="Bound">k</a> <a id="31477" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30557" class="Bound">up-c</a><a id="31481" class="Symbol">))</a>
      <a id="31490" class="Symbol">(</a> <a id="31492" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#30616" class="Function">compute-map-colimit-hom-shift-sequential-diagram</a> <a id="31541" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#31028" class="Bound">k</a><a id="31542" class="Symbol">))</a>
</pre>