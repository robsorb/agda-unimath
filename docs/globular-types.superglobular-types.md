# Superglobular types

<pre class="Agda"><a id="32" class="Symbol">{-#</a> <a id="36" class="Keyword">OPTIONS</a> <a id="44" class="Pragma">--guardedness</a> <a id="58" class="Symbol">#-}</a>

<a id="63" class="Keyword">module</a> <a id="70" href="globular-types.superglobular-types.html" class="Module">globular-types.superglobular-types</a> <a id="105" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="globular-types.binary-dependent-reflexive-globular-types.html" class="Module">globular-types.binary-dependent-reflexive-globular-types</a>
<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="globular-types.points-reflexive-globular-types.html" class="Module">globular-types.points-reflexive-globular-types</a>
<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="globular-types.pointwise-extensions-binary-families-reflexive-globular-types.html" class="Module">globular-types.pointwise-extensions-binary-families-reflexive-globular-types</a>
<a id="504" class="Keyword">open</a> <a id="509" class="Keyword">import</a> <a id="516" href="globular-types.reflexive-globular-equivalences.html" class="Module">globular-types.reflexive-globular-equivalences</a>
<a id="563" class="Keyword">open</a> <a id="568" class="Keyword">import</a> <a id="575" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
</pre>
</details>

**Disclaimer.** The contents of this file are experimental, and likely to be
changed or reconsidered.

## Idea

An {{#concept "superglobular type" Agda=Superglobular-Type}} is a
[reflexive globular type](globular-types.reflexive-globular-types.md) `G` such
that the binary family of globular types

```text
  G' : G₀ → G₀ → Globular-Type
```

of 1-cells and higher cells
[extends pointwise](globular-types.pointwise-extensions-binary-families-globular-types.md)
to a
[binary dependent globular type](globular-types.binary-dependent-globular-types.md).
More specifically, a superglobular type consists of a reflexive globular type
`G` equipped with a binary dependent globular type

```text
  H : Binary-Dependent-Globular-Type l2 l2 G G
```

and a family of [globular equivalences](globular-types.globular-equivalences.md)

```text
  (x y : G₀) → ev-point H x y ≃ G' x y.
```

The low-dimensional data of a superglobular type is therefore as follows:

```text
  G₀ : Type

  G₁ : (x y : G₀) → Type
  H₀ : (x y : G₀) → Type
  e₀ : {x y : G₀} → H₀ x y ≃ G₀ x y
  refl G : (x : G₀) → G₁ x x

  G₂ : {x y : G₀} (s t : G₁ x y) → Type
  H₁ : {x x' y y' : G₀} → G₁ x x' → G₁ y y' → H₀ x y → H₀ x' y' → Type
  e₁ : {x y : G₀} {s t : H₀ x y} → H₁ (refl G x) (refl G y) s t ≃ G₂ (e₀ s) (e₀ t)
  refl G : {x y : G₀} (s : G₁ x y) → G₂ s s

  G₃ : {x y : G₀} {s t : G₁ x y} (u v : G₂ s t) → Type
  H₂ : {x x' y y' : G₀} {s s' : G₁ x x'} {t t' : G₁ y y'}
       (p : G₂ s s') (q : G₂ t t') → H₁ s t → H₁ s' t' → Type
  e₂ : {x y : G₀} {s t : H₀ x y} {u v : H₁ (refl G x) (refl G y) s t} →
       H₂ (refl G x) (refl G y) u v ≃ G₃ (e₁ u) (e₁ v)
```

Note that the type of pairs `(Gₙ₊₁ , eₙ)` in this structure is
[contractible](foundation-core.contractible-types.md). An equivalent way of
presenting the low-dimensional data of a superglobular type is therefore:

```text
  G₀ : Type

  H₀ : (x y : G₀) → Type
  refl G : (x : G₀) → H₀ x x

  H₁ : {x x' y y' : G₀} → H₁ x x' → H₁ y y' → H₀ x y → H₀ x' y' → Type
  refl G : {x y : G₀} (s : H₀ x y) → H₁ (refl G x) (refl G y) s s

  H₂ : {x x' y y' : G₀} {s s' : H₁ x x'} {t t' : H₁ y y'}
       (p : H₂ s s') (q : H₂ t t') → H₁ s t → H₁ s' t' → Type
```

## Definitions

### The predicate of being a superglobular type

<pre class="Agda"><a id="2893" class="Keyword">module</a> <a id="2900" href="globular-types.superglobular-types.html#2900" class="Module">_</a>
  <a id="2904" class="Symbol">{</a><a id="2905" href="globular-types.superglobular-types.html#2905" class="Bound">l1</a> <a id="2908" href="globular-types.superglobular-types.html#2908" class="Bound">l2</a> <a id="2911" class="Symbol">:</a> <a id="2913" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2918" class="Symbol">}</a> <a id="2920" class="Symbol">(</a><a id="2921" href="globular-types.superglobular-types.html#2921" class="Bound">l3</a> <a id="2924" href="globular-types.superglobular-types.html#2924" class="Bound">l4</a> <a id="2927" class="Symbol">:</a> <a id="2929" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2934" class="Symbol">)</a> <a id="2936" class="Symbol">(</a><a id="2937" href="globular-types.superglobular-types.html#2937" class="Bound">G</a> <a id="2939" class="Symbol">:</a> <a id="2941" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2965" href="globular-types.superglobular-types.html#2905" class="Bound">l1</a> <a id="2968" href="globular-types.superglobular-types.html#2908" class="Bound">l2</a><a id="2970" class="Symbol">)</a>
  <a id="2974" class="Keyword">where</a>

  <a id="2983" href="globular-types.superglobular-types.html#2983" class="Function">is-superglobular-Reflexive-Globular-Type</a> <a id="3024" class="Symbol">:</a> <a id="3026" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3029" class="Symbol">(</a><a id="3030" href="globular-types.superglobular-types.html#2905" class="Bound">l1</a> <a id="3033" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3035" href="globular-types.superglobular-types.html#2908" class="Bound">l2</a> <a id="3038" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3040" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3045" href="globular-types.superglobular-types.html#2921" class="Bound">l3</a> <a id="3048" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3050" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3055" href="globular-types.superglobular-types.html#2924" class="Bound">l4</a><a id="3057" class="Symbol">)</a>
  <a id="3061" href="globular-types.superglobular-types.html#2983" class="Function">is-superglobular-Reflexive-Globular-Type</a> <a id="3102" class="Symbol">=</a>
    <a id="3108" href="globular-types.pointwise-extensions-binary-families-reflexive-globular-types.html#2525" class="Function">pointwise-extension-binary-family-reflexive-globular-types</a> <a id="3167" href="globular-types.superglobular-types.html#2921" class="Bound">l3</a> <a id="3170" href="globular-types.superglobular-types.html#2924" class="Bound">l4</a> <a id="3173" href="globular-types.superglobular-types.html#2937" class="Bound">G</a> <a id="3175" href="globular-types.superglobular-types.html#2937" class="Bound">G</a>
      <a id="3183" class="Symbol">(</a> <a id="3185" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="3240" href="globular-types.superglobular-types.html#2937" class="Bound">G</a><a id="3241" class="Symbol">)</a>

<a id="3244" class="Keyword">module</a> <a id="3251" href="globular-types.superglobular-types.html#3251" class="Module">_</a>
  <a id="3255" class="Symbol">{</a><a id="3256" href="globular-types.superglobular-types.html#3256" class="Bound">l1</a> <a id="3259" href="globular-types.superglobular-types.html#3259" class="Bound">l2</a> <a id="3262" href="globular-types.superglobular-types.html#3262" class="Bound">l3</a> <a id="3265" href="globular-types.superglobular-types.html#3265" class="Bound">l4</a> <a id="3268" class="Symbol">:</a> <a id="3270" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3275" class="Symbol">}</a> <a id="3277" class="Symbol">{</a><a id="3278" href="globular-types.superglobular-types.html#3278" class="Bound">G</a> <a id="3280" class="Symbol">:</a> <a id="3282" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="3306" href="globular-types.superglobular-types.html#3256" class="Bound">l1</a> <a id="3309" href="globular-types.superglobular-types.html#3259" class="Bound">l2</a><a id="3311" class="Symbol">}</a>
  <a id="3315" class="Symbol">(</a><a id="3316" href="globular-types.superglobular-types.html#3316" class="Bound">H</a> <a id="3318" class="Symbol">:</a> <a id="3320" href="globular-types.superglobular-types.html#2983" class="Function">is-superglobular-Reflexive-Globular-Type</a> <a id="3361" href="globular-types.superglobular-types.html#3262" class="Bound">l3</a> <a id="3364" href="globular-types.superglobular-types.html#3265" class="Bound">l4</a> <a id="3367" href="globular-types.superglobular-types.html#3278" class="Bound">G</a><a id="3368" class="Symbol">)</a>
  <a id="3372" class="Keyword">where</a>

  <a id="3381" href="globular-types.superglobular-types.html#3381" class="Function">1-cell-binary-dependent-reflexive-globular-type-is-superglobular-Reflexive-Globular-Type</a> <a id="3470" class="Symbol">:</a>
    <a id="3476" href="globular-types.binary-dependent-reflexive-globular-types.html#2962" class="Record">Binary-Dependent-Reflexive-Globular-Type</a> <a id="3517" href="globular-types.superglobular-types.html#3262" class="Bound">l3</a> <a id="3520" href="globular-types.superglobular-types.html#3265" class="Bound">l4</a> <a id="3523" href="globular-types.superglobular-types.html#3278" class="Bound">G</a> <a id="3525" href="globular-types.superglobular-types.html#3278" class="Bound">G</a>
  <a id="3529" href="globular-types.superglobular-types.html#3381" class="Function">1-cell-binary-dependent-reflexive-globular-type-is-superglobular-Reflexive-Globular-Type</a> <a id="3618" class="Symbol">=</a>
    <a id="3624" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3628" href="globular-types.superglobular-types.html#3316" class="Bound">H</a>

  <a id="3633" href="globular-types.superglobular-types.html#3633" class="Function">reflexive-globular-equiv-is-superglobular-Reflexive-Globular-Type</a> <a id="3699" class="Symbol">:</a>
    <a id="3705" class="Symbol">(</a><a id="3706" href="globular-types.superglobular-types.html#3706" class="Bound">x</a> <a id="3708" href="globular-types.superglobular-types.html#3708" class="Bound">y</a> <a id="3710" class="Symbol">:</a> <a id="3712" href="globular-types.points-reflexive-globular-types.html#1331" class="Function">point-Reflexive-Globular-Type</a> <a id="3742" href="globular-types.superglobular-types.html#3278" class="Bound">G</a><a id="3743" class="Symbol">)</a> <a id="3745" class="Symbol">→</a>
    <a id="3751" href="globular-types.reflexive-globular-equivalences.html#1484" class="Record">reflexive-globular-equiv</a>
      <a id="3782" class="Symbol">(</a> <a id="3784" href="globular-types.binary-dependent-reflexive-globular-types.html#9587" class="Function">ev-point-Binary-Dependent-Reflexive-Globular-Type</a> <a id="3834" href="globular-types.superglobular-types.html#3278" class="Bound">G</a> <a id="3836" href="globular-types.superglobular-types.html#3278" class="Bound">G</a>
        <a id="3846" class="Symbol">(</a> <a id="3848" href="globular-types.superglobular-types.html#3381" class="Function">1-cell-binary-dependent-reflexive-globular-type-is-superglobular-Reflexive-Globular-Type</a><a id="3936" class="Symbol">)</a>
        <a id="3946" class="Symbol">(</a> <a id="3948" href="globular-types.superglobular-types.html#3706" class="Bound">x</a><a id="3949" class="Symbol">)</a>
        <a id="3959" class="Symbol">(</a> <a id="3961" href="globular-types.superglobular-types.html#3708" class="Bound">y</a><a id="3962" class="Symbol">))</a>
      <a id="3971" class="Symbol">(</a> <a id="3973" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="4028" href="globular-types.superglobular-types.html#3278" class="Bound">G</a> <a id="4030" href="globular-types.superglobular-types.html#3706" class="Bound">x</a> <a id="4032" href="globular-types.superglobular-types.html#3708" class="Bound">y</a><a id="4033" class="Symbol">)</a>
  <a id="4037" href="globular-types.superglobular-types.html#3633" class="Function">reflexive-globular-equiv-is-superglobular-Reflexive-Globular-Type</a> <a id="4103" class="Symbol">=</a>
    <a id="4109" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4113" href="globular-types.superglobular-types.html#3316" class="Bound">H</a>
</pre>
### Superglobular types

<pre class="Agda"><a id="4153" class="Keyword">record</a>
  <a id="Superglobular-Type"></a><a id="4162" href="globular-types.superglobular-types.html#4162" class="Record">Superglobular-Type</a>
    <a id="4185" class="Symbol">(</a><a id="4186" href="globular-types.superglobular-types.html#4186" class="Bound">l1</a> <a id="4189" href="globular-types.superglobular-types.html#4189" class="Bound">l2</a> <a id="4192" href="globular-types.superglobular-types.html#4192" class="Bound">l3</a> <a id="4195" href="globular-types.superglobular-types.html#4195" class="Bound">l4</a> <a id="4198" class="Symbol">:</a> <a id="4200" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4205" class="Symbol">)</a> <a id="4207" class="Symbol">:</a> <a id="4209" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4212" class="Symbol">(</a><a id="4213" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="4218" href="globular-types.superglobular-types.html#4186" class="Bound">l1</a> <a id="4221" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4223" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="4228" href="globular-types.superglobular-types.html#4189" class="Bound">l2</a> <a id="4231" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4233" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="4238" href="globular-types.superglobular-types.html#4192" class="Bound">l3</a> <a id="4241" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="4243" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="4248" href="globular-types.superglobular-types.html#4195" class="Bound">l4</a><a id="4250" class="Symbol">)</a>
  <a id="4254" class="Keyword">where</a>

  <a id="4263" class="Keyword">field</a>
    <a id="Superglobular-Type.reflexive-globular-type-Superglobular-Type"></a><a id="4273" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a> <a id="4316" class="Symbol">:</a> <a id="4318" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="4342" href="globular-types.superglobular-types.html#4186" class="Bound">l1</a> <a id="4345" href="globular-types.superglobular-types.html#4189" class="Bound">l2</a>

  <a id="Superglobular-Type.globular-type-Superglobular-Type"></a><a id="4351" href="globular-types.superglobular-types.html#4351" class="Function">globular-type-Superglobular-Type</a> <a id="4384" class="Symbol">:</a> <a id="4386" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="4400" href="globular-types.superglobular-types.html#4186" class="Bound">l1</a> <a id="4403" href="globular-types.superglobular-types.html#4189" class="Bound">l2</a>
  <a id="4408" href="globular-types.superglobular-types.html#4351" class="Function">globular-type-Superglobular-Type</a> <a id="4441" class="Symbol">=</a>
    <a id="4447" href="globular-types.reflexive-globular-types.html#4067" class="Field">globular-type-Reflexive-Globular-Type</a>
      <a id="4491" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a>

  <a id="Superglobular-Type.0-cell-Superglobular-Type"></a><a id="4537" href="globular-types.superglobular-types.html#4537" class="Function">0-cell-Superglobular-Type</a> <a id="4563" class="Symbol">:</a> <a id="4565" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4568" href="globular-types.superglobular-types.html#4186" class="Bound">l1</a>
  <a id="4573" href="globular-types.superglobular-types.html#4537" class="Function">0-cell-Superglobular-Type</a> <a id="4599" class="Symbol">=</a>
    <a id="4605" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="4636" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a>

  <a id="Superglobular-Type.point-Superglobular-Type"></a><a id="4682" href="globular-types.superglobular-types.html#4682" class="Function">point-Superglobular-Type</a> <a id="4707" class="Symbol">:</a> <a id="4709" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4712" href="globular-types.superglobular-types.html#4186" class="Bound">l1</a>
  <a id="4717" href="globular-types.superglobular-types.html#4682" class="Function">point-Superglobular-Type</a> <a id="4742" class="Symbol">=</a>
    <a id="4748" href="globular-types.points-reflexive-globular-types.html#1331" class="Function">point-Reflexive-Globular-Type</a> <a id="4778" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a>

  <a id="Superglobular-Type.1-cell-reflexive-globular-type-Superglobular-Type"></a><a id="4824" href="globular-types.superglobular-types.html#4824" class="Function">1-cell-reflexive-globular-type-Superglobular-Type</a> <a id="4874" class="Symbol">:</a>
    <a id="4880" class="Symbol">(</a><a id="4881" href="globular-types.superglobular-types.html#4881" class="Bound">x</a> <a id="4883" href="globular-types.superglobular-types.html#4883" class="Bound">y</a> <a id="4885" class="Symbol">:</a> <a id="4887" href="globular-types.superglobular-types.html#4537" class="Function">0-cell-Superglobular-Type</a><a id="4912" class="Symbol">)</a> <a id="4914" class="Symbol">→</a>
    <a id="4920" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="4944" href="globular-types.superglobular-types.html#4189" class="Bound">l2</a> <a id="4947" href="globular-types.superglobular-types.html#4189" class="Bound">l2</a>
  <a id="4952" href="globular-types.superglobular-types.html#4824" class="Function">1-cell-reflexive-globular-type-Superglobular-Type</a> <a id="5002" class="Symbol">=</a>
    <a id="5008" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a>
      <a id="5069" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a>

  <a id="5115" class="Keyword">field</a>
    <a id="Superglobular-Type.is-superglobular-Superglobular-Type"></a><a id="5125" href="globular-types.superglobular-types.html#5125" class="Field">is-superglobular-Superglobular-Type</a> <a id="5161" class="Symbol">:</a>
      <a id="5169" href="globular-types.superglobular-types.html#2983" class="Function">is-superglobular-Reflexive-Globular-Type</a> <a id="5210" href="globular-types.superglobular-types.html#4192" class="Bound">l3</a> <a id="5213" href="globular-types.superglobular-types.html#4195" class="Bound">l4</a>
        <a id="5224" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a>

  <a id="Superglobular-Type.1-cell-binary-dependent-reflexive-globular-type-Superglobular-Type"></a><a id="5270" href="globular-types.superglobular-types.html#5270" class="Function">1-cell-binary-dependent-reflexive-globular-type-Superglobular-Type</a> <a id="5337" class="Symbol">:</a>
    <a id="5343" href="globular-types.binary-dependent-reflexive-globular-types.html#2962" class="Record">Binary-Dependent-Reflexive-Globular-Type</a> <a id="5384" href="globular-types.superglobular-types.html#4192" class="Bound">l3</a> <a id="5387" href="globular-types.superglobular-types.html#4195" class="Bound">l4</a>
      <a id="5396" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a>
      <a id="5445" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a>
  <a id="5490" href="globular-types.superglobular-types.html#5270" class="Function">1-cell-binary-dependent-reflexive-globular-type-Superglobular-Type</a> <a id="5557" class="Symbol">=</a>
    <a id="5563" href="globular-types.superglobular-types.html#3381" class="Function">1-cell-binary-dependent-reflexive-globular-type-is-superglobular-Reflexive-Globular-Type</a>
      <a id="5658" href="globular-types.superglobular-types.html#5125" class="Field">is-superglobular-Superglobular-Type</a>

  <a id="Superglobular-Type.reflexive-globular-equiv-Superglobular-Type"></a><a id="5697" href="globular-types.superglobular-types.html#5697" class="Function">reflexive-globular-equiv-Superglobular-Type</a> <a id="5741" class="Symbol">:</a>
    <a id="5747" class="Symbol">(</a><a id="5748" href="globular-types.superglobular-types.html#5748" class="Bound">x</a> <a id="5750" href="globular-types.superglobular-types.html#5750" class="Bound">y</a> <a id="5752" class="Symbol">:</a> <a id="5754" href="globular-types.superglobular-types.html#4682" class="Function">point-Superglobular-Type</a><a id="5778" class="Symbol">)</a> <a id="5780" class="Symbol">→</a>
    <a id="5786" href="globular-types.reflexive-globular-equivalences.html#1484" class="Record">reflexive-globular-equiv</a>
      <a id="5817" class="Symbol">(</a> <a id="5819" href="globular-types.binary-dependent-reflexive-globular-types.html#9587" class="Function">ev-point-Binary-Dependent-Reflexive-Globular-Type</a>
        <a id="5877" class="Symbol">(</a> <a id="5879" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a><a id="5921" class="Symbol">)</a>
        <a id="5931" class="Symbol">(</a> <a id="5933" href="globular-types.superglobular-types.html#4273" class="Field">reflexive-globular-type-Superglobular-Type</a><a id="5975" class="Symbol">)</a>
        <a id="5985" class="Symbol">(</a> <a id="5987" href="globular-types.superglobular-types.html#5270" class="Function">1-cell-binary-dependent-reflexive-globular-type-Superglobular-Type</a><a id="6053" class="Symbol">)</a>
        <a id="6063" class="Symbol">(</a> <a id="6065" href="globular-types.superglobular-types.html#5748" class="Bound">x</a><a id="6066" class="Symbol">)</a>
        <a id="6076" class="Symbol">(</a> <a id="6078" href="globular-types.superglobular-types.html#5750" class="Bound">y</a><a id="6079" class="Symbol">))</a>
      <a id="6088" class="Symbol">(</a> <a id="6090" href="globular-types.superglobular-types.html#4824" class="Function">1-cell-reflexive-globular-type-Superglobular-Type</a> <a id="6140" href="globular-types.superglobular-types.html#5748" class="Bound">x</a> <a id="6142" href="globular-types.superglobular-types.html#5750" class="Bound">y</a><a id="6143" class="Symbol">)</a>
  <a id="6147" href="globular-types.superglobular-types.html#5697" class="Function">reflexive-globular-equiv-Superglobular-Type</a> <a id="6191" class="Symbol">=</a>
    <a id="6197" href="globular-types.superglobular-types.html#3633" class="Function">reflexive-globular-equiv-is-superglobular-Reflexive-Globular-Type</a>
      <a id="6269" href="globular-types.superglobular-types.html#5125" class="Field">is-superglobular-Superglobular-Type</a>
</pre>