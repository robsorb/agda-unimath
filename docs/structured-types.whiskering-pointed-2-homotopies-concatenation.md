# Whiskering pointed homotopies with respect to concatenation

<pre class="Agda"><a id="72" class="Keyword">module</a> <a id="79" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html" class="Module">structured-types.whiskering-pointed-2-homotopies-concatenation</a> <a id="142" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.commuting-triangles-of-identifications.html" class="Module">foundation.commuting-triangles-of-identifications</a>
<a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="foundation.path-algebra.html" class="Module">foundation.path-algebra</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="476" class="Keyword">open</a> <a id="481" class="Keyword">import</a> <a id="488" href="foundation.whiskering-homotopies-concatenation.html" class="Module">foundation.whiskering-homotopies-concatenation</a>
<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="foundation.whiskering-identifications-concatenation.html" class="Module">foundation.whiskering-identifications-concatenation</a>

<a id="600" class="Keyword">open</a> <a id="605" class="Keyword">import</a> <a id="612" href="structured-types.pointed-2-homotopies.html" class="Module">structured-types.pointed-2-homotopies</a>
<a id="650" class="Keyword">open</a> <a id="655" class="Keyword">import</a> <a id="662" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="698" class="Keyword">open</a> <a id="703" class="Keyword">import</a> <a id="710" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="740" class="Keyword">open</a> <a id="745" class="Keyword">import</a> <a id="752" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The [whiskering operations](foundation.whiskering-operations.md) of
[pointed `2`-homotopies](structured-types.pointed-2-homotopies.md) with respect
to concatenation of [pointed homotopies](structured-types.pointed-homotopies.md)
are two operations that produce pointed 2-homotopies between concatenations of
pointed homotopies from either a pointed 2-homotopy on the left or on the right
of the concatenations.

- The
  {{#concept "left whiskering" Disambiguation="pointed `2`-homotopies with respect to concatenation" Agda=left-whisker-concat-pointed-2-htpy}}
  is an operation that takes a pointed homotopy `H : f ~∗ g` and a pointed
  `2`-homotopy `α : K ~²∗ L` between two pointed homotopies `K L : g ~∗ h` as
  indicated in the diagram

  ```text
                 K
        H      ----->
    f -----> g -----> h,
                 L
  ```

  and returns a pointed `2`-homotopy `H ∙h K ~²∗ H ∙h L`.

- The
  {{#concept "right whiskering" Disambiguation="pointed `2`-homotopies with respect to concatenation" Agda=right-whisker-concat-pointed-2-htpy}}
  is an operation that takes a pointed `2`-homotopy `α : H ~²∗ K` between two
  pointed homotopies `H K : f ~∗ g` and a pointed homotopy `L : g ~∗ h` as
  indicated in the diagram

  ```text
        H
      ----->
    f -----> g -----> h,
        K        L
  ```

  and returns a pointed `2`-homotopy `H ∙h L ~²∗ K ∙h L`.

## Definitions

### Left whiskering of pointed `2`-homotopies with respect to concatenation

Consider three pointed maps `f := (f₀ , f₁)`, `g := (g₀ , g₁)`, and
`h := (h₀ , h₁)` from `A` to `B`, a pointed homotopy `H := (H₀ , H₁) : f ~∗ g`
and a pointed `2`-homotopy `α := (α₀ , α₁) : K ~²∗ L` between two pointed
homotopies `K := (K₀ , K₁)` and `L := (L₀ , L₁)` from `g` to `h` as indicated in
the diagram

```text
               K
      H      ----->
  f -----> g -----> h.
               L
```

The underlying homotopy of the left whiskering `H ·l∗ α : H ∙h K ~²∗ H ∙h L` is
the homotopy

```text
  H₀ ·l α₀ : H₀ ∙h K₀ ~ H₀ ∙h L₀.
```

The base point coherence of this homotopy is an identification witnessing that
the triangle

```text
           (H ∙h K)₁
        f₁ --------> ((H₀ *) ∙ (K₀ *)) ∙ h₁
           \       /
  (H ∙h L)₁ \     / right-whisker (left-whisker (H₀ *) (α₀ *)) h₁
             \   /
              ∨ ∨
    ((H₀ *) ∙ (L₀ *)) ∙ h₁
```

commutes. Here, the identifications `(H ∙h K)₁` and `(H ∙h L)₁` are the
horizontal pastings of the
[commuting triangles of identifications](foundation.commuting-triangles-of-identifications.md)

```text
       H₀ *      K₀ *                   H₀ *      L₀ *
  f₀ * ---> g₀ * ----> h₀ *        f₀ * ---> g₀ * ----> h₀ *
       \      |      /                  \      |      /
        \  H₁ |  K₁ /                    \  H₁ |  L₁ /
     f₁  \    |g₁  / h₁               f₁  \    |g₁  / h₁
          \   |   /                        \   |   /
           \  |  /                          \  |  /
            ∨ ∨ ∨                            ∨ ∨ ∨
              *                                *.
```

Then the triangle

```text
                   horizontal-pasting H₁ K₁
                       f₁ --------> (H₀ * ∙ K₀ *) ∙ h₁
                         \         /
                          \       /
  horizontal-pasting H₁ L₁ \     / right-whisker (left-whisker (H₀ *) (α₀ *)) h₁
                            \   /
                             ∨ ∨
                        (H₀ * ∙ K₀ *) ∙ h₁
```

commutes by left whiskering of horizontal pasting of commuting triangles of
identifications.

<pre class="Agda"><a id="4343" class="Keyword">module</a> <a id="4350" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4350" class="Module">_</a>
  <a id="4354" class="Symbol">{</a><a id="4355" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4355" class="Bound">l1</a> <a id="4358" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4358" class="Bound">l2</a> <a id="4361" class="Symbol">:</a> <a id="4363" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4368" class="Symbol">}</a> <a id="4370" class="Symbol">{</a><a id="4371" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4371" class="Bound">A</a> <a id="4373" class="Symbol">:</a> <a id="4375" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4388" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4355" class="Bound">l1</a><a id="4390" class="Symbol">}</a> <a id="4392" class="Symbol">{</a><a id="4393" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4393" class="Bound">B</a> <a id="4395" class="Symbol">:</a> <a id="4397" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4410" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4358" class="Bound">l2</a><a id="4412" class="Symbol">}</a>
  <a id="4416" class="Symbol">{</a><a id="4417" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4417" class="Bound">f</a> <a id="4419" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4419" class="Bound">g</a> <a id="4421" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4421" class="Bound">h</a> <a id="4423" class="Symbol">:</a> <a id="4425" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4371" class="Bound">A</a> <a id="4427" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="4430" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4393" class="Bound">B</a><a id="4431" class="Symbol">}</a> <a id="4433" class="Symbol">(</a><a id="4434" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a> <a id="4436" class="Symbol">:</a> <a id="4438" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4417" class="Bound">f</a> <a id="4440" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="4443" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4419" class="Bound">g</a><a id="4444" class="Symbol">)</a> <a id="4446" class="Symbol">(</a><a id="4447" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4447" class="Bound">K</a> <a id="4449" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4449" class="Bound">L</a> <a id="4451" class="Symbol">:</a> <a id="4453" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4419" class="Bound">g</a> <a id="4455" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="4458" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4421" class="Bound">h</a><a id="4459" class="Symbol">)</a> <a id="4461" class="Symbol">(</a><a id="4462" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4462" class="Bound">α</a> <a id="4464" class="Symbol">:</a> <a id="4466" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4447" class="Bound">K</a> <a id="4468" href="structured-types.pointed-2-homotopies.html#4175" class="Function Operator">~²∗</a> <a id="4472" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4449" class="Bound">L</a><a id="4473" class="Symbol">)</a>
  <a id="4477" class="Keyword">where</a>

  <a id="4486" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4486" class="Function">htpy-left-whisker-concat-pointed-2-htpy</a> <a id="4526" class="Symbol">:</a>
    <a id="4532" href="structured-types.pointed-2-homotopies.html#3532" class="Function">unpointed-htpy-pointed-htpy</a>
      <a id="4566" class="Symbol">(</a> <a id="4568" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="4588" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a> <a id="4590" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4447" class="Bound">K</a><a id="4591" class="Symbol">)</a>
      <a id="4599" class="Symbol">(</a> <a id="4601" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="4621" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a> <a id="4623" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4449" class="Bound">L</a><a id="4624" class="Symbol">)</a>
  <a id="4628" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4486" class="Function">htpy-left-whisker-concat-pointed-2-htpy</a> <a id="4668" class="Symbol">=</a>
    <a id="4674" href="foundation-core.whiskering-homotopies-concatenation.html#1554" class="Function">left-whisker-concat-htpy</a> <a id="4699" class="Symbol">(</a><a id="4700" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="4718" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a><a id="4719" class="Symbol">)</a> <a id="4721" class="Symbol">(</a><a id="4722" href="structured-types.pointed-2-homotopies.html#4381" class="Function">htpy-pointed-2-htpy</a> <a id="4742" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4462" class="Bound">α</a><a id="4743" class="Symbol">)</a>

  <a id="4748" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4748" class="Function">coherence-point-left-whisker-concat-pointed-2-htpy</a> <a id="4799" class="Symbol">:</a>
    <a id="4805" href="structured-types.pointed-2-homotopies.html#3656" class="Function">coherence-point-unpointed-htpy-pointed-htpy</a>
      <a id="4855" class="Symbol">(</a> <a id="4857" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="4877" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a> <a id="4879" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4447" class="Bound">K</a><a id="4880" class="Symbol">)</a>
      <a id="4888" class="Symbol">(</a> <a id="4890" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="4910" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a> <a id="4912" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4449" class="Bound">L</a><a id="4913" class="Symbol">)</a>
      <a id="4921" class="Symbol">(</a> <a id="4923" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4486" class="Function">htpy-left-whisker-concat-pointed-2-htpy</a><a id="4962" class="Symbol">)</a>
  <a id="4966" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4748" class="Function">coherence-point-left-whisker-concat-pointed-2-htpy</a> <a id="5017" class="Symbol">=</a>
    <a id="5023" href="foundation.commuting-triangles-of-identifications.html#32965" class="Function">left-whisker-horizontal-pasting-coherence-triangle-identifications</a>
      <a id="5096" class="Symbol">(</a> <a id="5098" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="5126" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4417" class="Bound">f</a><a id="5127" class="Symbol">)</a>
      <a id="5135" class="Symbol">(</a> <a id="5137" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="5165" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4419" class="Bound">g</a><a id="5166" class="Symbol">)</a>
      <a id="5174" class="Symbol">(</a> <a id="5176" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="5204" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4421" class="Bound">h</a><a id="5205" class="Symbol">)</a>
      <a id="5213" class="Symbol">(</a> <a id="5215" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="5233" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a> <a id="5235" class="Symbol">(</a><a id="5236" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5255" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4371" class="Bound">A</a><a id="5256" class="Symbol">))</a>
      <a id="5265" class="Symbol">(</a> <a id="5267" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="5285" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4447" class="Bound">K</a> <a id="5287" class="Symbol">(</a><a id="5288" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5307" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4371" class="Bound">A</a><a id="5308" class="Symbol">))</a>
      <a id="5317" class="Symbol">(</a> <a id="5319" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="5337" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4449" class="Bound">L</a> <a id="5339" class="Symbol">(</a><a id="5340" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5359" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4371" class="Bound">A</a><a id="5360" class="Symbol">))</a>
      <a id="5369" class="Symbol">(</a> <a id="5371" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="5400" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a><a id="5401" class="Symbol">)</a>
      <a id="5409" class="Symbol">(</a> <a id="5411" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="5440" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4447" class="Bound">K</a><a id="5441" class="Symbol">)</a>
      <a id="5449" class="Symbol">(</a> <a id="5451" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="5480" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4449" class="Bound">L</a><a id="5481" class="Symbol">)</a>
      <a id="5489" class="Symbol">(</a> <a id="5491" href="structured-types.pointed-2-homotopies.html#4381" class="Function">htpy-pointed-2-htpy</a> <a id="5511" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4462" class="Bound">α</a> <a id="5513" class="Symbol">(</a><a id="5514" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5533" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4371" class="Bound">A</a><a id="5534" class="Symbol">))</a>
      <a id="5543" class="Symbol">(</a> <a id="5545" href="structured-types.pointed-2-homotopies.html#4468" class="Function">coherence-point-pointed-2-htpy</a> <a id="5576" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4462" class="Bound">α</a><a id="5577" class="Symbol">)</a>

  <a id="5582" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#5582" class="Function">left-whisker-concat-pointed-2-htpy</a> <a id="5617" class="Symbol">:</a>
    <a id="5623" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="5643" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a> <a id="5645" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4447" class="Bound">K</a> <a id="5647" href="structured-types.pointed-2-homotopies.html#4175" class="Function Operator">~²∗</a> <a id="5651" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="5671" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4434" class="Bound">H</a> <a id="5673" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4449" class="Bound">L</a>
  <a id="5677" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5681" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#5582" class="Function">left-whisker-concat-pointed-2-htpy</a> <a id="5716" class="Symbol">=</a>
    <a id="5722" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4486" class="Function">htpy-left-whisker-concat-pointed-2-htpy</a>
  <a id="5764" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5768" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#5582" class="Function">left-whisker-concat-pointed-2-htpy</a> <a id="5803" class="Symbol">=</a>
    <a id="5809" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#4748" class="Function">coherence-point-left-whisker-concat-pointed-2-htpy</a>
</pre>
### Right whiskering of pointed `2`-homotopies with respect to concatenation

Consider three pointed maps `f := (f₀ , f₁)`, `g := (g₀ , g₁)`, and
`h := (h₀ , h₁)` from `A` to `B`, a pointed `2`-homotopy
`α := (α₀ , α₁) : H ~²∗ K` between two pointed homotopies `H := (H₀ , H₁)` and
`K := (K₀ , K₁)` from `f` to `g` and a pointed homotopy
`L := (L₀ , L₁) : g ~∗ h` as indicated in the diagram

```text
      H
    ----->
  f -----> g -----> h.
      K        L
```

The underlying homotopy of the right whiskering `α ·r∗ L : H ∙h L ~²∗ K ∙h L` is
the homotopy

```text
  α₀ ·r L₀ : H₀ ∙h L₀ ~ K₀ ∙h L₀.
```

The base point coherence of this homotopy is an identification witnessing that
the triangle

```text
           (H ∙h L)₁
         f₁ --------> ((H₀ *) ∙ (L₀ *)) ∙ h₁
           \         /
  (K ∙h L)₁ \       / right-whisker (right-whisker (α₀ *) (L₀ *)) h₁
             \     /
              ∨   ∨
      ((K₀ *) ∙ (L₀ *)) ∙ h₁
```

commutes. Here, the identifications `(H ∙h L)₁` and `(K ∙h L)₁` are the
horizontal pastings of the
[commuting triangles of identifications](foundation.commuting-triangles-of-identifications.md)

```text
       H₀ *      L₀ *                   K₀ *      L₀ *
  f₀ * ---> g₀ * ----> h₀ *        f₀ * ---> g₀ * ----> h₀ *
       \      |      /                  \      |      /
        \  H₁ |  L₁ /                    \  K₁ |  L₁ /
     f₁  \    |g₁  / h₁               f₁  \    |g₁  / h₁
          \   |   /                        \   |   /
           \  |  /                          \  |  /
            ∨ ∨ ∨                            ∨ ∨ ∨
              *                                *.
```

Then the triangle

```text
                   horizontal-pasting H₁ L₁
                       f₁ --------> (H₀ * ∙ L₀ *) ∙ h₁
                         \         /
                          \       /
  horizontal-pasting K₁ L₁ \     / right-whisker (right-whisker (α₀ *) (L₀ *)) h₁
                            \   /
                             ∨ ∨
                        (K₀ * ∙ L₀ *) ∙ h₁
```

commutes by right whiskering of horizontal pasting of commuting triangles of
identifications.

<pre class="Agda"><a id="8003" class="Keyword">module</a> <a id="8010" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8010" class="Module">_</a>
  <a id="8014" class="Symbol">{</a><a id="8015" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8015" class="Bound">l1</a> <a id="8018" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8018" class="Bound">l2</a> <a id="8021" class="Symbol">:</a> <a id="8023" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8028" class="Symbol">}</a> <a id="8030" class="Symbol">{</a><a id="8031" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8031" class="Bound">A</a> <a id="8033" class="Symbol">:</a> <a id="8035" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="8048" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8015" class="Bound">l1</a><a id="8050" class="Symbol">}</a> <a id="8052" class="Symbol">{</a><a id="8053" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8053" class="Bound">B</a> <a id="8055" class="Symbol">:</a> <a id="8057" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="8070" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8018" class="Bound">l2</a><a id="8072" class="Symbol">}</a>
  <a id="8076" class="Symbol">{</a><a id="8077" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8077" class="Bound">f</a> <a id="8079" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8079" class="Bound">g</a> <a id="8081" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8081" class="Bound">h</a> <a id="8083" class="Symbol">:</a> <a id="8085" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8031" class="Bound">A</a> <a id="8087" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="8090" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8053" class="Bound">B</a><a id="8091" class="Symbol">}</a> <a id="8093" class="Symbol">(</a><a id="8094" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8094" class="Bound">H</a> <a id="8096" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8096" class="Bound">K</a> <a id="8098" class="Symbol">:</a> <a id="8100" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8077" class="Bound">f</a> <a id="8102" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="8105" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8079" class="Bound">g</a><a id="8106" class="Symbol">)</a> <a id="8108" class="Symbol">(</a><a id="8109" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8109" class="Bound">α</a> <a id="8111" class="Symbol">:</a> <a id="8113" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8094" class="Bound">H</a> <a id="8115" href="structured-types.pointed-2-homotopies.html#4175" class="Function Operator">~²∗</a> <a id="8119" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8096" class="Bound">K</a><a id="8120" class="Symbol">)</a> <a id="8122" class="Symbol">(</a><a id="8123" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a> <a id="8125" class="Symbol">:</a> <a id="8127" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8079" class="Bound">g</a> <a id="8129" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="8132" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8081" class="Bound">h</a><a id="8133" class="Symbol">)</a>
  <a id="8137" class="Keyword">where</a>

  <a id="8146" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8146" class="Function">htpy-right-whisker-concat-pointed-2-htpy</a> <a id="8187" class="Symbol">:</a>
    <a id="8193" href="structured-types.pointed-2-homotopies.html#3532" class="Function">unpointed-htpy-pointed-htpy</a>
      <a id="8227" class="Symbol">(</a> <a id="8229" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="8249" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8094" class="Bound">H</a> <a id="8251" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a><a id="8252" class="Symbol">)</a>
      <a id="8260" class="Symbol">(</a> <a id="8262" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="8282" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8096" class="Bound">K</a> <a id="8284" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a><a id="8285" class="Symbol">)</a>
  <a id="8289" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8146" class="Function">htpy-right-whisker-concat-pointed-2-htpy</a> <a id="8330" class="Symbol">=</a>
    <a id="8336" href="foundation-core.whiskering-homotopies-concatenation.html#2334" class="Function">right-whisker-concat-htpy</a> <a id="8362" class="Symbol">(</a><a id="8363" href="structured-types.pointed-2-homotopies.html#4381" class="Function">htpy-pointed-2-htpy</a> <a id="8383" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8109" class="Bound">α</a><a id="8384" class="Symbol">)</a> <a id="8386" class="Symbol">(</a><a id="8387" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="8405" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a><a id="8406" class="Symbol">)</a>

  <a id="8411" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8411" class="Function">coherence-point-right-whisker-concat-pointed-2-htpy</a> <a id="8463" class="Symbol">:</a>
    <a id="8469" href="structured-types.pointed-2-homotopies.html#3656" class="Function">coherence-point-unpointed-htpy-pointed-htpy</a>
      <a id="8519" class="Symbol">(</a> <a id="8521" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="8541" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8094" class="Bound">H</a> <a id="8543" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a><a id="8544" class="Symbol">)</a>
      <a id="8552" class="Symbol">(</a> <a id="8554" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="8574" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8096" class="Bound">K</a> <a id="8576" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a><a id="8577" class="Symbol">)</a>
      <a id="8585" class="Symbol">(</a> <a id="8587" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8146" class="Function">htpy-right-whisker-concat-pointed-2-htpy</a><a id="8627" class="Symbol">)</a>
  <a id="8631" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8411" class="Function">coherence-point-right-whisker-concat-pointed-2-htpy</a> <a id="8683" class="Symbol">=</a>
    <a id="8689" href="foundation.commuting-triangles-of-identifications.html#35358" class="Function">right-whisker-horizontal-pasting-coherence-triangle-identifications</a>
      <a id="8763" class="Symbol">(</a> <a id="8765" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="8793" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8077" class="Bound">f</a><a id="8794" class="Symbol">)</a>
      <a id="8802" class="Symbol">(</a> <a id="8804" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="8832" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8079" class="Bound">g</a><a id="8833" class="Symbol">)</a>
      <a id="8841" class="Symbol">(</a> <a id="8843" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="8871" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8081" class="Bound">h</a><a id="8872" class="Symbol">)</a>
      <a id="8880" class="Symbol">(</a> <a id="8882" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="8900" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8094" class="Bound">H</a> <a id="8902" class="Symbol">(</a><a id="8903" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="8922" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8031" class="Bound">A</a><a id="8923" class="Symbol">))</a>
      <a id="8932" class="Symbol">(</a> <a id="8934" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="8952" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8096" class="Bound">K</a> <a id="8954" class="Symbol">(</a><a id="8955" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="8974" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8031" class="Bound">A</a><a id="8975" class="Symbol">))</a>
      <a id="8984" class="Symbol">(</a> <a id="8986" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="9004" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a> <a id="9006" class="Symbol">(</a><a id="9007" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="9026" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8031" class="Bound">A</a><a id="9027" class="Symbol">))</a>
      <a id="9036" class="Symbol">(</a> <a id="9038" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="9067" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8094" class="Bound">H</a><a id="9068" class="Symbol">)</a>
      <a id="9076" class="Symbol">(</a> <a id="9078" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="9107" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8096" class="Bound">K</a><a id="9108" class="Symbol">)</a>
      <a id="9116" class="Symbol">(</a> <a id="9118" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="9147" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a><a id="9148" class="Symbol">)</a>
      <a id="9156" class="Symbol">(</a> <a id="9158" href="structured-types.pointed-2-homotopies.html#4381" class="Function">htpy-pointed-2-htpy</a> <a id="9178" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8109" class="Bound">α</a> <a id="9180" class="Symbol">(</a><a id="9181" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="9200" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8031" class="Bound">A</a><a id="9201" class="Symbol">))</a>
      <a id="9210" class="Symbol">(</a> <a id="9212" href="structured-types.pointed-2-homotopies.html#4468" class="Function">coherence-point-pointed-2-htpy</a> <a id="9243" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8109" class="Bound">α</a><a id="9244" class="Symbol">)</a>

  <a id="9249" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#9249" class="Function">right-whisker-concat-pointed-2-htpy</a> <a id="9285" class="Symbol">:</a>
    <a id="9291" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="9311" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8094" class="Bound">H</a> <a id="9313" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a> <a id="9315" href="structured-types.pointed-2-homotopies.html#4175" class="Function Operator">~²∗</a> <a id="9319" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="9339" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8096" class="Bound">K</a> <a id="9341" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8123" class="Bound">L</a>
  <a id="9345" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="9349" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#9249" class="Function">right-whisker-concat-pointed-2-htpy</a> <a id="9385" class="Symbol">=</a>
    <a id="9391" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8146" class="Function">htpy-right-whisker-concat-pointed-2-htpy</a>
  <a id="9434" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="9438" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#9249" class="Function">right-whisker-concat-pointed-2-htpy</a> <a id="9474" class="Symbol">=</a>
    <a id="9480" href="structured-types.whiskering-pointed-2-homotopies-concatenation.html#8411" class="Function">coherence-point-right-whisker-concat-pointed-2-htpy</a>
</pre>