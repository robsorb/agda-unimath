# Whiskering of pointed homotopies with respect to composition of pointed maps

<pre class="Agda"><a id="89" class="Keyword">module</a> <a id="96" href="structured-types.whiskering-pointed-homotopies-composition.html" class="Module">structured-types.whiskering-pointed-homotopies-composition</a> <a id="155" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.action-on-identifications-binary-functions.html" class="Module">foundation.action-on-identifications-binary-functions</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation.commuting-squares-of-identifications.html" class="Module">foundation.commuting-squares-of-identifications</a>
<a id="396" class="Keyword">open</a> <a id="401" class="Keyword">import</a> <a id="408" href="foundation.commuting-triangles-of-identifications.html" class="Module">foundation.commuting-triangles-of-identifications</a>
<a id="458" class="Keyword">open</a> <a id="463" class="Keyword">import</a> <a id="470" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="502" class="Keyword">open</a> <a id="507" class="Keyword">import</a> <a id="514" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="536" class="Keyword">open</a> <a id="541" class="Keyword">import</a> <a id="548" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="574" class="Keyword">open</a> <a id="579" class="Keyword">import</a> <a id="586" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="613" class="Keyword">open</a> <a id="618" class="Keyword">import</a> <a id="625" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>
<a id="670" class="Keyword">open</a> <a id="675" class="Keyword">import</a> <a id="682" href="foundation.whiskering-identifications-concatenation.html" class="Module">foundation.whiskering-identifications-concatenation</a>

<a id="735" class="Keyword">open</a> <a id="740" class="Keyword">import</a> <a id="747" href="structured-types.pointed-2-homotopies.html" class="Module">structured-types.pointed-2-homotopies</a>
<a id="785" class="Keyword">open</a> <a id="790" class="Keyword">import</a> <a id="797" href="structured-types.pointed-families-of-types.html" class="Module">structured-types.pointed-families-of-types</a>
<a id="840" class="Keyword">open</a> <a id="845" class="Keyword">import</a> <a id="852" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="888" class="Keyword">open</a> <a id="893" class="Keyword">import</a> <a id="900" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="930" class="Keyword">open</a> <a id="935" class="Keyword">import</a> <a id="942" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The [whiskering operations](foundation.whiskering-operations.md) of
[pointed homotopies](structured-types.pointed-homotopies.md) with respect to
composition of [pointed maps](structured-types.pointed-maps.md) are two
operations that produce pointed homotopies between composites of pointed maps
from either a pointed homotopy on the left or on the right of the composition.

- Consider a pointed homotopy `H : f ~∗ g` between pointed maps `f g : A →∗ B`,
  and consider a pointed map `h : B →∗ C`, as indicated in the diagram

  ```text
        f
      ----->     h
    A -----> B -----> C.
        g
  ```

  The
  {{#concept "left whiskering operation on pointed homotopies" Agda=left-whisker-comp-pointed-htpy}}
  of `h` and `H` is a pointed homotopy

  ```text
    h ·l∗ H : h ∘∗ f ~∗ h ∘∗ g.
  ```

- Consider a pointed map `f : A →∗ B` and consider a pointed homotopy
  `H : g ~∗ g` between tw pointed maps `g h : B →∗ C`, as indicated in the
  diagram

  ```text
                 g
        f      ----->
    A -----> B -----> C.
                 h
  ```

  The
  {{#concept "right whiskering operation on pointed homotopies" Agda=right-whisker-comp-pointed-htpy}}
  of `H` and `f` is a pointed homotopy

  ```text
    H ·r∗ f : g ∘∗ f ~∗ h ∘∗ f.
  ```

## Definitions

### Left whiskering of pointed homotopies

Consider two pointed maps `f := (f₀ , f₁) : A →∗ B` and
`g := (g₀ , g₁) : A →∗ B` equipped with a pointed homotopy
`H := (H₀ , H₁) : f ~∗ g`, and consider furthermore a pointed map
`h := (h₀ , h₁) : B →∗ C`. Then we construct a pointed homotopy

```text
  h ·l∗ H : (h ∘∗ f) ~∗ (h ∘∗ g).
```

**Construction.** The underlying homotopy of `h ·l∗ H` is the whiskered homotpy

```text
  h₀ ·l H₀.
```

For the coherence, we have to show that the triangle

```text
            ap h₀ (H₀ *)
  h₀ (f₀ *) ------------> h₀ (g₀ *)
           \             /
   ap h₀ f₁ \           / ap h₀ g₁
             ∨         ∨
           h₀ *       h₀ *
               \     /
             h₁ \   / h₁
                 ∨ ∨
                  ∗
```

commutes. By right whiskering of
[commuting triangles of identifications](foundation.commuting-squares-of-identifications.md)
with respect to concatenation it suffices to show that the triangle

```text
           ap h₀ (H₀ *)
  h₀ (f₀ *) ---------> h₀ (g₀ *)
           \          /
   ap h₀ f₁ \        / ap h₀ g₁
             \      /
              ∨    ∨
               h₀ *
```

commutes. By functoriality of commuting triangles of identifications, this
follows from the fact that the triangle

```text
        H₀ *
  f₀ * ------> g₀ *
      \       /
    f₁ \     / g₁
        \   /
         ∨ ∨
          *
```

commutes.

<pre class="Agda"><a id="3686" class="Keyword">module</a> <a id="3693" href="structured-types.whiskering-pointed-homotopies-composition.html#3693" class="Module">_</a>
  <a id="3697" class="Symbol">{</a><a id="3698" href="structured-types.whiskering-pointed-homotopies-composition.html#3698" class="Bound">l1</a> <a id="3701" href="structured-types.whiskering-pointed-homotopies-composition.html#3701" class="Bound">l2</a> <a id="3704" href="structured-types.whiskering-pointed-homotopies-composition.html#3704" class="Bound">l3</a> <a id="3707" class="Symbol">:</a> <a id="3709" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3714" class="Symbol">}</a>
  <a id="3718" class="Symbol">{</a><a id="3719" href="structured-types.whiskering-pointed-homotopies-composition.html#3719" class="Bound">A</a> <a id="3721" class="Symbol">:</a> <a id="3723" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3736" href="structured-types.whiskering-pointed-homotopies-composition.html#3698" class="Bound">l1</a><a id="3738" class="Symbol">}</a> <a id="3740" class="Symbol">{</a><a id="3741" href="structured-types.whiskering-pointed-homotopies-composition.html#3741" class="Bound">B</a> <a id="3743" class="Symbol">:</a> <a id="3745" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3758" href="structured-types.whiskering-pointed-homotopies-composition.html#3701" class="Bound">l2</a><a id="3760" class="Symbol">}</a> <a id="3762" class="Symbol">{</a><a id="3763" href="structured-types.whiskering-pointed-homotopies-composition.html#3763" class="Bound">C</a> <a id="3765" class="Symbol">:</a> <a id="3767" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3780" href="structured-types.whiskering-pointed-homotopies-composition.html#3704" class="Bound">l3</a><a id="3782" class="Symbol">}</a>
  <a id="3786" class="Symbol">(</a><a id="3787" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a> <a id="3789" class="Symbol">:</a> <a id="3791" href="structured-types.whiskering-pointed-homotopies-composition.html#3741" class="Bound">B</a> <a id="3793" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="3796" href="structured-types.whiskering-pointed-homotopies-composition.html#3763" class="Bound">C</a><a id="3797" class="Symbol">)</a> <a id="3799" class="Symbol">(</a><a id="3800" href="structured-types.whiskering-pointed-homotopies-composition.html#3800" class="Bound">f</a> <a id="3802" href="structured-types.whiskering-pointed-homotopies-composition.html#3802" class="Bound">g</a> <a id="3804" class="Symbol">:</a> <a id="3806" href="structured-types.whiskering-pointed-homotopies-composition.html#3719" class="Bound">A</a> <a id="3808" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="3811" href="structured-types.whiskering-pointed-homotopies-composition.html#3741" class="Bound">B</a><a id="3812" class="Symbol">)</a> <a id="3814" class="Symbol">(</a><a id="3815" href="structured-types.whiskering-pointed-homotopies-composition.html#3815" class="Bound">H</a> <a id="3817" class="Symbol">:</a> <a id="3819" href="structured-types.whiskering-pointed-homotopies-composition.html#3800" class="Bound">f</a> <a id="3821" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="3824" href="structured-types.whiskering-pointed-homotopies-composition.html#3802" class="Bound">g</a><a id="3825" class="Symbol">)</a>
  <a id="3829" class="Keyword">where</a>

  <a id="3838" href="structured-types.whiskering-pointed-homotopies-composition.html#3838" class="Function">htpy-left-whisker-comp-pointed-htpy</a> <a id="3874" class="Symbol">:</a>
    <a id="3880" href="structured-types.pointed-maps.html#2776" class="Function">map-comp-pointed-map</a> <a id="3901" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a> <a id="3903" href="structured-types.whiskering-pointed-homotopies-composition.html#3800" class="Bound">f</a> <a id="3905" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="3907" href="structured-types.pointed-maps.html#2776" class="Function">map-comp-pointed-map</a> <a id="3928" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a> <a id="3930" href="structured-types.whiskering-pointed-homotopies-composition.html#3802" class="Bound">g</a>
  <a id="3934" href="structured-types.whiskering-pointed-homotopies-composition.html#3838" class="Function">htpy-left-whisker-comp-pointed-htpy</a> <a id="3970" class="Symbol">=</a>
    <a id="3976" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="3992" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a> <a id="3994" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a> <a id="3997" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="4015" href="structured-types.whiskering-pointed-homotopies-composition.html#3815" class="Bound">H</a>

  <a id="4020" href="structured-types.whiskering-pointed-homotopies-composition.html#4020" class="Function">coherence-point-left-whisker-comp-pointed-htpy</a> <a id="4067" class="Symbol">:</a>
    <a id="4073" href="structured-types.pointed-homotopies.html#5970" class="Function">coherence-point-unpointed-htpy-pointed-Π</a>
      <a id="4120" class="Symbol">(</a> <a id="4122" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a> <a id="4124" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="4127" href="structured-types.whiskering-pointed-homotopies-composition.html#3800" class="Bound">f</a><a id="4128" class="Symbol">)</a>
      <a id="4136" class="Symbol">(</a> <a id="4138" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a> <a id="4140" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="4143" href="structured-types.whiskering-pointed-homotopies-composition.html#3802" class="Bound">g</a><a id="4144" class="Symbol">)</a>
      <a id="4152" class="Symbol">(</a> <a id="4154" href="structured-types.whiskering-pointed-homotopies-composition.html#3838" class="Function">htpy-left-whisker-comp-pointed-htpy</a><a id="4189" class="Symbol">)</a>
  <a id="4193" href="structured-types.whiskering-pointed-homotopies-composition.html#4020" class="Function">coherence-point-left-whisker-comp-pointed-htpy</a> <a id="4240" class="Symbol">=</a>
    <a id="4246" href="foundation.commuting-triangles-of-identifications.html#7682" class="Function">right-whisker-concat-coherence-triangle-identifications</a>
      <a id="4308" class="Symbol">(</a> <a id="4310" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4313" class="Symbol">(</a><a id="4314" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="4330" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a><a id="4331" class="Symbol">)</a> <a id="4333" class="Symbol">(</a><a id="4334" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="4362" href="structured-types.whiskering-pointed-homotopies-composition.html#3800" class="Bound">f</a><a id="4363" class="Symbol">))</a>
      <a id="4372" class="Symbol">(</a> <a id="4374" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4377" class="Symbol">(</a><a id="4378" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="4394" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a><a id="4395" class="Symbol">)</a> <a id="4397" class="Symbol">(</a><a id="4398" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="4426" href="structured-types.whiskering-pointed-homotopies-composition.html#3802" class="Bound">g</a><a id="4427" class="Symbol">))</a>
      <a id="4436" class="Symbol">(</a> <a id="4438" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
        <a id="4449" class="Symbol">(</a> <a id="4451" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="4467" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a><a id="4468" class="Symbol">)</a>
        <a id="4478" class="Symbol">(</a> <a id="4480" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="4498" href="structured-types.whiskering-pointed-homotopies-composition.html#3815" class="Bound">H</a> <a id="4500" class="Symbol">(</a><a id="4501" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="4520" href="structured-types.whiskering-pointed-homotopies-composition.html#3719" class="Bound">A</a><a id="4521" class="Symbol">)))</a>
      <a id="4531" class="Symbol">(</a> <a id="4533" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="4561" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a><a id="4562" class="Symbol">)</a>
      <a id="4570" class="Symbol">(</a> <a id="4572" href="foundation.commuting-triangles-of-identifications.html#14158" class="Function">map-coherence-triangle-identifications</a>
        <a id="4619" class="Symbol">(</a> <a id="4621" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="4637" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a><a id="4638" class="Symbol">)</a>
        <a id="4648" class="Symbol">(</a> <a id="4650" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="4678" href="structured-types.whiskering-pointed-homotopies-composition.html#3800" class="Bound">f</a><a id="4679" class="Symbol">)</a>
        <a id="4689" class="Symbol">(</a> <a id="4691" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="4719" href="structured-types.whiskering-pointed-homotopies-composition.html#3802" class="Bound">g</a><a id="4720" class="Symbol">)</a>
        <a id="4730" class="Symbol">(</a> <a id="4732" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="4750" href="structured-types.whiskering-pointed-homotopies-composition.html#3815" class="Bound">H</a> <a id="4752" class="Symbol">(</a><a id="4753" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="4772" href="structured-types.whiskering-pointed-homotopies-composition.html#3719" class="Bound">A</a><a id="4773" class="Symbol">))</a>
        <a id="4784" class="Symbol">(</a> <a id="4786" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="4815" href="structured-types.whiskering-pointed-homotopies-composition.html#3815" class="Bound">H</a><a id="4816" class="Symbol">))</a>

  <a id="4822" href="structured-types.whiskering-pointed-homotopies-composition.html#4822" class="Function">left-whisker-comp-pointed-htpy</a> <a id="4853" class="Symbol">:</a> <a id="4855" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a> <a id="4857" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="4860" href="structured-types.whiskering-pointed-homotopies-composition.html#3800" class="Bound">f</a> <a id="4862" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="4865" href="structured-types.whiskering-pointed-homotopies-composition.html#3787" class="Bound">h</a> <a id="4867" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="4870" href="structured-types.whiskering-pointed-homotopies-composition.html#3802" class="Bound">g</a>
  <a id="4874" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4878" href="structured-types.whiskering-pointed-homotopies-composition.html#4822" class="Function">left-whisker-comp-pointed-htpy</a> <a id="4909" class="Symbol">=</a>
    <a id="4915" href="structured-types.whiskering-pointed-homotopies-composition.html#3838" class="Function">htpy-left-whisker-comp-pointed-htpy</a>
  <a id="4953" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4957" href="structured-types.whiskering-pointed-homotopies-composition.html#4822" class="Function">left-whisker-comp-pointed-htpy</a> <a id="4988" class="Symbol">=</a>
    <a id="4994" href="structured-types.whiskering-pointed-homotopies-composition.html#4020" class="Function">coherence-point-left-whisker-comp-pointed-htpy</a>
</pre>
### Right whiskering of pointed homotopies

Consider a pointed map `f := (f₀ , f₁) : A →∗ B` and two pointed maps
`g := (g₀ , g₁) : B →∗ C` and `h := (h₀ , h₁) : B →∗ C` equipped with a pointed
homotopy `H := (H₀ , H₁) : g ~∗ h`. Then we construct a pointed homotopy

```text
  H ·r∗ f : (g ∘∗ f) ~∗ (h ∘∗ f).
```

**Construction.** The underlying homotopy of `H ·r∗ f` is the homotopy

```text
  H₀ ·r f₀ : (g₀ ∘ f₀) ~ (h₀ ∘ f₀).
```

Then we have to show that the outer triangle in the diagram

```text
              H₀ (f₀ *)
  g₀ (f₀ *) ------------> h₀ (f₀ *)
           \             /
   ap g₀ f₁ \           / ap h₀ f₁
             ∨  H₀ *   ∨
           g₀ * ----> h₀ *
               \     /
             g₁ \   / h₁
                 ∨ ∨
                  ∗
```

commutes. This is done by vertically pasting the upper square and the lower
triangle. The upper square commutes by inverse naturality of the homotopy `H₀`.
The lower triangle is the base point coherence `H₁` of the pointed homotopy
`H ≐ (H₀ , H₁)`.

<pre class="Agda"><a id="6077" class="Keyword">module</a> <a id="6084" href="structured-types.whiskering-pointed-homotopies-composition.html#6084" class="Module">_</a>
  <a id="6088" class="Symbol">{</a><a id="6089" href="structured-types.whiskering-pointed-homotopies-composition.html#6089" class="Bound">l1</a> <a id="6092" href="structured-types.whiskering-pointed-homotopies-composition.html#6092" class="Bound">l2</a> <a id="6095" href="structured-types.whiskering-pointed-homotopies-composition.html#6095" class="Bound">l3</a> <a id="6098" class="Symbol">:</a> <a id="6100" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6105" class="Symbol">}</a>
  <a id="6109" class="Symbol">{</a><a id="6110" href="structured-types.whiskering-pointed-homotopies-composition.html#6110" class="Bound">A</a> <a id="6112" class="Symbol">:</a> <a id="6114" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6127" href="structured-types.whiskering-pointed-homotopies-composition.html#6089" class="Bound">l1</a><a id="6129" class="Symbol">}</a> <a id="6131" class="Symbol">{</a><a id="6132" href="structured-types.whiskering-pointed-homotopies-composition.html#6132" class="Bound">B</a> <a id="6134" class="Symbol">:</a> <a id="6136" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6149" href="structured-types.whiskering-pointed-homotopies-composition.html#6092" class="Bound">l2</a><a id="6151" class="Symbol">}</a> <a id="6153" class="Symbol">{</a><a id="6154" href="structured-types.whiskering-pointed-homotopies-composition.html#6154" class="Bound">C</a> <a id="6156" class="Symbol">:</a> <a id="6158" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6171" href="structured-types.whiskering-pointed-homotopies-composition.html#6095" class="Bound">l3</a><a id="6173" class="Symbol">}</a>
  <a id="6177" class="Symbol">(</a><a id="6178" href="structured-types.whiskering-pointed-homotopies-composition.html#6178" class="Bound">g1</a> <a id="6181" href="structured-types.whiskering-pointed-homotopies-composition.html#6181" class="Bound">g2</a> <a id="6184" class="Symbol">:</a> <a id="6186" href="structured-types.whiskering-pointed-homotopies-composition.html#6132" class="Bound">B</a> <a id="6188" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6191" href="structured-types.whiskering-pointed-homotopies-composition.html#6154" class="Bound">C</a><a id="6192" class="Symbol">)</a> <a id="6194" class="Symbol">(</a><a id="6195" href="structured-types.whiskering-pointed-homotopies-composition.html#6195" class="Bound">H</a> <a id="6197" class="Symbol">:</a> <a id="6199" href="structured-types.whiskering-pointed-homotopies-composition.html#6178" class="Bound">g1</a> <a id="6202" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="6205" href="structured-types.whiskering-pointed-homotopies-composition.html#6181" class="Bound">g2</a><a id="6207" class="Symbol">)</a> <a id="6209" class="Symbol">(</a><a id="6210" href="structured-types.whiskering-pointed-homotopies-composition.html#6210" class="Bound">f</a> <a id="6212" class="Symbol">:</a> <a id="6214" href="structured-types.whiskering-pointed-homotopies-composition.html#6110" class="Bound">A</a> <a id="6216" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6219" href="structured-types.whiskering-pointed-homotopies-composition.html#6132" class="Bound">B</a><a id="6220" class="Symbol">)</a>
  <a id="6224" class="Keyword">where</a>

  <a id="6233" href="structured-types.whiskering-pointed-homotopies-composition.html#6233" class="Function">htpy-right-whisker-comp-pointed-htpy</a> <a id="6270" class="Symbol">:</a>
    <a id="6276" href="structured-types.pointed-homotopies.html#4961" class="Function">unpointed-htpy-pointed-Π</a> <a id="6301" class="Symbol">(</a><a id="6302" href="structured-types.whiskering-pointed-homotopies-composition.html#6178" class="Bound">g1</a> <a id="6305" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="6308" href="structured-types.whiskering-pointed-homotopies-composition.html#6210" class="Bound">f</a><a id="6309" class="Symbol">)</a> <a id="6311" class="Symbol">(</a><a id="6312" href="structured-types.whiskering-pointed-homotopies-composition.html#6181" class="Bound">g2</a> <a id="6315" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="6318" href="structured-types.whiskering-pointed-homotopies-composition.html#6210" class="Bound">f</a><a id="6319" class="Symbol">)</a>
  <a id="6323" href="structured-types.whiskering-pointed-homotopies-composition.html#6233" class="Function">htpy-right-whisker-comp-pointed-htpy</a> <a id="6360" class="Symbol">=</a>
    <a id="6366" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="6384" href="structured-types.whiskering-pointed-homotopies-composition.html#6195" class="Bound">H</a> <a id="6386" href="foundation.whiskering-homotopies-composition.html#2725" class="Function Operator">·r</a> <a id="6389" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="6405" href="structured-types.whiskering-pointed-homotopies-composition.html#6210" class="Bound">f</a>

  <a id="6410" href="structured-types.whiskering-pointed-homotopies-composition.html#6410" class="Function">coherence-point-right-whisker-comp-pointed-htpy</a> <a id="6458" class="Symbol">:</a>
    <a id="6464" href="structured-types.pointed-homotopies.html#5970" class="Function">coherence-point-unpointed-htpy-pointed-Π</a>
      <a id="6511" class="Symbol">(</a> <a id="6513" href="structured-types.whiskering-pointed-homotopies-composition.html#6178" class="Bound">g1</a> <a id="6516" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="6519" href="structured-types.whiskering-pointed-homotopies-composition.html#6210" class="Bound">f</a><a id="6520" class="Symbol">)</a>
      <a id="6528" class="Symbol">(</a> <a id="6530" href="structured-types.whiskering-pointed-homotopies-composition.html#6181" class="Bound">g2</a> <a id="6533" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="6536" href="structured-types.whiskering-pointed-homotopies-composition.html#6210" class="Bound">f</a><a id="6537" class="Symbol">)</a>
      <a id="6545" class="Symbol">(</a> <a id="6547" href="structured-types.whiskering-pointed-homotopies-composition.html#6233" class="Function">htpy-right-whisker-comp-pointed-htpy</a><a id="6583" class="Symbol">)</a>
  <a id="6587" href="structured-types.whiskering-pointed-homotopies-composition.html#6410" class="Function">coherence-point-right-whisker-comp-pointed-htpy</a> <a id="6635" class="Symbol">=</a>
    <a id="6641" href="foundation.commuting-triangles-of-identifications.html#43161" class="Function">vertical-pasting-coherence-square-coherence-triangle-identifications</a>
      <a id="6716" class="Symbol">(</a> <a id="6718" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="6736" href="structured-types.whiskering-pointed-homotopies-composition.html#6195" class="Bound">H</a> <a id="6738" class="Symbol">_)</a>
      <a id="6747" class="Symbol">(</a> <a id="6749" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="6752" class="Symbol">(</a><a id="6753" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="6769" href="structured-types.whiskering-pointed-homotopies-composition.html#6178" class="Bound">g1</a><a id="6771" class="Symbol">)</a> <a id="6773" class="Symbol">_)</a>
      <a id="6782" class="Symbol">(</a> <a id="6784" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="6787" class="Symbol">(</a><a id="6788" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="6804" href="structured-types.whiskering-pointed-homotopies-composition.html#6181" class="Bound">g2</a><a id="6806" class="Symbol">)</a> <a id="6808" class="Symbol">_)</a>
      <a id="6817" class="Symbol">(</a> <a id="6819" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="6837" href="structured-types.whiskering-pointed-homotopies-composition.html#6195" class="Bound">H</a> <a id="6839" class="Symbol">_)</a>
      <a id="6848" class="Symbol">(</a> <a id="6850" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="6878" href="structured-types.whiskering-pointed-homotopies-composition.html#6178" class="Bound">g1</a><a id="6880" class="Symbol">)</a>
      <a id="6888" class="Symbol">(</a> <a id="6890" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="6918" href="structured-types.whiskering-pointed-homotopies-composition.html#6181" class="Bound">g2</a><a id="6920" class="Symbol">)</a>
      <a id="6928" class="Symbol">(</a> <a id="6930" href="foundation-core.homotopies.html#7217" class="Function">inv-nat-htpy</a> <a id="6943" class="Symbol">(</a><a id="6944" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="6962" href="structured-types.whiskering-pointed-homotopies-composition.html#6195" class="Bound">H</a><a id="6963" class="Symbol">)</a> <a id="6965" class="Symbol">_)</a>
      <a id="6974" class="Symbol">(</a> <a id="6976" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="7005" href="structured-types.whiskering-pointed-homotopies-composition.html#6195" class="Bound">H</a><a id="7006" class="Symbol">)</a>

  <a id="7011" href="structured-types.whiskering-pointed-homotopies-composition.html#7011" class="Function">right-whisker-comp-pointed-htpy</a> <a id="7043" class="Symbol">:</a> <a id="7045" href="structured-types.whiskering-pointed-homotopies-composition.html#6178" class="Bound">g1</a> <a id="7048" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="7051" href="structured-types.whiskering-pointed-homotopies-composition.html#6210" class="Bound">f</a> <a id="7053" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="7056" href="structured-types.whiskering-pointed-homotopies-composition.html#6181" class="Bound">g2</a> <a id="7059" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="7062" href="structured-types.whiskering-pointed-homotopies-composition.html#6210" class="Bound">f</a>
  <a id="7066" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="7070" href="structured-types.whiskering-pointed-homotopies-composition.html#7011" class="Function">right-whisker-comp-pointed-htpy</a> <a id="7102" class="Symbol">=</a>
    <a id="7108" href="structured-types.whiskering-pointed-homotopies-composition.html#6233" class="Function">htpy-right-whisker-comp-pointed-htpy</a>
  <a id="7147" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7151" href="structured-types.whiskering-pointed-homotopies-composition.html#7011" class="Function">right-whisker-comp-pointed-htpy</a> <a id="7183" class="Symbol">=</a>
    <a id="7189" href="structured-types.whiskering-pointed-homotopies-composition.html#6410" class="Function">coherence-point-right-whisker-comp-pointed-htpy</a>
</pre>
## Properties

### Computing the left whiskering of the reflexive pointed homotopy

<pre class="Agda"><a id="7334" class="Keyword">module</a> <a id="7341" href="structured-types.whiskering-pointed-homotopies-composition.html#7341" class="Module">_</a>
  <a id="7345" class="Symbol">{</a><a id="7346" href="structured-types.whiskering-pointed-homotopies-composition.html#7346" class="Bound">l1</a> <a id="7349" href="structured-types.whiskering-pointed-homotopies-composition.html#7349" class="Bound">l2</a> <a id="7352" href="structured-types.whiskering-pointed-homotopies-composition.html#7352" class="Bound">l3</a> <a id="7355" class="Symbol">:</a> <a id="7357" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7362" class="Symbol">}</a>
  <a id="7366" class="Symbol">{</a><a id="7367" href="structured-types.whiskering-pointed-homotopies-composition.html#7367" class="Bound">A</a> <a id="7369" class="Symbol">:</a> <a id="7371" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="7384" href="structured-types.whiskering-pointed-homotopies-composition.html#7346" class="Bound">l1</a><a id="7386" class="Symbol">}</a> <a id="7388" class="Symbol">{</a><a id="7389" href="structured-types.whiskering-pointed-homotopies-composition.html#7389" class="Bound">B</a> <a id="7391" class="Symbol">:</a> <a id="7393" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="7406" href="structured-types.whiskering-pointed-homotopies-composition.html#7349" class="Bound">l2</a><a id="7408" class="Symbol">}</a> <a id="7410" class="Symbol">{</a><a id="7411" href="structured-types.whiskering-pointed-homotopies-composition.html#7411" class="Bound">C</a> <a id="7413" class="Symbol">:</a> <a id="7415" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="7428" href="structured-types.whiskering-pointed-homotopies-composition.html#7352" class="Bound">l3</a><a id="7430" class="Symbol">}</a>
  <a id="7434" class="Symbol">(</a><a id="7435" href="structured-types.whiskering-pointed-homotopies-composition.html#7435" class="Bound">h</a> <a id="7437" class="Symbol">:</a> <a id="7439" href="structured-types.whiskering-pointed-homotopies-composition.html#7389" class="Bound">B</a> <a id="7441" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="7444" href="structured-types.whiskering-pointed-homotopies-composition.html#7411" class="Bound">C</a><a id="7445" class="Symbol">)</a> <a id="7447" class="Symbol">(</a><a id="7448" href="structured-types.whiskering-pointed-homotopies-composition.html#7448" class="Bound">f</a> <a id="7450" class="Symbol">:</a> <a id="7452" href="structured-types.whiskering-pointed-homotopies-composition.html#7367" class="Bound">A</a> <a id="7454" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="7457" href="structured-types.whiskering-pointed-homotopies-composition.html#7389" class="Bound">B</a><a id="7458" class="Symbol">)</a>
  <a id="7462" class="Keyword">where</a>

  <a id="7471" href="structured-types.whiskering-pointed-homotopies-composition.html#7471" class="Function">compute-refl-left-whisker-comp-pointed-htpy</a> <a id="7515" class="Symbol">:</a>
    <a id="7521" href="structured-types.pointed-2-homotopies.html#4028" class="Function">pointed-2-htpy</a>
      <a id="7542" class="Symbol">(</a> <a id="7544" href="structured-types.whiskering-pointed-homotopies-composition.html#4822" class="Function">left-whisker-comp-pointed-htpy</a> <a id="7575" href="structured-types.whiskering-pointed-homotopies-composition.html#7435" class="Bound">h</a> <a id="7577" href="structured-types.whiskering-pointed-homotopies-composition.html#7448" class="Bound">f</a> <a id="7579" href="structured-types.whiskering-pointed-homotopies-composition.html#7448" class="Bound">f</a> <a id="7581" class="Symbol">(</a><a id="7582" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="7600" href="structured-types.whiskering-pointed-homotopies-composition.html#7448" class="Bound">f</a><a id="7601" class="Symbol">))</a>
      <a id="7610" class="Symbol">(</a> <a id="7612" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="7630" class="Symbol">(</a><a id="7631" href="structured-types.whiskering-pointed-homotopies-composition.html#7435" class="Bound">h</a> <a id="7633" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="7636" href="structured-types.whiskering-pointed-homotopies-composition.html#7448" class="Bound">f</a><a id="7637" class="Symbol">))</a>
  <a id="7642" href="structured-types.whiskering-pointed-homotopies-composition.html#7471" class="Function">compute-refl-left-whisker-comp-pointed-htpy</a> <a id="7686" class="Symbol">=</a>
    <a id="7692" href="structured-types.pointed-2-homotopies.html#6348" class="Function">refl-pointed-2-htpy</a> <a id="7712" class="Symbol">(</a><a id="7713" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="7731" class="Symbol">(</a><a id="7732" href="structured-types.whiskering-pointed-homotopies-composition.html#7435" class="Bound">h</a> <a id="7734" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="7737" href="structured-types.whiskering-pointed-homotopies-composition.html#7448" class="Bound">f</a><a id="7738" class="Symbol">))</a>
</pre>
### Computing the right whiskering of the reflexive pointed homotopy

Consider two pointed maps `f := (f₀ , f₁) : A →∗ B` and
`g := (g₀ , g₁) : B →∗ C`. We are constructing a pointed `2`-homotopy

```text
  right-whisker-comp-pointed-htpy (refl-pointed-htpy h) f ~∗
  refl-pointed-htpy (g ∘∗ f)
```

The underlying homotopy of this pointed `2`-homotopy is `refl-htpy`. The base
point coherence of this homotopy is an identification witnessing that the
triangle

```text
                   H₁
  ap g₀ f₁ ∙ g₁ ------> refl ∙ (ap g₀ f₁ ∙ g₁)
               \       /
           refl \     / right-whisker-concat refl (ap g₀ f₁ ∙ g₁) ≐ refl
                 \   /
                  ∨ ∨
       refl ∙ (ap g₀ f₁ ∙ g₁)
```

commutes. Here, the identification `H₁` is the vertical pasting of the upper
square and the lower triangle in the diagram

```text
                refl
  g₀ (f₀ *) ------------> g₀ (f₀ *)
           \             /
   ap g₀ f₁ \           / ap g₀ f₁
             ∨  refl   ∨
           g₀ * ----> g₀ *
               \     /
             g₁ \   / g₁
                 ∨ ∨
                  ∗.
```

The upper square in this diagram is the inverse naturality of the reflexive
homotopy `refl-htpy` and the lower triangle in this diagram is the reflexive
identification.

Recall that the inverse naturality of the reflexive homotopy
`inv-nat-htpy refl-htpy f₁` computes to the horizontally constant square of
identifications. Furthermore, the vertical pasting of the horizontally constant
square `right-unit` and any commuting triangle `refl` computes to `refl`.
Therefore it follows that the identification `H₁` above is equal to `refl`, as
was required to show.

<pre class="Agda"><a id="9431" class="Keyword">module</a> <a id="9438" href="structured-types.whiskering-pointed-homotopies-composition.html#9438" class="Module">_</a>
  <a id="9442" class="Symbol">{</a><a id="9443" href="structured-types.whiskering-pointed-homotopies-composition.html#9443" class="Bound">l1</a> <a id="9446" href="structured-types.whiskering-pointed-homotopies-composition.html#9446" class="Bound">l2</a> <a id="9449" href="structured-types.whiskering-pointed-homotopies-composition.html#9449" class="Bound">l3</a> <a id="9452" class="Symbol">:</a> <a id="9454" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9459" class="Symbol">}</a>
  <a id="9463" class="Symbol">{</a><a id="9464" href="structured-types.whiskering-pointed-homotopies-composition.html#9464" class="Bound">A</a> <a id="9466" class="Symbol">:</a> <a id="9468" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9481" href="structured-types.whiskering-pointed-homotopies-composition.html#9443" class="Bound">l1</a><a id="9483" class="Symbol">}</a> <a id="9485" class="Symbol">{</a><a id="9486" href="structured-types.whiskering-pointed-homotopies-composition.html#9486" class="Bound">B</a> <a id="9488" class="Symbol">:</a> <a id="9490" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9503" href="structured-types.whiskering-pointed-homotopies-composition.html#9446" class="Bound">l2</a><a id="9505" class="Symbol">}</a> <a id="9507" class="Symbol">{</a><a id="9508" href="structured-types.whiskering-pointed-homotopies-composition.html#9508" class="Bound">C</a> <a id="9510" class="Symbol">:</a> <a id="9512" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9525" href="structured-types.whiskering-pointed-homotopies-composition.html#9449" class="Bound">l3</a><a id="9527" class="Symbol">}</a>
  <a id="9531" class="Symbol">(</a><a id="9532" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="9534" class="Symbol">:</a> <a id="9536" href="structured-types.whiskering-pointed-homotopies-composition.html#9486" class="Bound">B</a> <a id="9538" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9541" href="structured-types.whiskering-pointed-homotopies-composition.html#9508" class="Bound">C</a><a id="9542" class="Symbol">)</a> <a id="9544" class="Symbol">(</a><a id="9545" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a> <a id="9547" class="Symbol">:</a> <a id="9549" href="structured-types.whiskering-pointed-homotopies-composition.html#9464" class="Bound">A</a> <a id="9551" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9554" href="structured-types.whiskering-pointed-homotopies-composition.html#9486" class="Bound">B</a><a id="9555" class="Symbol">)</a>
  <a id="9559" class="Keyword">where</a>

  <a id="9568" href="structured-types.whiskering-pointed-homotopies-composition.html#9568" class="Function">htpy-compute-refl-right-whisker-comp-pointed-htpy</a> <a id="9618" class="Symbol">:</a>
    <a id="9624" href="structured-types.pointed-2-homotopies.html#3532" class="Function">unpointed-htpy-pointed-htpy</a>
      <a id="9658" class="Symbol">(</a> <a id="9660" href="structured-types.whiskering-pointed-homotopies-composition.html#7011" class="Function">right-whisker-comp-pointed-htpy</a> <a id="9692" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="9694" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="9696" class="Symbol">(</a><a id="9697" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="9715" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="9716" class="Symbol">)</a> <a id="9718" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="9719" class="Symbol">)</a>
      <a id="9727" class="Symbol">(</a> <a id="9729" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="9747" class="Symbol">(</a><a id="9748" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="9750" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="9753" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="9754" class="Symbol">))</a>
  <a id="9759" href="structured-types.whiskering-pointed-homotopies-composition.html#9568" class="Function">htpy-compute-refl-right-whisker-comp-pointed-htpy</a> <a id="9809" class="Symbol">=</a> <a id="9811" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>

  <a id="9824" href="structured-types.whiskering-pointed-homotopies-composition.html#9824" class="Function">coherence-point-compute-refl-right-whisker-comp-pointed-htpy</a> <a id="9885" class="Symbol">:</a>
    <a id="9891" href="structured-types.pointed-2-homotopies.html#3656" class="Function">coherence-point-unpointed-htpy-pointed-htpy</a>
      <a id="9941" class="Symbol">(</a> <a id="9943" href="structured-types.whiskering-pointed-homotopies-composition.html#7011" class="Function">right-whisker-comp-pointed-htpy</a> <a id="9975" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="9977" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="9979" class="Symbol">(</a><a id="9980" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="9998" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="9999" class="Symbol">)</a> <a id="10001" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="10002" class="Symbol">)</a>
      <a id="10010" class="Symbol">(</a> <a id="10012" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="10030" class="Symbol">(</a><a id="10031" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="10033" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="10036" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="10037" class="Symbol">))</a>
      <a id="10046" class="Symbol">(</a> <a id="10048" href="structured-types.whiskering-pointed-homotopies-composition.html#9568" class="Function">htpy-compute-refl-right-whisker-comp-pointed-htpy</a><a id="10097" class="Symbol">)</a>
  <a id="10101" href="structured-types.whiskering-pointed-homotopies-composition.html#9824" class="Function">coherence-point-compute-refl-right-whisker-comp-pointed-htpy</a> <a id="10162" class="Symbol">=</a>
    <a id="10168" href="foundation-core.identity-types.html#6358" class="Function">inv</a>
      <a id="10178" class="Symbol">(</a> <a id="10180" class="Symbol">(</a> <a id="10182" href="foundation-core.identity-types.html#8440" class="Function">right-unit</a><a id="10192" class="Symbol">)</a> <a id="10194" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
        <a id="10204" class="Symbol">(</a> <a id="10206" class="Symbol">(</a> <a id="10208" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
            <a id="10223" class="Symbol">(</a> <a id="10225" class="Symbol">λ</a> <a id="10227" href="structured-types.whiskering-pointed-homotopies-composition.html#10227" class="Bound">t</a> <a id="10229" class="Symbol">→</a>
              <a id="10245" href="foundation.commuting-triangles-of-identifications.html#43161" class="Function">vertical-pasting-coherence-square-coherence-triangle-identifications</a>
                <a id="10330" class="Symbol">(</a> <a id="10332" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="10336" class="Symbol">)</a>
                <a id="10354" class="Symbol">(</a> <a id="10356" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="10359" class="Symbol">(</a><a id="10360" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="10376" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="10377" class="Symbol">)</a> <a id="10379" class="Symbol">(</a><a id="10380" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="10408" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="10409" class="Symbol">))</a>
                <a id="10428" class="Symbol">(</a> <a id="10430" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="10433" class="Symbol">(</a><a id="10434" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="10450" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="10451" class="Symbol">)</a> <a id="10453" class="Symbol">(</a><a id="10454" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="10482" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="10483" class="Symbol">))</a>
                <a id="10502" class="Symbol">(</a> <a id="10504" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="10508" class="Symbol">)</a>
                <a id="10526" class="Symbol">(</a> <a id="10528" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="10556" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="10557" class="Symbol">)</a>
                <a id="10575" class="Symbol">(</a> <a id="10577" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="10605" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="10606" class="Symbol">)</a>
                <a id="10624" class="Symbol">(</a> <a id="10626" href="structured-types.whiskering-pointed-homotopies-composition.html#10227" class="Bound">t</a><a id="10627" class="Symbol">)</a>
                <a id="10645" class="Symbol">(</a> <a id="10647" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="10651" class="Symbol">))</a>
            <a id="10666" class="Symbol">(</a> <a id="10668" href="foundation-core.homotopies.html#7565" class="Function">inv-nat-refl-htpy</a>
              <a id="10700" class="Symbol">(</a> <a id="10702" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="10718" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="10719" class="Symbol">)</a>
              <a id="10735" class="Symbol">(</a> <a id="10737" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="10765" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="10766" class="Symbol">)))</a> <a id="10770" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
          <a id="10782" class="Symbol">(</a> <a id="10784" href="foundation-core.commuting-squares-of-identifications.html#35931" class="Function">right-whisker-concat-horizontal-refl-coherence-square-identifications</a>
            <a id="10866" class="Symbol">(</a> <a id="10868" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="10871" class="Symbol">(</a><a id="10872" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="10888" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="10889" class="Symbol">)</a> <a id="10891" class="Symbol">(</a><a id="10892" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="10920" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="10921" class="Symbol">))</a>
            <a id="10936" class="Symbol">(</a> <a id="10938" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="10966" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="10967" class="Symbol">))))</a>

  <a id="10975" href="structured-types.whiskering-pointed-homotopies-composition.html#10975" class="Function">compute-refl-right-whisker-comp-pointed-htpy</a> <a id="11020" class="Symbol">:</a>
    <a id="11026" href="structured-types.pointed-2-homotopies.html#4028" class="Function">pointed-2-htpy</a>
      <a id="11047" class="Symbol">(</a> <a id="11049" href="structured-types.whiskering-pointed-homotopies-composition.html#7011" class="Function">right-whisker-comp-pointed-htpy</a> <a id="11081" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="11083" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="11085" class="Symbol">(</a><a id="11086" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="11104" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a><a id="11105" class="Symbol">)</a> <a id="11107" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="11108" class="Symbol">)</a>
      <a id="11116" class="Symbol">(</a> <a id="11118" href="structured-types.pointed-homotopies.html#7093" class="Function">refl-pointed-htpy</a> <a id="11136" class="Symbol">(</a><a id="11137" href="structured-types.whiskering-pointed-homotopies-composition.html#9532" class="Bound">h</a> <a id="11139" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="11142" href="structured-types.whiskering-pointed-homotopies-composition.html#9545" class="Bound">f</a><a id="11143" class="Symbol">))</a>
  <a id="11148" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="11152" href="structured-types.whiskering-pointed-homotopies-composition.html#10975" class="Function">compute-refl-right-whisker-comp-pointed-htpy</a> <a id="11197" class="Symbol">=</a>
    <a id="11203" href="structured-types.whiskering-pointed-homotopies-composition.html#9568" class="Function">htpy-compute-refl-right-whisker-comp-pointed-htpy</a>
  <a id="11255" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="11259" href="structured-types.whiskering-pointed-homotopies-composition.html#10975" class="Function">compute-refl-right-whisker-comp-pointed-htpy</a> <a id="11304" class="Symbol">=</a>
    <a id="11310" href="structured-types.whiskering-pointed-homotopies-composition.html#9824" class="Function">coherence-point-compute-refl-right-whisker-comp-pointed-htpy</a>
</pre>