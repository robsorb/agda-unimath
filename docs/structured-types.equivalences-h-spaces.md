# Equivalences of H-spaces

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="structured-types.equivalences-h-spaces.html" class="Module">structured-types.equivalences-h-spaces</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.action-on-higher-identifications-functions.html" class="Module">foundation.action-on-higher-identifications-functions</a>
<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.action-on-identifications-binary-functions.html" class="Module">foundation.action-on-identifications-binary-functions</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="foundation.commuting-squares-of-identifications.html" class="Module">foundation.commuting-squares-of-identifications</a>
<a id="390" class="Keyword">open</a> <a id="395" class="Keyword">import</a> <a id="402" href="foundation.commuting-triangles-of-identifications.html" class="Module">foundation.commuting-triangles-of-identifications</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="496" class="Keyword">open</a> <a id="501" class="Keyword">import</a> <a id="508" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="534" class="Keyword">open</a> <a id="539" class="Keyword">import</a> <a id="546" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="568" class="Keyword">open</a> <a id="573" class="Keyword">import</a> <a id="580" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="606" class="Keyword">open</a> <a id="611" class="Keyword">import</a> <a id="618" href="foundation.path-algebra.html" class="Module">foundation.path-algebra</a>
<a id="642" class="Keyword">open</a> <a id="647" class="Keyword">import</a> <a id="654" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="681" class="Keyword">open</a> <a id="686" class="Keyword">import</a> <a id="693" href="foundation.whiskering-identifications-concatenation.html" class="Module">foundation.whiskering-identifications-concatenation</a>

<a id="746" class="Keyword">open</a> <a id="751" class="Keyword">import</a> <a id="758" href="group-theory.homomorphisms-semigroups.html" class="Module">group-theory.homomorphisms-semigroups</a>

<a id="797" class="Keyword">open</a> <a id="802" class="Keyword">import</a> <a id="809" href="structured-types.h-spaces.html" class="Module">structured-types.h-spaces</a>
<a id="835" class="Keyword">open</a> <a id="840" class="Keyword">import</a> <a id="847" href="structured-types.morphisms-h-spaces.html" class="Module">structured-types.morphisms-h-spaces</a>
<a id="883" class="Keyword">open</a> <a id="888" class="Keyword">import</a> <a id="895" href="structured-types.pointed-equivalences.html" class="Module">structured-types.pointed-equivalences</a>
<a id="933" class="Keyword">open</a> <a id="938" class="Keyword">import</a> <a id="945" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="975" class="Keyword">open</a> <a id="980" class="Keyword">import</a> <a id="987" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

Consider two [H-spaces](structured-types.h-spaces.md) `X` and `Y`. An
{{#concept "equivalence of H-spaces" Agda=equiv-H-Space}} from `X` to `Y`
consists of a [pointed equivalence](structured-types.pointed-equivalences.md)
`e : X ≃∗ Y` that preserves the unital binary operation

```text
  α : (x x' : X) → e (μ x x') ＝ μ (e x) (e x')
```

and which furthermore comes equipped with the following structure, witnessing
that the unit laws are preserved:

- For each `x' : X` an identification `α₁ x'` witnessing that the triangle

  ```text
                              α * x'
                  e (μ * x') -------> μ (e *) (e x')
                        \                 /
                         \               / ap (μ - (e x')) e₁
                          \             /
                           \           ∨
    ap e (left-unit-law x') \       μ * (e x')
                             \       /
                              \     / left-unit-law (e x')
                               \   /
                                ∨ ∨
                                e x'
  ```

  commutes.

- For each `x : X` an identification `α₂ x` witnessing that the triangle

  ```text
                              α x *
                  e (μ x *) --------> μ (e x) (e *)
                        \                 /
                         \               / ap (μ (e x) -) e₁
                          \             /
                           \           ∨
    ap e (right-unit-law x) \       μ (e x) *
                             \       /
                              \     / right-unit-law (e x)
                               \   /
                                ∨ ∨
                                e x
  ```

  commutes.

- An identification `α₃` witnessing that the square

  ```text
                                                     α₁
     α₀ * * ∙ (ap (μ - (e *)) e₁ ∙ left-unit-law *) ---> ap e (left-unit-law *)
                       |                                         |
         (α₀ * *) ·l β |                                         |
                       ∨                                         ∨
    α₀ * * ∙ (ap (μ (e *) -) e₁ ∙ right-unit-law *) ---> ap e (right-unit-law *)
                                                     α₂
  ```

  Here, the identification on the left is obtained by left whiskering the
  identification witnessing that the square

  ```text
                               ap (μ (e *)) e₁
                μ (e *) (e *) -----------------> μ (e *) *
                      |                               |
    ap (μ - (e *)) e₁ |                 β             | right-unit-law (e *)
                      ∨                               ∨
                   μ * (e *) ----------------------> e *
                               left-unit-law (e *)
  ```

  commutes, with the identification `α * * : e (μ * *) ＝ μ (e *) (e *)`. The
  quickest way to see that this square commutes is by identification elimination
  on the identification `e₁ : e * ＝ *`, using the coherence
  `left-unit-law * ＝ right-unit-law *`. Alternatively, note that all the
  squares in the diagram

  ```text
                               ap (μ (e *)) e₁
                μ (e *) (e *) -----------------> μ (e *) * --------> e *
                      |                               |               |
    ap (μ - (e *)) e₁ |                 ap (μ - *) e₁ |               |
                      ∨                               ∨               ∨
                   μ * (e *) ---------------------> μ * * ----------> *
                      |            ap (μ *) e₁        |               |
                      |                               |  coh ·r refl  | refl
                      ∨                               ∨               ∨
                     e * ---------------------------> * ------------> *
                                       e₁                  refl
  ```

  commute. Therefore we obtain an identification

  ```text
    ap (μ - (e *)) e₁ ∙ (left-unit-law (e *) ∙ e₁) ＝
    ap (μ (e *) -) e₁ ∙ (right-unit-law (e *) ∙ e₁).
  ```

  By unwhiskering of commuting squares of identifications, i.e., by canceling
  out `e₁` on both sides, it follows that the asserted square commutes.

## Definition

### The predicate of preserving H-space structure on a pointed type

<pre class="Agda"><a id="5367" class="Keyword">module</a> <a id="5374" href="structured-types.equivalences-h-spaces.html#5374" class="Module">_</a>
  <a id="5378" class="Symbol">{</a><a id="5379" href="structured-types.equivalences-h-spaces.html#5379" class="Bound">l1</a> <a id="5382" href="structured-types.equivalences-h-spaces.html#5382" class="Bound">l2</a> <a id="5385" class="Symbol">:</a> <a id="5387" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5392" class="Symbol">}</a> <a id="5394" class="Symbol">(</a><a id="5395" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="5397" class="Symbol">:</a> <a id="5399" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="5407" href="structured-types.equivalences-h-spaces.html#5379" class="Bound">l1</a><a id="5409" class="Symbol">)</a> <a id="5411" class="Symbol">(</a><a id="5412" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a> <a id="5414" class="Symbol">:</a> <a id="5416" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="5424" href="structured-types.equivalences-h-spaces.html#5382" class="Bound">l2</a><a id="5426" class="Symbol">)</a>
  <a id="5430" class="Keyword">where</a>

  <a id="5439" href="structured-types.equivalences-h-spaces.html#5439" class="Function">preserves-mul-pointed-equiv-H-Space</a> <a id="5475" class="Symbol">:</a>
    <a id="5481" class="Symbol">(</a><a id="5482" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="5503" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="5505" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="5508" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="5529" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a><a id="5530" class="Symbol">)</a> <a id="5532" class="Symbol">→</a> <a id="5534" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5537" class="Symbol">(</a><a id="5538" href="structured-types.equivalences-h-spaces.html#5379" class="Bound">l1</a> <a id="5541" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="5543" href="structured-types.equivalences-h-spaces.html#5382" class="Bound">l2</a><a id="5545" class="Symbol">)</a>
  <a id="5549" href="structured-types.equivalences-h-spaces.html#5439" class="Function">preserves-mul-pointed-equiv-H-Space</a> <a id="5585" href="structured-types.equivalences-h-spaces.html#5585" class="Bound">e</a> <a id="5587" class="Symbol">=</a>
    <a id="5593" href="structured-types.morphisms-h-spaces.html#6584" class="Function">preserves-mul-pointed-map-H-Space</a> <a id="5627" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="5629" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a> <a id="5631" class="Symbol">(</a><a id="5632" href="structured-types.pointed-equivalences.html#7765" class="Function">pointed-map-pointed-equiv</a> <a id="5658" href="structured-types.equivalences-h-spaces.html#5585" class="Bound">e</a><a id="5659" class="Symbol">)</a>

  <a id="5664" href="structured-types.equivalences-h-spaces.html#5664" class="Function">preserves-left-unit-law-mul-pointed-equiv-H-Space</a> <a id="5714" class="Symbol">:</a>
    <a id="5720" class="Symbol">(</a><a id="5721" href="structured-types.equivalences-h-spaces.html#5721" class="Bound">e</a> <a id="5723" class="Symbol">:</a> <a id="5725" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="5746" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="5748" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="5751" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="5772" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a><a id="5773" class="Symbol">)</a> <a id="5775" class="Symbol">→</a>
    <a id="5781" href="structured-types.equivalences-h-spaces.html#5439" class="Function">preserves-mul-pointed-equiv-H-Space</a> <a id="5817" href="structured-types.equivalences-h-spaces.html#5721" class="Bound">e</a> <a id="5819" class="Symbol">→</a> <a id="5821" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5824" class="Symbol">(</a><a id="5825" href="structured-types.equivalences-h-spaces.html#5379" class="Bound">l1</a> <a id="5828" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="5830" href="structured-types.equivalences-h-spaces.html#5382" class="Bound">l2</a><a id="5832" class="Symbol">)</a>
  <a id="5836" href="structured-types.equivalences-h-spaces.html#5664" class="Function">preserves-left-unit-law-mul-pointed-equiv-H-Space</a> <a id="5886" href="structured-types.equivalences-h-spaces.html#5886" class="Bound">e</a> <a id="5888" class="Symbol">=</a>
    <a id="5894" href="structured-types.morphisms-h-spaces.html#6803" class="Function">preserves-left-unit-law-mul-pointed-map-H-Space</a> <a id="5942" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="5944" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a>
      <a id="5952" class="Symbol">(</a> <a id="5954" href="structured-types.pointed-equivalences.html#7765" class="Function">pointed-map-pointed-equiv</a> <a id="5980" href="structured-types.equivalences-h-spaces.html#5886" class="Bound">e</a><a id="5981" class="Symbol">)</a>

  <a id="5986" href="structured-types.equivalences-h-spaces.html#5986" class="Function">preserves-right-unit-law-mul-pointed-equiv-H-Space</a> <a id="6037" class="Symbol">:</a>
    <a id="6043" class="Symbol">(</a><a id="6044" href="structured-types.equivalences-h-spaces.html#6044" class="Bound">e</a> <a id="6046" class="Symbol">:</a> <a id="6048" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="6069" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="6071" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="6074" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="6095" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a><a id="6096" class="Symbol">)</a> <a id="6098" class="Symbol">→</a>
    <a id="6104" href="structured-types.equivalences-h-spaces.html#5439" class="Function">preserves-mul-pointed-equiv-H-Space</a> <a id="6140" href="structured-types.equivalences-h-spaces.html#6044" class="Bound">e</a> <a id="6142" class="Symbol">→</a> <a id="6144" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6147" class="Symbol">(</a><a id="6148" href="structured-types.equivalences-h-spaces.html#5379" class="Bound">l1</a> <a id="6151" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="6153" href="structured-types.equivalences-h-spaces.html#5382" class="Bound">l2</a><a id="6155" class="Symbol">)</a>
  <a id="6159" href="structured-types.equivalences-h-spaces.html#5986" class="Function">preserves-right-unit-law-mul-pointed-equiv-H-Space</a> <a id="6210" href="structured-types.equivalences-h-spaces.html#6210" class="Bound">e</a> <a id="6212" class="Symbol">=</a>
    <a id="6218" href="structured-types.morphisms-h-spaces.html#7195" class="Function">preserves-right-unit-law-mul-pointed-map-H-Space</a> <a id="6267" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="6269" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a>
      <a id="6277" class="Symbol">(</a> <a id="6279" href="structured-types.pointed-equivalences.html#7765" class="Function">pointed-map-pointed-equiv</a> <a id="6305" href="structured-types.equivalences-h-spaces.html#6210" class="Bound">e</a><a id="6306" class="Symbol">)</a>

  <a id="6311" href="structured-types.equivalences-h-spaces.html#6311" class="Function">preserves-coherence-unit-laws-mul-pointed-equiv-H-Space</a> <a id="6367" class="Symbol">:</a>
    <a id="6373" class="Symbol">(</a><a id="6374" href="structured-types.equivalences-h-spaces.html#6374" class="Bound">e</a> <a id="6376" class="Symbol">:</a> <a id="6378" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="6399" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="6401" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="6404" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="6425" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a><a id="6426" class="Symbol">)</a> <a id="6428" class="Symbol">→</a>
    <a id="6434" class="Symbol">(</a><a id="6435" href="structured-types.equivalences-h-spaces.html#6435" class="Bound">μ</a> <a id="6437" class="Symbol">:</a> <a id="6439" href="structured-types.equivalences-h-spaces.html#5439" class="Function">preserves-mul-pointed-equiv-H-Space</a> <a id="6475" href="structured-types.equivalences-h-spaces.html#6374" class="Bound">e</a><a id="6476" class="Symbol">)</a> <a id="6478" class="Symbol">→</a>
    <a id="6484" class="Symbol">(</a><a id="6485" href="structured-types.equivalences-h-spaces.html#6485" class="Bound">ν</a> <a id="6487" class="Symbol">:</a> <a id="6489" href="structured-types.equivalences-h-spaces.html#5664" class="Function">preserves-left-unit-law-mul-pointed-equiv-H-Space</a> <a id="6539" href="structured-types.equivalences-h-spaces.html#6374" class="Bound">e</a> <a id="6541" href="structured-types.equivalences-h-spaces.html#6435" class="Bound">μ</a><a id="6542" class="Symbol">)</a> <a id="6544" class="Symbol">→</a>
    <a id="6550" class="Symbol">(</a><a id="6551" href="structured-types.equivalences-h-spaces.html#6551" class="Bound">ρ</a> <a id="6553" class="Symbol">:</a> <a id="6555" href="structured-types.equivalences-h-spaces.html#5986" class="Function">preserves-right-unit-law-mul-pointed-equiv-H-Space</a> <a id="6606" href="structured-types.equivalences-h-spaces.html#6374" class="Bound">e</a> <a id="6608" href="structured-types.equivalences-h-spaces.html#6435" class="Bound">μ</a><a id="6609" class="Symbol">)</a> <a id="6611" class="Symbol">→</a> <a id="6613" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6616" href="structured-types.equivalences-h-spaces.html#5382" class="Bound">l2</a>
  <a id="6621" href="structured-types.equivalences-h-spaces.html#6311" class="Function">preserves-coherence-unit-laws-mul-pointed-equiv-H-Space</a> <a id="6677" href="structured-types.equivalences-h-spaces.html#6677" class="Bound">e</a> <a id="6679" class="Symbol">=</a>
    <a id="6685" href="structured-types.morphisms-h-spaces.html#8248" class="Function">preserves-coherence-unit-laws-mul-pointed-map-H-Space</a> <a id="6739" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="6741" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a>
      <a id="6749" class="Symbol">(</a> <a id="6751" href="structured-types.pointed-equivalences.html#7765" class="Function">pointed-map-pointed-equiv</a> <a id="6777" href="structured-types.equivalences-h-spaces.html#6677" class="Bound">e</a><a id="6778" class="Symbol">)</a>

  <a id="6783" href="structured-types.equivalences-h-spaces.html#6783" class="Function">preserves-unital-mul-pointed-equiv-H-Space</a> <a id="6826" class="Symbol">:</a>
    <a id="6832" class="Symbol">(</a><a id="6833" href="structured-types.equivalences-h-spaces.html#6833" class="Bound">e</a> <a id="6835" class="Symbol">:</a> <a id="6837" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="6858" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="6860" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="6863" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="6884" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a><a id="6885" class="Symbol">)</a> <a id="6887" class="Symbol">→</a>
    <a id="6893" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6896" class="Symbol">(</a><a id="6897" href="structured-types.equivalences-h-spaces.html#5379" class="Bound">l1</a> <a id="6900" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="6902" href="structured-types.equivalences-h-spaces.html#5382" class="Bound">l2</a><a id="6904" class="Symbol">)</a>
  <a id="6908" href="structured-types.equivalences-h-spaces.html#6783" class="Function">preserves-unital-mul-pointed-equiv-H-Space</a> <a id="6951" href="structured-types.equivalences-h-spaces.html#6951" class="Bound">e</a> <a id="6953" class="Symbol">=</a>
    <a id="6959" href="structured-types.morphisms-h-spaces.html#8891" class="Function">preserves-unital-mul-pointed-map-H-Space</a> <a id="7000" href="structured-types.equivalences-h-spaces.html#5395" class="Bound">M</a> <a id="7002" href="structured-types.equivalences-h-spaces.html#5412" class="Bound">N</a> <a id="7004" class="Symbol">(</a><a id="7005" href="structured-types.pointed-equivalences.html#7765" class="Function">pointed-map-pointed-equiv</a> <a id="7031" href="structured-types.equivalences-h-spaces.html#6951" class="Bound">e</a><a id="7032" class="Symbol">)</a>
</pre>
### Equivalences of H-spaces

<pre class="Agda"><a id="7077" class="Keyword">module</a> <a id="7084" href="structured-types.equivalences-h-spaces.html#7084" class="Module">_</a>
  <a id="7088" class="Symbol">{</a><a id="7089" href="structured-types.equivalences-h-spaces.html#7089" class="Bound">l1</a> <a id="7092" href="structured-types.equivalences-h-spaces.html#7092" class="Bound">l2</a> <a id="7095" class="Symbol">:</a> <a id="7097" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7102" class="Symbol">}</a> <a id="7104" class="Symbol">(</a><a id="7105" href="structured-types.equivalences-h-spaces.html#7105" class="Bound">M</a> <a id="7107" class="Symbol">:</a> <a id="7109" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="7117" href="structured-types.equivalences-h-spaces.html#7089" class="Bound">l1</a><a id="7119" class="Symbol">)</a> <a id="7121" class="Symbol">(</a><a id="7122" href="structured-types.equivalences-h-spaces.html#7122" class="Bound">N</a> <a id="7124" class="Symbol">:</a> <a id="7126" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="7134" href="structured-types.equivalences-h-spaces.html#7092" class="Bound">l2</a><a id="7136" class="Symbol">)</a>
  <a id="7140" class="Keyword">where</a>

  <a id="7149" href="structured-types.equivalences-h-spaces.html#7149" class="Function">equiv-H-Space</a> <a id="7163" class="Symbol">:</a> <a id="7165" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="7168" class="Symbol">(</a><a id="7169" href="structured-types.equivalences-h-spaces.html#7089" class="Bound">l1</a> <a id="7172" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="7174" href="structured-types.equivalences-h-spaces.html#7092" class="Bound">l2</a><a id="7176" class="Symbol">)</a>
  <a id="7180" href="structured-types.equivalences-h-spaces.html#7149" class="Function">equiv-H-Space</a> <a id="7194" class="Symbol">=</a>
    <a id="7200" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="7202" class="Symbol">(</a> <a id="7204" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="7225" href="structured-types.equivalences-h-spaces.html#7105" class="Bound">M</a> <a id="7227" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="7230" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="7251" href="structured-types.equivalences-h-spaces.html#7122" class="Bound">N</a><a id="7252" class="Symbol">)</a>
      <a id="7260" class="Symbol">(</a> <a id="7262" href="structured-types.equivalences-h-spaces.html#6783" class="Function">preserves-unital-mul-pointed-equiv-H-Space</a> <a id="7305" href="structured-types.equivalences-h-spaces.html#7105" class="Bound">M</a> <a id="7307" href="structured-types.equivalences-h-spaces.html#7122" class="Bound">N</a><a id="7308" class="Symbol">)</a>

<a id="7311" class="Keyword">module</a> <a id="7318" href="structured-types.equivalences-h-spaces.html#7318" class="Module">_</a>
  <a id="7322" class="Symbol">{</a><a id="7323" href="structured-types.equivalences-h-spaces.html#7323" class="Bound">l1</a> <a id="7326" href="structured-types.equivalences-h-spaces.html#7326" class="Bound">l2</a> <a id="7329" class="Symbol">:</a> <a id="7331" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7336" class="Symbol">}</a> <a id="7338" class="Symbol">{</a><a id="7339" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="7341" class="Symbol">:</a> <a id="7343" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="7351" href="structured-types.equivalences-h-spaces.html#7323" class="Bound">l1</a><a id="7353" class="Symbol">}</a> <a id="7355" class="Symbol">{</a><a id="7356" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a> <a id="7358" class="Symbol">:</a> <a id="7360" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="7368" href="structured-types.equivalences-h-spaces.html#7326" class="Bound">l2</a><a id="7370" class="Symbol">}</a> <a id="7372" class="Symbol">(</a><a id="7373" href="structured-types.equivalences-h-spaces.html#7373" class="Bound">e</a> <a id="7375" class="Symbol">:</a> <a id="7377" href="structured-types.equivalences-h-spaces.html#7149" class="Function">equiv-H-Space</a> <a id="7391" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="7393" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a><a id="7394" class="Symbol">)</a>
  <a id="7398" class="Keyword">where</a>

  <a id="7407" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a> <a id="7435" class="Symbol">:</a> <a id="7437" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="7458" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="7460" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="7463" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="7484" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a>
  <a id="7488" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a> <a id="7516" class="Symbol">=</a> <a id="7518" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="7522" href="structured-types.equivalences-h-spaces.html#7373" class="Bound">e</a>

  <a id="7527" href="structured-types.equivalences-h-spaces.html#7527" class="Function">map-equiv-H-Space</a> <a id="7545" class="Symbol">:</a> <a id="7547" href="structured-types.h-spaces.html#2880" class="Function">type-H-Space</a> <a id="7560" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="7562" class="Symbol">→</a> <a id="7564" href="structured-types.h-spaces.html#2880" class="Function">type-H-Space</a> <a id="7577" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a>
  <a id="7581" href="structured-types.equivalences-h-spaces.html#7527" class="Function">map-equiv-H-Space</a> <a id="7599" class="Symbol">=</a> <a id="7601" href="structured-types.pointed-equivalences.html#7505" class="Function">map-pointed-equiv</a> <a id="7619" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a>

  <a id="7650" href="structured-types.equivalences-h-spaces.html#7650" class="Function">preserves-unit-equiv-H-Space</a> <a id="7679" class="Symbol">:</a>
    <a id="7685" href="structured-types.equivalences-h-spaces.html#7527" class="Function">map-equiv-H-Space</a> <a id="7703" class="Symbol">(</a><a id="7704" href="structured-types.h-spaces.html#2959" class="Function">unit-H-Space</a> <a id="7717" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a><a id="7718" class="Symbol">)</a> <a id="7720" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="7722" href="structured-types.h-spaces.html#2959" class="Function">unit-H-Space</a> <a id="7735" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a>
  <a id="7739" href="structured-types.equivalences-h-spaces.html#7650" class="Function">preserves-unit-equiv-H-Space</a> <a id="7768" class="Symbol">=</a>
    <a id="7774" href="structured-types.pointed-equivalences.html#7622" class="Function">preserves-point-pointed-equiv</a> <a id="7804" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a>

  <a id="7835" href="structured-types.equivalences-h-spaces.html#7835" class="Function">preserves-unital-mul-equiv-H-Space</a> <a id="7870" class="Symbol">:</a>
    <a id="7876" href="structured-types.equivalences-h-spaces.html#6783" class="Function">preserves-unital-mul-pointed-equiv-H-Space</a> <a id="7919" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="7921" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a> <a id="7923" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a>
  <a id="7953" href="structured-types.equivalences-h-spaces.html#7835" class="Function">preserves-unital-mul-equiv-H-Space</a> <a id="7988" class="Symbol">=</a> <a id="7990" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7994" href="structured-types.equivalences-h-spaces.html#7373" class="Bound">e</a>

  <a id="7999" href="structured-types.equivalences-h-spaces.html#7999" class="Function">preserves-mul-equiv-H-Space</a> <a id="8027" class="Symbol">:</a>
    <a id="8033" href="structured-types.equivalences-h-spaces.html#5439" class="Function">preserves-mul-pointed-equiv-H-Space</a> <a id="8069" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="8071" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a> <a id="8073" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a>
  <a id="8103" href="structured-types.equivalences-h-spaces.html#7999" class="Function">preserves-mul-equiv-H-Space</a> <a id="8131" class="Symbol">=</a>
    <a id="8137" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8141" href="structured-types.equivalences-h-spaces.html#7835" class="Function">preserves-unital-mul-equiv-H-Space</a>

  <a id="8179" href="structured-types.equivalences-h-spaces.html#8179" class="Function">preserves-left-unit-law-mul-equiv-H-Space</a> <a id="8221" class="Symbol">:</a>
    <a id="8227" href="structured-types.equivalences-h-spaces.html#5664" class="Function">preserves-left-unit-law-mul-pointed-equiv-H-Space</a> <a id="8277" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="8279" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a>
      <a id="8287" class="Symbol">(</a> <a id="8289" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a><a id="8316" class="Symbol">)</a>
      <a id="8324" class="Symbol">(</a> <a id="8326" href="structured-types.equivalences-h-spaces.html#7999" class="Function">preserves-mul-equiv-H-Space</a><a id="8353" class="Symbol">)</a>
  <a id="8357" href="structured-types.equivalences-h-spaces.html#8179" class="Function">preserves-left-unit-law-mul-equiv-H-Space</a> <a id="8399" class="Symbol">=</a>
    <a id="8405" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8409" class="Symbol">(</a><a id="8410" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8414" href="structured-types.equivalences-h-spaces.html#7835" class="Function">preserves-unital-mul-equiv-H-Space</a><a id="8448" class="Symbol">)</a>

  <a id="8453" href="structured-types.equivalences-h-spaces.html#8453" class="Function">preserves-right-unit-law-mul-equiv-H-Space</a> <a id="8496" class="Symbol">:</a>
    <a id="8502" href="structured-types.equivalences-h-spaces.html#5986" class="Function">preserves-right-unit-law-mul-pointed-equiv-H-Space</a> <a id="8553" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="8555" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a>
      <a id="8563" class="Symbol">(</a> <a id="8565" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a><a id="8592" class="Symbol">)</a>
      <a id="8600" class="Symbol">(</a> <a id="8602" href="structured-types.equivalences-h-spaces.html#7999" class="Function">preserves-mul-equiv-H-Space</a><a id="8629" class="Symbol">)</a>
  <a id="8633" href="structured-types.equivalences-h-spaces.html#8453" class="Function">preserves-right-unit-law-mul-equiv-H-Space</a> <a id="8676" class="Symbol">=</a>
    <a id="8682" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8686" class="Symbol">(</a><a id="8687" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8691" class="Symbol">(</a><a id="8692" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8696" href="structured-types.equivalences-h-spaces.html#7835" class="Function">preserves-unital-mul-equiv-H-Space</a><a id="8730" class="Symbol">))</a>

  <a id="8736" href="structured-types.equivalences-h-spaces.html#8736" class="Function">preserves-coherence-unit-laws-mul-equiv-H-Space</a> <a id="8784" class="Symbol">:</a>
    <a id="8790" href="structured-types.equivalences-h-spaces.html#6311" class="Function">preserves-coherence-unit-laws-mul-pointed-equiv-H-Space</a> <a id="8846" href="structured-types.equivalences-h-spaces.html#7339" class="Bound">M</a> <a id="8848" href="structured-types.equivalences-h-spaces.html#7356" class="Bound">N</a>
      <a id="8856" class="Symbol">(</a> <a id="8858" href="structured-types.equivalences-h-spaces.html#7407" class="Function">pointed-equiv-equiv-H-Space</a><a id="8885" class="Symbol">)</a>
      <a id="8893" class="Symbol">(</a> <a id="8895" href="structured-types.equivalences-h-spaces.html#7999" class="Function">preserves-mul-equiv-H-Space</a><a id="8922" class="Symbol">)</a>
      <a id="8930" class="Symbol">(</a> <a id="8932" href="structured-types.equivalences-h-spaces.html#8179" class="Function">preserves-left-unit-law-mul-equiv-H-Space</a><a id="8973" class="Symbol">)</a>
      <a id="8981" class="Symbol">(</a> <a id="8983" href="structured-types.equivalences-h-spaces.html#8453" class="Function">preserves-right-unit-law-mul-equiv-H-Space</a><a id="9025" class="Symbol">)</a>
  <a id="9029" href="structured-types.equivalences-h-spaces.html#8736" class="Function">preserves-coherence-unit-laws-mul-equiv-H-Space</a> <a id="9077" class="Symbol">=</a>
    <a id="9083" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="9087" class="Symbol">(</a><a id="9088" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="9092" class="Symbol">(</a><a id="9093" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="9097" href="structured-types.equivalences-h-spaces.html#7835" class="Function">preserves-unital-mul-equiv-H-Space</a><a id="9131" class="Symbol">))</a>
</pre>