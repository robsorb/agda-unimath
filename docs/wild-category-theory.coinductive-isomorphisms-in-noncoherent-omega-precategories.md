# Coinductive isomorphisms in noncoherent ω-precategories

<pre class="Agda"><a id="68" class="Symbol">{-#</a> <a id="72" class="Keyword">OPTIONS</a> <a id="80" class="Pragma">--guardedness</a> <a id="94" class="Symbol">#-}</a>

<a id="99" class="Keyword">module</a> <a id="106" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html" class="Module">wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories</a> <a id="187" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="wild-category-theory.noncoherent-omega-precategories.html" class="Module">wild-category-theory.noncoherent-omega-precategories</a>
</pre>
</details>

## Idea

Consider a
[noncoherent ω-precategory](wild-category-theory.noncoherent-omega-precategories.md)
`𝒞`. A
{{#concept "coinductive isomorphism" Disambiguation="in noncoherent ω-precategories" Agda=is-coinductive-iso-Noncoherent-ω-Precategory}}
in `𝒞` is a morphism `f : 𝒞₁ x y` [equipped](foundation.structure.md) with,
coinductively,

- a morphism `s : 𝒞₁ y x`
- a $2$-morphism `η : 𝒞₂ id (f ∘ s)`
- a witness that `η` is itself a coinductive isomorphism
- another morphism `r : 𝒞₁ y x`
- a $2$-morphism `ε : 𝒞₂ (r ∘ f) id`
- a witness that `ε` is a coinductive isomorphism.

Thus, the specified data is a commuting diagram of the form

```text
  y ========= y
    \  ~⇓η  ∧   \
   s \     /f    \ r
      ∨   /  ~⇓ε  ∨
        x ========= x
```

where `η` and `ε` again are coinductive isomorphisms in their respective
hom-ω-categories.

> **Disclaimer.** We do not assert that the proposed definition of a coinductive
> isomorphism is fully coherent, and thus it may be subject to change in the
> future.

While a noncoherent ω-precategory is the most general setting that allows us to
_define_ coinductive isomorphisms, the missing coherences obstruct us from
showing many of the expected properties. For example, we cannot show that all
identities are coinductive isomorphisms or that coinductive isomorphisms
compose.

The concept of coinductive isomorphisms in ω-categories is strictly weaker than
the concept of _isomorphisms_. Indeed, the coindutive nature of this concept
allows us, in an informal sense, to indefinitely postpone constructing a witness
that `s` or `r` are "proper" inverses to `f`. To take an example, consider the
ω-category of spans and higher spans. In this ω-category every morphism is a
coinductive isomorphism since every morphism is a biadjoint, but not every
morphism is an isomorphism. Moreover, this ω-category is univalent with respect
to isomorphisms, but not with respect to all coinductive isomorphisms. More
generally, every morphism in an "ω-category with duals" is a coinductive
isomorphism {{#cite Cheng07}}.

## Definitions

### The predicate on morphisms of being coinductive isomorphisms

<pre class="Agda"><a id="2559" class="Keyword">record</a>
  <a id="is-coinductive-iso-Noncoherent-ω-Precategory"></a><a id="2568" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2568" class="Record">is-coinductive-iso-Noncoherent-ω-Precategory</a>
  <a id="2615" class="Symbol">{</a><a id="2616" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2616" class="Bound">l1</a> <a id="2619" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2619" class="Bound">l2</a> <a id="2622" class="Symbol">:</a> <a id="2624" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2629" class="Symbol">}</a> <a id="2631" class="Symbol">(</a><a id="2632" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a> <a id="2634" class="Symbol">:</a> <a id="2636" href="wild-category-theory.noncoherent-omega-precategories.html#2243" class="Function">Noncoherent-ω-Precategory</a> <a id="2662" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2616" class="Bound">l1</a> <a id="2665" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2619" class="Bound">l2</a><a id="2667" class="Symbol">)</a>
  <a id="2671" class="Symbol">{</a><a id="2672" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2672" class="Bound">x</a> <a id="2674" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2674" class="Bound">y</a> <a id="2676" class="Symbol">:</a> <a id="2678" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a> <a id="2708" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a><a id="2709" class="Symbol">}</a>
  <a id="2713" class="Symbol">(</a><a id="2714" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2714" class="Bound">f</a> <a id="2716" class="Symbol">:</a> <a id="2718" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="2748" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a> <a id="2750" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2672" class="Bound">x</a> <a id="2752" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2674" class="Bound">y</a><a id="2753" class="Symbol">)</a> <a id="2755" class="Symbol">:</a> <a id="2757" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2760" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2619" class="Bound">l2</a>
  <a id="2765" class="Keyword">where</a>
  <a id="2773" class="Keyword">coinductive</a>
  <a id="2787" class="Keyword">field</a>
    <a id="is-coinductive-iso-Noncoherent-ω-Precategory.hom-section-is-coinductive-iso-Noncoherent-ω-Precategory"></a><a id="2797" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2797" class="Field">hom-section-is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="2854" class="Symbol">:</a>
      <a id="2862" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="2892" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a> <a id="2894" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2674" class="Bound">y</a> <a id="2896" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2672" class="Bound">x</a>

    <a id="is-coinductive-iso-Noncoherent-ω-Precategory.unit-is-coinductive-iso-Noncoherent-ω-Precategory"></a><a id="2903" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2903" class="Field">unit-is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="2953" class="Symbol">:</a>
      <a id="2961" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="2993" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a>
        <a id="3003" class="Symbol">(</a> <a id="3005" href="wild-category-theory.noncoherent-omega-precategories.html#3822" class="Function">id-hom-Noncoherent-ω-Precategory</a> <a id="3038" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a><a id="3039" class="Symbol">)</a>
        <a id="3049" class="Symbol">(</a> <a id="3051" href="wild-category-theory.noncoherent-omega-precategories.html#5374" class="Function">comp-hom-Noncoherent-ω-Precategory</a> <a id="3086" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a>
          <a id="3098" class="Symbol">(</a> <a id="3100" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2714" class="Bound">f</a><a id="3101" class="Symbol">)</a>
          <a id="3113" class="Symbol">(</a> <a id="3115" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2797" class="Field">hom-section-is-coinductive-iso-Noncoherent-ω-Precategory</a><a id="3171" class="Symbol">))</a>

    <a id="is-coinductive-iso-Noncoherent-ω-Precategory.is-coinductive-iso-unit-is-coinductive-iso-Noncoherent-ω-Precategory"></a><a id="3179" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3179" class="Field">is-coinductive-iso-unit-is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="3248" class="Symbol">:</a>
      <a id="3256" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2568" class="Record">is-coinductive-iso-Noncoherent-ω-Precategory</a>
        <a id="3309" class="Symbol">(</a> <a id="3311" href="wild-category-theory.noncoherent-omega-precategories.html#6911" class="Function">hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory</a>
          <a id="3377" class="Symbol">(</a> <a id="3379" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a><a id="3380" class="Symbol">)</a>
          <a id="3392" class="Symbol">(</a> <a id="3394" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2674" class="Bound">y</a><a id="3395" class="Symbol">)</a>
          <a id="3407" class="Symbol">(</a> <a id="3409" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2674" class="Bound">y</a><a id="3410" class="Symbol">))</a>
        <a id="3421" class="Symbol">(</a> <a id="3423" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2903" class="Field">unit-is-coinductive-iso-Noncoherent-ω-Precategory</a><a id="3472" class="Symbol">)</a>

    <a id="is-coinductive-iso-Noncoherent-ω-Precategory.hom-retraction-is-coinductive-iso-Noncoherent-ω-Precategory"></a><a id="3479" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3479" class="Field">hom-retraction-is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="3539" class="Symbol">:</a>
      <a id="3547" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="3577" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a> <a id="3579" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2674" class="Bound">y</a> <a id="3581" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2672" class="Bound">x</a>

    <a id="is-coinductive-iso-Noncoherent-ω-Precategory.counit-is-coinductive-iso-Noncoherent-ω-Precategory"></a><a id="3588" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3588" class="Field">counit-is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="3640" class="Symbol">:</a>
      <a id="3648" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="3680" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a>
        <a id="3690" class="Symbol">(</a> <a id="3692" href="wild-category-theory.noncoherent-omega-precategories.html#5374" class="Function">comp-hom-Noncoherent-ω-Precategory</a> <a id="3727" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a>
          <a id="3739" class="Symbol">(</a> <a id="3741" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3479" class="Field">hom-retraction-is-coinductive-iso-Noncoherent-ω-Precategory</a><a id="3800" class="Symbol">)</a>
          <a id="3812" class="Symbol">(</a> <a id="3814" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2714" class="Bound">f</a><a id="3815" class="Symbol">))</a>
        <a id="3826" class="Symbol">(</a> <a id="3828" href="wild-category-theory.noncoherent-omega-precategories.html#3822" class="Function">id-hom-Noncoherent-ω-Precategory</a> <a id="3861" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a><a id="3862" class="Symbol">)</a>

    <a id="is-coinductive-iso-Noncoherent-ω-Precategory.is-coinductive-iso-counit-is-coinductive-iso-Noncoherent-ω-Precategory"></a><a id="3869" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3869" class="Field">is-coinductive-iso-counit-is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="3940" class="Symbol">:</a>
      <a id="3948" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2568" class="Record">is-coinductive-iso-Noncoherent-ω-Precategory</a>
        <a id="4001" class="Symbol">(</a> <a id="4003" href="wild-category-theory.noncoherent-omega-precategories.html#6911" class="Function">hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory</a>
          <a id="4069" class="Symbol">(</a> <a id="4071" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2632" class="Bound">𝒞</a><a id="4072" class="Symbol">)</a>
          <a id="4084" class="Symbol">(</a> <a id="4086" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2672" class="Bound">x</a><a id="4087" class="Symbol">)</a>
          <a id="4099" class="Symbol">(</a> <a id="4101" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2672" class="Bound">x</a><a id="4102" class="Symbol">))</a>
        <a id="4113" class="Symbol">(</a> <a id="4115" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3588" class="Field">counit-is-coinductive-iso-Noncoherent-ω-Precategory</a><a id="4166" class="Symbol">)</a>

<a id="4169" class="Keyword">open</a> <a id="4174" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2568" class="Module">is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="4219" class="Keyword">public</a>
</pre>
### Coinductive isomorphisms in a noncoherent ω-precategory

<pre class="Agda"><a id="coinductive-iso-Noncoherent-ω-Precategory"></a><a id="4300" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4300" class="Function">coinductive-iso-Noncoherent-ω-Precategory</a> <a id="4342" class="Symbol">:</a>
  <a id="4346" class="Symbol">{</a><a id="4347" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4347" class="Bound">l1</a> <a id="4350" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4350" class="Bound">l2</a> <a id="4353" class="Symbol">:</a> <a id="4355" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4360" class="Symbol">}</a> <a id="4362" class="Symbol">(</a><a id="4363" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4363" class="Bound">𝒞</a> <a id="4365" class="Symbol">:</a> <a id="4367" href="wild-category-theory.noncoherent-omega-precategories.html#2243" class="Function">Noncoherent-ω-Precategory</a> <a id="4393" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4347" class="Bound">l1</a> <a id="4396" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4350" class="Bound">l2</a><a id="4398" class="Symbol">)</a>
  <a id="4402" class="Symbol">(</a><a id="4403" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4403" class="Bound">x</a> <a id="4405" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4405" class="Bound">y</a> <a id="4407" class="Symbol">:</a> <a id="4409" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a> <a id="4439" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4363" class="Bound">𝒞</a><a id="4440" class="Symbol">)</a> <a id="4442" class="Symbol">→</a>
  <a id="4446" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4449" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4350" class="Bound">l2</a>
<a id="4452" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4300" class="Function">coinductive-iso-Noncoherent-ω-Precategory</a> <a id="4494" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4494" class="Bound">𝒞</a> <a id="4496" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4496" class="Bound">x</a> <a id="4498" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4498" class="Bound">y</a> <a id="4500" class="Symbol">=</a>
  <a id="4504" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="4506" class="Symbol">(</a> <a id="4508" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="4538" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4494" class="Bound">𝒞</a> <a id="4540" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4496" class="Bound">x</a> <a id="4542" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4498" class="Bound">y</a><a id="4543" class="Symbol">)</a>
    <a id="4549" class="Symbol">(</a> <a id="4551" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2568" class="Record">is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="4596" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4494" class="Bound">𝒞</a><a id="4597" class="Symbol">)</a>
</pre>
### Components of a coinductive isomorphism in a noncoherent ω-precategory

<pre class="Agda"><a id="4688" class="Keyword">module</a> <a id="4695" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4695" class="Module">_</a>
  <a id="4699" class="Symbol">{</a><a id="4700" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4700" class="Bound">l1</a> <a id="4703" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4703" class="Bound">l2</a> <a id="4706" class="Symbol">:</a> <a id="4708" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4713" class="Symbol">}</a> <a id="4715" class="Symbol">{</a><a id="4716" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a> <a id="4718" class="Symbol">:</a> <a id="4720" href="wild-category-theory.noncoherent-omega-precategories.html#2243" class="Function">Noncoherent-ω-Precategory</a> <a id="4746" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4700" class="Bound">l1</a> <a id="4749" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4703" class="Bound">l2</a><a id="4751" class="Symbol">}</a>
  <a id="4755" class="Symbol">{</a><a id="4756" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a> <a id="4758" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a> <a id="4760" class="Symbol">:</a> <a id="4762" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a> <a id="4792" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="4793" class="Symbol">}</a>
  <a id="4797" class="Symbol">(</a><a id="4798" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4798" class="Bound">f</a> <a id="4800" class="Symbol">:</a> <a id="4802" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4300" class="Function">coinductive-iso-Noncoherent-ω-Precategory</a> <a id="4844" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a> <a id="4846" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a> <a id="4848" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a><a id="4849" class="Symbol">)</a>
  <a id="4853" class="Keyword">where</a>

  <a id="4862" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4862" class="Function">hom-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="4908" class="Symbol">:</a>
    <a id="4914" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="4944" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a> <a id="4946" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a> <a id="4948" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a>
  <a id="4952" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4862" class="Function">hom-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="4998" class="Symbol">=</a> <a id="5000" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5004" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4798" class="Bound">f</a>

  <a id="5009" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5009" class="Function">is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="5074" class="Symbol">:</a>
    <a id="5080" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2568" class="Record">is-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="5125" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a>
      <a id="5133" class="Symbol">(</a> <a id="5135" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4862" class="Function">hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="5180" class="Symbol">)</a>
  <a id="5184" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5009" class="Function">is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="5249" class="Symbol">=</a> <a id="5251" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5255" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4798" class="Bound">f</a>

  <a id="5260" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5260" class="Function">hom-section-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="5314" class="Symbol">:</a>
    <a id="5320" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="5350" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a> <a id="5352" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a> <a id="5354" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a>
  <a id="5358" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5260" class="Function">hom-section-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="5412" class="Symbol">=</a>
    <a id="5418" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2797" class="Field">hom-section-is-coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="5481" class="Symbol">(</a> <a id="5483" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5009" class="Function">is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="5547" class="Symbol">)</a>

  <a id="5552" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5552" class="Function">unit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="5599" class="Symbol">:</a>
    <a id="5605" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="5637" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a>
      <a id="5645" class="Symbol">(</a> <a id="5647" href="wild-category-theory.noncoherent-omega-precategories.html#3822" class="Function">id-hom-Noncoherent-ω-Precategory</a> <a id="5680" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="5681" class="Symbol">)</a>
      <a id="5689" class="Symbol">(</a> <a id="5691" href="wild-category-theory.noncoherent-omega-precategories.html#5374" class="Function">comp-hom-Noncoherent-ω-Precategory</a> <a id="5726" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a>
        <a id="5736" class="Symbol">(</a> <a id="5738" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4862" class="Function">hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="5783" class="Symbol">)</a>
        <a id="5793" class="Symbol">(</a> <a id="5795" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5260" class="Function">hom-section-coinductive-iso-Noncoherent-ω-Precategory</a><a id="5848" class="Symbol">))</a>
  <a id="5853" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5552" class="Function">unit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="5900" class="Symbol">=</a>
    <a id="5906" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2903" class="Field">unit-is-coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="5962" class="Symbol">(</a> <a id="5964" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5009" class="Function">is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="6028" class="Symbol">)</a>

  <a id="6033" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#6033" class="Function">is-coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="6099" class="Symbol">:</a>
    <a id="6105" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2568" class="Record">is-coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="6156" class="Symbol">(</a> <a id="6158" href="wild-category-theory.noncoherent-omega-precategories.html#6911" class="Function">hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory</a>
        <a id="6222" class="Symbol">(</a> <a id="6224" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="6225" class="Symbol">)</a>
        <a id="6235" class="Symbol">(</a> <a id="6237" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a><a id="6238" class="Symbol">)</a>
        <a id="6248" class="Symbol">(</a> <a id="6250" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a><a id="6251" class="Symbol">))</a>
      <a id="6260" class="Symbol">(</a> <a id="6262" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5552" class="Function">unit-coinductive-iso-Noncoherent-ω-Precategory</a><a id="6308" class="Symbol">)</a>
  <a id="6312" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#6033" class="Function">is-coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="6378" class="Symbol">=</a>
    <a id="6384" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3179" class="Field">is-coinductive-iso-unit-is-coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="6459" class="Symbol">(</a> <a id="6461" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5009" class="Function">is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="6525" class="Symbol">)</a>

  <a id="6530" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#6530" class="Function">coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="6593" class="Symbol">:</a>
    <a id="6599" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4300" class="Function">coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="6647" class="Symbol">(</a> <a id="6649" href="wild-category-theory.noncoherent-omega-precategories.html#6911" class="Function">hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory</a>
        <a id="6713" class="Symbol">(</a> <a id="6715" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="6716" class="Symbol">)</a>
        <a id="6726" class="Symbol">(</a> <a id="6728" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a><a id="6729" class="Symbol">)</a>
        <a id="6739" class="Symbol">(</a> <a id="6741" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a><a id="6742" class="Symbol">))</a>
      <a id="6751" class="Symbol">(</a> <a id="6753" href="wild-category-theory.noncoherent-omega-precategories.html#3822" class="Function">id-hom-Noncoherent-ω-Precategory</a> <a id="6786" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="6787" class="Symbol">)</a>
      <a id="6795" class="Symbol">(</a> <a id="6797" href="wild-category-theory.noncoherent-omega-precategories.html#5374" class="Function">comp-hom-Noncoherent-ω-Precategory</a> <a id="6832" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a>
        <a id="6842" class="Symbol">(</a> <a id="6844" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4862" class="Function">hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="6889" class="Symbol">)</a>
        <a id="6899" class="Symbol">(</a> <a id="6901" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5260" class="Function">hom-section-coinductive-iso-Noncoherent-ω-Precategory</a><a id="6954" class="Symbol">))</a>
  <a id="6959" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="6963" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#6530" class="Function">coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="7026" class="Symbol">=</a>
    <a id="7032" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5552" class="Function">unit-coinductive-iso-Noncoherent-ω-Precategory</a>
  <a id="7081" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7085" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#6530" class="Function">coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="7148" class="Symbol">=</a>
    <a id="7154" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#6033" class="Function">is-coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory</a>

  <a id="7223" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#7223" class="Function">hom-retraction-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="7280" class="Symbol">:</a>
    <a id="7286" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="7316" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a> <a id="7318" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4758" class="Bound">y</a> <a id="7320" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a>
  <a id="7324" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#7223" class="Function">hom-retraction-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="7381" class="Symbol">=</a>
    <a id="7387" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3479" class="Field">hom-retraction-is-coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="7453" class="Symbol">(</a> <a id="7455" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5009" class="Function">is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="7519" class="Symbol">)</a>

  <a id="7524" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#7524" class="Function">counit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="7573" class="Symbol">:</a>
    <a id="7579" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="7611" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a>
      <a id="7619" class="Symbol">(</a> <a id="7621" href="wild-category-theory.noncoherent-omega-precategories.html#5374" class="Function">comp-hom-Noncoherent-ω-Precategory</a> <a id="7656" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a>
        <a id="7666" class="Symbol">(</a> <a id="7668" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#7223" class="Function">hom-retraction-coinductive-iso-Noncoherent-ω-Precategory</a><a id="7724" class="Symbol">)</a>
        <a id="7734" class="Symbol">(</a> <a id="7736" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4862" class="Function">hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="7781" class="Symbol">))</a>
      <a id="7790" class="Symbol">(</a> <a id="7792" href="wild-category-theory.noncoherent-omega-precategories.html#3822" class="Function">id-hom-Noncoherent-ω-Precategory</a> <a id="7825" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="7826" class="Symbol">)</a>
  <a id="7830" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#7524" class="Function">counit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="7879" class="Symbol">=</a>
    <a id="7885" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3588" class="Field">counit-is-coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="7943" class="Symbol">(</a> <a id="7945" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5009" class="Function">is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="8009" class="Symbol">)</a>

  <a id="8014" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#8014" class="Function">is-coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="8082" class="Symbol">:</a>
    <a id="8088" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#2568" class="Record">is-coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="8139" class="Symbol">(</a> <a id="8141" href="wild-category-theory.noncoherent-omega-precategories.html#6911" class="Function">hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory</a>
        <a id="8205" class="Symbol">(</a> <a id="8207" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="8208" class="Symbol">)</a>
        <a id="8218" class="Symbol">(</a> <a id="8220" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a><a id="8221" class="Symbol">)</a>
        <a id="8231" class="Symbol">(</a> <a id="8233" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a><a id="8234" class="Symbol">))</a>
      <a id="8243" class="Symbol">(</a> <a id="8245" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#7524" class="Function">counit-coinductive-iso-Noncoherent-ω-Precategory</a><a id="8293" class="Symbol">)</a>
  <a id="8297" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#8014" class="Function">is-coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="8365" class="Symbol">=</a>
    <a id="8371" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#3869" class="Field">is-coinductive-iso-counit-is-coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="8448" class="Symbol">(</a> <a id="8450" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#5009" class="Function">is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="8514" class="Symbol">)</a>

  <a id="8519" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#8519" class="Function">coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="8584" class="Symbol">:</a>
    <a id="8590" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4300" class="Function">coinductive-iso-Noncoherent-ω-Precategory</a>
      <a id="8638" class="Symbol">(</a> <a id="8640" href="wild-category-theory.noncoherent-omega-precategories.html#6911" class="Function">hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory</a>
        <a id="8704" class="Symbol">(</a> <a id="8706" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="8707" class="Symbol">)</a>
        <a id="8717" class="Symbol">(</a> <a id="8719" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a><a id="8720" class="Symbol">)</a>
        <a id="8730" class="Symbol">(</a> <a id="8732" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4756" class="Bound">x</a><a id="8733" class="Symbol">))</a>
      <a id="8742" class="Symbol">(</a> <a id="8744" href="wild-category-theory.noncoherent-omega-precategories.html#5374" class="Function">comp-hom-Noncoherent-ω-Precategory</a> <a id="8779" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a>
        <a id="8789" class="Symbol">(</a> <a id="8791" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#7223" class="Function">hom-retraction-coinductive-iso-Noncoherent-ω-Precategory</a><a id="8847" class="Symbol">)</a>
        <a id="8857" class="Symbol">(</a> <a id="8859" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4862" class="Function">hom-coinductive-iso-Noncoherent-ω-Precategory</a><a id="8904" class="Symbol">))</a>
      <a id="8913" class="Symbol">(</a> <a id="8915" href="wild-category-theory.noncoherent-omega-precategories.html#3822" class="Function">id-hom-Noncoherent-ω-Precategory</a> <a id="8948" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#4716" class="Bound">𝒞</a><a id="8949" class="Symbol">)</a>
  <a id="8953" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8957" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#8519" class="Function">coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="9022" class="Symbol">=</a>
    <a id="9028" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#7524" class="Function">counit-coinductive-iso-Noncoherent-ω-Precategory</a>
  <a id="9079" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="9083" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#8519" class="Function">coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory</a> <a id="9148" class="Symbol">=</a>
    <a id="9154" href="wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.html#8014" class="Function">is-coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory</a>
</pre>
## See also

- [Coinductive isomorphisms in noncoherent large ω-precategories](wild-category-theory.coinductive-isomorphisms-in-noncoherent-large-omega-precategories.md)

## References

{{#bibliography}}
