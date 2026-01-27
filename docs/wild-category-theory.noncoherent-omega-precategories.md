# Noncoherent ω-precategories

<pre class="Agda"><a id="40" class="Symbol">{-#</a> <a id="44" class="Keyword">OPTIONS</a> <a id="52" class="Pragma">--guardedness</a> <a id="66" class="Symbol">#-}</a>

<a id="71" class="Keyword">module</a> <a id="78" href="wild-category-theory.noncoherent-omega-precategories.html" class="Module">wild-category-theory.noncoherent-omega-precategories</a> <a id="131" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="foundation.action-on-identifications-binary-functions.html" class="Module">foundation.action-on-identifications-binary-functions</a>
<a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="425" class="Keyword">open</a> <a id="430" class="Keyword">import</a> <a id="437" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="459" class="Keyword">open</a> <a id="464" class="Keyword">import</a> <a id="471" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="foundation.strictly-involutive-identity-types.html" class="Module">foundation.strictly-involutive-identity-types</a>
<a id="583" class="Keyword">open</a> <a id="588" class="Keyword">import</a> <a id="595" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="623" class="Keyword">open</a> <a id="628" class="Keyword">import</a> <a id="635" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
<a id="665" class="Keyword">open</a> <a id="670" class="Keyword">import</a> <a id="677" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
<a id="717" class="Keyword">open</a> <a id="722" class="Keyword">import</a> <a id="729" href="globular-types.transitive-globular-types.html" class="Module">globular-types.transitive-globular-types</a>
</pre>
</details>

## Idea

It is an important open problem known as the _coherence problem_ to define a
fully coherent notion of $∞$-category or higher variants in univalent type
theory. The subject of _wild category theory_ attempts to recover some of the
benefits of $∞$-category theory without tackling this problem. We introduce, as
one of our basic building blocks in this subject, the notion of a _noncoherent
ω-precategory_.

A _noncoherent ω-precategory_ `𝒞` is a structure that attempts at capturing the
structure of an ω-category to the $0$'th order. It consists of in some sense all
of the operations and none of the coherence. Thus, it is defined as a
[globular type](globular-types.globular-types.md) with families of $n$-morphisms
labeled as "identities"

```text
  id-hom : (x : 𝒞ₙ) → 𝒞ₙ₊₁ x x
```

and a composition operation at every dimension

```text
  comp-hom : {x y z : 𝒞ₙ} → 𝒞ₙ₊₁ y z → 𝒞ₙ₊₁ x y → 𝒞ₙ₊₁ x z.
```

Entirely concretely, we define a
{{#concept "noncoherent ω-precategory" Agda=Noncoherent-ω-Precategory}} to be a
[reflexive](globular-types.reflexive-globular-types.md) and
[transitive](globular-types.transitive-globular-types.md) globular type. We call
the 0-cells the _objects_, the 1-cells the _morphisms_ and the higher cells the
_$n$-morphisms_. The reflexivities are called the _identity morphisms_, and the
transitivity operations are branded as _composition of morphisms_.

## Definitions

### Noncoherent ω-precategories

<pre class="Agda"><a id="Noncoherent-ω-Precategory"></a><a id="2243" href="wild-category-theory.noncoherent-omega-precategories.html#2243" class="Function">Noncoherent-ω-Precategory</a> <a id="2269" class="Symbol">:</a> <a id="2271" class="Symbol">(</a><a id="2272" href="wild-category-theory.noncoherent-omega-precategories.html#2272" class="Bound">l1</a> <a id="2275" href="wild-category-theory.noncoherent-omega-precategories.html#2275" class="Bound">l2</a> <a id="2278" class="Symbol">:</a> <a id="2280" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2285" class="Symbol">)</a> <a id="2287" class="Symbol">→</a> <a id="2289" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2292" class="Symbol">(</a><a id="2293" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2298" href="wild-category-theory.noncoherent-omega-precategories.html#2272" class="Bound">l1</a> <a id="2301" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2303" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2308" href="wild-category-theory.noncoherent-omega-precategories.html#2275" class="Bound">l2</a><a id="2310" class="Symbol">)</a>
<a id="2312" href="wild-category-theory.noncoherent-omega-precategories.html#2243" class="Function">Noncoherent-ω-Precategory</a> <a id="2338" href="wild-category-theory.noncoherent-omega-precategories.html#2338" class="Bound">l1</a> <a id="2341" href="wild-category-theory.noncoherent-omega-precategories.html#2341" class="Bound">l2</a> <a id="2344" class="Symbol">=</a>
  <a id="2348" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2350" class="Symbol">(</a> <a id="2352" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="2366" href="wild-category-theory.noncoherent-omega-precategories.html#2338" class="Bound">l1</a> <a id="2369" href="wild-category-theory.noncoherent-omega-precategories.html#2341" class="Bound">l2</a><a id="2371" class="Symbol">)</a>
    <a id="2377" class="Symbol">(</a> <a id="2379" class="Symbol">λ</a> <a id="2381" href="wild-category-theory.noncoherent-omega-precategories.html#2381" class="Bound">X</a> <a id="2383" class="Symbol">→</a> <a id="2385" href="globular-types.reflexive-globular-types.html#744" class="Record">is-reflexive-Globular-Type</a> <a id="2412" href="wild-category-theory.noncoherent-omega-precategories.html#2381" class="Bound">X</a> <a id="2414" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="2416" href="globular-types.transitive-globular-types.html#876" class="Record">is-transitive-Globular-Type</a> <a id="2444" href="wild-category-theory.noncoherent-omega-precategories.html#2381" class="Bound">X</a><a id="2445" class="Symbol">)</a>

<a id="make-Noncoherent-ω-Precategory"></a><a id="2448" href="wild-category-theory.noncoherent-omega-precategories.html#2448" class="Function">make-Noncoherent-ω-Precategory</a> <a id="2479" class="Symbol">:</a>
  <a id="2483" class="Symbol">{</a><a id="2484" href="wild-category-theory.noncoherent-omega-precategories.html#2484" class="Bound">l1</a> <a id="2487" href="wild-category-theory.noncoherent-omega-precategories.html#2487" class="Bound">l2</a> <a id="2490" class="Symbol">:</a> <a id="2492" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2497" class="Symbol">}</a> <a id="2499" class="Symbol">{</a><a id="2500" href="wild-category-theory.noncoherent-omega-precategories.html#2500" class="Bound">X</a> <a id="2502" class="Symbol">:</a> <a id="2504" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="2518" href="wild-category-theory.noncoherent-omega-precategories.html#2484" class="Bound">l1</a> <a id="2521" href="wild-category-theory.noncoherent-omega-precategories.html#2487" class="Bound">l2</a><a id="2523" class="Symbol">}</a> <a id="2525" class="Symbol">→</a> <a id="2527" href="globular-types.reflexive-globular-types.html#744" class="Record">is-reflexive-Globular-Type</a> <a id="2554" href="wild-category-theory.noncoherent-omega-precategories.html#2500" class="Bound">X</a> <a id="2556" class="Symbol">→</a>
  <a id="2560" href="globular-types.transitive-globular-types.html#876" class="Record">is-transitive-Globular-Type</a> <a id="2588" href="wild-category-theory.noncoherent-omega-precategories.html#2500" class="Bound">X</a> <a id="2590" class="Symbol">→</a> <a id="2592" href="wild-category-theory.noncoherent-omega-precategories.html#2243" class="Function">Noncoherent-ω-Precategory</a> <a id="2618" href="wild-category-theory.noncoherent-omega-precategories.html#2484" class="Bound">l1</a> <a id="2621" href="wild-category-theory.noncoherent-omega-precategories.html#2487" class="Bound">l2</a>
<a id="2624" href="wild-category-theory.noncoherent-omega-precategories.html#2448" class="Function">make-Noncoherent-ω-Precategory</a> <a id="2655" href="wild-category-theory.noncoherent-omega-precategories.html#2655" class="Bound">id</a> <a id="2658" href="wild-category-theory.noncoherent-omega-precategories.html#2658" class="Bound">comp</a> <a id="2663" class="Symbol">=</a>
  <a id="2667" class="Symbol">(</a> <a id="2669" class="Symbol">_</a> <a id="2671" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2673" href="wild-category-theory.noncoherent-omega-precategories.html#2655" class="Bound">id</a> <a id="2676" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2678" href="wild-category-theory.noncoherent-omega-precategories.html#2658" class="Bound">comp</a><a id="2682" class="Symbol">)</a>

<a id="2685" class="Symbol">{-#</a> <a id="2689" class="Keyword">INLINE</a> <a id="2696" href="wild-category-theory.noncoherent-omega-precategories.html#2448" class="Function">make-Noncoherent-ω-Precategory</a> <a id="2727" class="Symbol">#-}</a>

<a id="2732" class="Keyword">module</a> <a id="2739" href="wild-category-theory.noncoherent-omega-precategories.html#2739" class="Module">_</a>
  <a id="2743" class="Symbol">{</a><a id="2744" href="wild-category-theory.noncoherent-omega-precategories.html#2744" class="Bound">l1</a> <a id="2747" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a> <a id="2750" class="Symbol">:</a> <a id="2752" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2757" class="Symbol">}</a> <a id="2759" class="Symbol">(</a><a id="2760" href="wild-category-theory.noncoherent-omega-precategories.html#2760" class="Bound">𝒞</a> <a id="2762" class="Symbol">:</a> <a id="2764" href="wild-category-theory.noncoherent-omega-precategories.html#2243" class="Function">Noncoherent-ω-Precategory</a> <a id="2790" href="wild-category-theory.noncoherent-omega-precategories.html#2744" class="Bound">l1</a> <a id="2793" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a><a id="2795" class="Symbol">)</a>
  <a id="2799" class="Keyword">where</a>

  <a id="2808" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a> <a id="2848" class="Symbol">:</a> <a id="2850" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="2864" href="wild-category-theory.noncoherent-omega-precategories.html#2744" class="Bound">l1</a> <a id="2867" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="2872" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a> <a id="2912" class="Symbol">=</a> <a id="2914" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2918" href="wild-category-theory.noncoherent-omega-precategories.html#2760" class="Bound">𝒞</a>

  <a id="2923" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a> <a id="2953" class="Symbol">:</a> <a id="2955" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2958" href="wild-category-theory.noncoherent-omega-precategories.html#2744" class="Bound">l1</a>
  <a id="2963" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a> <a id="2993" class="Symbol">=</a>
    <a id="2999" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="3020" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>
</pre>
Morphisms in a noncoherent ω-precategory:

<pre class="Agda">  <a id="3118" href="wild-category-theory.noncoherent-omega-precategories.html#3118" class="Function">hom-globular-type-Noncoherent-ω-Precategory</a> <a id="3162" class="Symbol">:</a>
    <a id="3168" class="Symbol">(</a><a id="3169" href="wild-category-theory.noncoherent-omega-precategories.html#3169" class="Bound">x</a> <a id="3171" href="wild-category-theory.noncoherent-omega-precategories.html#3171" class="Bound">y</a> <a id="3173" class="Symbol">:</a> <a id="3175" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="3204" class="Symbol">)</a> <a id="3206" class="Symbol">→</a>
    <a id="3212" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="3226" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a> <a id="3229" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="3234" href="wild-category-theory.noncoherent-omega-precategories.html#3118" class="Function">hom-globular-type-Noncoherent-ω-Precategory</a> <a id="3278" class="Symbol">=</a>
    <a id="3284" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a>
      <a id="3325" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>

  <a id="3368" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="3398" class="Symbol">:</a>
    <a id="3404" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a> <a id="3434" class="Symbol">→</a>
    <a id="3440" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a> <a id="3470" class="Symbol">→</a>
    <a id="3476" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3479" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="3484" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="3514" class="Symbol">=</a>
    <a id="3520" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="3541" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>
</pre>
Identity morphisms in a noncoherent ω-precategory:

<pre class="Agda">  <a id="3648" href="wild-category-theory.noncoherent-omega-precategories.html#3648" class="Function">id-structure-Noncoherent-ω-Precategory</a> <a id="3687" class="Symbol">:</a>
    <a id="3693" href="globular-types.reflexive-globular-types.html#744" class="Record">is-reflexive-Globular-Type</a> <a id="3720" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>
  <a id="3762" href="wild-category-theory.noncoherent-omega-precategories.html#3648" class="Function">id-structure-Noncoherent-ω-Precategory</a> <a id="3801" class="Symbol">=</a>
    <a id="3807" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3811" class="Symbol">(</a><a id="3812" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3816" href="wild-category-theory.noncoherent-omega-precategories.html#2760" class="Bound">𝒞</a><a id="3817" class="Symbol">)</a>

  <a id="3822" href="wild-category-theory.noncoherent-omega-precategories.html#3822" class="Function">id-hom-Noncoherent-ω-Precategory</a> <a id="3855" class="Symbol">:</a>
    <a id="3861" class="Symbol">{</a><a id="3862" href="wild-category-theory.noncoherent-omega-precategories.html#3862" class="Bound">x</a> <a id="3864" class="Symbol">:</a> <a id="3866" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="3895" class="Symbol">}</a> <a id="3897" class="Symbol">→</a>
    <a id="3903" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="3933" href="wild-category-theory.noncoherent-omega-precategories.html#3862" class="Bound">x</a> <a id="3935" href="wild-category-theory.noncoherent-omega-precategories.html#3862" class="Bound">x</a>
  <a id="3939" href="wild-category-theory.noncoherent-omega-precategories.html#3822" class="Function">id-hom-Noncoherent-ω-Precategory</a> <a id="3972" class="Symbol">{</a><a id="3973" href="wild-category-theory.noncoherent-omega-precategories.html#3973" class="Bound">x</a><a id="3974" class="Symbol">}</a> <a id="3976" class="Symbol">=</a>
    <a id="3982" href="globular-types.reflexive-globular-types.html#1293" class="Function">refl-2-cell-is-reflexive-Globular-Type</a>
      <a id="4027" href="wild-category-theory.noncoherent-omega-precategories.html#3648" class="Function">id-structure-Noncoherent-ω-Precategory</a>

  <a id="4069" href="wild-category-theory.noncoherent-omega-precategories.html#4069" class="Function">id-structure-hom-globular-type-Noncoherent-ω-Precategory</a> <a id="4126" class="Symbol">:</a>
    <a id="4132" class="Symbol">{</a><a id="4133" href="wild-category-theory.noncoherent-omega-precategories.html#4133" class="Bound">x</a> <a id="4135" href="wild-category-theory.noncoherent-omega-precategories.html#4135" class="Bound">y</a> <a id="4137" class="Symbol">:</a> <a id="4139" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="4168" class="Symbol">}</a> <a id="4170" class="Symbol">→</a>
    <a id="4176" href="globular-types.reflexive-globular-types.html#744" class="Record">is-reflexive-Globular-Type</a>
      <a id="4209" class="Symbol">(</a> <a id="4211" href="wild-category-theory.noncoherent-omega-precategories.html#3118" class="Function">hom-globular-type-Noncoherent-ω-Precategory</a> <a id="4255" href="wild-category-theory.noncoherent-omega-precategories.html#4133" class="Bound">x</a> <a id="4257" href="wild-category-theory.noncoherent-omega-precategories.html#4135" class="Bound">y</a><a id="4258" class="Symbol">)</a>
  <a id="4262" href="wild-category-theory.noncoherent-omega-precategories.html#4069" class="Function">id-structure-hom-globular-type-Noncoherent-ω-Precategory</a> <a id="4319" class="Symbol">=</a>
    <a id="4325" href="globular-types.reflexive-globular-types.html#973" class="Field">is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type</a>
      <a id="4392" href="wild-category-theory.noncoherent-omega-precategories.html#3648" class="Function">id-structure-Noncoherent-ω-Precategory</a>

  <a id="4434" href="wild-category-theory.noncoherent-omega-precategories.html#4434" class="Function">reflexive-globular-type-Noncoherent-ω-Precategory</a> <a id="4484" class="Symbol">:</a>
    <a id="4490" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="4514" href="wild-category-theory.noncoherent-omega-precategories.html#2744" class="Bound">l1</a> <a id="4517" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="4522" href="globular-types.reflexive-globular-types.html#4067" class="Field">globular-type-Reflexive-Globular-Type</a>
    <a id="4564" href="wild-category-theory.noncoherent-omega-precategories.html#4434" class="Function">reflexive-globular-type-Noncoherent-ω-Precategory</a> <a id="4614" class="Symbol">=</a>
    <a id="4620" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>
  <a id="4662" href="globular-types.reflexive-globular-types.html#5323" class="Field">refl-Reflexive-Globular-Type</a>
    <a id="4695" href="wild-category-theory.noncoherent-omega-precategories.html#4434" class="Function">reflexive-globular-type-Noncoherent-ω-Precategory</a> <a id="4745" class="Symbol">=</a>
    <a id="4751" href="wild-category-theory.noncoherent-omega-precategories.html#3648" class="Function">id-structure-Noncoherent-ω-Precategory</a>

  <a id="4793" href="wild-category-theory.noncoherent-omega-precategories.html#4793" class="Function">hom-reflexive-globular-type-Noncoherent-ω-Precategory</a> <a id="4847" class="Symbol">:</a>
    <a id="4853" class="Symbol">(</a><a id="4854" href="wild-category-theory.noncoherent-omega-precategories.html#4854" class="Bound">x</a> <a id="4856" href="wild-category-theory.noncoherent-omega-precategories.html#4856" class="Bound">y</a> <a id="4858" class="Symbol">:</a> <a id="4860" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="4889" class="Symbol">)</a> <a id="4891" class="Symbol">→</a>
    <a id="4897" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="4921" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a> <a id="4924" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="4929" href="wild-category-theory.noncoherent-omega-precategories.html#4793" class="Function">hom-reflexive-globular-type-Noncoherent-ω-Precategory</a> <a id="4983" href="wild-category-theory.noncoherent-omega-precategories.html#4983" class="Bound">x</a> <a id="4985" href="wild-category-theory.noncoherent-omega-precategories.html#4985" class="Bound">y</a> <a id="4987" class="Symbol">=</a>
    <a id="4993" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a>
      <a id="5054" class="Symbol">(</a> <a id="5056" href="wild-category-theory.noncoherent-omega-precategories.html#4434" class="Function">reflexive-globular-type-Noncoherent-ω-Precategory</a><a id="5105" class="Symbol">)</a>
      <a id="5113" class="Symbol">(</a> <a id="5115" href="wild-category-theory.noncoherent-omega-precategories.html#4983" class="Bound">x</a><a id="5116" class="Symbol">)</a>
      <a id="5124" class="Symbol">(</a> <a id="5126" href="wild-category-theory.noncoherent-omega-precategories.html#4985" class="Bound">y</a><a id="5127" class="Symbol">)</a>
</pre>
Composition in a noncoherent ω-precategory:

<pre class="Agda">  <a id="5189" href="wild-category-theory.noncoherent-omega-precategories.html#5189" class="Function">comp-structure-Noncoherent-ω-Precategory</a> <a id="5230" class="Symbol">:</a>
    <a id="5236" href="globular-types.transitive-globular-types.html#876" class="Record">is-transitive-Globular-Type</a>
      <a id="5270" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>
  <a id="5312" href="wild-category-theory.noncoherent-omega-precategories.html#5189" class="Function">comp-structure-Noncoherent-ω-Precategory</a> <a id="5353" class="Symbol">=</a>
    <a id="5359" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5363" class="Symbol">(</a><a id="5364" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5368" href="wild-category-theory.noncoherent-omega-precategories.html#2760" class="Bound">𝒞</a><a id="5369" class="Symbol">)</a>

  <a id="5374" href="wild-category-theory.noncoherent-omega-precategories.html#5374" class="Function">comp-hom-Noncoherent-ω-Precategory</a> <a id="5409" class="Symbol">:</a>
    <a id="5415" class="Symbol">{</a><a id="5416" href="wild-category-theory.noncoherent-omega-precategories.html#5416" class="Bound">x</a> <a id="5418" href="wild-category-theory.noncoherent-omega-precategories.html#5418" class="Bound">y</a> <a id="5420" href="wild-category-theory.noncoherent-omega-precategories.html#5420" class="Bound">z</a> <a id="5422" class="Symbol">:</a> <a id="5424" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="5453" class="Symbol">}</a> <a id="5455" class="Symbol">→</a>
    <a id="5461" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="5491" href="wild-category-theory.noncoherent-omega-precategories.html#5418" class="Bound">y</a> <a id="5493" href="wild-category-theory.noncoherent-omega-precategories.html#5420" class="Bound">z</a> <a id="5495" class="Symbol">→</a>
    <a id="5501" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="5531" href="wild-category-theory.noncoherent-omega-precategories.html#5416" class="Bound">x</a> <a id="5533" href="wild-category-theory.noncoherent-omega-precategories.html#5418" class="Bound">y</a> <a id="5535" class="Symbol">→</a>
    <a id="5541" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="5571" href="wild-category-theory.noncoherent-omega-precategories.html#5416" class="Bound">x</a> <a id="5573" href="wild-category-theory.noncoherent-omega-precategories.html#5420" class="Bound">z</a>
  <a id="5577" href="wild-category-theory.noncoherent-omega-precategories.html#5374" class="Function">comp-hom-Noncoherent-ω-Precategory</a> <a id="5612" class="Symbol">=</a>
    <a id="5618" href="globular-types.transitive-globular-types.html#1000" class="Field">comp-1-cell-is-transitive-Globular-Type</a>
      <a id="5664" href="wild-category-theory.noncoherent-omega-precategories.html#5189" class="Function">comp-structure-Noncoherent-ω-Precategory</a>

  <a id="5708" href="wild-category-theory.noncoherent-omega-precategories.html#5708" class="Function">comp-structure-hom-globular-type-Noncoherent-ω-Precategory</a> <a id="5767" class="Symbol">:</a>
    <a id="5773" class="Symbol">{</a><a id="5774" href="wild-category-theory.noncoherent-omega-precategories.html#5774" class="Bound">x</a> <a id="5776" href="wild-category-theory.noncoherent-omega-precategories.html#5776" class="Bound">y</a> <a id="5778" class="Symbol">:</a> <a id="5780" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="5809" class="Symbol">}</a> <a id="5811" class="Symbol">→</a>
    <a id="5817" href="globular-types.transitive-globular-types.html#876" class="Record">is-transitive-Globular-Type</a>
      <a id="5851" class="Symbol">(</a> <a id="5853" href="wild-category-theory.noncoherent-omega-precategories.html#3118" class="Function">hom-globular-type-Noncoherent-ω-Precategory</a> <a id="5897" href="wild-category-theory.noncoherent-omega-precategories.html#5774" class="Bound">x</a> <a id="5899" href="wild-category-theory.noncoherent-omega-precategories.html#5776" class="Bound">y</a><a id="5900" class="Symbol">)</a>
  <a id="5904" href="wild-category-theory.noncoherent-omega-precategories.html#5708" class="Function">comp-structure-hom-globular-type-Noncoherent-ω-Precategory</a> <a id="5963" class="Symbol">=</a>
    <a id="5969" href="globular-types.transitive-globular-types.html#1101" class="Field">is-transitive-1-cell-globular-type-is-transitive-Globular-Type</a>
      <a id="6038" href="wild-category-theory.noncoherent-omega-precategories.html#5189" class="Function">comp-structure-Noncoherent-ω-Precategory</a>

  <a id="6082" href="wild-category-theory.noncoherent-omega-precategories.html#6082" class="Function">transitive-globular-type-Noncoherent-ω-Precategory</a> <a id="6133" class="Symbol">:</a>
    <a id="6139" href="globular-types.transitive-globular-types.html#3131" class="Record">Transitive-Globular-Type</a> <a id="6164" href="wild-category-theory.noncoherent-omega-precategories.html#2744" class="Bound">l1</a> <a id="6167" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="6172" href="globular-types.transitive-globular-types.html#3344" class="Field">globular-type-Transitive-Globular-Type</a>
    <a id="6215" href="wild-category-theory.noncoherent-omega-precategories.html#6082" class="Function">transitive-globular-type-Noncoherent-ω-Precategory</a> <a id="6266" class="Symbol">=</a>
    <a id="6272" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>
  <a id="6314" href="globular-types.transitive-globular-types.html#5494" class="Field">is-transitive-Transitive-Globular-Type</a>
    <a id="6357" href="wild-category-theory.noncoherent-omega-precategories.html#6082" class="Function">transitive-globular-type-Noncoherent-ω-Precategory</a> <a id="6408" class="Symbol">=</a>
    <a id="6414" href="wild-category-theory.noncoherent-omega-precategories.html#5189" class="Function">comp-structure-Noncoherent-ω-Precategory</a>

  <a id="6458" href="wild-category-theory.noncoherent-omega-precategories.html#6458" class="Function">hom-transitive-globular-type-Noncoherent-ω-Precategory</a> <a id="6513" class="Symbol">:</a>
    <a id="6519" class="Symbol">(</a><a id="6520" href="wild-category-theory.noncoherent-omega-precategories.html#6520" class="Bound">x</a> <a id="6522" href="wild-category-theory.noncoherent-omega-precategories.html#6522" class="Bound">y</a> <a id="6524" class="Symbol">:</a> <a id="6526" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="6555" class="Symbol">)</a> <a id="6557" class="Symbol">→</a>
    <a id="6563" href="globular-types.transitive-globular-types.html#3131" class="Record">Transitive-Globular-Type</a> <a id="6588" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a> <a id="6591" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="6596" href="wild-category-theory.noncoherent-omega-precategories.html#6458" class="Function">hom-transitive-globular-type-Noncoherent-ω-Precategory</a> <a id="6651" href="wild-category-theory.noncoherent-omega-precategories.html#6651" class="Bound">x</a> <a id="6653" href="wild-category-theory.noncoherent-omega-precategories.html#6653" class="Bound">y</a> <a id="6655" class="Symbol">=</a>
    <a id="6661" href="globular-types.transitive-globular-types.html#6448" class="Function">1-cell-transitive-globular-type-Transitive-Globular-Type</a>
      <a id="6724" class="Symbol">(</a> <a id="6726" href="wild-category-theory.noncoherent-omega-precategories.html#6082" class="Function">transitive-globular-type-Noncoherent-ω-Precategory</a><a id="6776" class="Symbol">)</a>
      <a id="6784" class="Symbol">(</a> <a id="6786" href="wild-category-theory.noncoherent-omega-precategories.html#6651" class="Bound">x</a><a id="6787" class="Symbol">)</a>
      <a id="6795" class="Symbol">(</a> <a id="6797" href="wild-category-theory.noncoherent-omega-precategories.html#6653" class="Bound">y</a><a id="6798" class="Symbol">)</a>
</pre>
The noncoherent ω-precategory of morphisms between two objects in a noncoherent
ω-precategory:

<pre class="Agda">  <a id="6911" href="wild-category-theory.noncoherent-omega-precategories.html#6911" class="Function">hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory</a> <a id="6967" class="Symbol">:</a>
    <a id="6973" class="Symbol">(</a><a id="6974" href="wild-category-theory.noncoherent-omega-precategories.html#6974" class="Bound">x</a> <a id="6976" href="wild-category-theory.noncoherent-omega-precategories.html#6976" class="Bound">y</a> <a id="6978" class="Symbol">:</a> <a id="6980" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="7009" class="Symbol">)</a> <a id="7011" class="Symbol">→</a>
    <a id="7017" href="wild-category-theory.noncoherent-omega-precategories.html#2243" class="Function">Noncoherent-ω-Precategory</a> <a id="7043" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a> <a id="7046" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="7051" href="wild-category-theory.noncoherent-omega-precategories.html#6911" class="Function">hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory</a>
    <a id="7111" href="wild-category-theory.noncoherent-omega-precategories.html#7111" class="Bound">x</a> <a id="7113" href="wild-category-theory.noncoherent-omega-precategories.html#7113" class="Bound">y</a> <a id="7115" class="Symbol">=</a>
    <a id="7121" href="wild-category-theory.noncoherent-omega-precategories.html#2448" class="Function">make-Noncoherent-ω-Precategory</a>
      <a id="7158" class="Symbol">(</a> <a id="7160" href="wild-category-theory.noncoherent-omega-precategories.html#4069" class="Function">id-structure-hom-globular-type-Noncoherent-ω-Precategory</a>
        <a id="7225" class="Symbol">{</a><a id="7226" href="wild-category-theory.noncoherent-omega-precategories.html#7111" class="Bound">x</a><a id="7227" class="Symbol">}</a> <a id="7229" class="Symbol">{</a><a id="7230" href="wild-category-theory.noncoherent-omega-precategories.html#7113" class="Bound">y</a><a id="7231" class="Symbol">})</a>
      <a id="7240" class="Symbol">(</a> <a id="7242" href="wild-category-theory.noncoherent-omega-precategories.html#5708" class="Function">comp-structure-hom-globular-type-Noncoherent-ω-Precategory</a><a id="7300" class="Symbol">)</a>
</pre>
2-Morphisms in a noncoherent ω-precategory:

<pre class="Agda">  <a id="7362" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="7394" class="Symbol">:</a>
    <a id="7400" class="Symbol">{</a><a id="7401" href="wild-category-theory.noncoherent-omega-precategories.html#7401" class="Bound">x</a> <a id="7403" href="wild-category-theory.noncoherent-omega-precategories.html#7403" class="Bound">y</a> <a id="7405" class="Symbol">:</a> <a id="7407" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="7436" class="Symbol">}</a> <a id="7438" class="Symbol">→</a>
    <a id="7444" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="7474" href="wild-category-theory.noncoherent-omega-precategories.html#7401" class="Bound">x</a> <a id="7476" href="wild-category-theory.noncoherent-omega-precategories.html#7403" class="Bound">y</a> <a id="7478" class="Symbol">→</a>
    <a id="7484" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="7514" href="wild-category-theory.noncoherent-omega-precategories.html#7401" class="Bound">x</a> <a id="7516" href="wild-category-theory.noncoherent-omega-precategories.html#7403" class="Bound">y</a> <a id="7518" class="Symbol">→</a>
    <a id="7524" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="7527" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="7532" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="7564" class="Symbol">=</a>
    <a id="7570" href="globular-types.globular-types.html#6027" class="Function">2-cell-Globular-Type</a> <a id="7591" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>

  <a id="7634" href="wild-category-theory.noncoherent-omega-precategories.html#7634" class="Function">id-2-hom-Noncoherent-ω-Precategory</a> <a id="7669" class="Symbol">:</a>
    <a id="7675" class="Symbol">{</a><a id="7676" href="wild-category-theory.noncoherent-omega-precategories.html#7676" class="Bound">x</a> <a id="7678" href="wild-category-theory.noncoherent-omega-precategories.html#7678" class="Bound">y</a> <a id="7680" class="Symbol">:</a> <a id="7682" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="7711" class="Symbol">}</a>
    <a id="7717" class="Symbol">{</a><a id="7718" href="wild-category-theory.noncoherent-omega-precategories.html#7718" class="Bound">f</a> <a id="7720" class="Symbol">:</a> <a id="7722" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="7752" href="wild-category-theory.noncoherent-omega-precategories.html#7676" class="Bound">x</a> <a id="7754" href="wild-category-theory.noncoherent-omega-precategories.html#7678" class="Bound">y</a><a id="7755" class="Symbol">}</a> <a id="7757" class="Symbol">→</a>
    <a id="7763" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="7795" href="wild-category-theory.noncoherent-omega-precategories.html#7718" class="Bound">f</a> <a id="7797" href="wild-category-theory.noncoherent-omega-precategories.html#7718" class="Bound">f</a>
  <a id="7801" href="wild-category-theory.noncoherent-omega-precategories.html#7634" class="Function">id-2-hom-Noncoherent-ω-Precategory</a> <a id="7836" class="Symbol">=</a>
    <a id="7842" href="globular-types.reflexive-globular-types.html#1814" class="Function">refl-3-cell-is-reflexive-Globular-Type</a>
      <a id="7887" href="wild-category-theory.noncoherent-omega-precategories.html#3648" class="Function">id-structure-Noncoherent-ω-Precategory</a>

  <a id="7929" href="wild-category-theory.noncoherent-omega-precategories.html#7929" class="Function">comp-2-hom-Noncoherent-ω-Precategory</a> <a id="7966" class="Symbol">:</a>
    <a id="7972" class="Symbol">{</a><a id="7973" href="wild-category-theory.noncoherent-omega-precategories.html#7973" class="Bound">x</a> <a id="7975" href="wild-category-theory.noncoherent-omega-precategories.html#7975" class="Bound">y</a> <a id="7977" class="Symbol">:</a> <a id="7979" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="8008" class="Symbol">}</a>
    <a id="8014" class="Symbol">{</a><a id="8015" href="wild-category-theory.noncoherent-omega-precategories.html#8015" class="Bound">f</a> <a id="8017" href="wild-category-theory.noncoherent-omega-precategories.html#8017" class="Bound">g</a> <a id="8019" href="wild-category-theory.noncoherent-omega-precategories.html#8019" class="Bound">h</a> <a id="8021" class="Symbol">:</a> <a id="8023" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="8053" href="wild-category-theory.noncoherent-omega-precategories.html#7973" class="Bound">x</a> <a id="8055" href="wild-category-theory.noncoherent-omega-precategories.html#7975" class="Bound">y</a><a id="8056" class="Symbol">}</a> <a id="8058" class="Symbol">→</a>
    <a id="8064" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="8096" href="wild-category-theory.noncoherent-omega-precategories.html#8017" class="Bound">g</a> <a id="8098" href="wild-category-theory.noncoherent-omega-precategories.html#8019" class="Bound">h</a> <a id="8100" class="Symbol">→</a>
    <a id="8106" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="8138" href="wild-category-theory.noncoherent-omega-precategories.html#8015" class="Bound">f</a> <a id="8140" href="wild-category-theory.noncoherent-omega-precategories.html#8017" class="Bound">g</a> <a id="8142" class="Symbol">→</a>
    <a id="8148" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="8180" href="wild-category-theory.noncoherent-omega-precategories.html#8015" class="Bound">f</a> <a id="8182" href="wild-category-theory.noncoherent-omega-precategories.html#8019" class="Bound">h</a>
  <a id="8186" href="wild-category-theory.noncoherent-omega-precategories.html#7929" class="Function">comp-2-hom-Noncoherent-ω-Precategory</a> <a id="8223" class="Symbol">=</a>
    <a id="8229" href="globular-types.transitive-globular-types.html#1435" class="Function">comp-2-cell-is-transitive-Globular-Type</a>
      <a id="8275" href="wild-category-theory.noncoherent-omega-precategories.html#5189" class="Function">comp-structure-Noncoherent-ω-Precategory</a>
</pre>
3-Morphisms in a noncoherent ω-precategory:

<pre class="Agda">  <a id="8376" href="wild-category-theory.noncoherent-omega-precategories.html#8376" class="Function">3-hom-Noncoherent-ω-Precategory</a> <a id="8408" class="Symbol">:</a>
    <a id="8414" class="Symbol">{</a><a id="8415" href="wild-category-theory.noncoherent-omega-precategories.html#8415" class="Bound">x</a> <a id="8417" href="wild-category-theory.noncoherent-omega-precategories.html#8417" class="Bound">y</a> <a id="8419" class="Symbol">:</a> <a id="8421" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="8450" class="Symbol">}</a>
    <a id="8456" class="Symbol">{</a><a id="8457" href="wild-category-theory.noncoherent-omega-precategories.html#8457" class="Bound">f</a> <a id="8459" href="wild-category-theory.noncoherent-omega-precategories.html#8459" class="Bound">g</a> <a id="8461" class="Symbol">:</a> <a id="8463" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="8493" href="wild-category-theory.noncoherent-omega-precategories.html#8415" class="Bound">x</a> <a id="8495" href="wild-category-theory.noncoherent-omega-precategories.html#8417" class="Bound">y</a><a id="8496" class="Symbol">}</a> <a id="8498" class="Symbol">→</a>
    <a id="8504" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="8536" href="wild-category-theory.noncoherent-omega-precategories.html#8457" class="Bound">f</a> <a id="8538" href="wild-category-theory.noncoherent-omega-precategories.html#8459" class="Bound">g</a> <a id="8540" class="Symbol">→</a>
    <a id="8546" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="8578" href="wild-category-theory.noncoherent-omega-precategories.html#8457" class="Bound">f</a> <a id="8580" href="wild-category-theory.noncoherent-omega-precategories.html#8459" class="Bound">g</a> <a id="8582" class="Symbol">→</a> <a id="8584" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="8587" href="wild-category-theory.noncoherent-omega-precategories.html#2747" class="Bound">l2</a>
  <a id="8592" href="wild-category-theory.noncoherent-omega-precategories.html#8376" class="Function">3-hom-Noncoherent-ω-Precategory</a> <a id="8624" class="Symbol">=</a>
    <a id="8630" href="globular-types.globular-types.html#6264" class="Function">3-cell-Globular-Type</a> <a id="8651" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>

  <a id="8694" href="wild-category-theory.noncoherent-omega-precategories.html#8694" class="Function">id-3-hom-Noncoherent-ω-Precategory</a> <a id="8729" class="Symbol">:</a>
    <a id="8735" class="Symbol">{</a><a id="8736" href="wild-category-theory.noncoherent-omega-precategories.html#8736" class="Bound">x</a> <a id="8738" href="wild-category-theory.noncoherent-omega-precategories.html#8738" class="Bound">y</a> <a id="8740" class="Symbol">:</a> <a id="8742" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="8771" class="Symbol">}</a>
    <a id="8777" class="Symbol">{</a><a id="8778" href="wild-category-theory.noncoherent-omega-precategories.html#8778" class="Bound">f</a> <a id="8780" href="wild-category-theory.noncoherent-omega-precategories.html#8780" class="Bound">g</a> <a id="8782" class="Symbol">:</a> <a id="8784" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="8814" href="wild-category-theory.noncoherent-omega-precategories.html#8736" class="Bound">x</a> <a id="8816" href="wild-category-theory.noncoherent-omega-precategories.html#8738" class="Bound">y</a><a id="8817" class="Symbol">}</a>
    <a id="8823" class="Symbol">{</a><a id="8824" href="wild-category-theory.noncoherent-omega-precategories.html#8824" class="Bound">H</a> <a id="8826" class="Symbol">:</a> <a id="8828" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="8860" href="wild-category-theory.noncoherent-omega-precategories.html#8778" class="Bound">f</a> <a id="8862" href="wild-category-theory.noncoherent-omega-precategories.html#8780" class="Bound">g</a><a id="8863" class="Symbol">}</a> <a id="8865" class="Symbol">→</a>
    <a id="8871" href="wild-category-theory.noncoherent-omega-precategories.html#8376" class="Function">3-hom-Noncoherent-ω-Precategory</a> <a id="8903" href="wild-category-theory.noncoherent-omega-precategories.html#8824" class="Bound">H</a> <a id="8905" href="wild-category-theory.noncoherent-omega-precategories.html#8824" class="Bound">H</a>
  <a id="8909" href="wild-category-theory.noncoherent-omega-precategories.html#8694" class="Function">id-3-hom-Noncoherent-ω-Precategory</a> <a id="8944" class="Symbol">=</a>
    <a id="8950" href="globular-types.reflexive-globular-types.html#3032" class="Function">refl-4-cell-is-reflexive-Globular-Type</a>
      <a id="8995" href="wild-category-theory.noncoherent-omega-precategories.html#2808" class="Function">globular-type-Noncoherent-ω-Precategory</a>
      <a id="9041" href="wild-category-theory.noncoherent-omega-precategories.html#3648" class="Function">id-structure-Noncoherent-ω-Precategory</a>

  <a id="9083" href="wild-category-theory.noncoherent-omega-precategories.html#9083" class="Function">comp-3-hom-Noncoherent-ω-Precategory</a> <a id="9120" class="Symbol">:</a>
    <a id="9126" class="Symbol">{</a><a id="9127" href="wild-category-theory.noncoherent-omega-precategories.html#9127" class="Bound">x</a> <a id="9129" href="wild-category-theory.noncoherent-omega-precategories.html#9129" class="Bound">y</a> <a id="9131" class="Symbol">:</a> <a id="9133" href="wild-category-theory.noncoherent-omega-precategories.html#2923" class="Function">obj-Noncoherent-ω-Precategory</a><a id="9162" class="Symbol">}</a>
    <a id="9168" class="Symbol">{</a><a id="9169" href="wild-category-theory.noncoherent-omega-precategories.html#9169" class="Bound">f</a> <a id="9171" href="wild-category-theory.noncoherent-omega-precategories.html#9171" class="Bound">g</a> <a id="9173" class="Symbol">:</a> <a id="9175" href="wild-category-theory.noncoherent-omega-precategories.html#3368" class="Function">hom-Noncoherent-ω-Precategory</a> <a id="9205" href="wild-category-theory.noncoherent-omega-precategories.html#9127" class="Bound">x</a> <a id="9207" href="wild-category-theory.noncoherent-omega-precategories.html#9129" class="Bound">y</a><a id="9208" class="Symbol">}</a>
    <a id="9214" class="Symbol">{</a><a id="9215" href="wild-category-theory.noncoherent-omega-precategories.html#9215" class="Bound">H</a> <a id="9217" href="wild-category-theory.noncoherent-omega-precategories.html#9217" class="Bound">K</a> <a id="9219" href="wild-category-theory.noncoherent-omega-precategories.html#9219" class="Bound">L</a> <a id="9221" class="Symbol">:</a> <a id="9223" href="wild-category-theory.noncoherent-omega-precategories.html#7362" class="Function">2-hom-Noncoherent-ω-Precategory</a> <a id="9255" href="wild-category-theory.noncoherent-omega-precategories.html#9169" class="Bound">f</a> <a id="9257" href="wild-category-theory.noncoherent-omega-precategories.html#9171" class="Bound">g</a><a id="9258" class="Symbol">}</a> <a id="9260" class="Symbol">→</a>
    <a id="9266" href="wild-category-theory.noncoherent-omega-precategories.html#8376" class="Function">3-hom-Noncoherent-ω-Precategory</a> <a id="9298" href="wild-category-theory.noncoherent-omega-precategories.html#9217" class="Bound">K</a> <a id="9300" href="wild-category-theory.noncoherent-omega-precategories.html#9219" class="Bound">L</a> <a id="9302" class="Symbol">→</a>
    <a id="9308" href="wild-category-theory.noncoherent-omega-precategories.html#8376" class="Function">3-hom-Noncoherent-ω-Precategory</a> <a id="9340" href="wild-category-theory.noncoherent-omega-precategories.html#9215" class="Bound">H</a> <a id="9342" href="wild-category-theory.noncoherent-omega-precategories.html#9217" class="Bound">K</a> <a id="9344" class="Symbol">→</a>
    <a id="9350" href="wild-category-theory.noncoherent-omega-precategories.html#8376" class="Function">3-hom-Noncoherent-ω-Precategory</a> <a id="9382" href="wild-category-theory.noncoherent-omega-precategories.html#9215" class="Bound">H</a> <a id="9384" href="wild-category-theory.noncoherent-omega-precategories.html#9219" class="Bound">L</a>
  <a id="9388" href="wild-category-theory.noncoherent-omega-precategories.html#9083" class="Function">comp-3-hom-Noncoherent-ω-Precategory</a> <a id="9425" class="Symbol">=</a>
    <a id="9431" href="globular-types.transitive-globular-types.html#2265" class="Function">comp-3-cell-is-transitive-Globular-Type</a>
      <a id="9477" href="wild-category-theory.noncoherent-omega-precategories.html#5189" class="Function">comp-structure-Noncoherent-ω-Precategory</a>
</pre>