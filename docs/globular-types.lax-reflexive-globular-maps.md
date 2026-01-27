# Lax reflexive globular maps

<pre class="Agda"><a id="40" class="Symbol">{-#</a> <a id="44" class="Keyword">OPTIONS</a> <a id="52" class="Pragma">--guardedness</a> <a id="66" class="Symbol">#-}</a>

<a id="71" class="Keyword">module</a> <a id="78" href="globular-types.lax-reflexive-globular-maps.html" class="Module">globular-types.lax-reflexive-globular-maps</a> <a id="121" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="globular-types.globular-maps.html" class="Module">globular-types.globular-maps</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
</pre>
</details>

## Idea

A {{#concept "lax reflexive globular map" Agda=lax-reflexive-globular-map}}
between two
[reflexive globular types](globular-types.reflexive-globular-types.md) `G` and
`H` is a [globular map](globular-types.globular-maps.md) `f : G → H` equipped
with a family of 2-cells

```text
  (x : G₀) → H₂ (refl H (f₀ x)) (f₁ (refl G x))
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at
`f₀ x`, such that the globular map `f' : G' x y → H' (f₀ x) (f₀ y)` is again lax
reflexive.

### Lack of composition for lax reflexive globular maps

Note that the lax reflexive globular maps lack composition. For the composition
of `g` and `f` to exist, there should be a `2`-cell from `g (f (refl G x))` to
`refl K (g (f x))`, we need to compose the 2-cell that `g` preserves reflexivity
with the action of `g` on the 2-cell that `f` preserves reflexivity. However,
since the reflexive globular type `G` is not assumed to be
[transitive](globular-types.transitive-globular-types.md), it might lack such
instances of the compositions.

### Lax reflexive globular maps versus the morphisms of presheaves on the reflexive globe category

When reflexive globular types are viewed as type valued presheaves over the
reflexive globe category, the resulting notion of morphism is that of
[reflexive globular maps](globular-types.reflexive-globular-maps.md), which is
stricter than the notion of lax reflexive globular maps.

### Lax versus colax

The notion of
[colax reflexive globular map](globular-types.colax-reflexive-globular-maps.md)
is almost the same, except with the direction of the 2-cell reversed. In
general, the direction of lax coherence cells is determined by applying the
morphism componentwise first, and then the operations, while the direction of
colax coherence cells is determined by first applying the operations and then
the morphism.

## Definitions

### The predicate of laxly preserving reflexivity

<pre class="Agda"><a id="2279" class="Keyword">record</a>
  <a id="is-lax-reflexive-globular-map"></a><a id="2288" href="globular-types.lax-reflexive-globular-maps.html#2288" class="Record">is-lax-reflexive-globular-map</a>
    <a id="2322" class="Symbol">{</a><a id="2323" href="globular-types.lax-reflexive-globular-maps.html#2323" class="Bound">l1</a> <a id="2326" href="globular-types.lax-reflexive-globular-maps.html#2326" class="Bound">l2</a> <a id="2329" href="globular-types.lax-reflexive-globular-maps.html#2329" class="Bound">l3</a> <a id="2332" href="globular-types.lax-reflexive-globular-maps.html#2332" class="Bound">l4</a> <a id="2335" class="Symbol">:</a> <a id="2337" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2342" class="Symbol">}</a>
    <a id="2348" class="Symbol">(</a><a id="2349" href="globular-types.lax-reflexive-globular-maps.html#2349" class="Bound">G</a> <a id="2351" class="Symbol">:</a> <a id="2353" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2377" href="globular-types.lax-reflexive-globular-maps.html#2323" class="Bound">l1</a> <a id="2380" href="globular-types.lax-reflexive-globular-maps.html#2326" class="Bound">l2</a><a id="2382" class="Symbol">)</a> <a id="2384" class="Symbol">(</a><a id="2385" href="globular-types.lax-reflexive-globular-maps.html#2385" class="Bound">H</a> <a id="2387" class="Symbol">:</a> <a id="2389" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2413" href="globular-types.lax-reflexive-globular-maps.html#2329" class="Bound">l3</a> <a id="2416" href="globular-types.lax-reflexive-globular-maps.html#2332" class="Bound">l4</a><a id="2418" class="Symbol">)</a>
    <a id="2424" class="Symbol">(</a><a id="2425" href="globular-types.lax-reflexive-globular-maps.html#2425" class="Bound">f</a> <a id="2427" class="Symbol">:</a> <a id="2429" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a> <a id="2466" href="globular-types.lax-reflexive-globular-maps.html#2349" class="Bound">G</a> <a id="2468" href="globular-types.lax-reflexive-globular-maps.html#2385" class="Bound">H</a><a id="2469" class="Symbol">)</a> <a id="2471" class="Symbol">:</a>
    <a id="2477" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2480" class="Symbol">(</a><a id="2481" href="globular-types.lax-reflexive-globular-maps.html#2323" class="Bound">l1</a> <a id="2484" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2486" href="globular-types.lax-reflexive-globular-maps.html#2326" class="Bound">l2</a> <a id="2489" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2491" href="globular-types.lax-reflexive-globular-maps.html#2332" class="Bound">l4</a><a id="2493" class="Symbol">)</a>
  <a id="2497" class="Keyword">where</a>
  <a id="2505" class="Keyword">coinductive</a>

  <a id="2520" class="Keyword">field</a>
    <a id="is-lax-reflexive-globular-map.preserves-refl-1-cell-is-lax-reflexive-globular-map"></a><a id="2530" href="globular-types.lax-reflexive-globular-maps.html#2530" class="Field">preserves-refl-1-cell-is-lax-reflexive-globular-map</a> <a id="2582" class="Symbol">:</a>
      <a id="2590" class="Symbol">(</a><a id="2591" href="globular-types.lax-reflexive-globular-maps.html#2591" class="Bound">x</a> <a id="2593" class="Symbol">:</a> <a id="2595" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="2626" href="globular-types.lax-reflexive-globular-maps.html#2349" class="Bound">G</a><a id="2627" class="Symbol">)</a> <a id="2629" class="Symbol">→</a>
      <a id="2637" href="globular-types.reflexive-globular-types.html#4480" class="Function">2-cell-Reflexive-Globular-Type</a> <a id="2668" href="globular-types.lax-reflexive-globular-maps.html#2385" class="Bound">H</a>
        <a id="2678" class="Symbol">(</a> <a id="2680" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="2716" href="globular-types.lax-reflexive-globular-maps.html#2385" class="Bound">H</a><a id="2717" class="Symbol">)</a>
        <a id="2727" class="Symbol">(</a> <a id="2729" href="globular-types.globular-maps.html#1422" class="Function">1-cell-globular-map</a> <a id="2749" href="globular-types.lax-reflexive-globular-maps.html#2425" class="Bound">f</a> <a id="2751" class="Symbol">(</a><a id="2752" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="2788" href="globular-types.lax-reflexive-globular-maps.html#2349" class="Bound">G</a> <a id="2790" class="Symbol">{</a><a id="2791" href="globular-types.lax-reflexive-globular-maps.html#2591" class="Bound">x</a><a id="2792" class="Symbol">}))</a>

  <a id="2799" class="Keyword">field</a>
    <a id="is-lax-reflexive-globular-map.is-lax-reflexive-1-cell-globular-map-is-lax-reflexive-globular-map"></a><a id="2809" href="globular-types.lax-reflexive-globular-maps.html#2809" class="Field">is-lax-reflexive-1-cell-globular-map-is-lax-reflexive-globular-map</a> <a id="2876" class="Symbol">:</a>
      <a id="2884" class="Symbol">{</a><a id="2885" href="globular-types.lax-reflexive-globular-maps.html#2885" class="Bound">x</a> <a id="2887" href="globular-types.lax-reflexive-globular-maps.html#2887" class="Bound">y</a> <a id="2889" class="Symbol">:</a> <a id="2891" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="2922" href="globular-types.lax-reflexive-globular-maps.html#2349" class="Bound">G</a><a id="2923" class="Symbol">}</a> <a id="2925" class="Symbol">→</a>
      <a id="2933" href="globular-types.lax-reflexive-globular-maps.html#2288" class="Record">is-lax-reflexive-globular-map</a>
        <a id="2971" class="Symbol">(</a> <a id="2973" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="3028" href="globular-types.lax-reflexive-globular-maps.html#2349" class="Bound">G</a> <a id="3030" href="globular-types.lax-reflexive-globular-maps.html#2885" class="Bound">x</a> <a id="3032" href="globular-types.lax-reflexive-globular-maps.html#2887" class="Bound">y</a><a id="3033" class="Symbol">)</a>
        <a id="3043" class="Symbol">(</a> <a id="3045" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="3100" href="globular-types.lax-reflexive-globular-maps.html#2385" class="Bound">H</a> <a id="3102" class="Symbol">_</a> <a id="3104" class="Symbol">_)</a>
        <a id="3115" class="Symbol">(</a> <a id="3117" href="globular-types.reflexive-globular-types.html#10984" class="Function">1-cell-globular-map-globular-map-Reflexive-Globular-Type</a> <a id="3174" href="globular-types.lax-reflexive-globular-maps.html#2349" class="Bound">G</a> <a id="3176" href="globular-types.lax-reflexive-globular-maps.html#2385" class="Bound">H</a> <a id="3178" href="globular-types.lax-reflexive-globular-maps.html#2425" class="Bound">f</a><a id="3179" class="Symbol">)</a>

<a id="3182" class="Keyword">open</a> <a id="3187" href="globular-types.lax-reflexive-globular-maps.html#2288" class="Module">is-lax-reflexive-globular-map</a> <a id="3217" class="Keyword">public</a>
</pre>
### Lax reflexive globular maps

<pre class="Agda"><a id="3270" class="Keyword">record</a>
  <a id="lax-reflexive-globular-map"></a><a id="3279" href="globular-types.lax-reflexive-globular-maps.html#3279" class="Record">lax-reflexive-globular-map</a>
    <a id="3310" class="Symbol">{</a><a id="3311" href="globular-types.lax-reflexive-globular-maps.html#3311" class="Bound">l1</a> <a id="3314" href="globular-types.lax-reflexive-globular-maps.html#3314" class="Bound">l2</a> <a id="3317" href="globular-types.lax-reflexive-globular-maps.html#3317" class="Bound">l3</a> <a id="3320" href="globular-types.lax-reflexive-globular-maps.html#3320" class="Bound">l4</a> <a id="3323" class="Symbol">:</a> <a id="3325" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3330" class="Symbol">}</a>
    <a id="3336" class="Symbol">(</a><a id="3337" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="3339" class="Symbol">:</a> <a id="3341" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="3365" href="globular-types.lax-reflexive-globular-maps.html#3311" class="Bound">l1</a> <a id="3368" href="globular-types.lax-reflexive-globular-maps.html#3314" class="Bound">l2</a><a id="3370" class="Symbol">)</a>
    <a id="3376" class="Symbol">(</a><a id="3377" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a> <a id="3379" class="Symbol">:</a> <a id="3381" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="3405" href="globular-types.lax-reflexive-globular-maps.html#3317" class="Bound">l3</a> <a id="3408" href="globular-types.lax-reflexive-globular-maps.html#3320" class="Bound">l4</a><a id="3410" class="Symbol">)</a> <a id="3412" class="Symbol">:</a>
    <a id="3418" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3421" class="Symbol">(</a><a id="3422" href="globular-types.lax-reflexive-globular-maps.html#3311" class="Bound">l1</a> <a id="3425" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3427" href="globular-types.lax-reflexive-globular-maps.html#3314" class="Bound">l2</a> <a id="3430" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3432" href="globular-types.lax-reflexive-globular-maps.html#3317" class="Bound">l3</a> <a id="3435" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3437" href="globular-types.lax-reflexive-globular-maps.html#3320" class="Bound">l4</a><a id="3439" class="Symbol">)</a>
  <a id="3443" class="Keyword">where</a>

  <a id="3452" class="Keyword">field</a>
    <a id="lax-reflexive-globular-map.globular-map-lax-reflexive-globular-map"></a><a id="3462" href="globular-types.lax-reflexive-globular-maps.html#3462" class="Field">globular-map-lax-reflexive-globular-map</a> <a id="3502" class="Symbol">:</a>
      <a id="3510" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a> <a id="3547" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="3549" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a>

  <a id="lax-reflexive-globular-map.0-cell-lax-reflexive-globular-map"></a><a id="3554" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="3588" class="Symbol">:</a>
    <a id="3594" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="3625" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="3627" class="Symbol">→</a> <a id="3629" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="3660" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a>
  <a id="3664" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="3698" class="Symbol">=</a>
    <a id="3704" href="globular-types.globular-maps.html#928" class="Field">0-cell-globular-map</a> <a id="3724" href="globular-types.lax-reflexive-globular-maps.html#3462" class="Field">globular-map-lax-reflexive-globular-map</a>

  <a id="lax-reflexive-globular-map.1-cell-lax-reflexive-globular-map"></a><a id="3767" href="globular-types.lax-reflexive-globular-maps.html#3767" class="Function">1-cell-lax-reflexive-globular-map</a> <a id="3801" class="Symbol">:</a>
    <a id="3807" class="Symbol">{</a><a id="3808" href="globular-types.lax-reflexive-globular-maps.html#3808" class="Bound">x</a> <a id="3810" href="globular-types.lax-reflexive-globular-maps.html#3810" class="Bound">y</a> <a id="3812" class="Symbol">:</a> <a id="3814" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="3845" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a><a id="3846" class="Symbol">}</a> <a id="3848" class="Symbol">→</a>
    <a id="3854" href="globular-types.reflexive-globular-types.html#4270" class="Function">1-cell-Reflexive-Globular-Type</a> <a id="3885" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="3887" href="globular-types.lax-reflexive-globular-maps.html#3808" class="Bound">x</a> <a id="3889" href="globular-types.lax-reflexive-globular-maps.html#3810" class="Bound">y</a> <a id="3891" class="Symbol">→</a>
    <a id="3897" href="globular-types.reflexive-globular-types.html#4270" class="Function">1-cell-Reflexive-Globular-Type</a> <a id="3928" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a>
      <a id="3936" class="Symbol">(</a> <a id="3938" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="3972" href="globular-types.lax-reflexive-globular-maps.html#3808" class="Bound">x</a><a id="3973" class="Symbol">)</a>
      <a id="3981" class="Symbol">(</a> <a id="3983" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="4017" href="globular-types.lax-reflexive-globular-maps.html#3810" class="Bound">y</a><a id="4018" class="Symbol">)</a>
  <a id="4022" href="globular-types.lax-reflexive-globular-maps.html#3767" class="Function">1-cell-lax-reflexive-globular-map</a> <a id="4056" class="Symbol">=</a>
    <a id="4062" href="globular-types.globular-maps.html#1422" class="Function">1-cell-globular-map</a> <a id="4082" href="globular-types.lax-reflexive-globular-maps.html#3462" class="Field">globular-map-lax-reflexive-globular-map</a>

  <a id="lax-reflexive-globular-map.1-cell-globular-map-lax-reflexive-globular-map"></a><a id="4125" href="globular-types.lax-reflexive-globular-maps.html#4125" class="Function">1-cell-globular-map-lax-reflexive-globular-map</a> <a id="4172" class="Symbol">:</a>
    <a id="4178" class="Symbol">{</a><a id="4179" href="globular-types.lax-reflexive-globular-maps.html#4179" class="Bound">x</a> <a id="4181" href="globular-types.lax-reflexive-globular-maps.html#4181" class="Bound">y</a> <a id="4183" class="Symbol">:</a> <a id="4185" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="4216" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a><a id="4217" class="Symbol">}</a> <a id="4219" class="Symbol">→</a>
    <a id="4225" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a>
      <a id="4268" class="Symbol">(</a> <a id="4270" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="4325" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="4327" href="globular-types.lax-reflexive-globular-maps.html#4179" class="Bound">x</a> <a id="4329" href="globular-types.lax-reflexive-globular-maps.html#4181" class="Bound">y</a><a id="4330" class="Symbol">)</a>
      <a id="4338" class="Symbol">(</a> <a id="4340" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="4395" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a>
        <a id="4405" class="Symbol">(</a> <a id="4407" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="4441" href="globular-types.lax-reflexive-globular-maps.html#4179" class="Bound">x</a><a id="4442" class="Symbol">)</a>
        <a id="4452" class="Symbol">(</a> <a id="4454" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="4488" href="globular-types.lax-reflexive-globular-maps.html#4181" class="Bound">y</a><a id="4489" class="Symbol">))</a>
  <a id="4494" href="globular-types.lax-reflexive-globular-maps.html#4125" class="Function">1-cell-globular-map-lax-reflexive-globular-map</a> <a id="4541" class="Symbol">=</a>
    <a id="4547" href="globular-types.globular-maps.html#1009" class="Field">1-cell-globular-map-globular-map</a> <a id="4580" href="globular-types.lax-reflexive-globular-maps.html#3462" class="Field">globular-map-lax-reflexive-globular-map</a>

  <a id="4623" class="Keyword">field</a>
    <a id="lax-reflexive-globular-map.is-lax-reflexive-lax-reflexive-globular-map"></a><a id="4633" href="globular-types.lax-reflexive-globular-maps.html#4633" class="Field">is-lax-reflexive-lax-reflexive-globular-map</a> <a id="4677" class="Symbol">:</a>
      <a id="4685" href="globular-types.lax-reflexive-globular-maps.html#2288" class="Record">is-lax-reflexive-globular-map</a> <a id="4715" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="4717" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a>
        <a id="4727" href="globular-types.lax-reflexive-globular-maps.html#3462" class="Field">globular-map-lax-reflexive-globular-map</a>

  <a id="lax-reflexive-globular-map.preserves-refl-1-cell-lax-reflexive-globular-map"></a><a id="4770" href="globular-types.lax-reflexive-globular-maps.html#4770" class="Function">preserves-refl-1-cell-lax-reflexive-globular-map</a> <a id="4819" class="Symbol">:</a>
    <a id="4825" class="Symbol">(</a><a id="4826" href="globular-types.lax-reflexive-globular-maps.html#4826" class="Bound">x</a> <a id="4828" class="Symbol">:</a> <a id="4830" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="4861" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a><a id="4862" class="Symbol">)</a> <a id="4864" class="Symbol">→</a>
    <a id="4870" href="globular-types.reflexive-globular-types.html#4480" class="Function">2-cell-Reflexive-Globular-Type</a> <a id="4901" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a>
      <a id="4909" class="Symbol">(</a> <a id="4911" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="4947" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a><a id="4948" class="Symbol">)</a>
      <a id="4956" class="Symbol">(</a> <a id="4958" href="globular-types.lax-reflexive-globular-maps.html#3767" class="Function">1-cell-lax-reflexive-globular-map</a>
        <a id="5000" class="Symbol">(</a> <a id="5002" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="5038" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="5040" class="Symbol">{</a><a id="5041" href="globular-types.lax-reflexive-globular-maps.html#4826" class="Bound">x</a><a id="5042" class="Symbol">}))</a>
  <a id="5048" href="globular-types.lax-reflexive-globular-maps.html#4770" class="Function">preserves-refl-1-cell-lax-reflexive-globular-map</a> <a id="5097" class="Symbol">=</a>
    <a id="5103" href="globular-types.lax-reflexive-globular-maps.html#2530" class="Field">preserves-refl-1-cell-is-lax-reflexive-globular-map</a>
      <a id="5161" href="globular-types.lax-reflexive-globular-maps.html#4633" class="Field">is-lax-reflexive-lax-reflexive-globular-map</a>

  <a id="lax-reflexive-globular-map.is-lax-reflexive-2-cell-globular-map-is-lax-reflexive-globular-map"></a><a id="5208" href="globular-types.lax-reflexive-globular-maps.html#5208" class="Function">is-lax-reflexive-2-cell-globular-map-is-lax-reflexive-globular-map</a> <a id="5275" class="Symbol">:</a>
    <a id="5281" class="Symbol">{</a><a id="5282" href="globular-types.lax-reflexive-globular-maps.html#5282" class="Bound">x</a> <a id="5284" href="globular-types.lax-reflexive-globular-maps.html#5284" class="Bound">y</a> <a id="5286" class="Symbol">:</a> <a id="5288" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="5319" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a><a id="5320" class="Symbol">}</a> <a id="5322" class="Symbol">→</a>
    <a id="5328" href="globular-types.lax-reflexive-globular-maps.html#2288" class="Record">is-lax-reflexive-globular-map</a>
      <a id="5364" class="Symbol">(</a> <a id="5366" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="5421" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="5423" href="globular-types.lax-reflexive-globular-maps.html#5282" class="Bound">x</a> <a id="5425" href="globular-types.lax-reflexive-globular-maps.html#5284" class="Bound">y</a><a id="5426" class="Symbol">)</a>
      <a id="5434" class="Symbol">(</a> <a id="5436" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="5491" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a>
        <a id="5501" class="Symbol">(</a> <a id="5503" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="5537" href="globular-types.lax-reflexive-globular-maps.html#5282" class="Bound">x</a><a id="5538" class="Symbol">)</a>
        <a id="5548" class="Symbol">(</a> <a id="5550" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="5584" href="globular-types.lax-reflexive-globular-maps.html#5284" class="Bound">y</a><a id="5585" class="Symbol">))</a>
      <a id="5594" class="Symbol">(</a> <a id="5596" href="globular-types.lax-reflexive-globular-maps.html#4125" class="Function">1-cell-globular-map-lax-reflexive-globular-map</a><a id="5642" class="Symbol">)</a>
  <a id="5646" href="globular-types.lax-reflexive-globular-maps.html#5208" class="Function">is-lax-reflexive-2-cell-globular-map-is-lax-reflexive-globular-map</a> <a id="5713" class="Symbol">=</a>
    <a id="5719" href="globular-types.lax-reflexive-globular-maps.html#2809" class="Field">is-lax-reflexive-1-cell-globular-map-is-lax-reflexive-globular-map</a>
      <a id="5792" href="globular-types.lax-reflexive-globular-maps.html#4633" class="Field">is-lax-reflexive-lax-reflexive-globular-map</a>

  <a id="lax-reflexive-globular-map.1-cell-lax-reflexive-globular-map-lax-reflexive-globular-map"></a><a id="5839" href="globular-types.lax-reflexive-globular-maps.html#5839" class="Function">1-cell-lax-reflexive-globular-map-lax-reflexive-globular-map</a> <a id="5900" class="Symbol">:</a>
    <a id="5906" class="Symbol">{</a><a id="5907" href="globular-types.lax-reflexive-globular-maps.html#5907" class="Bound">x</a> <a id="5909" href="globular-types.lax-reflexive-globular-maps.html#5909" class="Bound">y</a> <a id="5911" class="Symbol">:</a> <a id="5913" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="5944" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a><a id="5945" class="Symbol">}</a> <a id="5947" class="Symbol">→</a>
    <a id="5953" href="globular-types.lax-reflexive-globular-maps.html#3279" class="Record">lax-reflexive-globular-map</a>
      <a id="5986" class="Symbol">(</a> <a id="5988" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="6043" href="globular-types.lax-reflexive-globular-maps.html#3337" class="Bound">G</a> <a id="6045" href="globular-types.lax-reflexive-globular-maps.html#5907" class="Bound">x</a> <a id="6047" href="globular-types.lax-reflexive-globular-maps.html#5909" class="Bound">y</a><a id="6048" class="Symbol">)</a>
      <a id="6056" class="Symbol">(</a> <a id="6058" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="6113" href="globular-types.lax-reflexive-globular-maps.html#3377" class="Bound">H</a>
        <a id="6123" class="Symbol">(</a> <a id="6125" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="6159" href="globular-types.lax-reflexive-globular-maps.html#5907" class="Bound">x</a><a id="6160" class="Symbol">)</a>
        <a id="6170" class="Symbol">(</a> <a id="6172" href="globular-types.lax-reflexive-globular-maps.html#3554" class="Function">0-cell-lax-reflexive-globular-map</a> <a id="6206" href="globular-types.lax-reflexive-globular-maps.html#5909" class="Bound">y</a><a id="6207" class="Symbol">))</a>
  <a id="6212" href="globular-types.lax-reflexive-globular-maps.html#3462" class="Field">globular-map-lax-reflexive-globular-map</a>
    <a id="6256" href="globular-types.lax-reflexive-globular-maps.html#5839" class="Function">1-cell-lax-reflexive-globular-map-lax-reflexive-globular-map</a> <a id="6317" class="Symbol">=</a>
    <a id="6323" href="globular-types.lax-reflexive-globular-maps.html#4125" class="Function">1-cell-globular-map-lax-reflexive-globular-map</a>
  <a id="6372" href="globular-types.lax-reflexive-globular-maps.html#4633" class="Field">is-lax-reflexive-lax-reflexive-globular-map</a>
    <a id="6420" href="globular-types.lax-reflexive-globular-maps.html#5839" class="Function">1-cell-lax-reflexive-globular-map-lax-reflexive-globular-map</a> <a id="6481" class="Symbol">=</a>
    <a id="6487" href="globular-types.lax-reflexive-globular-maps.html#5208" class="Function">is-lax-reflexive-2-cell-globular-map-is-lax-reflexive-globular-map</a>

<a id="6555" class="Keyword">open</a> <a id="6560" href="globular-types.lax-reflexive-globular-maps.html#3279" class="Module">lax-reflexive-globular-map</a> <a id="6587" class="Keyword">public</a>
</pre>
### The identity lax reflexive globular map

<pre class="Agda"><a id="map-id-lax-reflexive-globular-map"></a><a id="6652" href="globular-types.lax-reflexive-globular-maps.html#6652" class="Function">map-id-lax-reflexive-globular-map</a> <a id="6686" class="Symbol">:</a>
  <a id="6690" class="Symbol">{</a><a id="6691" href="globular-types.lax-reflexive-globular-maps.html#6691" class="Bound">l1</a> <a id="6694" href="globular-types.lax-reflexive-globular-maps.html#6694" class="Bound">l2</a> <a id="6697" class="Symbol">:</a> <a id="6699" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6704" class="Symbol">}</a> <a id="6706" class="Symbol">(</a><a id="6707" href="globular-types.lax-reflexive-globular-maps.html#6707" class="Bound">G</a> <a id="6709" class="Symbol">:</a> <a id="6711" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="6735" href="globular-types.lax-reflexive-globular-maps.html#6691" class="Bound">l1</a> <a id="6738" href="globular-types.lax-reflexive-globular-maps.html#6694" class="Bound">l2</a><a id="6740" class="Symbol">)</a> <a id="6742" class="Symbol">→</a>
  <a id="6746" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a> <a id="6783" href="globular-types.lax-reflexive-globular-maps.html#6707" class="Bound">G</a> <a id="6785" href="globular-types.lax-reflexive-globular-maps.html#6707" class="Bound">G</a>
<a id="6787" href="globular-types.lax-reflexive-globular-maps.html#6652" class="Function">map-id-lax-reflexive-globular-map</a> <a id="6821" href="globular-types.lax-reflexive-globular-maps.html#6821" class="Bound">G</a> <a id="6823" class="Symbol">=</a> <a id="6825" href="globular-types.globular-maps.html#3526" class="Function">id-globular-map</a> <a id="6841" class="Symbol">_</a>

<a id="is-lax-reflexive-id-lax-reflexive-globular-map"></a><a id="6844" href="globular-types.lax-reflexive-globular-maps.html#6844" class="Function">is-lax-reflexive-id-lax-reflexive-globular-map</a> <a id="6891" class="Symbol">:</a>
  <a id="6895" class="Symbol">{</a><a id="6896" href="globular-types.lax-reflexive-globular-maps.html#6896" class="Bound">l1</a> <a id="6899" href="globular-types.lax-reflexive-globular-maps.html#6899" class="Bound">l2</a> <a id="6902" class="Symbol">:</a> <a id="6904" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6909" class="Symbol">}</a> <a id="6911" class="Symbol">(</a><a id="6912" href="globular-types.lax-reflexive-globular-maps.html#6912" class="Bound">G</a> <a id="6914" class="Symbol">:</a> <a id="6916" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="6940" href="globular-types.lax-reflexive-globular-maps.html#6896" class="Bound">l1</a> <a id="6943" href="globular-types.lax-reflexive-globular-maps.html#6899" class="Bound">l2</a><a id="6945" class="Symbol">)</a> <a id="6947" class="Symbol">→</a>
  <a id="6951" href="globular-types.lax-reflexive-globular-maps.html#2288" class="Record">is-lax-reflexive-globular-map</a> <a id="6981" href="globular-types.lax-reflexive-globular-maps.html#6912" class="Bound">G</a> <a id="6983" href="globular-types.lax-reflexive-globular-maps.html#6912" class="Bound">G</a> <a id="6985" class="Symbol">(</a><a id="6986" href="globular-types.lax-reflexive-globular-maps.html#6652" class="Function">map-id-lax-reflexive-globular-map</a> <a id="7020" href="globular-types.lax-reflexive-globular-maps.html#6912" class="Bound">G</a><a id="7021" class="Symbol">)</a>
<a id="7023" href="globular-types.lax-reflexive-globular-maps.html#2530" class="Field">preserves-refl-1-cell-is-lax-reflexive-globular-map</a>
  <a id="7077" class="Symbol">(</a> <a id="7079" href="globular-types.lax-reflexive-globular-maps.html#6844" class="Function">is-lax-reflexive-id-lax-reflexive-globular-map</a> <a id="7126" href="globular-types.lax-reflexive-globular-maps.html#7126" class="Bound">G</a><a id="7127" class="Symbol">)</a>
  <a id="7131" href="globular-types.lax-reflexive-globular-maps.html#7131" class="Bound">x</a> <a id="7133" class="Symbol">=</a>
  <a id="7137" href="globular-types.reflexive-globular-types.html#5932" class="Function">refl-2-cell-Reflexive-Globular-Type</a> <a id="7173" href="globular-types.lax-reflexive-globular-maps.html#7126" class="Bound">G</a>
<a id="7175" href="globular-types.lax-reflexive-globular-maps.html#2809" class="Field">is-lax-reflexive-1-cell-globular-map-is-lax-reflexive-globular-map</a>
  <a id="7244" class="Symbol">(</a> <a id="7246" href="globular-types.lax-reflexive-globular-maps.html#6844" class="Function">is-lax-reflexive-id-lax-reflexive-globular-map</a> <a id="7293" href="globular-types.lax-reflexive-globular-maps.html#7293" class="Bound">G</a><a id="7294" class="Symbol">)</a> <a id="7296" class="Symbol">=</a>
  <a id="7300" href="globular-types.lax-reflexive-globular-maps.html#6844" class="Function">is-lax-reflexive-id-lax-reflexive-globular-map</a>
    <a id="7351" class="Symbol">(</a> <a id="7353" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="7408" href="globular-types.lax-reflexive-globular-maps.html#7293" class="Bound">G</a> <a id="7410" class="Symbol">_</a> <a id="7412" class="Symbol">_)</a>

<a id="id-lax-reflexive-globular-map"></a><a id="7416" href="globular-types.lax-reflexive-globular-maps.html#7416" class="Function">id-lax-reflexive-globular-map</a> <a id="7446" class="Symbol">:</a>
  <a id="7450" class="Symbol">{</a><a id="7451" href="globular-types.lax-reflexive-globular-maps.html#7451" class="Bound">l1</a> <a id="7454" href="globular-types.lax-reflexive-globular-maps.html#7454" class="Bound">l2</a> <a id="7457" class="Symbol">:</a> <a id="7459" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7464" class="Symbol">}</a> <a id="7466" class="Symbol">(</a><a id="7467" href="globular-types.lax-reflexive-globular-maps.html#7467" class="Bound">G</a> <a id="7469" class="Symbol">:</a> <a id="7471" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="7495" href="globular-types.lax-reflexive-globular-maps.html#7451" class="Bound">l1</a> <a id="7498" href="globular-types.lax-reflexive-globular-maps.html#7454" class="Bound">l2</a><a id="7500" class="Symbol">)</a> <a id="7502" class="Symbol">→</a>
  <a id="7506" href="globular-types.lax-reflexive-globular-maps.html#3279" class="Record">lax-reflexive-globular-map</a> <a id="7533" href="globular-types.lax-reflexive-globular-maps.html#7467" class="Bound">G</a> <a id="7535" href="globular-types.lax-reflexive-globular-maps.html#7467" class="Bound">G</a>
<a id="7537" href="globular-types.lax-reflexive-globular-maps.html#3462" class="Field">globular-map-lax-reflexive-globular-map</a>
  <a id="7579" class="Symbol">(</a> <a id="7581" href="globular-types.lax-reflexive-globular-maps.html#7416" class="Function">id-lax-reflexive-globular-map</a> <a id="7611" href="globular-types.lax-reflexive-globular-maps.html#7611" class="Bound">G</a><a id="7612" class="Symbol">)</a> <a id="7614" class="Symbol">=</a>
  <a id="7618" href="globular-types.lax-reflexive-globular-maps.html#6652" class="Function">map-id-lax-reflexive-globular-map</a> <a id="7652" href="globular-types.lax-reflexive-globular-maps.html#7611" class="Bound">G</a>
<a id="7654" href="globular-types.lax-reflexive-globular-maps.html#4633" class="Field">is-lax-reflexive-lax-reflexive-globular-map</a>
  <a id="7700" class="Symbol">(</a> <a id="7702" href="globular-types.lax-reflexive-globular-maps.html#7416" class="Function">id-lax-reflexive-globular-map</a> <a id="7732" href="globular-types.lax-reflexive-globular-maps.html#7732" class="Bound">G</a><a id="7733" class="Symbol">)</a> <a id="7735" class="Symbol">=</a>
  <a id="7739" class="Symbol">(</a> <a id="7741" href="globular-types.lax-reflexive-globular-maps.html#6844" class="Function">is-lax-reflexive-id-lax-reflexive-globular-map</a> <a id="7788" href="globular-types.lax-reflexive-globular-maps.html#7732" class="Bound">G</a><a id="7789" class="Symbol">)</a>
</pre>
## See also

- [Colax reflexive globular maps](globular-types.colax-reflexive-globular-maps.md)
- [Reflexive globular maps](globular-types.reflexive-globular-maps.md)
