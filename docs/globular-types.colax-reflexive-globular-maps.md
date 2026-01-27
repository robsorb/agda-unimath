# Colax reflexive globular maps

<pre class="Agda"><a id="42" class="Symbol">{-#</a> <a id="46" class="Keyword">OPTIONS</a> <a id="54" class="Pragma">--guardedness</a> <a id="68" class="Symbol">#-}</a>

<a id="73" class="Keyword">module</a> <a id="80" href="globular-types.colax-reflexive-globular-maps.html" class="Module">globular-types.colax-reflexive-globular-maps</a> <a id="125" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="globular-types.globular-maps.html" class="Module">globular-types.globular-maps</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
</pre>
</details>

## Idea

A {{#concept "colax reflexive globular map" Agda=colax-reflexive-globular-map}}
between two
[reflexive globular types](globular-types.reflexive-globular-types.md) `G` and
`H` is a [globular map](globular-types.globular-maps.md) `f : G → H` equipped
with a family of 2-cells

```text
  (x : G₀) → H₂ (f₁ (refl G x)) (refl H (f₀ x))
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at
`f₀ x`, such that the globular map `f' : G' x y → H' (f₀ x) (f₀ y)` is again
colax reflexive.

### Lack of composition for colax reflexive globular maps

Note that the colax reflexive globular maps lack composition. For the
composition of `g` and `f` to exist, there should be a `2`-cell from
`g (f (refl G x))` to `refl K (g (f x))`, we need to compose the 2-cell that `g`
preserves reflexivity with the action of `g` on the 2-cell that `f` preserves
reflexivity. However, since the reflexive globular type `G` is not assumed to be
[transitive](globular-types.transitive-globular-types.md), it might lack such
instances of the compositions.

### Colax reflexive globular maps versus the morphisms of presheaves on the reflexive globe category

When reflexive globular types are viewed as type valued presheaves over the
reflexive globe category, the resulting notion of morphism is that of
[reflexive globular maps](globular-types.reflexive-globular-maps.md), which is
stricter than the notion of colax reflexive globular maps.

### Lax versus colax

The notion of
[lax reflexive globular map](globular-types.lax-reflexive-globular-maps.md) is
almost the same, except with the direction of the 2-cell reversed. In general,
the direction of lax coherence cells is determined by applying the morphism
componentwise first, and then the operations, while the direction of colax
coherence cells is determined by first applying the operations and then the
morphism.

## Definitions

### The predicate of colaxly preserving reflexivity

<pre class="Agda"><a id="2295" class="Keyword">record</a>
  <a id="is-colax-reflexive-globular-map"></a><a id="2304" href="globular-types.colax-reflexive-globular-maps.html#2304" class="Record">is-colax-reflexive-globular-map</a>
    <a id="2340" class="Symbol">{</a><a id="2341" href="globular-types.colax-reflexive-globular-maps.html#2341" class="Bound">l1</a> <a id="2344" href="globular-types.colax-reflexive-globular-maps.html#2344" class="Bound">l2</a> <a id="2347" href="globular-types.colax-reflexive-globular-maps.html#2347" class="Bound">l3</a> <a id="2350" href="globular-types.colax-reflexive-globular-maps.html#2350" class="Bound">l4</a> <a id="2353" class="Symbol">:</a> <a id="2355" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2360" class="Symbol">}</a>
    <a id="2366" class="Symbol">(</a><a id="2367" href="globular-types.colax-reflexive-globular-maps.html#2367" class="Bound">G</a> <a id="2369" class="Symbol">:</a> <a id="2371" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2395" href="globular-types.colax-reflexive-globular-maps.html#2341" class="Bound">l1</a> <a id="2398" href="globular-types.colax-reflexive-globular-maps.html#2344" class="Bound">l2</a><a id="2400" class="Symbol">)</a> <a id="2402" class="Symbol">(</a><a id="2403" href="globular-types.colax-reflexive-globular-maps.html#2403" class="Bound">H</a> <a id="2405" class="Symbol">:</a> <a id="2407" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2431" href="globular-types.colax-reflexive-globular-maps.html#2347" class="Bound">l3</a> <a id="2434" href="globular-types.colax-reflexive-globular-maps.html#2350" class="Bound">l4</a><a id="2436" class="Symbol">)</a>
    <a id="2442" class="Symbol">(</a><a id="2443" href="globular-types.colax-reflexive-globular-maps.html#2443" class="Bound">f</a> <a id="2445" class="Symbol">:</a> <a id="2447" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a> <a id="2484" href="globular-types.colax-reflexive-globular-maps.html#2367" class="Bound">G</a> <a id="2486" href="globular-types.colax-reflexive-globular-maps.html#2403" class="Bound">H</a><a id="2487" class="Symbol">)</a> <a id="2489" class="Symbol">:</a>
    <a id="2495" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2498" class="Symbol">(</a><a id="2499" href="globular-types.colax-reflexive-globular-maps.html#2341" class="Bound">l1</a> <a id="2502" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2504" href="globular-types.colax-reflexive-globular-maps.html#2344" class="Bound">l2</a> <a id="2507" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2509" href="globular-types.colax-reflexive-globular-maps.html#2350" class="Bound">l4</a><a id="2511" class="Symbol">)</a>
  <a id="2515" class="Keyword">where</a>
  <a id="2523" class="Keyword">coinductive</a>

  <a id="2538" class="Keyword">field</a>
    <a id="is-colax-reflexive-globular-map.preserves-refl-1-cell-is-colax-reflexive-globular-map"></a><a id="2548" href="globular-types.colax-reflexive-globular-maps.html#2548" class="Field">preserves-refl-1-cell-is-colax-reflexive-globular-map</a> <a id="2602" class="Symbol">:</a>
      <a id="2610" class="Symbol">(</a><a id="2611" href="globular-types.colax-reflexive-globular-maps.html#2611" class="Bound">x</a> <a id="2613" class="Symbol">:</a> <a id="2615" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="2646" href="globular-types.colax-reflexive-globular-maps.html#2367" class="Bound">G</a><a id="2647" class="Symbol">)</a> <a id="2649" class="Symbol">→</a>
      <a id="2657" href="globular-types.reflexive-globular-types.html#4480" class="Function">2-cell-Reflexive-Globular-Type</a> <a id="2688" href="globular-types.colax-reflexive-globular-maps.html#2403" class="Bound">H</a>
        <a id="2698" class="Symbol">(</a> <a id="2700" href="globular-types.globular-maps.html#1422" class="Function">1-cell-globular-map</a> <a id="2720" href="globular-types.colax-reflexive-globular-maps.html#2443" class="Bound">f</a> <a id="2722" class="Symbol">(</a><a id="2723" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="2759" href="globular-types.colax-reflexive-globular-maps.html#2367" class="Bound">G</a> <a id="2761" class="Symbol">{</a><a id="2762" href="globular-types.colax-reflexive-globular-maps.html#2611" class="Bound">x</a><a id="2763" class="Symbol">}))</a>
        <a id="2775" class="Symbol">(</a> <a id="2777" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="2813" href="globular-types.colax-reflexive-globular-maps.html#2403" class="Bound">H</a><a id="2814" class="Symbol">)</a>

  <a id="2819" class="Keyword">field</a>
    <a id="is-colax-reflexive-globular-map.is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map"></a><a id="2829" href="globular-types.colax-reflexive-globular-maps.html#2829" class="Field">is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map</a> <a id="2900" class="Symbol">:</a>
      <a id="2908" class="Symbol">{</a><a id="2909" href="globular-types.colax-reflexive-globular-maps.html#2909" class="Bound">x</a> <a id="2911" href="globular-types.colax-reflexive-globular-maps.html#2911" class="Bound">y</a> <a id="2913" class="Symbol">:</a> <a id="2915" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="2946" href="globular-types.colax-reflexive-globular-maps.html#2367" class="Bound">G</a><a id="2947" class="Symbol">}</a> <a id="2949" class="Symbol">→</a>
      <a id="2957" href="globular-types.colax-reflexive-globular-maps.html#2304" class="Record">is-colax-reflexive-globular-map</a>
        <a id="2997" class="Symbol">(</a> <a id="2999" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="3054" href="globular-types.colax-reflexive-globular-maps.html#2367" class="Bound">G</a> <a id="3056" href="globular-types.colax-reflexive-globular-maps.html#2909" class="Bound">x</a> <a id="3058" href="globular-types.colax-reflexive-globular-maps.html#2911" class="Bound">y</a><a id="3059" class="Symbol">)</a>
        <a id="3069" class="Symbol">(</a> <a id="3071" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="3126" href="globular-types.colax-reflexive-globular-maps.html#2403" class="Bound">H</a> <a id="3128" class="Symbol">_</a> <a id="3130" class="Symbol">_)</a>
        <a id="3141" class="Symbol">(</a> <a id="3143" href="globular-types.reflexive-globular-types.html#10984" class="Function">1-cell-globular-map-globular-map-Reflexive-Globular-Type</a> <a id="3200" href="globular-types.colax-reflexive-globular-maps.html#2367" class="Bound">G</a> <a id="3202" href="globular-types.colax-reflexive-globular-maps.html#2403" class="Bound">H</a> <a id="3204" href="globular-types.colax-reflexive-globular-maps.html#2443" class="Bound">f</a><a id="3205" class="Symbol">)</a>

<a id="3208" class="Keyword">open</a> <a id="3213" href="globular-types.colax-reflexive-globular-maps.html#2304" class="Module">is-colax-reflexive-globular-map</a> <a id="3245" class="Keyword">public</a>
</pre>
### Colax reflexive globular maps

<pre class="Agda"><a id="3300" class="Keyword">record</a>
  <a id="colax-reflexive-globular-map"></a><a id="3309" href="globular-types.colax-reflexive-globular-maps.html#3309" class="Record">colax-reflexive-globular-map</a>
    <a id="3342" class="Symbol">{</a><a id="3343" href="globular-types.colax-reflexive-globular-maps.html#3343" class="Bound">l1</a> <a id="3346" href="globular-types.colax-reflexive-globular-maps.html#3346" class="Bound">l2</a> <a id="3349" href="globular-types.colax-reflexive-globular-maps.html#3349" class="Bound">l3</a> <a id="3352" href="globular-types.colax-reflexive-globular-maps.html#3352" class="Bound">l4</a> <a id="3355" class="Symbol">:</a> <a id="3357" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3362" class="Symbol">}</a>
    <a id="3368" class="Symbol">(</a><a id="3369" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="3371" class="Symbol">:</a> <a id="3373" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="3397" href="globular-types.colax-reflexive-globular-maps.html#3343" class="Bound">l1</a> <a id="3400" href="globular-types.colax-reflexive-globular-maps.html#3346" class="Bound">l2</a><a id="3402" class="Symbol">)</a>
    <a id="3408" class="Symbol">(</a><a id="3409" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a> <a id="3411" class="Symbol">:</a> <a id="3413" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="3437" href="globular-types.colax-reflexive-globular-maps.html#3349" class="Bound">l3</a> <a id="3440" href="globular-types.colax-reflexive-globular-maps.html#3352" class="Bound">l4</a><a id="3442" class="Symbol">)</a> <a id="3444" class="Symbol">:</a>
    <a id="3450" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3453" class="Symbol">(</a><a id="3454" href="globular-types.colax-reflexive-globular-maps.html#3343" class="Bound">l1</a> <a id="3457" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3459" href="globular-types.colax-reflexive-globular-maps.html#3346" class="Bound">l2</a> <a id="3462" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3464" href="globular-types.colax-reflexive-globular-maps.html#3349" class="Bound">l3</a> <a id="3467" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3469" href="globular-types.colax-reflexive-globular-maps.html#3352" class="Bound">l4</a><a id="3471" class="Symbol">)</a>
  <a id="3475" class="Keyword">where</a>

  <a id="3484" class="Keyword">constructor</a>
    <a id="make-colax-reflexive-globular-map"></a><a id="3500" href="globular-types.colax-reflexive-globular-maps.html#3500" class="InductiveConstructor">make-colax-reflexive-globular-map</a>

  <a id="3537" class="Keyword">field</a>
    <a id="colax-reflexive-globular-map.globular-map-colax-reflexive-globular-map"></a><a id="3547" href="globular-types.colax-reflexive-globular-maps.html#3547" class="Field">globular-map-colax-reflexive-globular-map</a> <a id="3589" class="Symbol">:</a>
      <a id="3597" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a> <a id="3634" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="3636" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a>

  <a id="colax-reflexive-globular-map.0-cell-colax-reflexive-globular-map"></a><a id="3641" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="3677" class="Symbol">:</a>
    <a id="3683" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="3714" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="3716" class="Symbol">→</a> <a id="3718" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="3749" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a>
  <a id="3753" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="3789" class="Symbol">=</a>
    <a id="3795" href="globular-types.globular-maps.html#928" class="Field">0-cell-globular-map</a> <a id="3815" href="globular-types.colax-reflexive-globular-maps.html#3547" class="Field">globular-map-colax-reflexive-globular-map</a>

  <a id="colax-reflexive-globular-map.1-cell-colax-reflexive-globular-map"></a><a id="3860" href="globular-types.colax-reflexive-globular-maps.html#3860" class="Function">1-cell-colax-reflexive-globular-map</a> <a id="3896" class="Symbol">:</a>
    <a id="3902" class="Symbol">{</a><a id="3903" href="globular-types.colax-reflexive-globular-maps.html#3903" class="Bound">x</a> <a id="3905" href="globular-types.colax-reflexive-globular-maps.html#3905" class="Bound">y</a> <a id="3907" class="Symbol">:</a> <a id="3909" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="3940" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a><a id="3941" class="Symbol">}</a> <a id="3943" class="Symbol">→</a>
    <a id="3949" href="globular-types.reflexive-globular-types.html#4270" class="Function">1-cell-Reflexive-Globular-Type</a> <a id="3980" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="3982" href="globular-types.colax-reflexive-globular-maps.html#3903" class="Bound">x</a> <a id="3984" href="globular-types.colax-reflexive-globular-maps.html#3905" class="Bound">y</a> <a id="3986" class="Symbol">→</a>
    <a id="3992" href="globular-types.reflexive-globular-types.html#4270" class="Function">1-cell-Reflexive-Globular-Type</a> <a id="4023" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a>
      <a id="4031" class="Symbol">(</a> <a id="4033" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="4069" href="globular-types.colax-reflexive-globular-maps.html#3903" class="Bound">x</a><a id="4070" class="Symbol">)</a>
      <a id="4078" class="Symbol">(</a> <a id="4080" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="4116" href="globular-types.colax-reflexive-globular-maps.html#3905" class="Bound">y</a><a id="4117" class="Symbol">)</a>
  <a id="4121" href="globular-types.colax-reflexive-globular-maps.html#3860" class="Function">1-cell-colax-reflexive-globular-map</a> <a id="4157" class="Symbol">=</a>
    <a id="4163" href="globular-types.globular-maps.html#1422" class="Function">1-cell-globular-map</a> <a id="4183" href="globular-types.colax-reflexive-globular-maps.html#3547" class="Field">globular-map-colax-reflexive-globular-map</a>

  <a id="colax-reflexive-globular-map.1-cell-globular-map-colax-reflexive-globular-map"></a><a id="4228" href="globular-types.colax-reflexive-globular-maps.html#4228" class="Function">1-cell-globular-map-colax-reflexive-globular-map</a> <a id="4277" class="Symbol">:</a>
    <a id="4283" class="Symbol">{</a><a id="4284" href="globular-types.colax-reflexive-globular-maps.html#4284" class="Bound">x</a> <a id="4286" href="globular-types.colax-reflexive-globular-maps.html#4286" class="Bound">y</a> <a id="4288" class="Symbol">:</a> <a id="4290" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="4321" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a><a id="4322" class="Symbol">}</a> <a id="4324" class="Symbol">→</a>
    <a id="4330" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a>
      <a id="4373" class="Symbol">(</a> <a id="4375" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="4430" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="4432" href="globular-types.colax-reflexive-globular-maps.html#4284" class="Bound">x</a> <a id="4434" href="globular-types.colax-reflexive-globular-maps.html#4286" class="Bound">y</a><a id="4435" class="Symbol">)</a>
      <a id="4443" class="Symbol">(</a> <a id="4445" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="4500" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a>
        <a id="4510" class="Symbol">(</a> <a id="4512" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="4548" href="globular-types.colax-reflexive-globular-maps.html#4284" class="Bound">x</a><a id="4549" class="Symbol">)</a>
        <a id="4559" class="Symbol">(</a> <a id="4561" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="4597" href="globular-types.colax-reflexive-globular-maps.html#4286" class="Bound">y</a><a id="4598" class="Symbol">))</a>
  <a id="4603" href="globular-types.colax-reflexive-globular-maps.html#4228" class="Function">1-cell-globular-map-colax-reflexive-globular-map</a> <a id="4652" class="Symbol">=</a>
    <a id="4658" href="globular-types.globular-maps.html#1009" class="Field">1-cell-globular-map-globular-map</a> <a id="4691" href="globular-types.colax-reflexive-globular-maps.html#3547" class="Field">globular-map-colax-reflexive-globular-map</a>

  <a id="4736" class="Keyword">field</a>
    <a id="colax-reflexive-globular-map.is-colax-reflexive-colax-reflexive-globular-map"></a><a id="4746" href="globular-types.colax-reflexive-globular-maps.html#4746" class="Field">is-colax-reflexive-colax-reflexive-globular-map</a> <a id="4794" class="Symbol">:</a>
      <a id="4802" href="globular-types.colax-reflexive-globular-maps.html#2304" class="Record">is-colax-reflexive-globular-map</a> <a id="4834" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="4836" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a>
        <a id="4846" href="globular-types.colax-reflexive-globular-maps.html#3547" class="Field">globular-map-colax-reflexive-globular-map</a>

  <a id="colax-reflexive-globular-map.preserves-refl-1-cell-colax-reflexive-globular-map"></a><a id="4891" href="globular-types.colax-reflexive-globular-maps.html#4891" class="Function">preserves-refl-1-cell-colax-reflexive-globular-map</a> <a id="4942" class="Symbol">:</a>
    <a id="4948" class="Symbol">(</a> <a id="4950" href="globular-types.colax-reflexive-globular-maps.html#4950" class="Bound">x</a> <a id="4952" class="Symbol">:</a> <a id="4954" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="4985" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a><a id="4986" class="Symbol">)</a> <a id="4988" class="Symbol">→</a>
    <a id="4994" href="globular-types.reflexive-globular-types.html#4480" class="Function">2-cell-Reflexive-Globular-Type</a> <a id="5025" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a>
      <a id="5033" class="Symbol">(</a> <a id="5035" href="globular-types.colax-reflexive-globular-maps.html#3860" class="Function">1-cell-colax-reflexive-globular-map</a>
        <a id="5079" class="Symbol">(</a> <a id="5081" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="5117" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="5119" class="Symbol">{</a><a id="5120" href="globular-types.colax-reflexive-globular-maps.html#4950" class="Bound">x</a><a id="5121" class="Symbol">}))</a>
      <a id="5131" class="Symbol">(</a> <a id="5133" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="5169" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a><a id="5170" class="Symbol">)</a>
  <a id="5174" href="globular-types.colax-reflexive-globular-maps.html#4891" class="Function">preserves-refl-1-cell-colax-reflexive-globular-map</a> <a id="5225" class="Symbol">=</a>
    <a id="5231" href="globular-types.colax-reflexive-globular-maps.html#2548" class="Field">preserves-refl-1-cell-is-colax-reflexive-globular-map</a>
      <a id="5291" href="globular-types.colax-reflexive-globular-maps.html#4746" class="Field">is-colax-reflexive-colax-reflexive-globular-map</a>

  <a id="colax-reflexive-globular-map.is-colax-reflexive-2-cell-globular-map-is-colax-reflexive-globular-map"></a><a id="5342" href="globular-types.colax-reflexive-globular-maps.html#5342" class="Function">is-colax-reflexive-2-cell-globular-map-is-colax-reflexive-globular-map</a> <a id="5413" class="Symbol">:</a>
    <a id="5419" class="Symbol">{</a> <a id="5421" href="globular-types.colax-reflexive-globular-maps.html#5421" class="Bound">x</a> <a id="5423" href="globular-types.colax-reflexive-globular-maps.html#5423" class="Bound">y</a> <a id="5425" class="Symbol">:</a> <a id="5427" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="5458" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a><a id="5459" class="Symbol">}</a> <a id="5461" class="Symbol">→</a>
    <a id="5467" href="globular-types.colax-reflexive-globular-maps.html#2304" class="Record">is-colax-reflexive-globular-map</a>
      <a id="5505" class="Symbol">(</a> <a id="5507" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="5562" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="5564" href="globular-types.colax-reflexive-globular-maps.html#5421" class="Bound">x</a> <a id="5566" href="globular-types.colax-reflexive-globular-maps.html#5423" class="Bound">y</a><a id="5567" class="Symbol">)</a>
      <a id="5575" class="Symbol">(</a> <a id="5577" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="5632" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a>
        <a id="5642" class="Symbol">(</a> <a id="5644" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="5680" href="globular-types.colax-reflexive-globular-maps.html#5421" class="Bound">x</a><a id="5681" class="Symbol">)</a>
        <a id="5691" class="Symbol">(</a> <a id="5693" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="5729" href="globular-types.colax-reflexive-globular-maps.html#5423" class="Bound">y</a><a id="5730" class="Symbol">))</a>
      <a id="5739" class="Symbol">(</a> <a id="5741" href="globular-types.colax-reflexive-globular-maps.html#4228" class="Function">1-cell-globular-map-colax-reflexive-globular-map</a><a id="5789" class="Symbol">)</a>
  <a id="5793" href="globular-types.colax-reflexive-globular-maps.html#5342" class="Function">is-colax-reflexive-2-cell-globular-map-is-colax-reflexive-globular-map</a> <a id="5864" class="Symbol">=</a>
    <a id="5870" href="globular-types.colax-reflexive-globular-maps.html#2829" class="Field">is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map</a>
      <a id="5947" href="globular-types.colax-reflexive-globular-maps.html#4746" class="Field">is-colax-reflexive-colax-reflexive-globular-map</a>

  <a id="colax-reflexive-globular-map.1-cell-colax-reflexive-globular-map-colax-reflexive-globular-map"></a><a id="5998" href="globular-types.colax-reflexive-globular-maps.html#5998" class="Function">1-cell-colax-reflexive-globular-map-colax-reflexive-globular-map</a> <a id="6063" class="Symbol">:</a>
    <a id="6069" class="Symbol">{</a><a id="6070" href="globular-types.colax-reflexive-globular-maps.html#6070" class="Bound">x</a> <a id="6072" href="globular-types.colax-reflexive-globular-maps.html#6072" class="Bound">y</a> <a id="6074" class="Symbol">:</a> <a id="6076" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="6107" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a><a id="6108" class="Symbol">}</a> <a id="6110" class="Symbol">→</a>
    <a id="6116" href="globular-types.colax-reflexive-globular-maps.html#3309" class="Record">colax-reflexive-globular-map</a>
      <a id="6151" class="Symbol">(</a> <a id="6153" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="6208" href="globular-types.colax-reflexive-globular-maps.html#3369" class="Bound">G</a> <a id="6210" href="globular-types.colax-reflexive-globular-maps.html#6070" class="Bound">x</a> <a id="6212" href="globular-types.colax-reflexive-globular-maps.html#6072" class="Bound">y</a><a id="6213" class="Symbol">)</a>
      <a id="6221" class="Symbol">(</a> <a id="6223" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="6278" href="globular-types.colax-reflexive-globular-maps.html#3409" class="Bound">H</a>
        <a id="6288" class="Symbol">(</a> <a id="6290" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="6326" href="globular-types.colax-reflexive-globular-maps.html#6070" class="Bound">x</a><a id="6327" class="Symbol">)</a>
        <a id="6337" class="Symbol">(</a> <a id="6339" href="globular-types.colax-reflexive-globular-maps.html#3641" class="Function">0-cell-colax-reflexive-globular-map</a> <a id="6375" href="globular-types.colax-reflexive-globular-maps.html#6072" class="Bound">y</a><a id="6376" class="Symbol">))</a>
  <a id="6381" href="globular-types.colax-reflexive-globular-maps.html#3547" class="Field">globular-map-colax-reflexive-globular-map</a>
    <a id="6427" href="globular-types.colax-reflexive-globular-maps.html#5998" class="Function">1-cell-colax-reflexive-globular-map-colax-reflexive-globular-map</a> <a id="6492" class="Symbol">=</a>
    <a id="6498" href="globular-types.colax-reflexive-globular-maps.html#4228" class="Function">1-cell-globular-map-colax-reflexive-globular-map</a>
  <a id="6549" href="globular-types.colax-reflexive-globular-maps.html#4746" class="Field">is-colax-reflexive-colax-reflexive-globular-map</a>
    <a id="6601" href="globular-types.colax-reflexive-globular-maps.html#5998" class="Function">1-cell-colax-reflexive-globular-map-colax-reflexive-globular-map</a> <a id="6666" class="Symbol">=</a>
    <a id="6672" href="globular-types.colax-reflexive-globular-maps.html#5342" class="Function">is-colax-reflexive-2-cell-globular-map-is-colax-reflexive-globular-map</a>

<a id="6744" class="Keyword">open</a> <a id="6749" href="globular-types.colax-reflexive-globular-maps.html#3309" class="Module">colax-reflexive-globular-map</a> <a id="6778" class="Keyword">public</a>
</pre>
### The identity colax reflexive globular map

<pre class="Agda"><a id="map-id-colax-reflexive-globular-map"></a><a id="6845" href="globular-types.colax-reflexive-globular-maps.html#6845" class="Function">map-id-colax-reflexive-globular-map</a> <a id="6881" class="Symbol">:</a>
  <a id="6885" class="Symbol">{</a><a id="6886" href="globular-types.colax-reflexive-globular-maps.html#6886" class="Bound">l1</a> <a id="6889" href="globular-types.colax-reflexive-globular-maps.html#6889" class="Bound">l2</a> <a id="6892" class="Symbol">:</a> <a id="6894" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6899" class="Symbol">}</a> <a id="6901" class="Symbol">(</a><a id="6902" href="globular-types.colax-reflexive-globular-maps.html#6902" class="Bound">G</a> <a id="6904" class="Symbol">:</a> <a id="6906" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="6930" href="globular-types.colax-reflexive-globular-maps.html#6886" class="Bound">l1</a> <a id="6933" href="globular-types.colax-reflexive-globular-maps.html#6889" class="Bound">l2</a><a id="6935" class="Symbol">)</a> <a id="6937" class="Symbol">→</a>
  <a id="6941" href="globular-types.reflexive-globular-types.html#10403" class="Function">globular-map-Reflexive-Globular-Type</a> <a id="6978" href="globular-types.colax-reflexive-globular-maps.html#6902" class="Bound">G</a> <a id="6980" href="globular-types.colax-reflexive-globular-maps.html#6902" class="Bound">G</a>
<a id="6982" href="globular-types.colax-reflexive-globular-maps.html#6845" class="Function">map-id-colax-reflexive-globular-map</a> <a id="7018" href="globular-types.colax-reflexive-globular-maps.html#7018" class="Bound">G</a> <a id="7020" class="Symbol">=</a> <a id="7022" href="globular-types.globular-maps.html#3526" class="Function">id-globular-map</a> <a id="7038" class="Symbol">_</a>

<a id="is-colax-reflexive-id-colax-reflexive-globular-map"></a><a id="7041" href="globular-types.colax-reflexive-globular-maps.html#7041" class="Function">is-colax-reflexive-id-colax-reflexive-globular-map</a> <a id="7092" class="Symbol">:</a>
  <a id="7096" class="Symbol">{</a><a id="7097" href="globular-types.colax-reflexive-globular-maps.html#7097" class="Bound">l1</a> <a id="7100" href="globular-types.colax-reflexive-globular-maps.html#7100" class="Bound">l2</a> <a id="7103" class="Symbol">:</a> <a id="7105" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7110" class="Symbol">}</a> <a id="7112" class="Symbol">(</a><a id="7113" href="globular-types.colax-reflexive-globular-maps.html#7113" class="Bound">G</a> <a id="7115" class="Symbol">:</a> <a id="7117" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="7141" href="globular-types.colax-reflexive-globular-maps.html#7097" class="Bound">l1</a> <a id="7144" href="globular-types.colax-reflexive-globular-maps.html#7100" class="Bound">l2</a><a id="7146" class="Symbol">)</a> <a id="7148" class="Symbol">→</a>
  <a id="7152" href="globular-types.colax-reflexive-globular-maps.html#2304" class="Record">is-colax-reflexive-globular-map</a> <a id="7184" href="globular-types.colax-reflexive-globular-maps.html#7113" class="Bound">G</a> <a id="7186" href="globular-types.colax-reflexive-globular-maps.html#7113" class="Bound">G</a>
    <a id="7192" class="Symbol">(</a> <a id="7194" href="globular-types.colax-reflexive-globular-maps.html#6845" class="Function">map-id-colax-reflexive-globular-map</a> <a id="7230" href="globular-types.colax-reflexive-globular-maps.html#7113" class="Bound">G</a><a id="7231" class="Symbol">)</a>
<a id="7233" href="globular-types.colax-reflexive-globular-maps.html#2548" class="Field">preserves-refl-1-cell-is-colax-reflexive-globular-map</a>
  <a id="7289" class="Symbol">(</a> <a id="7291" href="globular-types.colax-reflexive-globular-maps.html#7041" class="Function">is-colax-reflexive-id-colax-reflexive-globular-map</a> <a id="7342" href="globular-types.colax-reflexive-globular-maps.html#7342" class="Bound">G</a><a id="7343" class="Symbol">)</a>
  <a id="7347" href="globular-types.colax-reflexive-globular-maps.html#7347" class="Bound">x</a> <a id="7349" class="Symbol">=</a>
  <a id="7353" href="globular-types.reflexive-globular-types.html#5932" class="Function">refl-2-cell-Reflexive-Globular-Type</a> <a id="7389" href="globular-types.colax-reflexive-globular-maps.html#7342" class="Bound">G</a>
<a id="7391" href="globular-types.colax-reflexive-globular-maps.html#2829" class="Field">is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map</a>
  <a id="7464" class="Symbol">(</a> <a id="7466" href="globular-types.colax-reflexive-globular-maps.html#7041" class="Function">is-colax-reflexive-id-colax-reflexive-globular-map</a> <a id="7517" href="globular-types.colax-reflexive-globular-maps.html#7517" class="Bound">G</a><a id="7518" class="Symbol">)</a> <a id="7520" class="Symbol">=</a>
  <a id="7524" href="globular-types.colax-reflexive-globular-maps.html#7041" class="Function">is-colax-reflexive-id-colax-reflexive-globular-map</a>
    <a id="7579" class="Symbol">(</a> <a id="7581" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="7636" href="globular-types.colax-reflexive-globular-maps.html#7517" class="Bound">G</a> <a id="7638" class="Symbol">_</a> <a id="7640" class="Symbol">_)</a>

<a id="id-colax-reflexive-globular-map"></a><a id="7644" href="globular-types.colax-reflexive-globular-maps.html#7644" class="Function">id-colax-reflexive-globular-map</a> <a id="7676" class="Symbol">:</a>
  <a id="7680" class="Symbol">{</a><a id="7681" href="globular-types.colax-reflexive-globular-maps.html#7681" class="Bound">l1</a> <a id="7684" href="globular-types.colax-reflexive-globular-maps.html#7684" class="Bound">l2</a> <a id="7687" class="Symbol">:</a> <a id="7689" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7694" class="Symbol">}</a> <a id="7696" class="Symbol">(</a><a id="7697" href="globular-types.colax-reflexive-globular-maps.html#7697" class="Bound">G</a> <a id="7699" class="Symbol">:</a> <a id="7701" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="7725" href="globular-types.colax-reflexive-globular-maps.html#7681" class="Bound">l1</a> <a id="7728" href="globular-types.colax-reflexive-globular-maps.html#7684" class="Bound">l2</a><a id="7730" class="Symbol">)</a> <a id="7732" class="Symbol">→</a>
  <a id="7736" href="globular-types.colax-reflexive-globular-maps.html#3309" class="Record">colax-reflexive-globular-map</a> <a id="7765" href="globular-types.colax-reflexive-globular-maps.html#7697" class="Bound">G</a> <a id="7767" href="globular-types.colax-reflexive-globular-maps.html#7697" class="Bound">G</a>
<a id="7769" href="globular-types.colax-reflexive-globular-maps.html#3547" class="Field">globular-map-colax-reflexive-globular-map</a>
  <a id="7813" class="Symbol">(</a> <a id="7815" href="globular-types.colax-reflexive-globular-maps.html#7644" class="Function">id-colax-reflexive-globular-map</a> <a id="7847" href="globular-types.colax-reflexive-globular-maps.html#7847" class="Bound">G</a><a id="7848" class="Symbol">)</a> <a id="7850" class="Symbol">=</a>
  <a id="7854" href="globular-types.colax-reflexive-globular-maps.html#6845" class="Function">map-id-colax-reflexive-globular-map</a> <a id="7890" href="globular-types.colax-reflexive-globular-maps.html#7847" class="Bound">G</a>
<a id="7892" href="globular-types.colax-reflexive-globular-maps.html#4746" class="Field">is-colax-reflexive-colax-reflexive-globular-map</a>
  <a id="7942" class="Symbol">(</a> <a id="7944" href="globular-types.colax-reflexive-globular-maps.html#7644" class="Function">id-colax-reflexive-globular-map</a> <a id="7976" href="globular-types.colax-reflexive-globular-maps.html#7976" class="Bound">G</a><a id="7977" class="Symbol">)</a> <a id="7979" class="Symbol">=</a>
  <a id="7983" class="Symbol">(</a> <a id="7985" href="globular-types.colax-reflexive-globular-maps.html#7041" class="Function">is-colax-reflexive-id-colax-reflexive-globular-map</a> <a id="8036" href="globular-types.colax-reflexive-globular-maps.html#7976" class="Bound">G</a><a id="8037" class="Symbol">)</a>
</pre>
## See also

- [Lax reflexive globular maps](globular-types.lax-reflexive-globular-maps.md)
- [Reflexive globular maps](globular-types.reflexive-globular-maps.md)
