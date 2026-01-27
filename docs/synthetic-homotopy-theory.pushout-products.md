# Pushout-products

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="synthetic-homotopy-theory.pushout-products.html" class="Module">synthetic-homotopy-theory.pushout-products</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="306" class="Keyword">open</a> <a id="311" class="Keyword">import</a> <a id="318" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="441" class="Keyword">open</a> <a id="446" class="Keyword">import</a> <a id="453" href="synthetic-homotopy-theory.cocones-under-spans.html" class="Module">synthetic-homotopy-theory.cocones-under-spans</a>
<a id="499" class="Keyword">open</a> <a id="504" class="Keyword">import</a> <a id="511" href="synthetic-homotopy-theory.pushouts.html" class="Module">synthetic-homotopy-theory.pushouts</a>
<a id="546" class="Keyword">open</a> <a id="551" class="Keyword">import</a> <a id="558" href="synthetic-homotopy-theory.universal-property-pushouts.html" class="Module">synthetic-homotopy-theory.universal-property-pushouts</a>
</pre>
</details>

## Idea

Consider two maps `f : A → X` and `g : B → Y`. The **pushout-product** `f □ g`
of `f` and `g` is defined as the
[cogap map](synthetic-homotopy-theory.pushouts.md) of the
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
              f × id
       A × B --------> X × B
         |               |
  id × g |      H ⇗      | id × g
         ∨               ∨
       A × Y --------> X × Y.
              f × id
```

In other words, the pushout-product is the unique map

```text
  f □ g : (X × B) ⊔_{A × B} (A × Y) → X × Y
```

equipped with [homotopies](foundation-core.homotopies.md)

```text
  K : (f □ g) ∘ inl ~ f × id
  L : (f □ g) ∘ inr ~ id × g
```

and a homotopy `M` witnessing that the
[square of homotopies](foundation.commuting-squares-of-homotopies.md)

```text
                                 K ·r (id × g)
       (f □ g) ∘ inl ∘ (id × g) ---------------> (f × id) ∘ (id × g)
                  |                                       |
  (f □ g) ·l glue |                                       | H
                  |                                       |
                  ∨                                       ∨
       (f □ g) ∘ inr ∘ (f × id) ---------------> (id × g) ∘ (f × id)
                                 L ·r (f × id)
```

commutes. The pushout-products is often called the **fiberwise join**, because
for each `(x , y) : X × Y` we have an
[equivalence](foundation-core.equivalences.md)

```text
  fiber (f □ g) (x , y) ≃ (fiber f x) * (fiber g y).
```

from the [fibers](foundation-core.fibers-of-maps.md) of `f □ g` to the
[join](synthetic-homotopy-theory.joins-of-types.md) of the fibers of `f` and
`g`.

There is an "adjoint relation" between the pushout-product and the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md): For any three
maps `f`, `g`, and `h` we have a [homotopy](foundation-core.homotopies.md)

```text
  ⟨f □ g , h⟩ ~ ⟨f , ⟨g , h⟩⟩.
```

## Definitions

### The pushout-product

<pre class="Agda"><a id="2616" class="Keyword">module</a> <a id="2623" href="synthetic-homotopy-theory.pushout-products.html#2623" class="Module">_</a>
  <a id="2627" class="Symbol">{</a><a id="2628" href="synthetic-homotopy-theory.pushout-products.html#2628" class="Bound">l1</a> <a id="2631" href="synthetic-homotopy-theory.pushout-products.html#2631" class="Bound">l2</a> <a id="2634" href="synthetic-homotopy-theory.pushout-products.html#2634" class="Bound">l3</a> <a id="2637" href="synthetic-homotopy-theory.pushout-products.html#2637" class="Bound">l4</a> <a id="2640" class="Symbol">:</a> <a id="2642" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2647" class="Symbol">}</a> <a id="2649" class="Symbol">{</a><a id="2650" href="synthetic-homotopy-theory.pushout-products.html#2650" class="Bound">A</a> <a id="2652" class="Symbol">:</a> <a id="2654" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2657" href="synthetic-homotopy-theory.pushout-products.html#2628" class="Bound">l1</a><a id="2659" class="Symbol">}</a> <a id="2661" class="Symbol">{</a><a id="2662" href="synthetic-homotopy-theory.pushout-products.html#2662" class="Bound">B</a> <a id="2664" class="Symbol">:</a> <a id="2666" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2669" href="synthetic-homotopy-theory.pushout-products.html#2631" class="Bound">l2</a><a id="2671" class="Symbol">}</a> <a id="2673" class="Symbol">{</a><a id="2674" href="synthetic-homotopy-theory.pushout-products.html#2674" class="Bound">X</a> <a id="2676" class="Symbol">:</a> <a id="2678" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2681" href="synthetic-homotopy-theory.pushout-products.html#2634" class="Bound">l3</a><a id="2683" class="Symbol">}</a> <a id="2685" class="Symbol">{</a><a id="2686" href="synthetic-homotopy-theory.pushout-products.html#2686" class="Bound">Y</a> <a id="2688" class="Symbol">:</a> <a id="2690" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2693" href="synthetic-homotopy-theory.pushout-products.html#2637" class="Bound">l4</a><a id="2695" class="Symbol">}</a>
  <a id="2699" class="Symbol">(</a><a id="2700" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="2702" class="Symbol">:</a> <a id="2704" href="synthetic-homotopy-theory.pushout-products.html#2650" class="Bound">A</a> <a id="2706" class="Symbol">→</a> <a id="2708" href="synthetic-homotopy-theory.pushout-products.html#2674" class="Bound">X</a><a id="2709" class="Symbol">)</a> <a id="2711" class="Symbol">(</a><a id="2712" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a> <a id="2714" class="Symbol">:</a> <a id="2716" href="synthetic-homotopy-theory.pushout-products.html#2662" class="Bound">B</a> <a id="2718" class="Symbol">→</a> <a id="2720" href="synthetic-homotopy-theory.pushout-products.html#2686" class="Bound">Y</a><a id="2721" class="Symbol">)</a>
  <a id="2725" class="Keyword">where</a>

  <a id="2734" href="synthetic-homotopy-theory.pushout-products.html#2734" class="Function">domain-pushout-product</a> <a id="2757" class="Symbol">:</a> <a id="2759" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2762" class="Symbol">(</a><a id="2763" href="synthetic-homotopy-theory.pushout-products.html#2628" class="Bound">l1</a> <a id="2766" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2768" href="synthetic-homotopy-theory.pushout-products.html#2631" class="Bound">l2</a> <a id="2771" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2773" href="synthetic-homotopy-theory.pushout-products.html#2634" class="Bound">l3</a> <a id="2776" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2778" href="synthetic-homotopy-theory.pushout-products.html#2637" class="Bound">l4</a><a id="2780" class="Symbol">)</a>
  <a id="2784" href="synthetic-homotopy-theory.pushout-products.html#2734" class="Function">domain-pushout-product</a> <a id="2807" class="Symbol">=</a>
    <a id="2813" href="synthetic-homotopy-theory.pushouts.html#2914" class="Postulate">pushout</a> <a id="2821" class="Symbol">(</a><a id="2822" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="2834" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2837" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="2838" class="Symbol">)</a> <a id="2840" class="Symbol">(</a><a id="2841" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="2853" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="2855" href="foundation-core.function-types.html#307" class="Function">id</a><a id="2857" class="Symbol">)</a>

  <a id="2862" href="synthetic-homotopy-theory.pushout-products.html#2862" class="Function">cocone-pushout-product</a> <a id="2885" class="Symbol">:</a> <a id="2887" href="synthetic-homotopy-theory.cocones-under-spans.html#1497" class="Function">cocone</a> <a id="2894" class="Symbol">(</a><a id="2895" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="2907" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2910" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="2911" class="Symbol">)</a> <a id="2913" class="Symbol">(</a><a id="2914" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="2926" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="2928" href="foundation-core.function-types.html#307" class="Function">id</a><a id="2930" class="Symbol">)</a> <a id="2932" class="Symbol">(</a><a id="2933" href="synthetic-homotopy-theory.pushout-products.html#2674" class="Bound">X</a> <a id="2935" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="2937" href="synthetic-homotopy-theory.pushout-products.html#2686" class="Bound">Y</a><a id="2938" class="Symbol">)</a>
  <a id="2942" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2946" href="synthetic-homotopy-theory.pushout-products.html#2862" class="Function">cocone-pushout-product</a> <a id="2969" class="Symbol">=</a> <a id="2971" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="2983" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="2985" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="2990" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2994" class="Symbol">(</a><a id="2995" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2999" href="synthetic-homotopy-theory.pushout-products.html#2862" class="Function">cocone-pushout-product</a><a id="3021" class="Symbol">)</a> <a id="3023" class="Symbol">=</a> <a id="3025" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3037" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="3040" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a>
  <a id="3044" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3048" class="Symbol">(</a><a id="3049" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3053" href="synthetic-homotopy-theory.pushout-products.html#2862" class="Function">cocone-pushout-product</a><a id="3075" class="Symbol">)</a> <a id="3077" class="Symbol">=</a> <a id="3079" href="foundation.functoriality-cartesian-product-types.html#2028" class="Function">coherence-square-map-product</a> <a id="3108" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="3110" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a>

  <a id="3115" class="Keyword">abstract</a>
    <a id="3128" href="synthetic-homotopy-theory.pushout-products.html#3128" class="Function">uniqueness-pushout-product</a> <a id="3155" class="Symbol">:</a>
      <a id="3163" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a>
        <a id="3180" class="Symbol">(</a> <a id="3182" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3184" class="Symbol">(</a> <a id="3186" href="synthetic-homotopy-theory.pushout-products.html#2734" class="Function">domain-pushout-product</a> <a id="3209" class="Symbol">→</a> <a id="3211" href="synthetic-homotopy-theory.pushout-products.html#2674" class="Bound">X</a> <a id="3213" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="3215" href="synthetic-homotopy-theory.pushout-products.html#2686" class="Bound">Y</a><a id="3216" class="Symbol">)</a>
            <a id="3230" class="Symbol">(</a> <a id="3232" class="Symbol">λ</a> <a id="3234" href="synthetic-homotopy-theory.pushout-products.html#3234" class="Bound">h</a> <a id="3236" class="Symbol">→</a>
              <a id="3252" href="synthetic-homotopy-theory.cocones-under-spans.html#2850" class="Function">htpy-cocone</a>
                <a id="3280" class="Symbol">(</a> <a id="3282" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3294" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="3297" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="3298" class="Symbol">)</a>
                <a id="3316" class="Symbol">(</a> <a id="3318" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3330" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="3332" href="foundation-core.function-types.html#307" class="Function">id</a><a id="3334" class="Symbol">)</a>
                <a id="3352" class="Symbol">(</a> <a id="3354" href="synthetic-homotopy-theory.cocones-under-spans.html#6059" class="Function">cocone-map</a>
                  <a id="3383" class="Symbol">(</a> <a id="3385" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3397" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="3400" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="3401" class="Symbol">)</a>
                  <a id="3421" class="Symbol">(</a> <a id="3423" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3435" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="3437" href="foundation-core.function-types.html#307" class="Function">id</a><a id="3439" class="Symbol">)</a>
                  <a id="3459" class="Symbol">(</a> <a id="3461" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a> <a id="3476" class="Symbol">(</a><a id="3477" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3489" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="3492" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="3493" class="Symbol">)</a> <a id="3495" class="Symbol">(</a><a id="3496" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3508" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="3510" href="foundation-core.function-types.html#307" class="Function">id</a><a id="3512" class="Symbol">))</a>
                  <a id="3533" class="Symbol">(</a> <a id="3535" href="synthetic-homotopy-theory.pushout-products.html#3234" class="Bound">h</a><a id="3536" class="Symbol">))</a>
                <a id="3555" class="Symbol">(</a> <a id="3557" href="synthetic-homotopy-theory.pushout-products.html#2862" class="Function">cocone-pushout-product</a><a id="3579" class="Symbol">)))</a>
    <a id="3587" href="synthetic-homotopy-theory.pushout-products.html#3128" class="Function">uniqueness-pushout-product</a> <a id="3614" class="Symbol">=</a>
      <a id="3622" href="synthetic-homotopy-theory.universal-property-pushouts.html#4862" class="Function">uniqueness-map-universal-property-pushout</a>
        <a id="3672" class="Symbol">(</a> <a id="3674" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3686" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="3689" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="3690" class="Symbol">)</a>
        <a id="3700" class="Symbol">(</a> <a id="3702" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3714" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="3716" href="foundation-core.function-types.html#307" class="Function">id</a><a id="3718" class="Symbol">)</a>
        <a id="3728" class="Symbol">(</a> <a id="3730" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a> <a id="3745" class="Symbol">(</a><a id="3746" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3758" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="3761" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="3762" class="Symbol">)</a> <a id="3764" class="Symbol">(</a><a id="3765" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3777" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="3779" href="foundation-core.function-types.html#307" class="Function">id</a><a id="3781" class="Symbol">))</a>
        <a id="3792" class="Symbol">(</a> <a id="3794" href="synthetic-homotopy-theory.pushouts.html#9291" class="Function">up-pushout</a> <a id="3805" class="Symbol">(</a><a id="3806" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3818" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="3821" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="3822" class="Symbol">)</a> <a id="3824" class="Symbol">(</a><a id="3825" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="3837" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="3839" href="foundation-core.function-types.html#307" class="Function">id</a><a id="3841" class="Symbol">))</a>
        <a id="3852" class="Symbol">(</a> <a id="3854" href="synthetic-homotopy-theory.pushout-products.html#2862" class="Function">cocone-pushout-product</a><a id="3876" class="Symbol">)</a>

  <a id="3881" class="Keyword">abstract</a>
    <a id="3894" href="synthetic-homotopy-theory.pushout-products.html#3894" class="Function">pushout-product</a> <a id="3910" class="Symbol">:</a> <a id="3912" href="synthetic-homotopy-theory.pushout-products.html#2734" class="Function">domain-pushout-product</a> <a id="3935" class="Symbol">→</a> <a id="3937" href="synthetic-homotopy-theory.pushout-products.html#2674" class="Bound">X</a> <a id="3939" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="3941" href="synthetic-homotopy-theory.pushout-products.html#2686" class="Bound">Y</a>
    <a id="3947" href="synthetic-homotopy-theory.pushout-products.html#3894" class="Function">pushout-product</a> <a id="3963" class="Symbol">=</a> <a id="3965" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3969" class="Symbol">(</a><a id="3970" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="3977" href="synthetic-homotopy-theory.pushout-products.html#3128" class="Function">uniqueness-pushout-product</a><a id="4003" class="Symbol">)</a>

    <a id="4010" href="synthetic-homotopy-theory.pushout-products.html#4010" class="Function">compute-inl-pushout-product</a> <a id="4038" class="Symbol">:</a>
      <a id="4046" href="synthetic-homotopy-theory.pushout-products.html#3894" class="Function">pushout-product</a> <a id="4062" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4064" href="synthetic-homotopy-theory.pushouts.html#3044" class="Postulate">inl-pushout</a> <a id="4076" class="Symbol">(</a><a id="4077" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4089" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="4092" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="4093" class="Symbol">)</a> <a id="4095" class="Symbol">(</a><a id="4096" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4108" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="4110" href="foundation-core.function-types.html#307" class="Function">id</a><a id="4112" class="Symbol">)</a> <a id="4114" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
      <a id="4122" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4134" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="4136" href="foundation-core.function-types.html#307" class="Function">id</a>
    <a id="4143" href="synthetic-homotopy-theory.pushout-products.html#4010" class="Function">compute-inl-pushout-product</a> <a id="4171" class="Symbol">=</a>
      <a id="4179" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4183" class="Symbol">(</a><a id="4184" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4188" class="Symbol">(</a><a id="4189" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="4196" href="synthetic-homotopy-theory.pushout-products.html#3128" class="Function">uniqueness-pushout-product</a><a id="4222" class="Symbol">))</a>

    <a id="4230" href="synthetic-homotopy-theory.pushout-products.html#4230" class="Function">compute-inr-pushout-product</a> <a id="4258" class="Symbol">:</a>
      <a id="4266" href="synthetic-homotopy-theory.pushout-products.html#3894" class="Function">pushout-product</a> <a id="4282" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4284" href="synthetic-homotopy-theory.pushouts.html#3176" class="Postulate">inr-pushout</a> <a id="4296" class="Symbol">(</a><a id="4297" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4309" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="4312" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="4313" class="Symbol">)</a> <a id="4315" class="Symbol">(</a><a id="4316" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4328" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="4330" href="foundation-core.function-types.html#307" class="Function">id</a><a id="4332" class="Symbol">)</a> <a id="4334" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
      <a id="4342" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4354" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="4357" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a>
    <a id="4363" href="synthetic-homotopy-theory.pushout-products.html#4230" class="Function">compute-inr-pushout-product</a> <a id="4391" class="Symbol">=</a>
      <a id="4399" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4403" class="Symbol">(</a><a id="4404" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4408" class="Symbol">(</a><a id="4409" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4413" class="Symbol">(</a><a id="4414" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="4421" href="synthetic-homotopy-theory.pushout-products.html#3128" class="Function">uniqueness-pushout-product</a><a id="4447" class="Symbol">)))</a>

    <a id="4456" href="synthetic-homotopy-theory.pushout-products.html#4456" class="Function">compute-glue-pushout-product</a> <a id="4485" class="Symbol">:</a>
      <a id="4493" href="synthetic-homotopy-theory.cocones-under-spans.html#2488" class="Function">statement-coherence-htpy-cocone</a>
        <a id="4533" class="Symbol">(</a> <a id="4535" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4547" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="4550" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="4551" class="Symbol">)</a>
        <a id="4561" class="Symbol">(</a> <a id="4563" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4575" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="4577" href="foundation-core.function-types.html#307" class="Function">id</a><a id="4579" class="Symbol">)</a>
        <a id="4589" class="Symbol">(</a> <a id="4591" href="synthetic-homotopy-theory.cocones-under-spans.html#6059" class="Function">cocone-map</a>
          <a id="4612" class="Symbol">(</a> <a id="4614" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4626" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="4629" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="4630" class="Symbol">)</a>
          <a id="4642" class="Symbol">(</a> <a id="4644" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4656" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="4658" href="foundation-core.function-types.html#307" class="Function">id</a><a id="4660" class="Symbol">)</a>
          <a id="4672" class="Symbol">(</a> <a id="4674" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a> <a id="4689" class="Symbol">(</a><a id="4690" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4702" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="4705" href="synthetic-homotopy-theory.pushout-products.html#2712" class="Bound">g</a><a id="4706" class="Symbol">)</a> <a id="4708" class="Symbol">(</a><a id="4709" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a> <a id="4721" href="synthetic-homotopy-theory.pushout-products.html#2700" class="Bound">f</a> <a id="4723" href="foundation-core.function-types.html#307" class="Function">id</a><a id="4725" class="Symbol">))</a>
          <a id="4738" class="Symbol">(</a> <a id="4740" href="synthetic-homotopy-theory.pushout-products.html#3894" class="Function">pushout-product</a><a id="4755" class="Symbol">))</a>
        <a id="4766" class="Symbol">(</a> <a id="4768" href="synthetic-homotopy-theory.pushout-products.html#2862" class="Function">cocone-pushout-product</a><a id="4790" class="Symbol">)</a>
        <a id="4800" class="Symbol">(</a> <a id="4802" href="synthetic-homotopy-theory.pushout-products.html#4010" class="Function">compute-inl-pushout-product</a><a id="4829" class="Symbol">)</a>
        <a id="4839" class="Symbol">(</a> <a id="4841" href="synthetic-homotopy-theory.pushout-products.html#4230" class="Function">compute-inr-pushout-product</a><a id="4868" class="Symbol">)</a>
    <a id="4874" href="synthetic-homotopy-theory.pushout-products.html#4456" class="Function">compute-glue-pushout-product</a> <a id="4903" class="Symbol">=</a>
      <a id="4911" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4915" class="Symbol">(</a><a id="4916" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4920" class="Symbol">(</a><a id="4921" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4925" class="Symbol">(</a><a id="4926" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="4933" href="synthetic-homotopy-theory.pushout-products.html#3128" class="Function">uniqueness-pushout-product</a><a id="4959" class="Symbol">)))</a>
</pre>
## See also

- [The dependent pushout-product](synthetic-homotopy-theory.dependent-pushout-products.md)

## External links

- [Pushout-product](https://ncatlab.org/nlab/show/pushout-product) at $n$lab

A wikidata identifier for this concept is not available.
