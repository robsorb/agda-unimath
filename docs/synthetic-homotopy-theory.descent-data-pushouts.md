# Descent data for pushouts

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="synthetic-homotopy-theory.descent-data-pushouts.html" class="Module">synthetic-homotopy-theory.descent-data-pushouts</a> <a id="93" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="276" class="Keyword">open</a> <a id="281" class="Keyword">import</a> <a id="288" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="406" class="Keyword">open</a> <a id="411" class="Keyword">import</a> <a id="418" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="446" class="Keyword">open</a> <a id="451" class="Keyword">import</a> <a id="458" href="synthetic-homotopy-theory.cocones-under-spans.html" class="Module">synthetic-homotopy-theory.cocones-under-spans</a>
</pre>
</details>

## Idea

{{#concept "Descent data" Disambiguation="pushouts" Agda=descent-data-pushout WDID=NA}}
for the [pushout](synthetic-homotopy-theory.universal-property-pushouts.md) of a
[span diagram](foundation.span-diagrams.md) `𝒮`

```text
     f     g
  A <-- S --> B
```

is a triple `(PA, PB, PS)`, where `PA : A → 𝒰` is a type family over `A`,
`PB : B → 𝒰` is a type family over `B`, and `PS` is a family of
[equivalences](foundation-core.equivalences.md)

```text
  PS : (s : S) → PA (f a) ≃ PB (g a).
```

In
[`descent-property-pushouts`](synthetic-homotopy-theory.descent-property-pushouts.md),
we show that this is exactly the data one needs to "glue together" a type family
`P : X → 𝒰` over the pushout `X` of `𝒮`.

The [identity type](foundation-core.identity-types.md) of descent data is
characterized in
[`equivalences-descent-data-pushouts`](synthetic-homotopy-theory.equivalences-descent-data-pushouts.md).

It may not be immediately clear why "descent data" is an appropriate name for
this concept, because there is no apparent downward motion. Traditionally,
descent is studied in the context of a collection of objects `Xᵢ` covering a
single object `X`, and local structure on the individual `Xᵢ`'s descending onto
`X`, collecting into a global structure, given that the pieces are appropriately
compatible on any "overlaps". A pushout of `𝒮` is covered by `A` and `B`, and
the overlaps are encoded in `f` and `g`. Then structure on `A` and `B`,
expressed as type families `PA` and `PB`, "descends" to a structure on `X` (a
type family over `X`). Two elements "overlap" in `X` if there is an
identification between them coming from `S`, and the gluing/compatibility
condition exactly requires the local structure of `PA` and `PB` to agree on such
elements, i.e. asks for an equivalence `PA(fs) ≃ PB(gs)`.

## Definitions

### Descent data for pushouts

<pre class="Agda"><a id="2394" class="Keyword">module</a> <a id="2401" href="synthetic-homotopy-theory.descent-data-pushouts.html#2401" class="Module">_</a>
  <a id="2405" class="Symbol">{</a><a id="2406" href="synthetic-homotopy-theory.descent-data-pushouts.html#2406" class="Bound">l1</a> <a id="2409" href="synthetic-homotopy-theory.descent-data-pushouts.html#2409" class="Bound">l2</a> <a id="2412" href="synthetic-homotopy-theory.descent-data-pushouts.html#2412" class="Bound">l3</a> <a id="2415" class="Symbol">:</a> <a id="2417" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2422" class="Symbol">}</a> <a id="2424" class="Symbol">(</a><a id="2425" href="synthetic-homotopy-theory.descent-data-pushouts.html#2425" class="Bound">𝒮</a> <a id="2427" class="Symbol">:</a> <a id="2429" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2442" href="synthetic-homotopy-theory.descent-data-pushouts.html#2406" class="Bound">l1</a> <a id="2445" href="synthetic-homotopy-theory.descent-data-pushouts.html#2409" class="Bound">l2</a> <a id="2448" href="synthetic-homotopy-theory.descent-data-pushouts.html#2412" class="Bound">l3</a><a id="2450" class="Symbol">)</a>
  <a id="2454" class="Keyword">where</a>

  <a id="2463" href="synthetic-homotopy-theory.descent-data-pushouts.html#2463" class="Function">descent-data-pushout</a> <a id="2484" class="Symbol">:</a> <a id="2486" class="Symbol">(</a><a id="2487" href="synthetic-homotopy-theory.descent-data-pushouts.html#2487" class="Bound">l4</a> <a id="2490" href="synthetic-homotopy-theory.descent-data-pushouts.html#2490" class="Bound">l5</a> <a id="2493" class="Symbol">:</a> <a id="2495" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2500" class="Symbol">)</a> <a id="2502" class="Symbol">→</a> <a id="2504" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2507" class="Symbol">(</a><a id="2508" href="synthetic-homotopy-theory.descent-data-pushouts.html#2406" class="Bound">l1</a> <a id="2511" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2513" href="synthetic-homotopy-theory.descent-data-pushouts.html#2409" class="Bound">l2</a> <a id="2516" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2518" href="synthetic-homotopy-theory.descent-data-pushouts.html#2412" class="Bound">l3</a> <a id="2521" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2523" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2528" href="synthetic-homotopy-theory.descent-data-pushouts.html#2487" class="Bound">l4</a> <a id="2531" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2533" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2538" href="synthetic-homotopy-theory.descent-data-pushouts.html#2490" class="Bound">l5</a><a id="2540" class="Symbol">)</a>
  <a id="2544" href="synthetic-homotopy-theory.descent-data-pushouts.html#2463" class="Function">descent-data-pushout</a> <a id="2565" href="synthetic-homotopy-theory.descent-data-pushouts.html#2565" class="Bound">l4</a> <a id="2568" href="synthetic-homotopy-theory.descent-data-pushouts.html#2568" class="Bound">l5</a> <a id="2571" class="Symbol">=</a>
    <a id="2577" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2579" class="Symbol">(</a> <a id="2581" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="2601" href="synthetic-homotopy-theory.descent-data-pushouts.html#2425" class="Bound">𝒮</a> <a id="2603" class="Symbol">→</a> <a id="2605" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2608" href="synthetic-homotopy-theory.descent-data-pushouts.html#2565" class="Bound">l4</a><a id="2610" class="Symbol">)</a>
      <a id="2618" class="Symbol">(</a> <a id="2620" class="Symbol">λ</a> <a id="2622" href="synthetic-homotopy-theory.descent-data-pushouts.html#2622" class="Bound">PA</a> <a id="2625" class="Symbol">→</a>
        <a id="2635" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2637" class="Symbol">(</a> <a id="2639" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="2661" href="synthetic-homotopy-theory.descent-data-pushouts.html#2425" class="Bound">𝒮</a> <a id="2663" class="Symbol">→</a> <a id="2665" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2668" href="synthetic-homotopy-theory.descent-data-pushouts.html#2568" class="Bound">l5</a><a id="2670" class="Symbol">)</a>
          <a id="2682" class="Symbol">(</a> <a id="2684" class="Symbol">λ</a> <a id="2686" href="synthetic-homotopy-theory.descent-data-pushouts.html#2686" class="Bound">PB</a> <a id="2689" class="Symbol">→</a>
            <a id="2703" class="Symbol">(</a><a id="2704" href="synthetic-homotopy-theory.descent-data-pushouts.html#2704" class="Bound">s</a> <a id="2706" class="Symbol">:</a> <a id="2708" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="2735" href="synthetic-homotopy-theory.descent-data-pushouts.html#2425" class="Bound">𝒮</a><a id="2736" class="Symbol">)</a> <a id="2738" class="Symbol">→</a>
            <a id="2752" href="synthetic-homotopy-theory.descent-data-pushouts.html#2622" class="Bound">PA</a> <a id="2755" class="Symbol">(</a><a id="2756" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="2778" href="synthetic-homotopy-theory.descent-data-pushouts.html#2425" class="Bound">𝒮</a> <a id="2780" href="synthetic-homotopy-theory.descent-data-pushouts.html#2704" class="Bound">s</a><a id="2781" class="Symbol">)</a> <a id="2783" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2785" href="synthetic-homotopy-theory.descent-data-pushouts.html#2686" class="Bound">PB</a> <a id="2788" class="Symbol">(</a><a id="2789" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="2812" href="synthetic-homotopy-theory.descent-data-pushouts.html#2425" class="Bound">𝒮</a> <a id="2814" href="synthetic-homotopy-theory.descent-data-pushouts.html#2704" class="Bound">s</a><a id="2815" class="Symbol">)))</a>
</pre>
### Components of descent data for pushouts

<pre class="Agda"><a id="2877" class="Keyword">module</a> <a id="2884" href="synthetic-homotopy-theory.descent-data-pushouts.html#2884" class="Module">_</a>
  <a id="2888" class="Symbol">{</a><a id="2889" href="synthetic-homotopy-theory.descent-data-pushouts.html#2889" class="Bound">l1</a> <a id="2892" href="synthetic-homotopy-theory.descent-data-pushouts.html#2892" class="Bound">l2</a> <a id="2895" href="synthetic-homotopy-theory.descent-data-pushouts.html#2895" class="Bound">l3</a> <a id="2898" href="synthetic-homotopy-theory.descent-data-pushouts.html#2898" class="Bound">l4</a> <a id="2901" href="synthetic-homotopy-theory.descent-data-pushouts.html#2901" class="Bound">l5</a> <a id="2904" class="Symbol">:</a> <a id="2906" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2911" class="Symbol">}</a> <a id="2913" class="Symbol">{</a><a id="2914" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="2916" class="Symbol">:</a> <a id="2918" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2931" href="synthetic-homotopy-theory.descent-data-pushouts.html#2889" class="Bound">l1</a> <a id="2934" href="synthetic-homotopy-theory.descent-data-pushouts.html#2892" class="Bound">l2</a> <a id="2937" href="synthetic-homotopy-theory.descent-data-pushouts.html#2895" class="Bound">l3</a><a id="2939" class="Symbol">}</a>
  <a id="2943" class="Symbol">(</a><a id="2944" href="synthetic-homotopy-theory.descent-data-pushouts.html#2944" class="Bound">P</a> <a id="2946" class="Symbol">:</a> <a id="2948" href="synthetic-homotopy-theory.descent-data-pushouts.html#2463" class="Function">descent-data-pushout</a> <a id="2969" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="2971" href="synthetic-homotopy-theory.descent-data-pushouts.html#2898" class="Bound">l4</a> <a id="2974" href="synthetic-homotopy-theory.descent-data-pushouts.html#2901" class="Bound">l5</a><a id="2976" class="Symbol">)</a>
  <a id="2980" class="Keyword">where</a>

  <a id="2989" href="synthetic-homotopy-theory.descent-data-pushouts.html#2989" class="Function">left-family-descent-data-pushout</a> <a id="3022" class="Symbol">:</a> <a id="3024" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="3044" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="3046" class="Symbol">→</a> <a id="3048" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3051" href="synthetic-homotopy-theory.descent-data-pushouts.html#2898" class="Bound">l4</a>
  <a id="3056" href="synthetic-homotopy-theory.descent-data-pushouts.html#2989" class="Function">left-family-descent-data-pushout</a> <a id="3089" class="Symbol">=</a> <a id="3091" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3095" href="synthetic-homotopy-theory.descent-data-pushouts.html#2944" class="Bound">P</a>

  <a id="3100" href="synthetic-homotopy-theory.descent-data-pushouts.html#3100" class="Function">right-family-descent-data-pushout</a> <a id="3134" class="Symbol">:</a> <a id="3136" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="3158" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="3160" class="Symbol">→</a> <a id="3162" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3165" href="synthetic-homotopy-theory.descent-data-pushouts.html#2901" class="Bound">l5</a>
  <a id="3170" href="synthetic-homotopy-theory.descent-data-pushouts.html#3100" class="Function">right-family-descent-data-pushout</a> <a id="3204" class="Symbol">=</a> <a id="3206" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3210" class="Symbol">(</a><a id="3211" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3215" href="synthetic-homotopy-theory.descent-data-pushouts.html#2944" class="Bound">P</a><a id="3216" class="Symbol">)</a>

  <a id="3221" href="synthetic-homotopy-theory.descent-data-pushouts.html#3221" class="Function">equiv-family-descent-data-pushout</a> <a id="3255" class="Symbol">:</a>
    <a id="3261" class="Symbol">(</a><a id="3262" href="synthetic-homotopy-theory.descent-data-pushouts.html#3262" class="Bound">s</a> <a id="3264" class="Symbol">:</a> <a id="3266" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="3293" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a><a id="3294" class="Symbol">)</a> <a id="3296" class="Symbol">→</a>
    <a id="3302" href="synthetic-homotopy-theory.descent-data-pushouts.html#2989" class="Function">left-family-descent-data-pushout</a> <a id="3335" class="Symbol">(</a><a id="3336" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="3358" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="3360" href="synthetic-homotopy-theory.descent-data-pushouts.html#3262" class="Bound">s</a><a id="3361" class="Symbol">)</a> <a id="3363" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="3369" href="synthetic-homotopy-theory.descent-data-pushouts.html#3100" class="Function">right-family-descent-data-pushout</a> <a id="3403" class="Symbol">(</a><a id="3404" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="3427" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="3429" href="synthetic-homotopy-theory.descent-data-pushouts.html#3262" class="Bound">s</a><a id="3430" class="Symbol">)</a>
  <a id="3434" href="synthetic-homotopy-theory.descent-data-pushouts.html#3221" class="Function">equiv-family-descent-data-pushout</a> <a id="3468" class="Symbol">=</a> <a id="3470" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3474" class="Symbol">(</a><a id="3475" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3479" href="synthetic-homotopy-theory.descent-data-pushouts.html#2944" class="Bound">P</a><a id="3480" class="Symbol">)</a>

  <a id="3485" href="synthetic-homotopy-theory.descent-data-pushouts.html#3485" class="Function">map-family-descent-data-pushout</a> <a id="3517" class="Symbol">:</a>
    <a id="3523" class="Symbol">(</a><a id="3524" href="synthetic-homotopy-theory.descent-data-pushouts.html#3524" class="Bound">s</a> <a id="3526" class="Symbol">:</a> <a id="3528" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="3555" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a><a id="3556" class="Symbol">)</a> <a id="3558" class="Symbol">→</a>
    <a id="3564" href="synthetic-homotopy-theory.descent-data-pushouts.html#2989" class="Function">left-family-descent-data-pushout</a> <a id="3597" class="Symbol">(</a><a id="3598" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="3620" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="3622" href="synthetic-homotopy-theory.descent-data-pushouts.html#3524" class="Bound">s</a><a id="3623" class="Symbol">)</a> <a id="3625" class="Symbol">→</a>
    <a id="3631" href="synthetic-homotopy-theory.descent-data-pushouts.html#3100" class="Function">right-family-descent-data-pushout</a> <a id="3665" class="Symbol">(</a><a id="3666" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="3689" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="3691" href="synthetic-homotopy-theory.descent-data-pushouts.html#3524" class="Bound">s</a><a id="3692" class="Symbol">)</a>
  <a id="3696" href="synthetic-homotopy-theory.descent-data-pushouts.html#3485" class="Function">map-family-descent-data-pushout</a> <a id="3728" href="synthetic-homotopy-theory.descent-data-pushouts.html#3728" class="Bound">s</a> <a id="3730" class="Symbol">=</a>
    <a id="3736" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="3746" class="Symbol">(</a><a id="3747" href="synthetic-homotopy-theory.descent-data-pushouts.html#3221" class="Function">equiv-family-descent-data-pushout</a> <a id="3781" href="synthetic-homotopy-theory.descent-data-pushouts.html#3728" class="Bound">s</a><a id="3782" class="Symbol">)</a>

  <a id="3787" href="synthetic-homotopy-theory.descent-data-pushouts.html#3787" class="Function">map-inv-family-descent-data-pushout</a> <a id="3823" class="Symbol">:</a>
    <a id="3829" class="Symbol">(</a><a id="3830" href="synthetic-homotopy-theory.descent-data-pushouts.html#3830" class="Bound">s</a> <a id="3832" class="Symbol">:</a> <a id="3834" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="3861" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a><a id="3862" class="Symbol">)</a> <a id="3864" class="Symbol">→</a>
    <a id="3870" href="synthetic-homotopy-theory.descent-data-pushouts.html#3100" class="Function">right-family-descent-data-pushout</a> <a id="3904" class="Symbol">(</a><a id="3905" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="3928" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="3930" href="synthetic-homotopy-theory.descent-data-pushouts.html#3830" class="Bound">s</a><a id="3931" class="Symbol">)</a> <a id="3933" class="Symbol">→</a>
    <a id="3939" href="synthetic-homotopy-theory.descent-data-pushouts.html#2989" class="Function">left-family-descent-data-pushout</a> <a id="3972" class="Symbol">(</a><a id="3973" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="3995" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a> <a id="3997" href="synthetic-homotopy-theory.descent-data-pushouts.html#3830" class="Bound">s</a><a id="3998" class="Symbol">)</a>
  <a id="4002" href="synthetic-homotopy-theory.descent-data-pushouts.html#3787" class="Function">map-inv-family-descent-data-pushout</a> <a id="4038" href="synthetic-homotopy-theory.descent-data-pushouts.html#4038" class="Bound">s</a> <a id="4040" class="Symbol">=</a>
    <a id="4046" href="foundation-core.equivalences.html#8070" class="Function">map-inv-equiv</a> <a id="4060" class="Symbol">(</a><a id="4061" href="synthetic-homotopy-theory.descent-data-pushouts.html#3221" class="Function">equiv-family-descent-data-pushout</a> <a id="4095" href="synthetic-homotopy-theory.descent-data-pushouts.html#4038" class="Bound">s</a><a id="4096" class="Symbol">)</a>

  <a id="4101" href="synthetic-homotopy-theory.descent-data-pushouts.html#4101" class="Function">is-equiv-map-family-descent-data-pushout</a> <a id="4142" class="Symbol">:</a>
    <a id="4148" class="Symbol">(</a><a id="4149" href="synthetic-homotopy-theory.descent-data-pushouts.html#4149" class="Bound">s</a> <a id="4151" class="Symbol">:</a> <a id="4153" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="4180" href="synthetic-homotopy-theory.descent-data-pushouts.html#2914" class="Bound">𝒮</a><a id="4181" class="Symbol">)</a> <a id="4183" class="Symbol">→</a>
    <a id="4189" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="4198" class="Symbol">(</a><a id="4199" href="synthetic-homotopy-theory.descent-data-pushouts.html#3485" class="Function">map-family-descent-data-pushout</a> <a id="4231" href="synthetic-homotopy-theory.descent-data-pushouts.html#4149" class="Bound">s</a><a id="4232" class="Symbol">)</a>
  <a id="4236" href="synthetic-homotopy-theory.descent-data-pushouts.html#4101" class="Function">is-equiv-map-family-descent-data-pushout</a> <a id="4277" href="synthetic-homotopy-theory.descent-data-pushouts.html#4277" class="Bound">s</a> <a id="4279" class="Symbol">=</a>
    <a id="4285" href="foundation-core.equivalences.html#2795" class="Function">is-equiv-map-equiv</a> <a id="4304" class="Symbol">(</a><a id="4305" href="synthetic-homotopy-theory.descent-data-pushouts.html#3221" class="Function">equiv-family-descent-data-pushout</a> <a id="4339" href="synthetic-homotopy-theory.descent-data-pushouts.html#4277" class="Bound">s</a><a id="4340" class="Symbol">)</a>
</pre>
### Descent data induced by families over cocones

Given a [cocone](synthetic-homotopy-theory.cocones-under-spans.md)

```text
        g
    S -----> B
    |        |
  f |        | j
    ∨        ∨
    A -----> X
        i
```

and a family `P : X → 𝒰`, we can obtain `PA` and `PB` by precomposing with `i`
and `j`, respectively. Then to produce an equivalence
`PS s : P (ifs) ≃ P (jgs)`, we
[transport](foundation-core.transport-along-identifications.md) along the
coherence `H s : ifs = jgs`, which is an equivalence.

<pre class="Agda"><a id="4877" class="Keyword">module</a> <a id="4884" href="synthetic-homotopy-theory.descent-data-pushouts.html#4884" class="Module">_</a>
  <a id="4888" class="Symbol">{</a><a id="4889" href="synthetic-homotopy-theory.descent-data-pushouts.html#4889" class="Bound">l1</a> <a id="4892" href="synthetic-homotopy-theory.descent-data-pushouts.html#4892" class="Bound">l2</a> <a id="4895" href="synthetic-homotopy-theory.descent-data-pushouts.html#4895" class="Bound">l3</a> <a id="4898" href="synthetic-homotopy-theory.descent-data-pushouts.html#4898" class="Bound">l4</a> <a id="4901" class="Symbol">:</a> <a id="4903" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4908" class="Symbol">}</a> <a id="4910" class="Symbol">{</a><a id="4911" href="synthetic-homotopy-theory.descent-data-pushouts.html#4911" class="Bound">𝒮</a> <a id="4913" class="Symbol">:</a> <a id="4915" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="4928" href="synthetic-homotopy-theory.descent-data-pushouts.html#4889" class="Bound">l1</a> <a id="4931" href="synthetic-homotopy-theory.descent-data-pushouts.html#4892" class="Bound">l2</a> <a id="4934" href="synthetic-homotopy-theory.descent-data-pushouts.html#4895" class="Bound">l3</a><a id="4936" class="Symbol">}</a>
  <a id="4940" class="Symbol">{</a><a id="4941" href="synthetic-homotopy-theory.descent-data-pushouts.html#4941" class="Bound">X</a> <a id="4943" class="Symbol">:</a> <a id="4945" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4948" href="synthetic-homotopy-theory.descent-data-pushouts.html#4898" class="Bound">l4</a><a id="4950" class="Symbol">}</a> <a id="4952" class="Symbol">(</a><a id="4953" href="synthetic-homotopy-theory.descent-data-pushouts.html#4953" class="Bound">c</a> <a id="4955" class="Symbol">:</a> <a id="4957" href="synthetic-homotopy-theory.cocones-under-spans.html#1725" class="Function">cocone-span-diagram</a> <a id="4977" href="synthetic-homotopy-theory.descent-data-pushouts.html#4911" class="Bound">𝒮</a> <a id="4979" href="synthetic-homotopy-theory.descent-data-pushouts.html#4941" class="Bound">X</a><a id="4980" class="Symbol">)</a>
  <a id="4984" class="Keyword">where</a>

  <a id="4993" href="synthetic-homotopy-theory.descent-data-pushouts.html#4993" class="Function">descent-data-family-cocone-span-diagram</a> <a id="5033" class="Symbol">:</a>
    <a id="5039" class="Symbol">{</a><a id="5040" href="synthetic-homotopy-theory.descent-data-pushouts.html#5040" class="Bound">l5</a> <a id="5043" class="Symbol">:</a> <a id="5045" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5050" class="Symbol">}</a> <a id="5052" class="Symbol">→</a> <a id="5054" class="Symbol">(</a><a id="5055" href="synthetic-homotopy-theory.descent-data-pushouts.html#4941" class="Bound">X</a> <a id="5057" class="Symbol">→</a> <a id="5059" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5062" href="synthetic-homotopy-theory.descent-data-pushouts.html#5040" class="Bound">l5</a><a id="5064" class="Symbol">)</a> <a id="5066" class="Symbol">→</a> <a id="5068" href="synthetic-homotopy-theory.descent-data-pushouts.html#2463" class="Function">descent-data-pushout</a> <a id="5089" href="synthetic-homotopy-theory.descent-data-pushouts.html#4911" class="Bound">𝒮</a> <a id="5091" href="synthetic-homotopy-theory.descent-data-pushouts.html#5040" class="Bound">l5</a> <a id="5094" href="synthetic-homotopy-theory.descent-data-pushouts.html#5040" class="Bound">l5</a>
  <a id="5099" href="synthetic-homotopy-theory.descent-data-pushouts.html#4993" class="Function">descent-data-family-cocone-span-diagram</a> <a id="5139" href="synthetic-homotopy-theory.descent-data-pushouts.html#5139" class="Bound">P</a> <a id="5141" class="Symbol">=</a>
    <a id="5147" class="Symbol">(</a> <a id="5149" class="Symbol">(</a> <a id="5151" href="synthetic-homotopy-theory.descent-data-pushouts.html#5139" class="Bound">P</a> <a id="5153" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="5155" href="synthetic-homotopy-theory.cocones-under-spans.html#2060" class="Function">horizontal-map-cocone</a> <a id="5177" class="Symbol">_</a> <a id="5179" class="Symbol">_</a> <a id="5181" href="synthetic-homotopy-theory.descent-data-pushouts.html#4953" class="Bound">c</a><a id="5182" class="Symbol">)</a> <a id="5184" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="5192" class="Symbol">(</a> <a id="5194" href="synthetic-homotopy-theory.descent-data-pushouts.html#5139" class="Bound">P</a> <a id="5196" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="5198" href="synthetic-homotopy-theory.cocones-under-spans.html#2125" class="Function">vertical-map-cocone</a> <a id="5218" class="Symbol">_</a> <a id="5220" class="Symbol">_</a> <a id="5222" href="synthetic-homotopy-theory.descent-data-pushouts.html#4953" class="Bound">c</a><a id="5223" class="Symbol">)</a> <a id="5225" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="5233" class="Symbol">(</a> <a id="5235" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="5244" href="synthetic-homotopy-theory.descent-data-pushouts.html#5139" class="Bound">P</a> <a id="5246" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="5248" href="synthetic-homotopy-theory.cocones-under-spans.html#2192" class="Function">coherence-square-cocone</a> <a id="5272" class="Symbol">_</a> <a id="5274" class="Symbol">_</a> <a id="5276" href="synthetic-homotopy-theory.descent-data-pushouts.html#4953" class="Bound">c</a><a id="5277" class="Symbol">))</a>
</pre>
## See also

- [Equifibered span diagrams](synthetic-homotopy-theory.equifibered-span-diagrams.md)
  is a variant of descent data for pushouts where an additional type family over
  the middle vertex is specified.
