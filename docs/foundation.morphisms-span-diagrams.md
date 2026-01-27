# Morphisms of span diagrams

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="foundation.morphisms-span-diagrams.html" class="Module">foundation.morphisms-span-diagrams</a> <a id="81" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.morphisms-spans.html" class="Module">foundation.morphisms-spans</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation.operations-spans.html" class="Module">foundation.operations-spans</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="377" class="Keyword">open</a> <a id="382" class="Keyword">import</a> <a id="389" href="foundation-core.commuting-squares-of-maps.html" class="Module">foundation-core.commuting-squares-of-maps</a>
</pre>
</details>

## Idea

A {{#concept "morphism of span diagrams" Agda=hom-span-diagram}} from a
[span diagram](foundation.span-diagrams.md) `A <-f- S -g-> B` to a span diagram
`C <-h- T -k-> D` consists of maps `u : A → C`, `v : B → D`, and `w : S → T`
[equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
         f       g
    A <----- S -----> B
    |        |        |
  u |        | w      | v
    ∨        ∨        ∨
    C <----- T -----> D
         h       k
```

[commutes](foundation-core.commuting-squares-of-maps.md).

The definition of morphisms of span diagrams is given concisely in terms of the
notion of morphisms of spans. In the resulting definitions, the commuting
squares of morphisms of spans are oriented in the following way:

- A homotopy
  `map-domain-hom-span ∘ left-map-span s ~ left-map-span t ∘ spanning-map-hom-span`
  witnessing that the square

  ```text
                       spanning-map-hom-span
                    S ----------------------> T
                    |                         |
    left-map-span s |                         | left-map-span t
                    ∨                         ∨
                    A ----------------------> C
                        map-domain-hom-span
  ```

  commutes.

- A homotopy
  `map-domain-hom-span ∘ right-map-span s ~ right-map-span t ∘ spanning-map-hom-span`
  witnessing that the square

  ```text
                        spanning-map-hom-span
                     S ----------------------> T
                     |                         |
    right-map-span s |                         | right-map-span t
                     ∨                         ∨
                     B ----------------------> D
                        map-codomain-hom-span
  ```

  commutes.

## Definitions

### Morphisms of span diagrams

<pre class="Agda"><a id="2327" class="Keyword">module</a> <a id="2334" href="foundation.morphisms-span-diagrams.html#2334" class="Module">_</a>
  <a id="2338" class="Symbol">{</a><a id="2339" href="foundation.morphisms-span-diagrams.html#2339" class="Bound">l1</a> <a id="2342" href="foundation.morphisms-span-diagrams.html#2342" class="Bound">l2</a> <a id="2345" href="foundation.morphisms-span-diagrams.html#2345" class="Bound">l3</a> <a id="2348" href="foundation.morphisms-span-diagrams.html#2348" class="Bound">l4</a> <a id="2351" href="foundation.morphisms-span-diagrams.html#2351" class="Bound">l5</a> <a id="2354" href="foundation.morphisms-span-diagrams.html#2354" class="Bound">l6</a> <a id="2357" class="Symbol">:</a> <a id="2359" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2364" class="Symbol">}</a>
  <a id="2368" class="Symbol">(</a><a id="2369" href="foundation.morphisms-span-diagrams.html#2369" class="Bound">𝒮</a> <a id="2371" class="Symbol">:</a> <a id="2373" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2386" href="foundation.morphisms-span-diagrams.html#2339" class="Bound">l1</a> <a id="2389" href="foundation.morphisms-span-diagrams.html#2342" class="Bound">l2</a> <a id="2392" href="foundation.morphisms-span-diagrams.html#2345" class="Bound">l3</a><a id="2394" class="Symbol">)</a> <a id="2396" class="Symbol">(</a><a id="2397" href="foundation.morphisms-span-diagrams.html#2397" class="Bound">𝒯</a> <a id="2399" class="Symbol">:</a> <a id="2401" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2414" href="foundation.morphisms-span-diagrams.html#2348" class="Bound">l4</a> <a id="2417" href="foundation.morphisms-span-diagrams.html#2351" class="Bound">l5</a> <a id="2420" href="foundation.morphisms-span-diagrams.html#2354" class="Bound">l6</a><a id="2422" class="Symbol">)</a>
  <a id="2426" class="Keyword">where</a>

  <a id="2435" href="foundation.morphisms-span-diagrams.html#2435" class="Function">hom-span-diagram</a> <a id="2452" class="Symbol">:</a> <a id="2454" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2457" class="Symbol">(</a><a id="2458" href="foundation.morphisms-span-diagrams.html#2339" class="Bound">l1</a> <a id="2461" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2463" href="foundation.morphisms-span-diagrams.html#2342" class="Bound">l2</a> <a id="2466" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2468" href="foundation.morphisms-span-diagrams.html#2345" class="Bound">l3</a> <a id="2471" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2473" href="foundation.morphisms-span-diagrams.html#2348" class="Bound">l4</a> <a id="2476" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2478" href="foundation.morphisms-span-diagrams.html#2351" class="Bound">l5</a> <a id="2481" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2483" href="foundation.morphisms-span-diagrams.html#2354" class="Bound">l6</a><a id="2485" class="Symbol">)</a>
  <a id="2489" href="foundation.morphisms-span-diagrams.html#2435" class="Function">hom-span-diagram</a> <a id="2506" class="Symbol">=</a>
    <a id="2512" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2514" class="Symbol">(</a> <a id="2516" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="2536" href="foundation.morphisms-span-diagrams.html#2369" class="Bound">𝒮</a> <a id="2538" class="Symbol">→</a> <a id="2540" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="2560" href="foundation.morphisms-span-diagrams.html#2397" class="Bound">𝒯</a><a id="2561" class="Symbol">)</a>
      <a id="2569" class="Symbol">(</a> <a id="2571" class="Symbol">λ</a> <a id="2573" href="foundation.morphisms-span-diagrams.html#2573" class="Bound">f</a> <a id="2575" class="Symbol">→</a>
        <a id="2585" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2587" class="Symbol">(</a> <a id="2589" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="2611" href="foundation.morphisms-span-diagrams.html#2369" class="Bound">𝒮</a> <a id="2613" class="Symbol">→</a> <a id="2615" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="2637" href="foundation.morphisms-span-diagrams.html#2397" class="Bound">𝒯</a><a id="2638" class="Symbol">)</a>
          <a id="2650" class="Symbol">(</a> <a id="2652" class="Symbol">λ</a> <a id="2654" href="foundation.morphisms-span-diagrams.html#2654" class="Bound">g</a> <a id="2656" class="Symbol">→</a>
            <a id="2670" href="foundation.morphisms-spans.html#1685" class="Function">hom-span</a>
              <a id="2693" class="Symbol">(</a> <a id="2695" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a>
                <a id="2723" class="Symbol">(</a> <a id="2725" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="2743" href="foundation.morphisms-span-diagrams.html#2369" class="Bound">𝒮</a><a id="2744" class="Symbol">)</a>
                <a id="2762" class="Symbol">(</a> <a id="2764" href="foundation.morphisms-span-diagrams.html#2573" class="Bound">f</a><a id="2765" class="Symbol">)</a>
                <a id="2783" class="Symbol">(</a> <a id="2785" href="foundation.morphisms-span-diagrams.html#2654" class="Bound">g</a><a id="2786" class="Symbol">))</a>
              <a id="2803" class="Symbol">(</a> <a id="2805" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="2823" href="foundation.morphisms-span-diagrams.html#2397" class="Bound">𝒯</a><a id="2824" class="Symbol">)))</a>

<a id="2829" class="Keyword">module</a> <a id="2836" href="foundation.morphisms-span-diagrams.html#2836" class="Module">_</a>
  <a id="2840" class="Symbol">{</a><a id="2841" href="foundation.morphisms-span-diagrams.html#2841" class="Bound">l1</a> <a id="2844" href="foundation.morphisms-span-diagrams.html#2844" class="Bound">l2</a> <a id="2847" href="foundation.morphisms-span-diagrams.html#2847" class="Bound">l3</a> <a id="2850" href="foundation.morphisms-span-diagrams.html#2850" class="Bound">l4</a> <a id="2853" href="foundation.morphisms-span-diagrams.html#2853" class="Bound">l5</a> <a id="2856" href="foundation.morphisms-span-diagrams.html#2856" class="Bound">l6</a> <a id="2859" class="Symbol">:</a> <a id="2861" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2866" class="Symbol">}</a>
  <a id="2870" class="Symbol">(</a><a id="2871" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a> <a id="2873" class="Symbol">:</a> <a id="2875" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2888" href="foundation.morphisms-span-diagrams.html#2841" class="Bound">l1</a> <a id="2891" href="foundation.morphisms-span-diagrams.html#2844" class="Bound">l2</a> <a id="2894" href="foundation.morphisms-span-diagrams.html#2847" class="Bound">l3</a><a id="2896" class="Symbol">)</a> <a id="2898" class="Symbol">(</a><a id="2899" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a> <a id="2901" class="Symbol">:</a> <a id="2903" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2916" href="foundation.morphisms-span-diagrams.html#2850" class="Bound">l4</a> <a id="2919" href="foundation.morphisms-span-diagrams.html#2853" class="Bound">l5</a> <a id="2922" href="foundation.morphisms-span-diagrams.html#2856" class="Bound">l6</a><a id="2924" class="Symbol">)</a>
  <a id="2928" class="Symbol">(</a><a id="2929" href="foundation.morphisms-span-diagrams.html#2929" class="Bound">f</a> <a id="2931" class="Symbol">:</a> <a id="2933" href="foundation.morphisms-span-diagrams.html#2435" class="Function">hom-span-diagram</a> <a id="2950" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a> <a id="2952" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="2953" class="Symbol">)</a>
  <a id="2957" class="Keyword">where</a>

  <a id="2966" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a> <a id="2994" class="Symbol">:</a>
    <a id="3000" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="3020" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a> <a id="3022" class="Symbol">→</a> <a id="3024" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="3044" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a>
  <a id="3048" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a> <a id="3076" class="Symbol">=</a> <a id="3078" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3082" href="foundation.morphisms-span-diagrams.html#2929" class="Bound">f</a>

  <a id="3087" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a> <a id="3117" class="Symbol">:</a>
    <a id="3123" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="3145" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a> <a id="3147" class="Symbol">→</a> <a id="3149" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="3171" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a>
  <a id="3175" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a> <a id="3205" class="Symbol">=</a> <a id="3207" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3211" class="Symbol">(</a><a id="3212" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3216" href="foundation.morphisms-span-diagrams.html#2929" class="Bound">f</a><a id="3217" class="Symbol">)</a>

  <a id="3222" href="foundation.morphisms-span-diagrams.html#3222" class="Function">hom-span-hom-span-diagram</a> <a id="3248" class="Symbol">:</a>
    <a id="3254" href="foundation.morphisms-spans.html#1685" class="Function">hom-span</a>
      <a id="3269" class="Symbol">(</a> <a id="3271" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a>
        <a id="3291" class="Symbol">(</a> <a id="3293" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="3311" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a><a id="3312" class="Symbol">)</a>
        <a id="3322" class="Symbol">(</a> <a id="3324" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a><a id="3351" class="Symbol">)</a>
        <a id="3361" class="Symbol">(</a> <a id="3363" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a><a id="3392" class="Symbol">))</a>
      <a id="3401" class="Symbol">(</a> <a id="3403" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="3421" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="3422" class="Symbol">)</a>
  <a id="3426" href="foundation.morphisms-span-diagrams.html#3222" class="Function">hom-span-hom-span-diagram</a> <a id="3452" class="Symbol">=</a> <a id="3454" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3458" class="Symbol">(</a><a id="3459" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3463" href="foundation.morphisms-span-diagrams.html#2929" class="Bound">f</a><a id="3464" class="Symbol">)</a>

  <a id="3469" href="foundation.morphisms-span-diagrams.html#3469" class="Function">spanning-map-hom-span-diagram</a> <a id="3499" class="Symbol">:</a>
    <a id="3505" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="3532" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a> <a id="3534" class="Symbol">→</a> <a id="3536" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="3563" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a>
  <a id="3567" href="foundation.morphisms-span-diagrams.html#3469" class="Function">spanning-map-hom-span-diagram</a> <a id="3597" class="Symbol">=</a>
    <a id="3603" href="foundation.morphisms-spans.html#1925" class="Function">map-hom-span</a>
      <a id="3622" class="Symbol">(</a> <a id="3624" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a>
        <a id="3644" class="Symbol">(</a> <a id="3646" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="3664" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a><a id="3665" class="Symbol">)</a>
        <a id="3675" class="Symbol">(</a> <a id="3677" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a><a id="3704" class="Symbol">)</a>
        <a id="3714" class="Symbol">(</a> <a id="3716" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a><a id="3745" class="Symbol">))</a>
      <a id="3754" class="Symbol">(</a> <a id="3756" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="3774" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="3775" class="Symbol">)</a>
      <a id="3783" class="Symbol">(</a> <a id="3785" href="foundation.morphisms-span-diagrams.html#3222" class="Function">hom-span-hom-span-diagram</a><a id="3810" class="Symbol">)</a>

  <a id="3815" href="foundation.morphisms-span-diagrams.html#3815" class="Function">left-square-hom-span-diagram</a> <a id="3844" class="Symbol">:</a>
    <a id="3850" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="3878" class="Symbol">(</a> <a id="3880" href="foundation.morphisms-span-diagrams.html#3469" class="Function">spanning-map-hom-span-diagram</a><a id="3909" class="Symbol">)</a>
      <a id="3917" class="Symbol">(</a> <a id="3919" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="3941" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a><a id="3942" class="Symbol">)</a>
      <a id="3950" class="Symbol">(</a> <a id="3952" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="3974" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="3975" class="Symbol">)</a>
      <a id="3983" class="Symbol">(</a> <a id="3985" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a><a id="4012" class="Symbol">)</a>
  <a id="4016" href="foundation.morphisms-span-diagrams.html#3815" class="Function">left-square-hom-span-diagram</a> <a id="4045" class="Symbol">=</a>
    <a id="4051" href="foundation.morphisms-spans.html#2010" class="Function">left-triangle-hom-span</a>
      <a id="4080" class="Symbol">(</a> <a id="4082" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a>
        <a id="4102" class="Symbol">(</a> <a id="4104" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="4122" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a><a id="4123" class="Symbol">)</a>
        <a id="4133" class="Symbol">(</a> <a id="4135" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a><a id="4162" class="Symbol">)</a>
        <a id="4172" class="Symbol">(</a> <a id="4174" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a><a id="4203" class="Symbol">))</a>
      <a id="4212" class="Symbol">(</a> <a id="4214" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="4232" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="4233" class="Symbol">)</a>
      <a id="4241" class="Symbol">(</a> <a id="4243" href="foundation.morphisms-span-diagrams.html#3222" class="Function">hom-span-hom-span-diagram</a><a id="4268" class="Symbol">)</a>

  <a id="4273" href="foundation.morphisms-span-diagrams.html#4273" class="Function">left-hom-arrow-hom-span-diagram</a> <a id="4305" class="Symbol">:</a>
    <a id="4311" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="4321" class="Symbol">(</a><a id="4322" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="4344" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a><a id="4345" class="Symbol">)</a> <a id="4347" class="Symbol">(</a><a id="4348" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="4370" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="4371" class="Symbol">)</a>
  <a id="4375" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4379" href="foundation.morphisms-span-diagrams.html#4273" class="Function">left-hom-arrow-hom-span-diagram</a> <a id="4411" class="Symbol">=</a>
    <a id="4417" href="foundation.morphisms-span-diagrams.html#3469" class="Function">spanning-map-hom-span-diagram</a>
  <a id="4449" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4453" class="Symbol">(</a><a id="4454" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4458" href="foundation.morphisms-span-diagrams.html#4273" class="Function">left-hom-arrow-hom-span-diagram</a><a id="4489" class="Symbol">)</a> <a id="4491" class="Symbol">=</a>
    <a id="4497" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a>
  <a id="4527" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4531" class="Symbol">(</a><a id="4532" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4536" href="foundation.morphisms-span-diagrams.html#4273" class="Function">left-hom-arrow-hom-span-diagram</a><a id="4567" class="Symbol">)</a> <a id="4569" class="Symbol">=</a>
    <a id="4575" href="foundation.morphisms-span-diagrams.html#3815" class="Function">left-square-hom-span-diagram</a>

  <a id="4607" href="foundation.morphisms-span-diagrams.html#4607" class="Function">right-square-hom-span-diagram</a> <a id="4637" class="Symbol">:</a>
    <a id="4643" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="4671" class="Symbol">(</a> <a id="4673" href="foundation.morphisms-span-diagrams.html#3469" class="Function">spanning-map-hom-span-diagram</a><a id="4702" class="Symbol">)</a>
      <a id="4710" class="Symbol">(</a> <a id="4712" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="4735" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a><a id="4736" class="Symbol">)</a>
      <a id="4744" class="Symbol">(</a> <a id="4746" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="4769" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="4770" class="Symbol">)</a>
      <a id="4778" class="Symbol">(</a> <a id="4780" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a><a id="4809" class="Symbol">)</a>
  <a id="4813" href="foundation.morphisms-span-diagrams.html#4607" class="Function">right-square-hom-span-diagram</a> <a id="4843" class="Symbol">=</a>
    <a id="4849" href="foundation.morphisms-spans.html#2118" class="Function">right-triangle-hom-span</a>
      <a id="4879" class="Symbol">(</a> <a id="4881" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a>
        <a id="4901" class="Symbol">(</a> <a id="4903" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="4921" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a><a id="4922" class="Symbol">)</a>
        <a id="4932" class="Symbol">(</a> <a id="4934" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a><a id="4961" class="Symbol">)</a>
        <a id="4971" class="Symbol">(</a> <a id="4973" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a><a id="5002" class="Symbol">))</a>
      <a id="5011" class="Symbol">(</a> <a id="5013" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="5031" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="5032" class="Symbol">)</a>
      <a id="5040" class="Symbol">(</a> <a id="5042" href="foundation.morphisms-span-diagrams.html#3222" class="Function">hom-span-hom-span-diagram</a><a id="5067" class="Symbol">)</a>

  <a id="5072" href="foundation.morphisms-span-diagrams.html#5072" class="Function">right-hom-arrow-hom-span-diagram</a> <a id="5105" class="Symbol">:</a>
    <a id="5111" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="5121" class="Symbol">(</a><a id="5122" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="5145" href="foundation.morphisms-span-diagrams.html#2871" class="Bound">𝒮</a><a id="5146" class="Symbol">)</a> <a id="5148" class="Symbol">(</a><a id="5149" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="5172" href="foundation.morphisms-span-diagrams.html#2899" class="Bound">𝒯</a><a id="5173" class="Symbol">)</a>
  <a id="5177" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5181" href="foundation.morphisms-span-diagrams.html#5072" class="Function">right-hom-arrow-hom-span-diagram</a> <a id="5214" class="Symbol">=</a>
    <a id="5220" href="foundation.morphisms-span-diagrams.html#3469" class="Function">spanning-map-hom-span-diagram</a>
  <a id="5252" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5256" class="Symbol">(</a><a id="5257" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5261" href="foundation.morphisms-span-diagrams.html#5072" class="Function">right-hom-arrow-hom-span-diagram</a><a id="5293" class="Symbol">)</a> <a id="5295" class="Symbol">=</a>
    <a id="5301" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a>
  <a id="5333" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5337" class="Symbol">(</a><a id="5338" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5342" href="foundation.morphisms-span-diagrams.html#5072" class="Function">right-hom-arrow-hom-span-diagram</a><a id="5374" class="Symbol">)</a> <a id="5376" class="Symbol">=</a>
    <a id="5382" href="foundation.morphisms-span-diagrams.html#4607" class="Function">right-square-hom-span-diagram</a>
</pre>