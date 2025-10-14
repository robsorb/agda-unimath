# Joins of maps

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="synthetic-homotopy-theory.joins-of-maps.html" class="Module">synthetic-homotopy-theory.joins-of-maps</a> <a id="73" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="129" class="Keyword">open</a> <a id="134" class="Keyword">import</a> <a id="141" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation.standard-pullbacks.html" class="Module">foundation.standard-pullbacks</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="synthetic-homotopy-theory.cocones-under-spans.html" class="Module">synthetic-homotopy-theory.cocones-under-spans</a>
<a id="427" class="Keyword">open</a> <a id="432" class="Keyword">import</a> <a id="439" href="synthetic-homotopy-theory.pushouts.html" class="Module">synthetic-homotopy-theory.pushouts</a>
<a id="474" class="Keyword">open</a> <a id="479" class="Keyword">import</a> <a id="486" href="synthetic-homotopy-theory.universal-property-pushouts.html" class="Module">synthetic-homotopy-theory.universal-property-pushouts</a>
</pre>
</details>

## Idea

Consider two maps `f : A → X` and `g : B → X` with a common codomain. The
**join** `f * g` of `f` and `g` is defined as the
[cogap map](synthetic-homotopy-theory.pushouts.md) of the
[pullback square](foundation.pullbacks.md)

```text
             π₂
   A ×_X B -----> B
     | ⌟          |
  π₁ |            | g
     ∨            ∨
     A ---------> X.
           f
```

We often write `A *_X B` for the domain of the fiberwise join. In other words,
the cogap map of any cartesian square

```text
        j
    A -----> X
    | ⌟      |
  f |        | g
    ∨        ∨
    B -----> Y
        i
```

is the join of `i` and `g`. The join of maps is also called the **fiberwise
join** because for each `x : X` we have an
[equivalence](foundation-core.equivalences.md)

```text
  fiber (f * g) x ≃ (fiber f x) * (fiber g x)
```

from the [fiber](foundation-core.fibers-of-maps.md) of `f * g` to the
[join](synthetic-homotopy-theory.joins-of-types.md) of the fibers of `f` and
`g`. In other words, there is a
[commuting triangle](foundation.commuting-triangles-of-maps.md)

```text
            ≃
   A *_X B --> Σ (x : X), (fiber f x) * (fiber g x)
        \       /
         \     /
          \   /
           ∨ ∨
            X.
```

in which the top map is an equivalence. The join of maps is related to the
[pushout-product](synthetic-homotopy-theory.pushout-products.md), because it
fits in a [pullback diagram](foundation.pullbacks.md)

```text
      A *_X B ------> (X × B) ⊔_{A × B} (A × X)
        | ⌟                   |
  f * g |                     | f □ g
        ∨                     ∨
        X ----------------> X × X.
                 Δ
```

A second way in which the pushout-product is related to the join of maps, is
that there is a commuting triangle

```text
                              ≃
  (X × B) ⊔_{A × B} (A × X) ----> (A × Y) *_{X × Y} (X × B)
                        \           /
                   f □ g \         / (f × id) * (id × g)
                          \       /
                           ∨     ∨
                            X × Y
```

This is an immediate consequence of the fact that the ambient square of the
pushout-product is cartesian, and therefore its cogap map is the join of the two
terminal maps in the square.

## Definitions

### The join of maps

<pre class="Agda"><a id="2870" class="Keyword">module</a> <a id="2877" href="synthetic-homotopy-theory.joins-of-maps.html#2877" class="Module">_</a>
  <a id="2881" class="Symbol">{</a><a id="2882" href="synthetic-homotopy-theory.joins-of-maps.html#2882" class="Bound">l1</a> <a id="2885" href="synthetic-homotopy-theory.joins-of-maps.html#2885" class="Bound">l2</a> <a id="2888" href="synthetic-homotopy-theory.joins-of-maps.html#2888" class="Bound">l3</a> <a id="2891" class="Symbol">:</a> <a id="2893" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2898" class="Symbol">}</a> <a id="2900" class="Symbol">{</a><a id="2901" href="synthetic-homotopy-theory.joins-of-maps.html#2901" class="Bound">X</a> <a id="2903" class="Symbol">:</a> <a id="2905" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2908" href="synthetic-homotopy-theory.joins-of-maps.html#2882" class="Bound">l1</a><a id="2910" class="Symbol">}</a> <a id="2912" class="Symbol">{</a><a id="2913" href="synthetic-homotopy-theory.joins-of-maps.html#2913" class="Bound">A</a> <a id="2915" class="Symbol">:</a> <a id="2917" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2920" href="synthetic-homotopy-theory.joins-of-maps.html#2885" class="Bound">l2</a><a id="2922" class="Symbol">}</a> <a id="2924" class="Symbol">{</a><a id="2925" href="synthetic-homotopy-theory.joins-of-maps.html#2925" class="Bound">B</a> <a id="2927" class="Symbol">:</a> <a id="2929" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2932" href="synthetic-homotopy-theory.joins-of-maps.html#2888" class="Bound">l3</a><a id="2934" class="Symbol">}</a> <a id="2936" class="Symbol">(</a><a id="2937" href="synthetic-homotopy-theory.joins-of-maps.html#2937" class="Bound">f</a> <a id="2939" class="Symbol">:</a> <a id="2941" href="synthetic-homotopy-theory.joins-of-maps.html#2913" class="Bound">A</a> <a id="2943" class="Symbol">→</a> <a id="2945" href="synthetic-homotopy-theory.joins-of-maps.html#2901" class="Bound">X</a><a id="2946" class="Symbol">)</a> <a id="2948" class="Symbol">(</a><a id="2949" href="synthetic-homotopy-theory.joins-of-maps.html#2949" class="Bound">g</a> <a id="2951" class="Symbol">:</a> <a id="2953" href="synthetic-homotopy-theory.joins-of-maps.html#2925" class="Bound">B</a> <a id="2955" class="Symbol">→</a> <a id="2957" href="synthetic-homotopy-theory.joins-of-maps.html#2901" class="Bound">X</a><a id="2958" class="Symbol">)</a>
  <a id="2962" class="Keyword">where</a>

  <a id="2971" href="synthetic-homotopy-theory.joins-of-maps.html#2971" class="Function">domain-join-maps</a> <a id="2988" class="Symbol">:</a> <a id="2990" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2993" class="Symbol">(</a><a id="2994" href="synthetic-homotopy-theory.joins-of-maps.html#2882" class="Bound">l1</a> <a id="2997" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2999" href="synthetic-homotopy-theory.joins-of-maps.html#2885" class="Bound">l2</a> <a id="3002" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3004" href="synthetic-homotopy-theory.joins-of-maps.html#2888" class="Bound">l3</a><a id="3006" class="Symbol">)</a>
  <a id="3010" href="synthetic-homotopy-theory.joins-of-maps.html#2971" class="Function">domain-join-maps</a> <a id="3027" class="Symbol">=</a>
    <a id="3033" href="synthetic-homotopy-theory.pushouts.html#2914" class="Postulate">pushout</a>
      <a id="3047" class="Symbol">(</a> <a id="3049" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a> <a id="3080" class="Symbol">{</a><a id="3081" class="Argument">f</a> <a id="3083" class="Symbol">=</a> <a id="3085" href="synthetic-homotopy-theory.joins-of-maps.html#2937" class="Bound">f</a><a id="3086" class="Symbol">}</a> <a id="3088" class="Symbol">{</a><a id="3089" class="Argument">g</a> <a id="3091" class="Symbol">=</a> <a id="3093" href="synthetic-homotopy-theory.joins-of-maps.html#2949" class="Bound">g</a><a id="3094" class="Symbol">})</a>
      <a id="3103" class="Symbol">(</a> <a id="3105" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a> <a id="3138" class="Symbol">{</a><a id="3139" class="Argument">f</a> <a id="3141" class="Symbol">=</a> <a id="3143" href="synthetic-homotopy-theory.joins-of-maps.html#2937" class="Bound">f</a><a id="3144" class="Symbol">}</a> <a id="3146" class="Symbol">{</a><a id="3147" class="Argument">g</a> <a id="3149" class="Symbol">=</a> <a id="3151" href="synthetic-homotopy-theory.joins-of-maps.html#2949" class="Bound">g</a><a id="3152" class="Symbol">})</a>

  <a id="3158" href="synthetic-homotopy-theory.joins-of-maps.html#3158" class="Function">cocone-join-maps</a> <a id="3175" class="Symbol">:</a>
    <a id="3181" href="synthetic-homotopy-theory.cocones-under-spans.html#1497" class="Function">cocone</a>
      <a id="3194" class="Symbol">(</a> <a id="3196" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a> <a id="3227" class="Symbol">{</a><a id="3228" class="Argument">f</a> <a id="3230" class="Symbol">=</a> <a id="3232" href="synthetic-homotopy-theory.joins-of-maps.html#2937" class="Bound">f</a><a id="3233" class="Symbol">}</a> <a id="3235" class="Symbol">{</a><a id="3236" class="Argument">g</a> <a id="3238" class="Symbol">=</a> <a id="3240" href="synthetic-homotopy-theory.joins-of-maps.html#2949" class="Bound">g</a><a id="3241" class="Symbol">})</a>
      <a id="3250" class="Symbol">(</a> <a id="3252" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a> <a id="3285" class="Symbol">{</a><a id="3286" class="Argument">f</a> <a id="3288" class="Symbol">=</a> <a id="3290" href="synthetic-homotopy-theory.joins-of-maps.html#2937" class="Bound">f</a><a id="3291" class="Symbol">}</a> <a id="3293" class="Symbol">{</a><a id="3294" class="Argument">g</a> <a id="3296" class="Symbol">=</a> <a id="3298" href="synthetic-homotopy-theory.joins-of-maps.html#2949" class="Bound">g</a><a id="3299" class="Symbol">})</a>
      <a id="3308" class="Symbol">(</a> <a id="3310" href="synthetic-homotopy-theory.joins-of-maps.html#2901" class="Bound">X</a><a id="3311" class="Symbol">)</a>
  <a id="3315" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3319" href="synthetic-homotopy-theory.joins-of-maps.html#3158" class="Function">cocone-join-maps</a> <a id="3336" class="Symbol">=</a> <a id="3338" href="synthetic-homotopy-theory.joins-of-maps.html#2937" class="Bound">f</a>
  <a id="3342" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3346" class="Symbol">(</a><a id="3347" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3351" href="synthetic-homotopy-theory.joins-of-maps.html#3158" class="Function">cocone-join-maps</a><a id="3367" class="Symbol">)</a> <a id="3369" class="Symbol">=</a> <a id="3371" href="synthetic-homotopy-theory.joins-of-maps.html#2949" class="Bound">g</a>
  <a id="3375" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3379" class="Symbol">(</a><a id="3380" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3384" href="synthetic-homotopy-theory.joins-of-maps.html#3158" class="Function">cocone-join-maps</a><a id="3400" class="Symbol">)</a> <a id="3402" class="Symbol">=</a> <a id="3404" href="foundation.standard-pullbacks.html#2587" class="Function">coherence-square-standard-pullback</a>

  <a id="3442" class="Keyword">abstract</a>
    <a id="3455" href="synthetic-homotopy-theory.joins-of-maps.html#3455" class="Function">uniqueness-join-maps</a> <a id="3476" class="Symbol">:</a>
      <a id="3484" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a>
        <a id="3501" class="Symbol">(</a> <a id="3503" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3505" class="Symbol">(</a> <a id="3507" href="synthetic-homotopy-theory.joins-of-maps.html#2971" class="Function">domain-join-maps</a> <a id="3524" class="Symbol">→</a> <a id="3526" href="synthetic-homotopy-theory.joins-of-maps.html#2901" class="Bound">X</a><a id="3527" class="Symbol">)</a>
            <a id="3541" class="Symbol">(</a> <a id="3543" class="Symbol">λ</a> <a id="3545" href="synthetic-homotopy-theory.joins-of-maps.html#3545" class="Bound">h</a> <a id="3547" class="Symbol">→</a>
              <a id="3563" href="synthetic-homotopy-theory.cocones-under-spans.html#2850" class="Function">htpy-cocone</a>
                <a id="3591" class="Symbol">(</a> <a id="3593" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a><a id="3623" class="Symbol">)</a>
                <a id="3641" class="Symbol">(</a> <a id="3643" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a><a id="3675" class="Symbol">)</a>
                <a id="3693" class="Symbol">(</a> <a id="3695" href="synthetic-homotopy-theory.cocones-under-spans.html#6059" class="Function">cocone-map</a>
                  <a id="3724" class="Symbol">(</a> <a id="3726" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a><a id="3756" class="Symbol">)</a>
                  <a id="3776" class="Symbol">(</a> <a id="3778" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a><a id="3810" class="Symbol">)</a>
                  <a id="3830" class="Symbol">(</a> <a id="3832" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a>
                    <a id="3867" class="Symbol">(</a> <a id="3869" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a><a id="3899" class="Symbol">)</a>
                    <a id="3921" class="Symbol">(</a> <a id="3923" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a><a id="3955" class="Symbol">))</a>
                  <a id="3976" class="Symbol">(</a> <a id="3978" href="synthetic-homotopy-theory.joins-of-maps.html#3545" class="Bound">h</a><a id="3979" class="Symbol">))</a>
                <a id="3998" class="Symbol">(</a> <a id="4000" href="synthetic-homotopy-theory.joins-of-maps.html#3158" class="Function">cocone-join-maps</a><a id="4016" class="Symbol">)))</a>
    <a id="4024" href="synthetic-homotopy-theory.joins-of-maps.html#3455" class="Function">uniqueness-join-maps</a> <a id="4045" class="Symbol">=</a>
      <a id="4053" href="synthetic-homotopy-theory.universal-property-pushouts.html#4862" class="Function">uniqueness-map-universal-property-pushout</a>
        <a id="4103" class="Symbol">(</a> <a id="4105" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a><a id="4135" class="Symbol">)</a>
        <a id="4145" class="Symbol">(</a> <a id="4147" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a><a id="4179" class="Symbol">)</a>
        <a id="4189" class="Symbol">(</a> <a id="4191" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a>
          <a id="4216" class="Symbol">(</a> <a id="4218" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a><a id="4248" class="Symbol">)</a>
          <a id="4260" class="Symbol">(</a> <a id="4262" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a><a id="4294" class="Symbol">))</a>
        <a id="4305" class="Symbol">(</a> <a id="4307" href="synthetic-homotopy-theory.pushouts.html#9291" class="Function">up-pushout</a> <a id="4318" class="Symbol">_</a> <a id="4320" class="Symbol">_)</a>
        <a id="4331" class="Symbol">(</a> <a id="4333" href="synthetic-homotopy-theory.joins-of-maps.html#3158" class="Function">cocone-join-maps</a><a id="4349" class="Symbol">)</a>

  <a id="4354" class="Keyword">abstract</a>
    <a id="4367" href="synthetic-homotopy-theory.joins-of-maps.html#4367" class="Function">join-maps</a> <a id="4377" class="Symbol">:</a> <a id="4379" href="synthetic-homotopy-theory.joins-of-maps.html#2971" class="Function">domain-join-maps</a> <a id="4396" class="Symbol">→</a> <a id="4398" href="synthetic-homotopy-theory.joins-of-maps.html#2901" class="Bound">X</a>
    <a id="4404" href="synthetic-homotopy-theory.joins-of-maps.html#4367" class="Function">join-maps</a> <a id="4414" class="Symbol">=</a> <a id="4416" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4420" class="Symbol">(</a><a id="4421" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="4428" href="synthetic-homotopy-theory.joins-of-maps.html#3455" class="Function">uniqueness-join-maps</a><a id="4448" class="Symbol">)</a>

    <a id="4455" href="synthetic-homotopy-theory.joins-of-maps.html#4455" class="Function">compute-inl-join-maps</a> <a id="4477" class="Symbol">:</a> <a id="4479" href="synthetic-homotopy-theory.joins-of-maps.html#4367" class="Function">join-maps</a> <a id="4489" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4491" href="synthetic-homotopy-theory.pushouts.html#3044" class="Postulate">inl-pushout</a> <a id="4503" class="Symbol">_</a> <a id="4505" class="Symbol">_</a> <a id="4507" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="4509" href="synthetic-homotopy-theory.joins-of-maps.html#2937" class="Bound">f</a>
    <a id="4515" href="synthetic-homotopy-theory.joins-of-maps.html#4455" class="Function">compute-inl-join-maps</a> <a id="4537" class="Symbol">=</a> <a id="4539" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4543" class="Symbol">(</a><a id="4544" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4548" class="Symbol">(</a><a id="4549" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="4556" href="synthetic-homotopy-theory.joins-of-maps.html#3455" class="Function">uniqueness-join-maps</a><a id="4576" class="Symbol">))</a>

    <a id="4584" href="synthetic-homotopy-theory.joins-of-maps.html#4584" class="Function">compute-inr-join-maps</a> <a id="4606" class="Symbol">:</a> <a id="4608" href="synthetic-homotopy-theory.joins-of-maps.html#4367" class="Function">join-maps</a> <a id="4618" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4620" href="synthetic-homotopy-theory.pushouts.html#3176" class="Postulate">inr-pushout</a> <a id="4632" class="Symbol">_</a> <a id="4634" class="Symbol">_</a> <a id="4636" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="4638" href="synthetic-homotopy-theory.joins-of-maps.html#2949" class="Bound">g</a>
    <a id="4644" href="synthetic-homotopy-theory.joins-of-maps.html#4584" class="Function">compute-inr-join-maps</a> <a id="4666" class="Symbol">=</a> <a id="4668" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4672" class="Symbol">(</a><a id="4673" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4677" class="Symbol">(</a><a id="4678" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4682" class="Symbol">(</a><a id="4683" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="4690" href="synthetic-homotopy-theory.joins-of-maps.html#3455" class="Function">uniqueness-join-maps</a><a id="4710" class="Symbol">)))</a>

    <a id="4719" href="synthetic-homotopy-theory.joins-of-maps.html#4719" class="Function">compute-glue-join-maps</a> <a id="4742" class="Symbol">:</a>
      <a id="4750" href="synthetic-homotopy-theory.cocones-under-spans.html#2488" class="Function">statement-coherence-htpy-cocone</a>
        <a id="4790" class="Symbol">(</a> <a id="4792" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a><a id="4822" class="Symbol">)</a>
        <a id="4832" class="Symbol">(</a> <a id="4834" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a><a id="4866" class="Symbol">)</a>
        <a id="4876" class="Symbol">(</a> <a id="4878" href="synthetic-homotopy-theory.cocones-under-spans.html#6059" class="Function">cocone-map</a>
          <a id="4899" class="Symbol">(</a> <a id="4901" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a><a id="4931" class="Symbol">)</a>
          <a id="4943" class="Symbol">(</a> <a id="4945" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a><a id="4977" class="Symbol">)</a>
          <a id="4989" class="Symbol">(</a> <a id="4991" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a>
            <a id="5018" class="Symbol">(</a> <a id="5020" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a><a id="5050" class="Symbol">)</a>
            <a id="5064" class="Symbol">(</a> <a id="5066" href="foundation.standard-pullbacks.html#2472" class="Function">horizontal-map-standard-pullback</a><a id="5098" class="Symbol">))</a>
          <a id="5111" class="Symbol">(</a> <a id="5113" href="synthetic-homotopy-theory.joins-of-maps.html#4367" class="Function">join-maps</a><a id="5122" class="Symbol">))</a>
        <a id="5133" class="Symbol">(</a> <a id="5135" href="synthetic-homotopy-theory.joins-of-maps.html#3158" class="Function">cocone-join-maps</a><a id="5151" class="Symbol">)</a>
        <a id="5161" class="Symbol">(</a> <a id="5163" href="synthetic-homotopy-theory.joins-of-maps.html#4455" class="Function">compute-inl-join-maps</a><a id="5184" class="Symbol">)</a>
        <a id="5194" class="Symbol">(</a> <a id="5196" href="synthetic-homotopy-theory.joins-of-maps.html#4584" class="Function">compute-inr-join-maps</a><a id="5217" class="Symbol">)</a>
    <a id="5223" href="synthetic-homotopy-theory.joins-of-maps.html#4719" class="Function">compute-glue-join-maps</a> <a id="5246" class="Symbol">=</a>
      <a id="5254" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5258" class="Symbol">(</a><a id="5259" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5263" class="Symbol">(</a><a id="5264" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5268" class="Symbol">(</a><a id="5269" href="foundation-core.contractible-types.html#986" class="Function">center</a> <a id="5276" href="synthetic-homotopy-theory.joins-of-maps.html#3455" class="Function">uniqueness-join-maps</a><a id="5296" class="Symbol">)))</a>
</pre>
## External links

- [Join of maps](https://ncatlab.org/nlab/show/join+of+maps) at the $n$Lab
