# Rewriting rules for pushouts

<pre class="Agda"><a id="41" class="Symbol">{-#</a> <a id="45" class="Keyword">OPTIONS</a> <a id="53" class="Pragma">--rewriting</a> <a id="65" class="Symbol">#-}</a>

<a id="70" class="Keyword">module</a> <a id="77" href="synthetic-homotopy-theory.rewriting-pushouts.html" class="Module">synthetic-homotopy-theory.rewriting-pushouts</a> <a id="122" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="reflection.rewriting.html" class="Module">reflection.rewriting</a>

<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="synthetic-homotopy-theory.cocones-under-spans.html" class="Module">synthetic-homotopy-theory.cocones-under-spans</a>
<a id="382" class="Keyword">open</a> <a id="387" class="Keyword">import</a> <a id="394" href="synthetic-homotopy-theory.dependent-cocones-under-spans.html" class="Module">synthetic-homotopy-theory.dependent-cocones-under-spans</a>
<a id="450" class="Keyword">open</a> <a id="455" class="Keyword">import</a> <a id="462" href="synthetic-homotopy-theory.pushouts.html" class="Module">synthetic-homotopy-theory.pushouts</a>
</pre>
</details>

## Idea

This module endows the eliminator of the
[standard pushouts](synthetic-homotopy-theory.pushouts.md) `cogap` with strict
computation rules on the point constructors using Agda's
[rewriting](reflection.rewriting.md) functionality. This gives the strict
equalities

```text
  cogap (inl-pushout f g a) ≐ horizontal-map-cocone f g c a
```

and

```text
  cogap (inr-pushout f g b) ≐ vertical-map-cocone f g c b.
```

More generally, strict computation rules for the dependent eliminator are
enabled, giving the strict equalities

```text
  dependent-cogap (inl-pushout f g a) ≐
  horizontal-map-dependent-cocone f g (cocone-pushout f g) P c a
```

and

```text
  dependent-cogap (inr-pushout f g b) ≐
  vertical-map-dependent-cocone f g (cocone-pushout f g) P c b.
```

In addition, the pre-existing witnesses of these equalities:
`compute-inl-dependent-cogap`, `compute-inr-dependent-cogap`, and their
nondependent counterparts, reduce to `refl`. This is achieved using Agda's
[equality erasure](reflection.erasing-equality.md) functionality.

To enable these computation rules in your own formalizations, set the
`--rewriting` option and import this module. Keep in mind, however, that we
offer no way to selectively disable these rules, so if your module depends on
any other module that imports this one, you will automatically also have
rewriting for pushouts enabled.

By default, we abstain from using rewrite rules in agda-unimath. However, we
recognize their usefulness in, for instance, exploratory formalizations. Since
formalizations with and without rewrite rules can coexist, there is no harm in
providing these tools for those that see a need to use them. We do, however,
emphasize that formalizations without the use of rewrite rules are preferred
over those that do use them in the library, as the former can also be applied in
other formalizations that do not enable rewrite rules.

## Rewrite rules

<pre class="Agda"><a id="2446" class="Symbol">{-#</a> <a id="2450" class="Keyword">REWRITE</a> <a id="2458" href="synthetic-homotopy-theory.pushouts.html#4439" class="Function">compute-inl-dependent-cogap</a> <a id="2486" class="Symbol">#-}</a>
<a id="2490" class="Symbol">{-#</a> <a id="2494" class="Keyword">REWRITE</a> <a id="2502" href="synthetic-homotopy-theory.pushouts.html#4850" class="Function">compute-inr-dependent-cogap</a> <a id="2530" class="Symbol">#-}</a>
</pre>
## Properties

### Verifying the reduction behavior of the computation rules for the eliminators of standard pushouts

<pre class="Agda"><a id="2666" class="Keyword">module</a> <a id="2673" href="synthetic-homotopy-theory.rewriting-pushouts.html#2673" class="Module">_</a>
  <a id="2677" class="Symbol">{</a><a id="2678" href="synthetic-homotopy-theory.rewriting-pushouts.html#2678" class="Bound">l1</a> <a id="2681" href="synthetic-homotopy-theory.rewriting-pushouts.html#2681" class="Bound">l2</a> <a id="2684" href="synthetic-homotopy-theory.rewriting-pushouts.html#2684" class="Bound">l3</a> <a id="2687" href="synthetic-homotopy-theory.rewriting-pushouts.html#2687" class="Bound">l4</a> <a id="2690" class="Symbol">:</a> <a id="2692" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2697" class="Symbol">}</a> <a id="2699" class="Symbol">{</a><a id="2700" href="synthetic-homotopy-theory.rewriting-pushouts.html#2700" class="Bound">S</a> <a id="2702" class="Symbol">:</a> <a id="2704" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2707" href="synthetic-homotopy-theory.rewriting-pushouts.html#2678" class="Bound">l1</a><a id="2709" class="Symbol">}</a> <a id="2711" class="Symbol">{</a><a id="2712" href="synthetic-homotopy-theory.rewriting-pushouts.html#2712" class="Bound">A</a> <a id="2714" class="Symbol">:</a> <a id="2716" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2719" href="synthetic-homotopy-theory.rewriting-pushouts.html#2681" class="Bound">l2</a><a id="2721" class="Symbol">}</a> <a id="2723" class="Symbol">{</a><a id="2724" href="synthetic-homotopy-theory.rewriting-pushouts.html#2724" class="Bound">B</a> <a id="2726" class="Symbol">:</a> <a id="2728" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2731" href="synthetic-homotopy-theory.rewriting-pushouts.html#2684" class="Bound">l3</a><a id="2733" class="Symbol">}</a>
  <a id="2737" class="Symbol">(</a><a id="2738" href="synthetic-homotopy-theory.rewriting-pushouts.html#2738" class="Bound">f</a> <a id="2740" class="Symbol">:</a> <a id="2742" href="synthetic-homotopy-theory.rewriting-pushouts.html#2700" class="Bound">S</a> <a id="2744" class="Symbol">→</a> <a id="2746" href="synthetic-homotopy-theory.rewriting-pushouts.html#2712" class="Bound">A</a><a id="2747" class="Symbol">)</a> <a id="2749" class="Symbol">(</a><a id="2750" href="synthetic-homotopy-theory.rewriting-pushouts.html#2750" class="Bound">g</a> <a id="2752" class="Symbol">:</a> <a id="2754" href="synthetic-homotopy-theory.rewriting-pushouts.html#2700" class="Bound">S</a> <a id="2756" class="Symbol">→</a> <a id="2758" href="synthetic-homotopy-theory.rewriting-pushouts.html#2724" class="Bound">B</a><a id="2759" class="Symbol">)</a> <a id="2761" class="Symbol">{</a><a id="2762" href="synthetic-homotopy-theory.rewriting-pushouts.html#2762" class="Bound">P</a> <a id="2764" class="Symbol">:</a> <a id="2766" href="synthetic-homotopy-theory.pushouts.html#2914" class="Postulate">pushout</a> <a id="2774" href="synthetic-homotopy-theory.rewriting-pushouts.html#2738" class="Bound">f</a> <a id="2776" href="synthetic-homotopy-theory.rewriting-pushouts.html#2750" class="Bound">g</a> <a id="2778" class="Symbol">→</a> <a id="2780" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2783" href="synthetic-homotopy-theory.rewriting-pushouts.html#2687" class="Bound">l4</a><a id="2785" class="Symbol">}</a>
  <a id="2789" class="Symbol">(</a><a id="2790" href="synthetic-homotopy-theory.rewriting-pushouts.html#2790" class="Bound">d</a> <a id="2792" class="Symbol">:</a> <a id="2794" href="synthetic-homotopy-theory.dependent-cocones-under-spans.html#2369" class="Function">dependent-cocone</a> <a id="2811" href="synthetic-homotopy-theory.rewriting-pushouts.html#2738" class="Bound">f</a> <a id="2813" href="synthetic-homotopy-theory.rewriting-pushouts.html#2750" class="Bound">g</a> <a id="2815" class="Symbol">(</a><a id="2816" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a> <a id="2831" href="synthetic-homotopy-theory.rewriting-pushouts.html#2738" class="Bound">f</a> <a id="2833" href="synthetic-homotopy-theory.rewriting-pushouts.html#2750" class="Bound">g</a><a id="2834" class="Symbol">)</a> <a id="2836" href="synthetic-homotopy-theory.rewriting-pushouts.html#2762" class="Bound">P</a><a id="2837" class="Symbol">)</a>
  <a id="2841" class="Keyword">where</a>

  <a id="2850" href="synthetic-homotopy-theory.rewriting-pushouts.html#2850" class="Function">_</a> <a id="2852" class="Symbol">:</a> <a id="2854" href="synthetic-homotopy-theory.pushouts.html#4439" class="Function">compute-inl-dependent-cogap</a> <a id="2882" href="synthetic-homotopy-theory.rewriting-pushouts.html#2738" class="Bound">f</a> <a id="2884" href="synthetic-homotopy-theory.rewriting-pushouts.html#2750" class="Bound">g</a> <a id="2886" href="synthetic-homotopy-theory.rewriting-pushouts.html#2790" class="Bound">d</a> <a id="2888" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="2890" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="2902" class="Symbol">_</a> <a id="2904" class="Symbol">=</a> <a id="2906" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>

  <a id="2919" href="synthetic-homotopy-theory.rewriting-pushouts.html#2919" class="Function">_</a> <a id="2921" class="Symbol">:</a> <a id="2923" href="synthetic-homotopy-theory.pushouts.html#4850" class="Function">compute-inr-dependent-cogap</a> <a id="2951" href="synthetic-homotopy-theory.rewriting-pushouts.html#2738" class="Bound">f</a> <a id="2953" href="synthetic-homotopy-theory.rewriting-pushouts.html#2750" class="Bound">g</a> <a id="2955" href="synthetic-homotopy-theory.rewriting-pushouts.html#2790" class="Bound">d</a> <a id="2957" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="2959" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="2971" class="Symbol">_</a> <a id="2973" class="Symbol">=</a> <a id="2975" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>

<a id="2986" class="Keyword">module</a> <a id="2993" href="synthetic-homotopy-theory.rewriting-pushouts.html#2993" class="Module">_</a>
  <a id="2997" class="Symbol">{</a><a id="2998" href="synthetic-homotopy-theory.rewriting-pushouts.html#2998" class="Bound">l1</a> <a id="3001" href="synthetic-homotopy-theory.rewriting-pushouts.html#3001" class="Bound">l2</a> <a id="3004" href="synthetic-homotopy-theory.rewriting-pushouts.html#3004" class="Bound">l3</a> <a id="3007" href="synthetic-homotopy-theory.rewriting-pushouts.html#3007" class="Bound">l4</a> <a id="3010" class="Symbol">:</a> <a id="3012" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3017" class="Symbol">}</a> <a id="3019" class="Symbol">{</a><a id="3020" href="synthetic-homotopy-theory.rewriting-pushouts.html#3020" class="Bound">S</a> <a id="3022" class="Symbol">:</a> <a id="3024" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3027" href="synthetic-homotopy-theory.rewriting-pushouts.html#2998" class="Bound">l1</a><a id="3029" class="Symbol">}</a> <a id="3031" class="Symbol">{</a><a id="3032" href="synthetic-homotopy-theory.rewriting-pushouts.html#3032" class="Bound">A</a> <a id="3034" class="Symbol">:</a> <a id="3036" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3039" href="synthetic-homotopy-theory.rewriting-pushouts.html#3001" class="Bound">l2</a><a id="3041" class="Symbol">}</a> <a id="3043" class="Symbol">{</a><a id="3044" href="synthetic-homotopy-theory.rewriting-pushouts.html#3044" class="Bound">B</a> <a id="3046" class="Symbol">:</a> <a id="3048" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3051" href="synthetic-homotopy-theory.rewriting-pushouts.html#3004" class="Bound">l3</a><a id="3053" class="Symbol">}</a>
  <a id="3057" class="Symbol">(</a><a id="3058" href="synthetic-homotopy-theory.rewriting-pushouts.html#3058" class="Bound">f</a> <a id="3060" class="Symbol">:</a> <a id="3062" href="synthetic-homotopy-theory.rewriting-pushouts.html#3020" class="Bound">S</a> <a id="3064" class="Symbol">→</a> <a id="3066" href="synthetic-homotopy-theory.rewriting-pushouts.html#3032" class="Bound">A</a><a id="3067" class="Symbol">)</a> <a id="3069" class="Symbol">(</a><a id="3070" href="synthetic-homotopy-theory.rewriting-pushouts.html#3070" class="Bound">g</a> <a id="3072" class="Symbol">:</a> <a id="3074" href="synthetic-homotopy-theory.rewriting-pushouts.html#3020" class="Bound">S</a> <a id="3076" class="Symbol">→</a> <a id="3078" href="synthetic-homotopy-theory.rewriting-pushouts.html#3044" class="Bound">B</a><a id="3079" class="Symbol">)</a> <a id="3081" class="Symbol">{</a><a id="3082" href="synthetic-homotopy-theory.rewriting-pushouts.html#3082" class="Bound">X</a> <a id="3084" class="Symbol">:</a> <a id="3086" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3089" href="synthetic-homotopy-theory.rewriting-pushouts.html#3007" class="Bound">l4</a><a id="3091" class="Symbol">}</a> <a id="3093" class="Symbol">(</a><a id="3094" href="synthetic-homotopy-theory.rewriting-pushouts.html#3094" class="Bound">c</a> <a id="3096" class="Symbol">:</a> <a id="3098" href="synthetic-homotopy-theory.cocones-under-spans.html#1497" class="Function">cocone</a> <a id="3105" href="synthetic-homotopy-theory.rewriting-pushouts.html#3058" class="Bound">f</a> <a id="3107" href="synthetic-homotopy-theory.rewriting-pushouts.html#3070" class="Bound">g</a> <a id="3109" href="synthetic-homotopy-theory.rewriting-pushouts.html#3082" class="Bound">X</a><a id="3110" class="Symbol">)</a>
  <a id="3114" class="Keyword">where</a>

  <a id="3123" href="synthetic-homotopy-theory.rewriting-pushouts.html#3123" class="Function">_</a> <a id="3125" class="Symbol">:</a> <a id="3127" href="synthetic-homotopy-theory.pushouts.html#10285" class="Function">compute-inl-cogap</a> <a id="3145" href="synthetic-homotopy-theory.rewriting-pushouts.html#3058" class="Bound">f</a> <a id="3147" href="synthetic-homotopy-theory.rewriting-pushouts.html#3070" class="Bound">g</a> <a id="3149" href="synthetic-homotopy-theory.rewriting-pushouts.html#3094" class="Bound">c</a> <a id="3151" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="3153" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="3165" class="Symbol">_</a> <a id="3167" class="Symbol">=</a> <a id="3169" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>

  <a id="3182" href="synthetic-homotopy-theory.rewriting-pushouts.html#3182" class="Function">_</a> <a id="3184" class="Symbol">:</a> <a id="3186" href="synthetic-homotopy-theory.pushouts.html#10511" class="Function">compute-inr-cogap</a> <a id="3204" href="synthetic-homotopy-theory.rewriting-pushouts.html#3058" class="Bound">f</a> <a id="3206" href="synthetic-homotopy-theory.rewriting-pushouts.html#3070" class="Bound">g</a> <a id="3208" href="synthetic-homotopy-theory.rewriting-pushouts.html#3094" class="Bound">c</a> <a id="3210" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="3212" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="3224" class="Symbol">_</a> <a id="3226" class="Symbol">=</a> <a id="3228" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
</pre>
## See also

- For some discussion on strict computation rules for higher inductive types,
  see the introduction to Section 6.2 of {{#cite UF13}}.

## References

{{#bibliography}}
