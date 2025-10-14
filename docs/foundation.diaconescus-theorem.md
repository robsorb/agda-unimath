# Diaconescu's theorem

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="foundation.diaconescus-theorem.html" class="Module">foundation.diaconescus-theorem</a> <a id="71" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.axiom-of-choice.html" class="Module">foundation.axiom-of-choice</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.decidable-propositions.html" class="Module">foundation.decidable-propositions</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="386" class="Keyword">open</a> <a id="391" class="Keyword">import</a> <a id="398" href="foundation.law-of-excluded-middle.html" class="Module">foundation.law-of-excluded-middle</a>
<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="476" class="Keyword">open</a> <a id="481" class="Keyword">import</a> <a id="488" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="601" class="Keyword">open</a> <a id="606" class="Keyword">import</a> <a id="613" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="644" class="Keyword">open</a> <a id="649" class="Keyword">import</a> <a id="656" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="687" class="Keyword">open</a> <a id="692" class="Keyword">import</a> <a id="699" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>

<a id="731" class="Keyword">open</a> <a id="736" class="Keyword">import</a> <a id="743" href="synthetic-homotopy-theory.suspensions-of-propositions.html" class="Module">synthetic-homotopy-theory.suspensions-of-propositions</a>
<a id="797" class="Keyword">open</a> <a id="802" class="Keyword">import</a> <a id="809" href="synthetic-homotopy-theory.suspensions-of-types.html" class="Module">synthetic-homotopy-theory.suspensions-of-types</a>
</pre>
</details>

## Idea

The [axiom of choice](foundation.axiom-of-choice.md) implies the
[law of excluded middle](foundation.law-of-excluded-middle.md). This is often
referred to as
{{#concept "Diaconescu's theorem" WD="Diaconescu's theorem" WDID=Q3527059 Agda=theorem-Diaconescu}}.

## Theorem

We follow the proof given under Theorem 10.1.14 in {{#cite UF13}}.

**Proof.** Given a [proposition](foundation-core.propositions.md) `P`, then its
[suspension](synthetic-homotopy-theory.suspensions-of-propositions.md) `ΣP` is a
[set](foundation-core.sets.md) with the property that `(N ＝ S) ≃ ΣP`, where `N`
and `S` are the _poles_ of `ΣP`. There is a surjection from the
[booleans](foundation.booleans.md) onto the suspension `f : bool ↠ ΣP` such that
`f true ≐ N` and `f false ≐ S`. Its
[fiber family](foundation-core.fibers-of-maps.md) is in other words an
[inhabited](foundation.inhabited-types.md) family over `ΣP`. Applying the axiom
of choice to this family, we obtain a
[mere](foundation.propositional-truncations.md)
[section](foundation-core.sections.md) `s` of `f` which thus exhibits `P` as a
[logical equivalent](foundation.logical-equivalences.md) to `f⁻¹ N ＝ f⁻¹ S`.
The latter is an [equation](foundation-core.identity-types.md) of booleans, and
the booleans have [decidable equality](foundation.decidable-equality.md) so `P`
must also be [decidable](foundation.decidable-propositions.md).

<pre class="Agda"><a id="instance-theorem-Diaconescu"></a><a id="2270" href="foundation.diaconescus-theorem.html#2270" class="Function">instance-theorem-Diaconescu</a> <a id="2298" class="Symbol">:</a>
  <a id="2302" class="Symbol">{</a><a id="2303" href="foundation.diaconescus-theorem.html#2303" class="Bound">l</a> <a id="2305" class="Symbol">:</a> <a id="2307" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2312" class="Symbol">}</a> <a id="2314" class="Symbol">(</a><a id="2315" href="foundation.diaconescus-theorem.html#2315" class="Bound">P</a> <a id="2317" class="Symbol">:</a> <a id="2319" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2324" href="foundation.diaconescus-theorem.html#2303" class="Bound">l</a><a id="2325" class="Symbol">)</a> <a id="2327" class="Symbol">→</a>
  <a id="2331" href="foundation.axiom-of-choice.html#2475" class="Function">instance-choice₀</a>
    <a id="2352" class="Symbol">(</a> <a id="2354" href="synthetic-homotopy-theory.suspensions-of-propositions.html#15908" class="Function">suspension-set-Prop</a> <a id="2374" href="foundation.diaconescus-theorem.html#2315" class="Bound">P</a><a id="2375" class="Symbol">)</a>
    <a id="2381" class="Symbol">(</a> <a id="2383" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="2389" href="synthetic-homotopy-theory.suspensions-of-types.html#18055" class="Function">map-surjection-bool-suspension</a><a id="2419" class="Symbol">)</a> <a id="2421" class="Symbol">→</a>
  <a id="2425" href="foundation-core.decidable-propositions.html#1521" class="Function">is-decidable-type-Prop</a> <a id="2448" href="foundation.diaconescus-theorem.html#2315" class="Bound">P</a>
<a id="2450" href="foundation.diaconescus-theorem.html#2270" class="Function">instance-theorem-Diaconescu</a> <a id="2478" href="foundation.diaconescus-theorem.html#2478" class="Bound">P</a> <a id="2480" href="foundation.diaconescus-theorem.html#2480" class="Bound">ac-P</a> <a id="2485" class="Symbol">=</a>
  <a id="2489" href="foundation.propositional-truncations.html#4671" class="Function">rec-trunc-Prop</a>
    <a id="2508" class="Symbol">(</a> <a id="2510" href="foundation-core.decidable-propositions.html#1342" class="Function">is-decidable-Prop</a> <a id="2528" href="foundation.diaconescus-theorem.html#2478" class="Bound">P</a><a id="2529" class="Symbol">)</a>
    <a id="2535" class="Symbol">(</a> <a id="2537" class="Symbol">λ</a> <a id="2539" href="foundation.diaconescus-theorem.html#2539" class="Bound">s</a> <a id="2541" class="Symbol">→</a>
      <a id="2549" href="foundation.decidable-types.html#5105" class="Function">is-decidable-iff&#39;</a>
        <a id="2575" class="Symbol">(</a> <a id="2577" class="Symbol">(</a> <a id="2579" href="foundation.logical-equivalences.html#5651" class="Function">iff-equiv</a> <a id="2589" class="Symbol">(</a><a id="2590" href="synthetic-homotopy-theory.suspensions-of-propositions.html#16018" class="Function">compute-eq-north-south-suspension-Prop</a> <a id="2629" href="foundation.diaconescus-theorem.html#2478" class="Bound">P</a><a id="2630" class="Symbol">))</a> <a id="2633" href="foundation.logical-equivalences.html#3079" class="Function Operator">∘iff</a>
          <a id="2648" class="Symbol">(</a> <a id="2650" class="Symbol">(</a> <a id="2652" class="Symbol">λ</a> <a id="2654" href="foundation.diaconescus-theorem.html#2654" class="Bound">p</a> <a id="2656" class="Symbol">→</a>
              <a id="2672" class="Symbol">(</a> <a id="2674" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="2678" class="Symbol">(</a><a id="2679" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2683" class="Symbol">(</a><a id="2684" href="foundation.diaconescus-theorem.html#2539" class="Bound">s</a> <a id="2686" href="synthetic-homotopy-theory.suspensions-of-types.html#2737" class="Function">north-suspension</a><a id="2702" class="Symbol">)))</a> <a id="2706" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
              <a id="2722" class="Symbol">(</a> <a id="2724" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="2727" href="synthetic-homotopy-theory.suspensions-of-types.html#18055" class="Function">map-surjection-bool-suspension</a> <a id="2758" href="foundation.diaconescus-theorem.html#2654" class="Bound">p</a><a id="2759" class="Symbol">)</a> <a id="2761" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
              <a id="2777" class="Symbol">(</a> <a id="2779" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2783" class="Symbol">(</a><a id="2784" href="foundation.diaconescus-theorem.html#2539" class="Bound">s</a> <a id="2786" href="synthetic-homotopy-theory.suspensions-of-types.html#2877" class="Function">south-suspension</a><a id="2802" class="Symbol">)))</a> <a id="2806" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
            <a id="2820" class="Symbol">(</a> <a id="2822" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="2825" class="Symbol">(</a><a id="2826" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2830" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2832" href="foundation.diaconescus-theorem.html#2539" class="Bound">s</a><a id="2833" class="Symbol">))))</a>
        <a id="2846" class="Symbol">(</a> <a id="2848" href="foundation.booleans.html#4487" class="Function">has-decidable-equality-bool</a>
          <a id="2886" class="Symbol">(</a> <a id="2888" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2892" class="Symbol">(</a><a id="2893" href="foundation.diaconescus-theorem.html#2539" class="Bound">s</a> <a id="2895" href="synthetic-homotopy-theory.suspensions-of-types.html#2737" class="Function">north-suspension</a><a id="2911" class="Symbol">))</a>
          <a id="2924" class="Symbol">(</a> <a id="2926" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2930" class="Symbol">(</a><a id="2931" href="foundation.diaconescus-theorem.html#2539" class="Bound">s</a> <a id="2933" href="synthetic-homotopy-theory.suspensions-of-types.html#2877" class="Function">south-suspension</a><a id="2949" class="Symbol">))))</a>
    <a id="2958" class="Symbol">(</a> <a id="2960" href="foundation.diaconescus-theorem.html#2480" class="Bound">ac-P</a> <a id="2965" href="synthetic-homotopy-theory.suspensions-of-types.html#18226" class="Function">is-surjective-map-surjection-bool-suspension</a><a id="3009" class="Symbol">)</a>

<a id="theorem-Diaconescu"></a><a id="3012" href="foundation.diaconescus-theorem.html#3012" class="Function">theorem-Diaconescu</a> <a id="3031" class="Symbol">:</a>
  <a id="3035" class="Symbol">{</a><a id="3036" href="foundation.diaconescus-theorem.html#3036" class="Bound">l</a> <a id="3038" class="Symbol">:</a> <a id="3040" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3045" class="Symbol">}</a> <a id="3047" class="Symbol">→</a> <a id="3049" href="foundation.axiom-of-choice.html#2614" class="Function">level-AC0</a> <a id="3059" href="foundation.diaconescus-theorem.html#3036" class="Bound">l</a> <a id="3061" href="foundation.diaconescus-theorem.html#3036" class="Bound">l</a> <a id="3063" class="Symbol">→</a> <a id="3065" href="foundation.law-of-excluded-middle.html#704" class="Function">LEM</a> <a id="3069" href="foundation.diaconescus-theorem.html#3036" class="Bound">l</a>
<a id="3071" href="foundation.diaconescus-theorem.html#3012" class="Function">theorem-Diaconescu</a> <a id="3090" href="foundation.diaconescus-theorem.html#3090" class="Bound">ac</a> <a id="3093" href="foundation.diaconescus-theorem.html#3093" class="Bound">P</a> <a id="3095" class="Symbol">=</a>
  <a id="3099" href="foundation.diaconescus-theorem.html#2270" class="Function">instance-theorem-Diaconescu</a> <a id="3127" href="foundation.diaconescus-theorem.html#3093" class="Bound">P</a>
    <a id="3133" class="Symbol">(</a> <a id="3135" href="foundation.diaconescus-theorem.html#3090" class="Bound">ac</a> <a id="3138" class="Symbol">(</a><a id="3139" href="synthetic-homotopy-theory.suspensions-of-propositions.html#15908" class="Function">suspension-set-Prop</a> <a id="3159" href="foundation.diaconescus-theorem.html#3093" class="Bound">P</a><a id="3160" class="Symbol">)</a> <a id="3162" class="Symbol">(</a><a id="3163" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="3169" href="synthetic-homotopy-theory.suspensions-of-types.html#18055" class="Function">map-surjection-bool-suspension</a><a id="3199" class="Symbol">))</a>
</pre>
## References

{{#bibliography}}
