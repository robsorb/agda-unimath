# Uniqueness quantification

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="foundation.uniqueness-quantification.html" class="Module">foundation.uniqueness-quantification</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="269" class="Keyword">open</a> <a id="274" class="Keyword">import</a> <a id="281" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="316" class="Keyword">open</a> <a id="321" class="Keyword">import</a> <a id="328" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="402" class="Keyword">open</a> <a id="407" class="Keyword">import</a> <a id="414" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

Given a predicate `P : A → Prop` we say there
{{#concept "uniquely exists" Disambiguation="in a subtype" WDID=Q2502253 WD="uniqueness quantification" Agda=∃!}}
_an `x : A` satisfying `P`_, if the [subtype](foundation-core.subtypes.md)
`Σ (x : A), (P x)` is [contractible](foundation-core.contractible-types.md).

More generally, given a [structure](foundation.structure.md) `B : A → 𝒰` we say
there
{{#concept "uniquely exists" Disambiguation="structure" Agda=uniquely-exists-structure}}
_an `x : A` and a `y : B x`_, if the
[total type](foundation.dependent-pair-types.md) `Σ (x : A), (B x)` is
contractible.

Note that the unique existence of structure is defined in the exact same way as
the concept of
[torsorial type families](foundation-core.torsorial-type-families.md). Whether
to use the concept of unique existence of a structure or the concept of
torsorial type family is dependent on the context. Torsoriality is used often to
emphasize the relation of the type family to the identity type, whereas
uniqueness of structure is used to emphasize the uniqueness of elements equipped
with further structure. For example, we tend to use unique existence in
combination with universal properties, in order to conclude that a certain map
equipped with some homotopies exists uniquely.

As a special case of uniqueness quantification, we recover
[exclusive disjunction](foundation.exclusive-disjunction.md) when the indexing
type is a [2-element type](univalent-combinatorics.2-element-types.md).
Concretely, we have the equivalence

```text
  ∃! (t : bool), (P t) ≐ is-contr (Σ (t : bool), (P t))
                       ≃ is-contr ((P false) + (P true))
                       ≐ P false ⊻ P true.
```

## Definitions

### Unique existence of structure

<pre class="Agda"><a id="2234" class="Keyword">module</a> <a id="2241" href="foundation.uniqueness-quantification.html#2241" class="Module">_</a>
  <a id="2245" class="Symbol">{</a><a id="2246" href="foundation.uniqueness-quantification.html#2246" class="Bound">l1</a> <a id="2249" href="foundation.uniqueness-quantification.html#2249" class="Bound">l2</a> <a id="2252" class="Symbol">:</a> <a id="2254" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2259" class="Symbol">}</a> <a id="2261" class="Symbol">(</a><a id="2262" href="foundation.uniqueness-quantification.html#2262" class="Bound">A</a> <a id="2264" class="Symbol">:</a> <a id="2266" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2269" href="foundation.uniqueness-quantification.html#2246" class="Bound">l1</a><a id="2271" class="Symbol">)</a> <a id="2273" class="Symbol">(</a><a id="2274" href="foundation.uniqueness-quantification.html#2274" class="Bound">B</a> <a id="2276" class="Symbol">:</a> <a id="2278" href="foundation.uniqueness-quantification.html#2262" class="Bound">A</a> <a id="2280" class="Symbol">→</a> <a id="2282" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2285" href="foundation.uniqueness-quantification.html#2249" class="Bound">l2</a><a id="2287" class="Symbol">)</a>
  <a id="2291" class="Keyword">where</a>

  <a id="2300" href="foundation.uniqueness-quantification.html#2300" class="Function">uniquely-exists-structure-Prop</a> <a id="2331" class="Symbol">:</a> <a id="2333" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2338" class="Symbol">(</a><a id="2339" href="foundation.uniqueness-quantification.html#2246" class="Bound">l1</a> <a id="2342" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2344" href="foundation.uniqueness-quantification.html#2249" class="Bound">l2</a><a id="2346" class="Symbol">)</a>
  <a id="2350" href="foundation.uniqueness-quantification.html#2300" class="Function">uniquely-exists-structure-Prop</a> <a id="2381" class="Symbol">=</a> <a id="2383" href="foundation.torsorial-type-families.html#1175" class="Function">is-torsorial-Prop</a> <a id="2401" href="foundation.uniqueness-quantification.html#2274" class="Bound">B</a>

  <a id="2406" href="foundation.uniqueness-quantification.html#2406" class="Function">uniquely-exists-structure</a> <a id="2432" class="Symbol">:</a> <a id="2434" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2437" class="Symbol">(</a><a id="2438" href="foundation.uniqueness-quantification.html#2246" class="Bound">l1</a> <a id="2441" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2443" href="foundation.uniqueness-quantification.html#2249" class="Bound">l2</a><a id="2445" class="Symbol">)</a>
  <a id="2449" href="foundation.uniqueness-quantification.html#2406" class="Function">uniquely-exists-structure</a> <a id="2475" class="Symbol">=</a> <a id="2477" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2487" href="foundation.uniqueness-quantification.html#2300" class="Function">uniquely-exists-structure-Prop</a>

  <a id="2521" href="foundation.uniqueness-quantification.html#2521" class="Function">is-prop-uniquely-exists-structure</a> <a id="2555" class="Symbol">:</a> <a id="2557" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2565" href="foundation.uniqueness-quantification.html#2406" class="Function">uniquely-exists-structure</a>
  <a id="2593" href="foundation.uniqueness-quantification.html#2521" class="Function">is-prop-uniquely-exists-structure</a> <a id="2627" class="Symbol">=</a>
    <a id="2633" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2651" href="foundation.uniqueness-quantification.html#2300" class="Function">uniquely-exists-structure-Prop</a>
</pre>
### Unique existence in a subtype

<pre class="Agda"><a id="2730" class="Keyword">module</a> <a id="2737" href="foundation.uniqueness-quantification.html#2737" class="Module">_</a>
  <a id="2741" class="Symbol">{</a><a id="2742" href="foundation.uniqueness-quantification.html#2742" class="Bound">l1</a> <a id="2745" href="foundation.uniqueness-quantification.html#2745" class="Bound">l2</a> <a id="2748" class="Symbol">:</a> <a id="2750" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2755" class="Symbol">}</a> <a id="2757" class="Symbol">(</a><a id="2758" href="foundation.uniqueness-quantification.html#2758" class="Bound">A</a> <a id="2760" class="Symbol">:</a> <a id="2762" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2765" href="foundation.uniqueness-quantification.html#2742" class="Bound">l1</a><a id="2767" class="Symbol">)</a> <a id="2769" class="Symbol">(</a><a id="2770" href="foundation.uniqueness-quantification.html#2770" class="Bound">P</a> <a id="2772" class="Symbol">:</a> <a id="2774" href="foundation.uniqueness-quantification.html#2758" class="Bound">A</a> <a id="2776" class="Symbol">→</a> <a id="2778" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2783" href="foundation.uniqueness-quantification.html#2745" class="Bound">l2</a><a id="2785" class="Symbol">)</a>
  <a id="2789" class="Keyword">where</a>

  <a id="2798" href="foundation.uniqueness-quantification.html#2798" class="Function">uniquely-exists-Prop</a> <a id="2819" class="Symbol">:</a> <a id="2821" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2826" class="Symbol">(</a><a id="2827" href="foundation.uniqueness-quantification.html#2742" class="Bound">l1</a> <a id="2830" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2832" href="foundation.uniqueness-quantification.html#2745" class="Bound">l2</a><a id="2834" class="Symbol">)</a>
  <a id="2838" href="foundation.uniqueness-quantification.html#2798" class="Function">uniquely-exists-Prop</a> <a id="2859" class="Symbol">=</a> <a id="2861" href="foundation.uniqueness-quantification.html#2300" class="Function">uniquely-exists-structure-Prop</a> <a id="2892" href="foundation.uniqueness-quantification.html#2758" class="Bound">A</a> <a id="2894" class="Symbol">(</a><a id="2895" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2905" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2907" href="foundation.uniqueness-quantification.html#2770" class="Bound">P</a><a id="2908" class="Symbol">)</a>

  <a id="2913" href="foundation.uniqueness-quantification.html#2913" class="Function">uniquely-exists</a> <a id="2929" class="Symbol">:</a> <a id="2931" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2934" class="Symbol">(</a><a id="2935" href="foundation.uniqueness-quantification.html#2742" class="Bound">l1</a> <a id="2938" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2940" href="foundation.uniqueness-quantification.html#2745" class="Bound">l2</a><a id="2942" class="Symbol">)</a>
  <a id="2946" href="foundation.uniqueness-quantification.html#2913" class="Function">uniquely-exists</a> <a id="2962" class="Symbol">=</a> <a id="2964" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2974" href="foundation.uniqueness-quantification.html#2798" class="Function">uniquely-exists-Prop</a>

  <a id="2998" href="foundation.uniqueness-quantification.html#2998" class="Function">is-prop-uniquely-exists</a> <a id="3022" class="Symbol">:</a> <a id="3024" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3032" href="foundation.uniqueness-quantification.html#2913" class="Function">uniquely-exists</a>
  <a id="3050" href="foundation.uniqueness-quantification.html#2998" class="Function">is-prop-uniquely-exists</a> <a id="3074" class="Symbol">=</a> <a id="3076" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="3094" href="foundation.uniqueness-quantification.html#2798" class="Function">uniquely-exists-Prop</a>

  <a id="3118" href="foundation.uniqueness-quantification.html#3118" class="Function">∃!</a> <a id="3121" class="Symbol">:</a> <a id="3123" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3128" class="Symbol">(</a><a id="3129" href="foundation.uniqueness-quantification.html#2742" class="Bound">l1</a> <a id="3132" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3134" href="foundation.uniqueness-quantification.html#2745" class="Bound">l2</a><a id="3136" class="Symbol">)</a>
  <a id="3140" href="foundation.uniqueness-quantification.html#3118" class="Function">∃!</a> <a id="3143" class="Symbol">=</a> <a id="3145" href="foundation.uniqueness-quantification.html#2798" class="Function">uniquely-exists-Prop</a>
</pre>
### Components of unique existence

<pre class="Agda"><a id="3215" class="Keyword">module</a> <a id="3222" href="foundation.uniqueness-quantification.html#3222" class="Module">_</a>
  <a id="3226" class="Symbol">{</a><a id="3227" href="foundation.uniqueness-quantification.html#3227" class="Bound">l1</a> <a id="3230" href="foundation.uniqueness-quantification.html#3230" class="Bound">l2</a> <a id="3233" class="Symbol">:</a> <a id="3235" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3240" class="Symbol">}</a> <a id="3242" class="Symbol">{</a><a id="3243" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a> <a id="3245" class="Symbol">:</a> <a id="3247" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3250" href="foundation.uniqueness-quantification.html#3227" class="Bound">l1</a><a id="3252" class="Symbol">}</a> <a id="3254" class="Symbol">{</a><a id="3255" href="foundation.uniqueness-quantification.html#3255" class="Bound">B</a> <a id="3257" class="Symbol">:</a> <a id="3259" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a> <a id="3261" class="Symbol">→</a> <a id="3263" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3266" href="foundation.uniqueness-quantification.html#3230" class="Bound">l2</a><a id="3268" class="Symbol">}</a>
  <a id="3272" class="Keyword">where</a>

  <a id="3281" href="foundation.uniqueness-quantification.html#3281" class="Function">pair-uniquely-exists</a> <a id="3302" class="Symbol">:</a> <a id="3304" href="foundation.uniqueness-quantification.html#2406" class="Function">uniquely-exists-structure</a> <a id="3330" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a> <a id="3332" href="foundation.uniqueness-quantification.html#3255" class="Bound">B</a> <a id="3334" class="Symbol">→</a> <a id="3336" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3338" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a> <a id="3340" href="foundation.uniqueness-quantification.html#3255" class="Bound">B</a>
  <a id="3344" href="foundation.uniqueness-quantification.html#3281" class="Function">pair-uniquely-exists</a> <a id="3365" class="Symbol">=</a> <a id="3367" href="foundation-core.contractible-types.html#986" class="Function">center</a>

  <a id="3377" href="foundation.uniqueness-quantification.html#3377" class="Function">pr1-uniquely-exists</a> <a id="3397" class="Symbol">:</a> <a id="3399" href="foundation.uniqueness-quantification.html#2406" class="Function">uniquely-exists-structure</a> <a id="3425" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a> <a id="3427" href="foundation.uniqueness-quantification.html#3255" class="Bound">B</a> <a id="3429" class="Symbol">→</a> <a id="3431" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a>
  <a id="3435" href="foundation.uniqueness-quantification.html#3377" class="Function">pr1-uniquely-exists</a> <a id="3455" class="Symbol">=</a> <a id="3457" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3461" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3463" href="foundation.uniqueness-quantification.html#3281" class="Function">pair-uniquely-exists</a>

  <a id="3487" href="foundation.uniqueness-quantification.html#3487" class="Function">pr2-uniquely-exists</a> <a id="3507" class="Symbol">:</a>
    <a id="3513" class="Symbol">(</a><a id="3514" href="foundation.uniqueness-quantification.html#3514" class="Bound">p</a> <a id="3516" class="Symbol">:</a> <a id="3518" href="foundation.uniqueness-quantification.html#2406" class="Function">uniquely-exists-structure</a> <a id="3544" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a> <a id="3546" href="foundation.uniqueness-quantification.html#3255" class="Bound">B</a><a id="3547" class="Symbol">)</a> <a id="3549" class="Symbol">→</a> <a id="3551" href="foundation.uniqueness-quantification.html#3255" class="Bound">B</a> <a id="3553" class="Symbol">(</a><a id="3554" href="foundation.uniqueness-quantification.html#3377" class="Function">pr1-uniquely-exists</a> <a id="3574" href="foundation.uniqueness-quantification.html#3514" class="Bound">p</a><a id="3575" class="Symbol">)</a>
  <a id="3579" href="foundation.uniqueness-quantification.html#3487" class="Function">pr2-uniquely-exists</a> <a id="3599" class="Symbol">=</a> <a id="3601" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3605" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3607" href="foundation.uniqueness-quantification.html#3281" class="Function">pair-uniquely-exists</a>

  <a id="3631" href="foundation.uniqueness-quantification.html#3631" class="Function">contraction-uniquely-exists</a> <a id="3659" class="Symbol">:</a>
    <a id="3665" class="Symbol">(</a><a id="3666" href="foundation.uniqueness-quantification.html#3666" class="Bound">p</a> <a id="3668" class="Symbol">:</a> <a id="3670" href="foundation.uniqueness-quantification.html#2406" class="Function">uniquely-exists-structure</a> <a id="3696" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a> <a id="3698" href="foundation.uniqueness-quantification.html#3255" class="Bound">B</a><a id="3699" class="Symbol">)</a> <a id="3701" class="Symbol">→</a>
    <a id="3707" class="Symbol">(</a><a id="3708" href="foundation.uniqueness-quantification.html#3708" class="Bound">q</a> <a id="3710" class="Symbol">:</a> <a id="3712" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="3714" href="foundation.uniqueness-quantification.html#3243" class="Bound">A</a> <a id="3716" href="foundation.uniqueness-quantification.html#3255" class="Bound">B</a><a id="3717" class="Symbol">)</a> <a id="3719" class="Symbol">→</a> <a id="3721" href="foundation.uniqueness-quantification.html#3281" class="Function">pair-uniquely-exists</a> <a id="3742" href="foundation.uniqueness-quantification.html#3666" class="Bound">p</a> <a id="3744" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3746" href="foundation.uniqueness-quantification.html#3708" class="Bound">q</a>
  <a id="3750" href="foundation.uniqueness-quantification.html#3631" class="Function">contraction-uniquely-exists</a> <a id="3778" class="Symbol">=</a> <a id="3780" href="foundation-core.contractible-types.html#1324" class="Function">contraction</a>
</pre>
## See also

- Unique existence is the indexed counterpart to
  [exclusive disjunction](foundation.exclusive-disjunction.md).
- A different name for _unique existence_ is
  [torsoriality](foundation.torsorial-type-families.md).

## External links

- [uniqueness quantifier](https://ncatlab.org/nlab/show/uniqueness+quantifier)
  at $n$Lab
- [Uniqueness quantification](https://en.wikipedia.org/wiki/Uniqueness_quantification)
  at Wikipedia
