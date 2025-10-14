# Discrete directed graphs

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="graph-theory.discrete-directed-graphs.html" class="Module">graph-theory.discrete-directed-graphs</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="foundation.discrete-binary-relations.html" class="Module">foundation.discrete-binary-relations</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="413" class="Keyword">open</a> <a id="418" class="Keyword">import</a> <a id="425" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="445" class="Keyword">open</a> <a id="450" class="Keyword">import</a> <a id="457" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="485" class="Keyword">open</a> <a id="490" class="Keyword">import</a> <a id="497" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="528" class="Keyword">open</a> <a id="533" class="Keyword">import</a> <a id="540" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="569" class="Keyword">open</a> <a id="574" class="Keyword">import</a> <a id="581" href="foundation-core.torsorial-type-families.html" class="Module">foundation-core.torsorial-type-families</a>

<a id="622" class="Keyword">open</a> <a id="627" class="Keyword">import</a> <a id="634" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="663" class="Keyword">open</a> <a id="668" class="Keyword">import</a> <a id="675" href="graph-theory.morphisms-directed-graphs.html" class="Module">graph-theory.morphisms-directed-graphs</a>
<a id="714" class="Keyword">open</a> <a id="719" class="Keyword">import</a> <a id="726" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
</pre>
</details>

## Idea

A [directed graph](graph-theory.directed-graphs.md) `G ≐ (V , E)` is said to be
{{#concept "discrete" Disambiguation="directed graph" Agda=is-discrete-Directed-Graph}}
if it has no edges. In other words, a directed graph is discrete if it is of the
form `Δ A`, where `Δ` is the left adjoint to the forgetful functor `(V , E) ↦ V`
from directed graphs to types.

Recall that [reflexive graphs](graph-theory.reflexive-graphs.md) are said to be
discrete if the edge relation is
[torsorial](foundation-core.torsorial-type-families.md). The condition that a
directed graph is discrete compares to the condition that a reflexive graph is
discrete in the sense that in both cases discreteness implies initiality of the
edge relation: The empty relation is the initial relation, while the identity
relation is the initial reflexive relation.

One may wonder if the torsoriality condition of discreteness shouldn't directly
carry over to the discreteness condition on directed graphs. Indeed, an earlier
implementation of discreteness in agda-unimath had this faulty definition.
However, this leads to examples that are not typically considered discrete.
Consider, for example, the directed graph with `V := ℕ` the
[natural numbers](elementary-number-theory.natural-numbers.md) and
`E m n := (m + 1 ＝ n)` as in

```text
  0 ---> 1 ---> 2 ---> ⋯.
```

This directed graph satisfies the condition that the type family `E m` is
torsorial for every `m : ℕ`, simply because `E` is a
[functional correspondence](foundation.functional-correspondences.md). However,
this graph is not considered discrete since it relates distinct vertices.

## Definitions

### The predicate on graphs of being discrete

<pre class="Agda"><a id="2477" class="Keyword">module</a> <a id="2484" href="graph-theory.discrete-directed-graphs.html#2484" class="Module">_</a>
  <a id="2488" class="Symbol">{</a><a id="2489" href="graph-theory.discrete-directed-graphs.html#2489" class="Bound">l1</a> <a id="2492" href="graph-theory.discrete-directed-graphs.html#2492" class="Bound">l2</a> <a id="2495" class="Symbol">:</a> <a id="2497" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2502" class="Symbol">}</a> <a id="2504" class="Symbol">(</a><a id="2505" href="graph-theory.discrete-directed-graphs.html#2505" class="Bound">G</a> <a id="2507" class="Symbol">:</a> <a id="2509" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="2524" href="graph-theory.discrete-directed-graphs.html#2489" class="Bound">l1</a> <a id="2527" href="graph-theory.discrete-directed-graphs.html#2492" class="Bound">l2</a><a id="2529" class="Symbol">)</a>
  <a id="2533" class="Keyword">where</a>

  <a id="2542" href="graph-theory.discrete-directed-graphs.html#2542" class="Function">is-discrete-prop-Directed-Graph</a> <a id="2574" class="Symbol">:</a> <a id="2576" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2581" class="Symbol">(</a><a id="2582" href="graph-theory.discrete-directed-graphs.html#2489" class="Bound">l1</a> <a id="2585" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2587" href="graph-theory.discrete-directed-graphs.html#2492" class="Bound">l2</a><a id="2589" class="Symbol">)</a>
  <a id="2593" href="graph-theory.discrete-directed-graphs.html#2542" class="Function">is-discrete-prop-Directed-Graph</a> <a id="2625" class="Symbol">=</a>
    <a id="2631" href="foundation.discrete-binary-relations.html#1804" class="Function">is-discrete-prop-Relation</a> <a id="2657" class="Symbol">(</a><a id="2658" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="2678" href="graph-theory.discrete-directed-graphs.html#2505" class="Bound">G</a><a id="2679" class="Symbol">)</a>

  <a id="2684" href="graph-theory.discrete-directed-graphs.html#2684" class="Function">is-discrete-Directed-Graph</a> <a id="2711" class="Symbol">:</a> <a id="2713" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2716" class="Symbol">(</a><a id="2717" href="graph-theory.discrete-directed-graphs.html#2489" class="Bound">l1</a> <a id="2720" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2722" href="graph-theory.discrete-directed-graphs.html#2492" class="Bound">l2</a><a id="2724" class="Symbol">)</a>
  <a id="2728" href="graph-theory.discrete-directed-graphs.html#2684" class="Function">is-discrete-Directed-Graph</a> <a id="2755" class="Symbol">=</a>
    <a id="2761" href="foundation.discrete-binary-relations.html#1940" class="Function">is-discrete-Relation</a> <a id="2782" class="Symbol">(</a><a id="2783" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="2803" href="graph-theory.discrete-directed-graphs.html#2505" class="Bound">G</a><a id="2804" class="Symbol">)</a>

  <a id="2809" href="graph-theory.discrete-directed-graphs.html#2809" class="Function">is-prop-is-discrete-Directed-Graph</a> <a id="2844" class="Symbol">:</a>
    <a id="2850" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2858" href="graph-theory.discrete-directed-graphs.html#2684" class="Function">is-discrete-Directed-Graph</a>
  <a id="2887" href="graph-theory.discrete-directed-graphs.html#2809" class="Function">is-prop-is-discrete-Directed-Graph</a> <a id="2922" class="Symbol">=</a>
    <a id="2928" href="foundation.discrete-binary-relations.html#2040" class="Function">is-prop-is-discrete-Relation</a> <a id="2957" class="Symbol">(</a><a id="2958" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="2978" href="graph-theory.discrete-directed-graphs.html#2505" class="Bound">G</a><a id="2979" class="Symbol">)</a>
</pre>
### The standard discrete directed graph

<pre class="Agda"><a id="3036" class="Keyword">module</a> <a id="3043" href="graph-theory.discrete-directed-graphs.html#3043" class="Module">_</a>
  <a id="3047" class="Symbol">{</a><a id="3048" href="graph-theory.discrete-directed-graphs.html#3048" class="Bound">l</a> <a id="3050" class="Symbol">:</a> <a id="3052" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3057" class="Symbol">}</a> <a id="3059" class="Symbol">(</a><a id="3060" href="graph-theory.discrete-directed-graphs.html#3060" class="Bound">A</a> <a id="3062" class="Symbol">:</a> <a id="3064" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3067" href="graph-theory.discrete-directed-graphs.html#3048" class="Bound">l</a><a id="3068" class="Symbol">)</a>
  <a id="3072" class="Keyword">where</a>

  <a id="3081" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="3105" class="Symbol">:</a> <a id="3107" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="3122" href="graph-theory.discrete-directed-graphs.html#3048" class="Bound">l</a> <a id="3124" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="3132" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3136" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="3160" class="Symbol">=</a> <a id="3162" href="graph-theory.discrete-directed-graphs.html#3060" class="Bound">A</a>
  <a id="3166" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3170" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="3194" href="graph-theory.discrete-directed-graphs.html#3194" class="Bound">x</a> <a id="3196" href="graph-theory.discrete-directed-graphs.html#3196" class="Bound">y</a> <a id="3198" class="Symbol">=</a> <a id="3200" href="foundation-core.empty-types.html#801" class="Datatype">empty</a>
</pre>
## Properties

### Morphisms from a standard discrete directed graph are maps into vertices

<pre class="Agda"><a id="3312" class="Keyword">module</a> <a id="3319" href="graph-theory.discrete-directed-graphs.html#3319" class="Module">_</a>
  <a id="3323" class="Symbol">{</a><a id="3324" href="graph-theory.discrete-directed-graphs.html#3324" class="Bound">l1</a> <a id="3327" href="graph-theory.discrete-directed-graphs.html#3327" class="Bound">l2</a> <a id="3330" href="graph-theory.discrete-directed-graphs.html#3330" class="Bound">l3</a> <a id="3333" class="Symbol">:</a> <a id="3335" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3340" class="Symbol">}</a> <a id="3342" class="Symbol">{</a><a id="3343" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a> <a id="3345" class="Symbol">:</a> <a id="3347" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3350" href="graph-theory.discrete-directed-graphs.html#3324" class="Bound">l1</a><a id="3352" class="Symbol">}</a> <a id="3354" class="Symbol">(</a><a id="3355" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a> <a id="3357" class="Symbol">:</a> <a id="3359" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="3374" href="graph-theory.discrete-directed-graphs.html#3324" class="Bound">l1</a> <a id="3377" href="graph-theory.discrete-directed-graphs.html#3327" class="Bound">l2</a><a id="3379" class="Symbol">)</a>
  <a id="3383" class="Keyword">where</a>

  <a id="3392" href="graph-theory.discrete-directed-graphs.html#3392" class="Function">ev-hom-discrete-Directed-Graph</a> <a id="3423" class="Symbol">:</a>
    <a id="3429" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="3448" class="Symbol">(</a><a id="3449" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="3473" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a><a id="3474" class="Symbol">)</a> <a id="3476" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a> <a id="3478" class="Symbol">→</a>
    <a id="3484" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a> <a id="3486" class="Symbol">→</a> <a id="3488" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="3510" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a>
  <a id="3514" href="graph-theory.discrete-directed-graphs.html#3392" class="Function">ev-hom-discrete-Directed-Graph</a> <a id="3545" class="Symbol">=</a>
    <a id="3551" href="graph-theory.morphisms-directed-graphs.html#1534" class="Function">vertex-hom-Directed-Graph</a> <a id="3577" class="Symbol">(</a><a id="3578" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="3602" class="Symbol">_)</a> <a id="3605" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a>

  <a id="3610" href="graph-theory.discrete-directed-graphs.html#3610" class="Function">map-inv-ev-hom-discrete-Directed-Graph</a> <a id="3649" class="Symbol">:</a>
    <a id="3655" class="Symbol">(</a><a id="3656" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a> <a id="3658" class="Symbol">→</a> <a id="3660" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="3682" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a><a id="3683" class="Symbol">)</a> <a id="3685" class="Symbol">→</a>
    <a id="3691" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="3710" class="Symbol">(</a><a id="3711" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="3735" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a><a id="3736" class="Symbol">)</a> <a id="3738" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a>
  <a id="3742" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3746" class="Symbol">(</a><a id="3747" href="graph-theory.discrete-directed-graphs.html#3610" class="Function">map-inv-ev-hom-discrete-Directed-Graph</a> <a id="3786" href="graph-theory.discrete-directed-graphs.html#3786" class="Bound">f</a><a id="3787" class="Symbol">)</a> <a id="3789" class="Symbol">=</a> <a id="3791" href="graph-theory.discrete-directed-graphs.html#3786" class="Bound">f</a>
  <a id="3795" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3799" class="Symbol">(</a><a id="3800" href="graph-theory.discrete-directed-graphs.html#3610" class="Function">map-inv-ev-hom-discrete-Directed-Graph</a> <a id="3839" href="graph-theory.discrete-directed-graphs.html#3839" class="Bound">f</a><a id="3840" class="Symbol">)</a> <a id="3842" href="graph-theory.discrete-directed-graphs.html#3842" class="Bound">x</a> <a id="3844" href="graph-theory.discrete-directed-graphs.html#3844" class="Bound">y</a> <a id="3846" class="Symbol">()</a>

  <a id="3852" href="graph-theory.discrete-directed-graphs.html#3852" class="Function">is-section-map-inv-ev-hom-discrete-Directed-Graph</a> <a id="3902" class="Symbol">:</a>
    <a id="3908" href="foundation-core.sections.html#1194" class="Function">is-section</a>
      <a id="3925" class="Symbol">(</a> <a id="3927" href="graph-theory.discrete-directed-graphs.html#3392" class="Function">ev-hom-discrete-Directed-Graph</a><a id="3957" class="Symbol">)</a>
      <a id="3965" class="Symbol">(</a> <a id="3967" href="graph-theory.discrete-directed-graphs.html#3610" class="Function">map-inv-ev-hom-discrete-Directed-Graph</a><a id="4005" class="Symbol">)</a>
  <a id="4009" href="graph-theory.discrete-directed-graphs.html#3852" class="Function">is-section-map-inv-ev-hom-discrete-Directed-Graph</a> <a id="4059" href="graph-theory.discrete-directed-graphs.html#4059" class="Bound">f</a> <a id="4061" class="Symbol">=</a> <a id="4063" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="4071" href="graph-theory.discrete-directed-graphs.html#4071" class="Function">htpy-is-retraction-map-inv-ev-hom-discrete-Directed-Graph</a> <a id="4129" class="Symbol">:</a>
    <a id="4135" class="Symbol">(</a><a id="4136" href="graph-theory.discrete-directed-graphs.html#4136" class="Bound">f</a> <a id="4138" class="Symbol">:</a> <a id="4140" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="4159" class="Symbol">(</a><a id="4160" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="4184" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a><a id="4185" class="Symbol">)</a> <a id="4187" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a><a id="4188" class="Symbol">)</a> <a id="4190" class="Symbol">→</a>
    <a id="4196" href="graph-theory.morphisms-directed-graphs.html#4239" class="Function">htpy-hom-Directed-Graph</a>
      <a id="4226" class="Symbol">(</a> <a id="4228" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="4252" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a><a id="4253" class="Symbol">)</a>
      <a id="4261" class="Symbol">(</a> <a id="4263" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a><a id="4264" class="Symbol">)</a>
      <a id="4272" class="Symbol">(</a> <a id="4274" href="graph-theory.discrete-directed-graphs.html#3610" class="Function">map-inv-ev-hom-discrete-Directed-Graph</a>
        <a id="4321" class="Symbol">(</a> <a id="4323" href="graph-theory.discrete-directed-graphs.html#3392" class="Function">ev-hom-discrete-Directed-Graph</a> <a id="4354" href="graph-theory.discrete-directed-graphs.html#4136" class="Bound">f</a><a id="4355" class="Symbol">))</a>
      <a id="4364" class="Symbol">(</a> <a id="4366" href="graph-theory.discrete-directed-graphs.html#4136" class="Bound">f</a><a id="4367" class="Symbol">)</a>
  <a id="4371" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4375" class="Symbol">(</a><a id="4376" href="graph-theory.discrete-directed-graphs.html#4071" class="Function">htpy-is-retraction-map-inv-ev-hom-discrete-Directed-Graph</a> <a id="4434" href="graph-theory.discrete-directed-graphs.html#4434" class="Bound">f</a><a id="4435" class="Symbol">)</a> <a id="4437" class="Symbol">=</a>
    <a id="4443" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="4455" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4459" class="Symbol">(</a><a id="4460" href="graph-theory.discrete-directed-graphs.html#4071" class="Function">htpy-is-retraction-map-inv-ev-hom-discrete-Directed-Graph</a> <a id="4518" href="graph-theory.discrete-directed-graphs.html#4518" class="Bound">f</a><a id="4519" class="Symbol">)</a> <a id="4521" href="graph-theory.discrete-directed-graphs.html#4521" class="Bound">x</a> <a id="4523" href="graph-theory.discrete-directed-graphs.html#4523" class="Bound">y</a> <a id="4525" class="Symbol">()</a>

  <a id="4531" href="graph-theory.discrete-directed-graphs.html#4531" class="Function">is-retraction-map-inv-ev-hom-discrete-Directed-Graph</a> <a id="4584" class="Symbol">:</a>
    <a id="4590" href="foundation-core.retractions.html#790" class="Function">is-retraction</a>
      <a id="4610" class="Symbol">(</a> <a id="4612" href="graph-theory.discrete-directed-graphs.html#3392" class="Function">ev-hom-discrete-Directed-Graph</a><a id="4642" class="Symbol">)</a>
      <a id="4650" class="Symbol">(</a> <a id="4652" href="graph-theory.discrete-directed-graphs.html#3610" class="Function">map-inv-ev-hom-discrete-Directed-Graph</a><a id="4690" class="Symbol">)</a>
  <a id="4694" href="graph-theory.discrete-directed-graphs.html#4531" class="Function">is-retraction-map-inv-ev-hom-discrete-Directed-Graph</a> <a id="4747" href="graph-theory.discrete-directed-graphs.html#4747" class="Bound">f</a> <a id="4749" class="Symbol">=</a>
    <a id="4755" href="graph-theory.morphisms-directed-graphs.html#6776" class="Function">eq-htpy-hom-Directed-Graph</a>
      <a id="4788" class="Symbol">(</a> <a id="4790" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="4814" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a><a id="4815" class="Symbol">)</a>
      <a id="4823" class="Symbol">(</a> <a id="4825" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a><a id="4826" class="Symbol">)</a>
      <a id="4834" class="Symbol">(</a> <a id="4836" href="graph-theory.discrete-directed-graphs.html#3610" class="Function">map-inv-ev-hom-discrete-Directed-Graph</a>
        <a id="4883" class="Symbol">(</a> <a id="4885" href="graph-theory.discrete-directed-graphs.html#3392" class="Function">ev-hom-discrete-Directed-Graph</a> <a id="4916" href="graph-theory.discrete-directed-graphs.html#4747" class="Bound">f</a><a id="4917" class="Symbol">))</a>
      <a id="4926" class="Symbol">(</a> <a id="4928" href="graph-theory.discrete-directed-graphs.html#4747" class="Bound">f</a><a id="4929" class="Symbol">)</a>
      <a id="4937" class="Symbol">(</a> <a id="4939" href="graph-theory.discrete-directed-graphs.html#4071" class="Function">htpy-is-retraction-map-inv-ev-hom-discrete-Directed-Graph</a> <a id="4997" href="graph-theory.discrete-directed-graphs.html#4747" class="Bound">f</a><a id="4998" class="Symbol">)</a>

  <a id="5003" class="Keyword">abstract</a>
    <a id="5016" href="graph-theory.discrete-directed-graphs.html#5016" class="Function">is-equiv-ev-hom-discrete-Directed-Graph</a> <a id="5056" class="Symbol">:</a>
      <a id="5064" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="5073" href="graph-theory.discrete-directed-graphs.html#3392" class="Function">ev-hom-discrete-Directed-Graph</a>
    <a id="5108" href="graph-theory.discrete-directed-graphs.html#5016" class="Function">is-equiv-ev-hom-discrete-Directed-Graph</a> <a id="5148" class="Symbol">=</a>
      <a id="5156" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
        <a id="5187" href="graph-theory.discrete-directed-graphs.html#3610" class="Function">map-inv-ev-hom-discrete-Directed-Graph</a>
        <a id="5234" href="graph-theory.discrete-directed-graphs.html#3852" class="Function">is-section-map-inv-ev-hom-discrete-Directed-Graph</a>
        <a id="5292" href="graph-theory.discrete-directed-graphs.html#4531" class="Function">is-retraction-map-inv-ev-hom-discrete-Directed-Graph</a>

  <a id="5348" href="graph-theory.discrete-directed-graphs.html#5348" class="Function">ev-equiv-hom-discrete-Directed-Graph</a> <a id="5385" class="Symbol">:</a>
    <a id="5391" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="5410" class="Symbol">(</a><a id="5411" href="graph-theory.discrete-directed-graphs.html#3081" class="Function">discrete-Directed-Graph</a> <a id="5435" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a><a id="5436" class="Symbol">)</a> <a id="5438" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a> <a id="5440" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="5446" class="Symbol">(</a><a id="5447" href="graph-theory.discrete-directed-graphs.html#3343" class="Bound">A</a> <a id="5449" class="Symbol">→</a> <a id="5451" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="5473" href="graph-theory.discrete-directed-graphs.html#3355" class="Bound">G</a><a id="5474" class="Symbol">)</a>
  <a id="5478" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5482" href="graph-theory.discrete-directed-graphs.html#5348" class="Function">ev-equiv-hom-discrete-Directed-Graph</a> <a id="5519" class="Symbol">=</a>
    <a id="5525" href="graph-theory.discrete-directed-graphs.html#3392" class="Function">ev-hom-discrete-Directed-Graph</a>
  <a id="5558" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5562" href="graph-theory.discrete-directed-graphs.html#5348" class="Function">ev-equiv-hom-discrete-Directed-Graph</a> <a id="5599" class="Symbol">=</a>
    <a id="5605" href="graph-theory.discrete-directed-graphs.html#5016" class="Function">is-equiv-ev-hom-discrete-Directed-Graph</a>
</pre>
## See also

- [Discrete reflexive graphs](graph-theory.discrete-reflexive-graphs.md)
