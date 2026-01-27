# Discrete reflexive graphs

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="graph-theory.discrete-reflexive-graphs.html" class="Module">graph-theory.discrete-reflexive-graphs</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.discrete-reflexive-relations.html" class="Module">foundation.discrete-reflexive-relations</a>
<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="318" class="Keyword">open</a> <a id="323" class="Keyword">import</a> <a id="330" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="402" class="Keyword">open</a> <a id="407" class="Keyword">import</a> <a id="414" href="foundation-core.torsorial-type-families.html" class="Module">foundation-core.torsorial-type-families</a>

<a id="455" class="Keyword">open</a> <a id="460" class="Keyword">import</a> <a id="467" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="496" class="Keyword">open</a> <a id="501" class="Keyword">import</a> <a id="508" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
</pre>
</details>

## Idea

A [reflexive graph](graph-theory.reflexive-graphs.md) `G ≐ (V , E , r)` is said
to be
{{#concept "discrete" Disambiguation="reflexive graph" Agda=is-discrete-Reflexive-Graph}}
if, for every vertex `x : V`, the type family of edges with source `x`, `E x`,
is [torsorial](foundation-core.torsorial-type-families.md). In other words, if
the [dependent sum](foundation.dependent-pair-types.md) `Σ (y : V), (E x y)` is
[contractible](foundation-core.contractible-types.md) for every `x`. The
{{#concept "standard discrete graph"}} associated to a type `X` is the reflexive
graph whose vertices are elements of `X`, and edges are
[identifications](foundation-core.identity-types.md),

```text
  E x y := (x ＝ y).
```

For any type `A` there is a
{{#concept "standard discrete reflexive graph" Agda=standard-Discrete-Reflexive-Graph}}
`Δ A`, which is defined by

```text
  (Δ A)₀ := A
  (Δ A)₁ := Id A
  refl (Δ A) := refl
```

Since torsorial type families are
[identity systems](foundation.identity-systems.md), it follows that a reflexive
graph is discrete precisely when its edge relation is initial. In other words,
the inclusion of the discrete reflexive graphs into the reflexive graphs
satisfies the universal property of being left adjoint to the forgetful functor
`G ↦ Δ G₀`, mapping a reflexive graph to the standard discrete graph on its type
of vertices.

## Definitions

### The predicate on reflexive graphs of being discrete

<pre class="Agda"><a id="2007" class="Keyword">module</a> <a id="2014" href="graph-theory.discrete-reflexive-graphs.html#2014" class="Module">_</a>
  <a id="2018" class="Symbol">{</a><a id="2019" href="graph-theory.discrete-reflexive-graphs.html#2019" class="Bound">l1</a> <a id="2022" href="graph-theory.discrete-reflexive-graphs.html#2022" class="Bound">l2</a> <a id="2025" class="Symbol">:</a> <a id="2027" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2032" class="Symbol">}</a> <a id="2034" class="Symbol">(</a><a id="2035" href="graph-theory.discrete-reflexive-graphs.html#2035" class="Bound">G</a> <a id="2037" class="Symbol">:</a> <a id="2039" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="2055" href="graph-theory.discrete-reflexive-graphs.html#2019" class="Bound">l1</a> <a id="2058" href="graph-theory.discrete-reflexive-graphs.html#2022" class="Bound">l2</a><a id="2060" class="Symbol">)</a>
  <a id="2064" class="Keyword">where</a>

  <a id="2073" href="graph-theory.discrete-reflexive-graphs.html#2073" class="Function">is-discrete-prop-Reflexive-Graph</a> <a id="2106" class="Symbol">:</a> <a id="2108" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2113" class="Symbol">(</a><a id="2114" href="graph-theory.discrete-reflexive-graphs.html#2019" class="Bound">l1</a> <a id="2117" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2119" href="graph-theory.discrete-reflexive-graphs.html#2022" class="Bound">l2</a><a id="2121" class="Symbol">)</a>
  <a id="2125" href="graph-theory.discrete-reflexive-graphs.html#2073" class="Function">is-discrete-prop-Reflexive-Graph</a> <a id="2158" class="Symbol">=</a>
    <a id="2164" href="foundation.discrete-reflexive-relations.html#1331" class="Function">is-discrete-prop-Reflexive-Relation</a>
      <a id="2206" class="Symbol">(</a> <a id="2208" href="graph-theory.reflexive-graphs.html#1345" class="Function">edge-reflexive-relation-Reflexive-Graph</a> <a id="2248" href="graph-theory.discrete-reflexive-graphs.html#2035" class="Bound">G</a><a id="2249" class="Symbol">)</a>

  <a id="2254" href="graph-theory.discrete-reflexive-graphs.html#2254" class="Function">is-discrete-Reflexive-Graph</a> <a id="2282" class="Symbol">:</a> <a id="2284" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2287" class="Symbol">(</a><a id="2288" href="graph-theory.discrete-reflexive-graphs.html#2019" class="Bound">l1</a> <a id="2291" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2293" href="graph-theory.discrete-reflexive-graphs.html#2022" class="Bound">l2</a><a id="2295" class="Symbol">)</a>
  <a id="2299" href="graph-theory.discrete-reflexive-graphs.html#2254" class="Function">is-discrete-Reflexive-Graph</a> <a id="2327" class="Symbol">=</a>
    <a id="2333" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2343" href="graph-theory.discrete-reflexive-graphs.html#2073" class="Function">is-discrete-prop-Reflexive-Graph</a>

  <a id="2379" href="graph-theory.discrete-reflexive-graphs.html#2379" class="Function">is-prop-is-discrete-Reflexive-Graph</a> <a id="2415" class="Symbol">:</a> <a id="2417" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2425" href="graph-theory.discrete-reflexive-graphs.html#2254" class="Function">is-discrete-Reflexive-Graph</a>
  <a id="2455" href="graph-theory.discrete-reflexive-graphs.html#2379" class="Function">is-prop-is-discrete-Reflexive-Graph</a> <a id="2491" class="Symbol">=</a>
    <a id="2497" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2515" href="graph-theory.discrete-reflexive-graphs.html#2073" class="Function">is-discrete-prop-Reflexive-Graph</a>
</pre>
### Discrete reflexive graphs

<pre class="Agda"><a id="2592" class="Keyword">module</a> <a id="2599" href="graph-theory.discrete-reflexive-graphs.html#2599" class="Module">_</a>
  <a id="2603" class="Symbol">(</a><a id="2604" href="graph-theory.discrete-reflexive-graphs.html#2604" class="Bound">l1</a> <a id="2607" href="graph-theory.discrete-reflexive-graphs.html#2607" class="Bound">l2</a> <a id="2610" class="Symbol">:</a> <a id="2612" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2617" class="Symbol">)</a>
  <a id="2621" class="Keyword">where</a>

  <a id="2630" href="graph-theory.discrete-reflexive-graphs.html#2630" class="Function">Discrete-Reflexive-Graph</a> <a id="2655" class="Symbol">:</a> <a id="2657" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2660" class="Symbol">(</a><a id="2661" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2666" href="graph-theory.discrete-reflexive-graphs.html#2604" class="Bound">l1</a> <a id="2669" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2671" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2676" href="graph-theory.discrete-reflexive-graphs.html#2607" class="Bound">l2</a><a id="2678" class="Symbol">)</a>
  <a id="2682" href="graph-theory.discrete-reflexive-graphs.html#2630" class="Function">Discrete-Reflexive-Graph</a> <a id="2707" class="Symbol">=</a>
    <a id="2713" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2715" class="Symbol">(</a><a id="2716" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="2732" href="graph-theory.discrete-reflexive-graphs.html#2604" class="Bound">l1</a> <a id="2735" href="graph-theory.discrete-reflexive-graphs.html#2607" class="Bound">l2</a><a id="2737" class="Symbol">)</a> <a id="2739" href="graph-theory.discrete-reflexive-graphs.html#2254" class="Function">is-discrete-Reflexive-Graph</a>
</pre>
### The standard discrete reflexive graph

<pre class="Agda"><a id="2823" class="Keyword">module</a> <a id="2830" href="graph-theory.discrete-reflexive-graphs.html#2830" class="Module">_</a>
  <a id="2834" class="Symbol">{</a><a id="2835" href="graph-theory.discrete-reflexive-graphs.html#2835" class="Bound">l1</a> <a id="2838" class="Symbol">:</a> <a id="2840" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2845" class="Symbol">}</a> <a id="2847" class="Symbol">(</a><a id="2848" href="graph-theory.discrete-reflexive-graphs.html#2848" class="Bound">A</a> <a id="2850" class="Symbol">:</a> <a id="2852" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2855" href="graph-theory.discrete-reflexive-graphs.html#2835" class="Bound">l1</a><a id="2857" class="Symbol">)</a>
  <a id="2861" class="Keyword">where</a>

  <a id="2870" href="graph-theory.discrete-reflexive-graphs.html#2870" class="Function">discrete-Reflexive-Graph</a> <a id="2895" class="Symbol">:</a> <a id="2897" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="2913" href="graph-theory.discrete-reflexive-graphs.html#2835" class="Bound">l1</a> <a id="2916" href="graph-theory.discrete-reflexive-graphs.html#2835" class="Bound">l1</a>
  <a id="2921" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2925" class="Symbol">(</a><a id="2926" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2930" href="graph-theory.discrete-reflexive-graphs.html#2870" class="Function">discrete-Reflexive-Graph</a><a id="2954" class="Symbol">)</a> <a id="2956" class="Symbol">=</a> <a id="2958" href="graph-theory.discrete-reflexive-graphs.html#2848" class="Bound">A</a>
  <a id="2962" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2966" class="Symbol">(</a><a id="2967" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2971" href="graph-theory.discrete-reflexive-graphs.html#2870" class="Function">discrete-Reflexive-Graph</a><a id="2995" class="Symbol">)</a> <a id="2997" class="Symbol">=</a> <a id="2999" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a>
  <a id="3004" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3008" href="graph-theory.discrete-reflexive-graphs.html#2870" class="Function">discrete-Reflexive-Graph</a> <a id="3033" href="graph-theory.discrete-reflexive-graphs.html#3033" class="Bound">x</a> <a id="3035" class="Symbol">=</a> <a id="3037" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="3045" href="graph-theory.discrete-reflexive-graphs.html#3045" class="Function">is-discrete-discrete-Reflexive-Graph</a> <a id="3082" class="Symbol">:</a>
    <a id="3088" href="graph-theory.discrete-reflexive-graphs.html#2254" class="Function">is-discrete-Reflexive-Graph</a> <a id="3116" href="graph-theory.discrete-reflexive-graphs.html#2870" class="Function">discrete-Reflexive-Graph</a>
  <a id="3143" href="graph-theory.discrete-reflexive-graphs.html#3045" class="Function">is-discrete-discrete-Reflexive-Graph</a> <a id="3180" class="Symbol">=</a>
    <a id="3186" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a>

  <a id="3205" href="graph-theory.discrete-reflexive-graphs.html#3205" class="Function">standard-Discrete-Reflexive-Graph</a> <a id="3239" class="Symbol">:</a>
    <a id="3245" href="graph-theory.discrete-reflexive-graphs.html#2630" class="Function">Discrete-Reflexive-Graph</a> <a id="3270" href="graph-theory.discrete-reflexive-graphs.html#2835" class="Bound">l1</a> <a id="3273" href="graph-theory.discrete-reflexive-graphs.html#2835" class="Bound">l1</a>
  <a id="3278" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3282" href="graph-theory.discrete-reflexive-graphs.html#3205" class="Function">standard-Discrete-Reflexive-Graph</a> <a id="3316" class="Symbol">=</a> <a id="3318" href="graph-theory.discrete-reflexive-graphs.html#2870" class="Function">discrete-Reflexive-Graph</a>
  <a id="3345" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3349" href="graph-theory.discrete-reflexive-graphs.html#3205" class="Function">standard-Discrete-Reflexive-Graph</a> <a id="3383" class="Symbol">=</a> <a id="3385" href="graph-theory.discrete-reflexive-graphs.html#3045" class="Function">is-discrete-discrete-Reflexive-Graph</a>
</pre>
## See also

- [Discrete directed graphs](graph-theory.discrete-directed-graphs.md)
- [Discrete dependent reflexive graphs](graph-theory.discrete-dependent-reflexive-graphs.md)
