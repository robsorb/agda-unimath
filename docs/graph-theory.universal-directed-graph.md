# The universal directed graph

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="graph-theory.universal-directed-graph.html" class="Module">graph-theory.universal-directed-graph</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="graph-theory.base-change-dependent-directed-graphs.html" class="Module">graph-theory.base-change-dependent-directed-graphs</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="graph-theory.dependent-directed-graphs.html" class="Module">graph-theory.dependent-directed-graphs</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="graph-theory.equivalences-dependent-directed-graphs.html" class="Module">graph-theory.equivalences-dependent-directed-graphs</a>
<a id="445" class="Keyword">open</a> <a id="450" class="Keyword">import</a> <a id="457" href="graph-theory.morphisms-directed-graphs.html" class="Module">graph-theory.morphisms-directed-graphs</a>
</pre>
</details>

## Idea

The {{#concept "universal directed graph" Agda=universal-Directed-Graph}} `𝒢 l`
at [universe level](foundation.universe-levels.md) `l` is the
[directed graph](graph-theory.directed-graphs.md) that has the universe `UU l`
as its type of vertices, and spans between types as its edges.

Specifically, the universal directed graph is a translation from category theory
into type theory of the Hofmann–Streicher universe {{#cite Awodey22}} of
presheaves on the representing pair of arrows

```text
      s
    ----->
  0 -----> 1
      t
```

The Hofmann–Streicher universe of presheaves on a category `𝒞` is the presheaf

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A *,
```

where `*` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute the instances of the slice category `⇉/I`:

- The slice category `⇉/0` is the terminal category.
- The slice category `⇉/1` is the representing cospan

  ```text
        s         t
    s -----> 1 <----- t
  ```

  The functors `s t : ⇉/0 → ⇉/1` are given by `* ↦ s` and `* ↦ t`, respectively.

This means that:

- The type of vertices of the universal directed graph is the universe of types
  `UU l`.
- The type of edges from `X` to `Y` of the universal directed graph is the type
  of spans from `X` to `Y`.

There is a
[directed graph duality theorem](graph-theory.directed-graph-duality.md), which
asserts that for any directed graph `G`, the type of
[morphisms](graph-theory.morphisms-directed-graphs.md) `hom G 𝒰` from `G` into
the universal directed graph is [equivalent](foundation-core.equivalences.md) to
the type of pairs `(H , f)` consisting of a directed graph `H` and a morphism
`f : hom H G` from `H` into `G`.

## Definitions

### The universal directed graph

<pre class="Agda"><a id="2277" class="Keyword">module</a> <a id="2284" href="graph-theory.universal-directed-graph.html#2284" class="Module">_</a>
  <a id="2288" class="Symbol">(</a><a id="2289" href="graph-theory.universal-directed-graph.html#2289" class="Bound">l1</a> <a id="2292" href="graph-theory.universal-directed-graph.html#2292" class="Bound">l2</a> <a id="2295" class="Symbol">:</a> <a id="2297" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2302" class="Symbol">)</a>
  <a id="2306" class="Keyword">where</a>

  <a id="2315" href="graph-theory.universal-directed-graph.html#2315" class="Function">vertex-universal-Directed-Graph</a> <a id="2347" class="Symbol">:</a> <a id="2349" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2352" class="Symbol">(</a><a id="2353" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2358" href="graph-theory.universal-directed-graph.html#2289" class="Bound">l1</a><a id="2360" class="Symbol">)</a>
  <a id="2364" href="graph-theory.universal-directed-graph.html#2315" class="Function">vertex-universal-Directed-Graph</a> <a id="2396" class="Symbol">=</a> <a id="2398" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2401" href="graph-theory.universal-directed-graph.html#2289" class="Bound">l1</a>

  <a id="2407" href="graph-theory.universal-directed-graph.html#2407" class="Function">edge-universal-Directed-Graph</a> <a id="2437" class="Symbol">:</a>
    <a id="2443" class="Symbol">(</a><a id="2444" href="graph-theory.universal-directed-graph.html#2444" class="Bound">X</a> <a id="2446" href="graph-theory.universal-directed-graph.html#2446" class="Bound">Y</a> <a id="2448" class="Symbol">:</a> <a id="2450" href="graph-theory.universal-directed-graph.html#2315" class="Function">vertex-universal-Directed-Graph</a><a id="2481" class="Symbol">)</a> <a id="2483" class="Symbol">→</a> <a id="2485" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2488" class="Symbol">(</a><a id="2489" href="graph-theory.universal-directed-graph.html#2289" class="Bound">l1</a> <a id="2492" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2494" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2499" href="graph-theory.universal-directed-graph.html#2292" class="Bound">l2</a><a id="2501" class="Symbol">)</a>
  <a id="2505" href="graph-theory.universal-directed-graph.html#2407" class="Function">edge-universal-Directed-Graph</a> <a id="2535" href="graph-theory.universal-directed-graph.html#2535" class="Bound">X</a> <a id="2537" href="graph-theory.universal-directed-graph.html#2537" class="Bound">Y</a> <a id="2539" class="Symbol">=</a> <a id="2541" href="graph-theory.universal-directed-graph.html#2535" class="Bound">X</a> <a id="2543" class="Symbol">→</a> <a id="2545" href="graph-theory.universal-directed-graph.html#2537" class="Bound">Y</a> <a id="2547" class="Symbol">→</a> <a id="2549" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2552" href="graph-theory.universal-directed-graph.html#2292" class="Bound">l2</a>

  <a id="2558" href="graph-theory.universal-directed-graph.html#2558" class="Function">universal-Directed-Graph</a> <a id="2583" class="Symbol">:</a> <a id="2585" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="2600" class="Symbol">(</a><a id="2601" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2606" href="graph-theory.universal-directed-graph.html#2289" class="Bound">l1</a><a id="2608" class="Symbol">)</a> <a id="2610" class="Symbol">(</a><a id="2611" href="graph-theory.universal-directed-graph.html#2289" class="Bound">l1</a> <a id="2614" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2616" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2621" href="graph-theory.universal-directed-graph.html#2292" class="Bound">l2</a><a id="2623" class="Symbol">)</a>
  <a id="2627" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2631" href="graph-theory.universal-directed-graph.html#2558" class="Function">universal-Directed-Graph</a> <a id="2656" class="Symbol">=</a> <a id="2658" href="graph-theory.universal-directed-graph.html#2315" class="Function">vertex-universal-Directed-Graph</a>
  <a id="2692" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2696" href="graph-theory.universal-directed-graph.html#2558" class="Function">universal-Directed-Graph</a> <a id="2721" class="Symbol">=</a> <a id="2723" href="graph-theory.universal-directed-graph.html#2407" class="Function">edge-universal-Directed-Graph</a>
</pre>
### The universal dependent directed graph

<pre class="Agda"><a id="2810" class="Keyword">module</a> <a id="2817" href="graph-theory.universal-directed-graph.html#2817" class="Module">_</a>
  <a id="2821" class="Symbol">(</a><a id="2822" href="graph-theory.universal-directed-graph.html#2822" class="Bound">l1</a> <a id="2825" href="graph-theory.universal-directed-graph.html#2825" class="Bound">l2</a> <a id="2828" class="Symbol">:</a> <a id="2830" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2835" class="Symbol">)</a>
  <a id="2839" class="Keyword">where</a>

  <a id="2848" href="graph-theory.universal-directed-graph.html#2848" class="Function">vertex-universal-Dependent-Directed-Graph</a> <a id="2890" class="Symbol">:</a>
    <a id="2896" href="graph-theory.universal-directed-graph.html#2315" class="Function">vertex-universal-Directed-Graph</a> <a id="2928" href="graph-theory.universal-directed-graph.html#2822" class="Bound">l1</a> <a id="2931" href="graph-theory.universal-directed-graph.html#2825" class="Bound">l2</a> <a id="2934" class="Symbol">→</a> <a id="2936" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2939" href="graph-theory.universal-directed-graph.html#2822" class="Bound">l1</a>
  <a id="2944" href="graph-theory.universal-directed-graph.html#2848" class="Function">vertex-universal-Dependent-Directed-Graph</a> <a id="2986" href="graph-theory.universal-directed-graph.html#2986" class="Bound">X</a> <a id="2988" class="Symbol">=</a> <a id="2990" href="graph-theory.universal-directed-graph.html#2986" class="Bound">X</a>

  <a id="2995" href="graph-theory.universal-directed-graph.html#2995" class="Function">edge-universal-Dependent-Directed-Graph</a> <a id="3035" class="Symbol">:</a>
    <a id="3041" class="Symbol">{</a><a id="3042" href="graph-theory.universal-directed-graph.html#3042" class="Bound">X</a> <a id="3044" href="graph-theory.universal-directed-graph.html#3044" class="Bound">Y</a> <a id="3046" class="Symbol">:</a> <a id="3048" href="graph-theory.universal-directed-graph.html#2315" class="Function">vertex-universal-Directed-Graph</a> <a id="3080" href="graph-theory.universal-directed-graph.html#2822" class="Bound">l1</a> <a id="3083" href="graph-theory.universal-directed-graph.html#2825" class="Bound">l2</a><a id="3085" class="Symbol">}</a>
    <a id="3091" class="Symbol">(</a><a id="3092" href="graph-theory.universal-directed-graph.html#3092" class="Bound">R</a> <a id="3094" class="Symbol">:</a> <a id="3096" href="graph-theory.universal-directed-graph.html#2407" class="Function">edge-universal-Directed-Graph</a> <a id="3126" href="graph-theory.universal-directed-graph.html#2822" class="Bound">l1</a> <a id="3129" href="graph-theory.universal-directed-graph.html#2825" class="Bound">l2</a> <a id="3132" href="graph-theory.universal-directed-graph.html#3042" class="Bound">X</a> <a id="3134" href="graph-theory.universal-directed-graph.html#3044" class="Bound">Y</a><a id="3135" class="Symbol">)</a> <a id="3137" class="Symbol">→</a>
    <a id="3143" href="graph-theory.universal-directed-graph.html#2848" class="Function">vertex-universal-Dependent-Directed-Graph</a> <a id="3185" href="graph-theory.universal-directed-graph.html#3042" class="Bound">X</a> <a id="3187" class="Symbol">→</a>
    <a id="3193" href="graph-theory.universal-directed-graph.html#2848" class="Function">vertex-universal-Dependent-Directed-Graph</a> <a id="3235" href="graph-theory.universal-directed-graph.html#3044" class="Bound">Y</a> <a id="3237" class="Symbol">→</a> <a id="3239" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3242" href="graph-theory.universal-directed-graph.html#2825" class="Bound">l2</a>
  <a id="3247" href="graph-theory.universal-directed-graph.html#2995" class="Function">edge-universal-Dependent-Directed-Graph</a> <a id="3287" href="graph-theory.universal-directed-graph.html#3287" class="Bound">R</a> <a id="3289" href="graph-theory.universal-directed-graph.html#3289" class="Bound">x</a> <a id="3291" href="graph-theory.universal-directed-graph.html#3291" class="Bound">y</a> <a id="3293" class="Symbol">=</a> <a id="3295" href="graph-theory.universal-directed-graph.html#3287" class="Bound">R</a> <a id="3297" href="graph-theory.universal-directed-graph.html#3289" class="Bound">x</a> <a id="3299" href="graph-theory.universal-directed-graph.html#3291" class="Bound">y</a>

  <a id="3304" href="graph-theory.universal-directed-graph.html#3304" class="Function">universal-Dependent-Directed-Graph</a> <a id="3339" class="Symbol">:</a>
    <a id="3345" href="graph-theory.dependent-directed-graphs.html#1231" class="Function">Dependent-Directed-Graph</a> <a id="3370" href="graph-theory.universal-directed-graph.html#2822" class="Bound">l1</a> <a id="3373" href="graph-theory.universal-directed-graph.html#2825" class="Bound">l2</a> <a id="3376" class="Symbol">(</a><a id="3377" href="graph-theory.universal-directed-graph.html#2558" class="Function">universal-Directed-Graph</a> <a id="3402" href="graph-theory.universal-directed-graph.html#2822" class="Bound">l1</a> <a id="3405" href="graph-theory.universal-directed-graph.html#2825" class="Bound">l2</a><a id="3407" class="Symbol">)</a>
  <a id="3411" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3415" href="graph-theory.universal-directed-graph.html#3304" class="Function">universal-Dependent-Directed-Graph</a> <a id="3450" class="Symbol">=</a>
    <a id="3456" href="graph-theory.universal-directed-graph.html#2848" class="Function">vertex-universal-Dependent-Directed-Graph</a>
  <a id="3500" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3504" href="graph-theory.universal-directed-graph.html#3304" class="Function">universal-Dependent-Directed-Graph</a> <a id="3539" class="Symbol">_</a> <a id="3541" class="Symbol">_</a> <a id="3543" class="Symbol">=</a>
    <a id="3549" href="graph-theory.universal-directed-graph.html#2995" class="Function">edge-universal-Dependent-Directed-Graph</a>
</pre>
## Properties

### Every dependent directed graph is a base change of the universal dependent directed graph

#### The characteristic morphism of a dependent directed graph

<pre class="Agda"><a id="3776" class="Keyword">module</a> <a id="3783" href="graph-theory.universal-directed-graph.html#3783" class="Module">_</a>
  <a id="3787" class="Symbol">{</a><a id="3788" href="graph-theory.universal-directed-graph.html#3788" class="Bound">l1</a> <a id="3791" href="graph-theory.universal-directed-graph.html#3791" class="Bound">l2</a> <a id="3794" href="graph-theory.universal-directed-graph.html#3794" class="Bound">l3</a> <a id="3797" href="graph-theory.universal-directed-graph.html#3797" class="Bound">l4</a> <a id="3800" class="Symbol">:</a> <a id="3802" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3807" class="Symbol">}</a>
  <a id="3811" class="Symbol">{</a><a id="3812" href="graph-theory.universal-directed-graph.html#3812" class="Bound">G</a> <a id="3814" class="Symbol">:</a> <a id="3816" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="3831" href="graph-theory.universal-directed-graph.html#3788" class="Bound">l1</a> <a id="3834" href="graph-theory.universal-directed-graph.html#3791" class="Bound">l2</a><a id="3836" class="Symbol">}</a> <a id="3838" class="Symbol">(</a><a id="3839" href="graph-theory.universal-directed-graph.html#3839" class="Bound">H</a> <a id="3841" class="Symbol">:</a> <a id="3843" href="graph-theory.dependent-directed-graphs.html#1231" class="Function">Dependent-Directed-Graph</a> <a id="3868" href="graph-theory.universal-directed-graph.html#3794" class="Bound">l3</a> <a id="3871" href="graph-theory.universal-directed-graph.html#3797" class="Bound">l4</a> <a id="3874" href="graph-theory.universal-directed-graph.html#3812" class="Bound">G</a><a id="3875" class="Symbol">)</a>
  <a id="3879" class="Keyword">where</a>

  <a id="3888" href="graph-theory.universal-directed-graph.html#3888" class="Function">vertex-characteristic-hom-Dependent-Directed-Graph</a> <a id="3939" class="Symbol">:</a>
    <a id="3945" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="3967" href="graph-theory.universal-directed-graph.html#3812" class="Bound">G</a> <a id="3969" class="Symbol">→</a> <a id="3971" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3974" href="graph-theory.universal-directed-graph.html#3794" class="Bound">l3</a>
  <a id="3979" href="graph-theory.universal-directed-graph.html#3888" class="Function">vertex-characteristic-hom-Dependent-Directed-Graph</a> <a id="4030" class="Symbol">=</a>
    <a id="4036" href="graph-theory.dependent-directed-graphs.html#1647" class="Function">vertex-Dependent-Directed-Graph</a> <a id="4068" href="graph-theory.universal-directed-graph.html#3839" class="Bound">H</a>

  <a id="4073" href="graph-theory.universal-directed-graph.html#4073" class="Function">edge-characteristic-hom-Dependent-Directed-Graph</a> <a id="4122" class="Symbol">:</a>
    <a id="4128" class="Symbol">{</a><a id="4129" href="graph-theory.universal-directed-graph.html#4129" class="Bound">x</a> <a id="4131" href="graph-theory.universal-directed-graph.html#4131" class="Bound">y</a> <a id="4133" class="Symbol">:</a> <a id="4135" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="4157" href="graph-theory.universal-directed-graph.html#3812" class="Bound">G</a><a id="4158" class="Symbol">}</a> <a id="4160" class="Symbol">(</a><a id="4161" href="graph-theory.universal-directed-graph.html#4161" class="Bound">e</a> <a id="4163" class="Symbol">:</a> <a id="4165" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="4185" href="graph-theory.universal-directed-graph.html#3812" class="Bound">G</a> <a id="4187" href="graph-theory.universal-directed-graph.html#4129" class="Bound">x</a> <a id="4189" href="graph-theory.universal-directed-graph.html#4131" class="Bound">y</a><a id="4190" class="Symbol">)</a> <a id="4192" class="Symbol">→</a>
    <a id="4198" href="graph-theory.universal-directed-graph.html#3888" class="Function">vertex-characteristic-hom-Dependent-Directed-Graph</a> <a id="4249" href="graph-theory.universal-directed-graph.html#4129" class="Bound">x</a> <a id="4251" class="Symbol">→</a>
    <a id="4257" href="graph-theory.universal-directed-graph.html#3888" class="Function">vertex-characteristic-hom-Dependent-Directed-Graph</a> <a id="4308" href="graph-theory.universal-directed-graph.html#4131" class="Bound">y</a> <a id="4310" class="Symbol">→</a>
    <a id="4316" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4319" href="graph-theory.universal-directed-graph.html#3797" class="Bound">l4</a>
  <a id="4324" href="graph-theory.universal-directed-graph.html#4073" class="Function">edge-characteristic-hom-Dependent-Directed-Graph</a> <a id="4373" class="Symbol">=</a>
    <a id="4379" href="graph-theory.dependent-directed-graphs.html#1758" class="Function">edge-Dependent-Directed-Graph</a> <a id="4409" href="graph-theory.universal-directed-graph.html#3839" class="Bound">H</a>

  <a id="4414" href="graph-theory.universal-directed-graph.html#4414" class="Function">characteristic-hom-Dependent-Directed-Graph</a> <a id="4458" class="Symbol">:</a>
    <a id="4464" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="4483" href="graph-theory.universal-directed-graph.html#3812" class="Bound">G</a> <a id="4485" class="Symbol">(</a><a id="4486" href="graph-theory.universal-directed-graph.html#2558" class="Function">universal-Directed-Graph</a> <a id="4511" href="graph-theory.universal-directed-graph.html#3794" class="Bound">l3</a> <a id="4514" href="graph-theory.universal-directed-graph.html#3797" class="Bound">l4</a><a id="4516" class="Symbol">)</a>
  <a id="4520" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4524" href="graph-theory.universal-directed-graph.html#4414" class="Function">characteristic-hom-Dependent-Directed-Graph</a> <a id="4568" class="Symbol">=</a>
    <a id="4574" href="graph-theory.universal-directed-graph.html#3888" class="Function">vertex-characteristic-hom-Dependent-Directed-Graph</a>
  <a id="4627" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4631" href="graph-theory.universal-directed-graph.html#4414" class="Function">characteristic-hom-Dependent-Directed-Graph</a> <a id="4675" class="Symbol">_</a> <a id="4677" class="Symbol">_</a> <a id="4679" class="Symbol">=</a>
    <a id="4685" href="graph-theory.universal-directed-graph.html#4073" class="Function">edge-characteristic-hom-Dependent-Directed-Graph</a>
</pre>
#### Base change of the universal dependent directed graph along the characteristic morphism of a dependent directed graph

<pre class="Agda"><a id="4871" class="Keyword">module</a> <a id="4878" href="graph-theory.universal-directed-graph.html#4878" class="Module">_</a>
  <a id="4882" class="Symbol">{</a><a id="4883" href="graph-theory.universal-directed-graph.html#4883" class="Bound">l1</a> <a id="4886" href="graph-theory.universal-directed-graph.html#4886" class="Bound">l2</a> <a id="4889" href="graph-theory.universal-directed-graph.html#4889" class="Bound">l3</a> <a id="4892" href="graph-theory.universal-directed-graph.html#4892" class="Bound">l4</a> <a id="4895" class="Symbol">:</a> <a id="4897" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4902" class="Symbol">}</a>
  <a id="4906" class="Symbol">{</a><a id="4907" href="graph-theory.universal-directed-graph.html#4907" class="Bound">G</a> <a id="4909" class="Symbol">:</a> <a id="4911" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="4926" href="graph-theory.universal-directed-graph.html#4883" class="Bound">l1</a> <a id="4929" href="graph-theory.universal-directed-graph.html#4886" class="Bound">l2</a><a id="4931" class="Symbol">}</a> <a id="4933" class="Symbol">(</a><a id="4934" href="graph-theory.universal-directed-graph.html#4934" class="Bound">H</a> <a id="4936" class="Symbol">:</a> <a id="4938" href="graph-theory.dependent-directed-graphs.html#1231" class="Function">Dependent-Directed-Graph</a> <a id="4963" href="graph-theory.universal-directed-graph.html#4889" class="Bound">l3</a> <a id="4966" href="graph-theory.universal-directed-graph.html#4892" class="Bound">l4</a> <a id="4969" href="graph-theory.universal-directed-graph.html#4907" class="Bound">G</a><a id="4970" class="Symbol">)</a>
  <a id="4974" class="Keyword">where</a>

  <a id="4983" href="graph-theory.universal-directed-graph.html#4983" class="Function">base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph</a> <a id="5055" class="Symbol">:</a>
    <a id="5061" href="graph-theory.dependent-directed-graphs.html#1231" class="Function">Dependent-Directed-Graph</a> <a id="5086" href="graph-theory.universal-directed-graph.html#4889" class="Bound">l3</a> <a id="5089" href="graph-theory.universal-directed-graph.html#4892" class="Bound">l4</a> <a id="5092" href="graph-theory.universal-directed-graph.html#4907" class="Bound">G</a>
  <a id="5096" href="graph-theory.universal-directed-graph.html#4983" class="Function">base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph</a> <a id="5168" class="Symbol">=</a>
    <a id="5174" href="graph-theory.base-change-dependent-directed-graphs.html#1760" class="Function">base-change-Dependent-Directed-Graph</a> <a id="5211" href="graph-theory.universal-directed-graph.html#4907" class="Bound">G</a>
      <a id="5219" class="Symbol">(</a> <a id="5221" href="graph-theory.universal-directed-graph.html#4414" class="Function">characteristic-hom-Dependent-Directed-Graph</a> <a id="5265" href="graph-theory.universal-directed-graph.html#4934" class="Bound">H</a><a id="5266" class="Symbol">)</a>
      <a id="5274" class="Symbol">(</a> <a id="5276" href="graph-theory.universal-directed-graph.html#3304" class="Function">universal-Dependent-Directed-Graph</a> <a id="5311" href="graph-theory.universal-directed-graph.html#4889" class="Bound">l3</a> <a id="5314" href="graph-theory.universal-directed-graph.html#4892" class="Bound">l4</a><a id="5316" class="Symbol">)</a>

  <a id="5321" href="graph-theory.universal-directed-graph.html#5321" class="Function">compute-base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph</a> <a id="5401" class="Symbol">:</a>
    <a id="5407" href="graph-theory.equivalences-dependent-directed-graphs.html#1595" class="Function">equiv-Dependent-Directed-Graph</a> <a id="5438" href="graph-theory.universal-directed-graph.html#4934" class="Bound">H</a>
      <a id="5446" href="graph-theory.universal-directed-graph.html#4983" class="Function">base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph</a>
  <a id="5520" href="graph-theory.universal-directed-graph.html#5321" class="Function">compute-base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph</a> <a id="5600" class="Symbol">=</a>
    <a id="5606" href="graph-theory.equivalences-dependent-directed-graphs.html#4857" class="Function">id-equiv-Dependent-Directed-Graph</a> <a id="5640" href="graph-theory.universal-directed-graph.html#4934" class="Bound">H</a>
</pre>
## See also

- [The universal reflexive graph](graph-theory.universal-reflexive-graph.md)
- [Directed graph duality](graph-theory.directed-graph-duality.md)
