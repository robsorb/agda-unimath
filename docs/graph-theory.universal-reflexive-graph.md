# The universal reflexive graph

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="graph-theory.universal-reflexive-graph.html" class="Module">graph-theory.universal-reflexive-graph</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="graph-theory.dependent-directed-graphs.html" class="Module">graph-theory.dependent-directed-graphs</a>
<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="graph-theory.dependent-reflexive-graphs.html" class="Module">graph-theory.dependent-reflexive-graphs</a>
<a id="331" class="Keyword">open</a> <a id="336" class="Keyword">import</a> <a id="343" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
</pre>
</details>

## Idea

The {{#concept "universal reflexive graph" Agda=universal-Reflexive-Graph}}
`𝒢 l` at [universe level](foundation.universe-levels.md) is a translation from
category theory into type theory of the Hofmann–Streicher universe
{{#cite Awodey22}} of presheaves on the reflexive graph category `Γʳ`

```text
      s
    ----->
  0 <-r--- 1,
    ----->
      t
```

in which we have `rs = id` and `rt = id`. The Hofmann–Streicher universe of
presheaves on a category `𝒞` is the presheaf

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A 0,
```

where `0` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute a few instances of the slice category `Γʳ/I`:

- The category Γʳ/0 is the category

  ```text
        s
      ----->
    1 <-r--- r
      ----->
        t
  ```

  in which we have `rs = id` and `rt = id`. In other words, we have an
  isomorphism of categories `Γʳ/0 ≅ Γʳ`.

- The category Γʳ/1 is the category

  ```text
         s                          s
       <-----                     ----->
    rs --r--> s -----> 1 <----- t <-r--- rt
       <-----                     ----->
         t                          t
  ```

  in which we have `rs = id` and `rt = id`.

This means that the universal reflexive graph `𝒰` can be defined type
theoretically as follows:

- The type of vertices of `𝒰` is the type of
  [reflexive graphs](graph-theory.reflexive-graphs.md).
- The type of edges from `G` to `H` is the type

  ```text
    G₀ → H₀ → Type
  ```

  of binary relations from the type `G₀` of vertices of `G` to the type `H₀` of
  vertices of `H`.

- The proof of reflexivity of a reflexive graph `G` is the relation

  ```text
    G₁ : G₀ → G₀ → Type
  ```

  of edges of `G`.

## Definitions

### The universal reflexive graph

<pre class="Agda"><a id="2218" class="Keyword">module</a> <a id="2225" href="graph-theory.universal-reflexive-graph.html#2225" class="Module">_</a>
  <a id="2229" class="Symbol">(</a><a id="2230" href="graph-theory.universal-reflexive-graph.html#2230" class="Bound">l1</a> <a id="2233" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a> <a id="2236" class="Symbol">:</a> <a id="2238" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2243" class="Symbol">)</a>
  <a id="2247" class="Keyword">where</a>

  <a id="2256" href="graph-theory.universal-reflexive-graph.html#2256" class="Function">vertex-universal-Reflexive-Graph</a> <a id="2289" class="Symbol">:</a> <a id="2291" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2294" class="Symbol">(</a><a id="2295" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2300" href="graph-theory.universal-reflexive-graph.html#2230" class="Bound">l1</a> <a id="2303" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2305" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2310" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a><a id="2312" class="Symbol">)</a>
  <a id="2316" href="graph-theory.universal-reflexive-graph.html#2256" class="Function">vertex-universal-Reflexive-Graph</a> <a id="2349" class="Symbol">=</a> <a id="2351" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="2367" href="graph-theory.universal-reflexive-graph.html#2230" class="Bound">l1</a> <a id="2370" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a>

  <a id="2376" href="graph-theory.universal-reflexive-graph.html#2376" class="Function">edge-universal-Reflexvie-Graph</a> <a id="2407" class="Symbol">:</a>
    <a id="2413" class="Symbol">(</a><a id="2414" href="graph-theory.universal-reflexive-graph.html#2414" class="Bound">G</a> <a id="2416" href="graph-theory.universal-reflexive-graph.html#2416" class="Bound">H</a> <a id="2418" class="Symbol">:</a> <a id="2420" href="graph-theory.universal-reflexive-graph.html#2256" class="Function">vertex-universal-Reflexive-Graph</a><a id="2452" class="Symbol">)</a> <a id="2454" class="Symbol">→</a> <a id="2456" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2459" class="Symbol">(</a><a id="2460" href="graph-theory.universal-reflexive-graph.html#2230" class="Bound">l1</a> <a id="2463" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2465" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2470" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a><a id="2472" class="Symbol">)</a>
  <a id="2476" href="graph-theory.universal-reflexive-graph.html#2376" class="Function">edge-universal-Reflexvie-Graph</a> <a id="2507" href="graph-theory.universal-reflexive-graph.html#2507" class="Bound">G</a> <a id="2509" href="graph-theory.universal-reflexive-graph.html#2509" class="Bound">H</a> <a id="2511" class="Symbol">=</a>
    <a id="2517" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="2540" href="graph-theory.universal-reflexive-graph.html#2507" class="Bound">G</a> <a id="2542" class="Symbol">→</a> <a id="2544" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="2567" href="graph-theory.universal-reflexive-graph.html#2509" class="Bound">H</a> <a id="2569" class="Symbol">→</a> <a id="2571" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2574" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a>

  <a id="2580" href="graph-theory.universal-reflexive-graph.html#2580" class="Function">refl-universal-Reflexive-Graph</a> <a id="2611" class="Symbol">:</a>
    <a id="2617" class="Symbol">(</a><a id="2618" href="graph-theory.universal-reflexive-graph.html#2618" class="Bound">G</a> <a id="2620" class="Symbol">:</a> <a id="2622" href="graph-theory.universal-reflexive-graph.html#2256" class="Function">vertex-universal-Reflexive-Graph</a><a id="2654" class="Symbol">)</a> <a id="2656" class="Symbol">→</a>
    <a id="2662" href="graph-theory.universal-reflexive-graph.html#2376" class="Function">edge-universal-Reflexvie-Graph</a> <a id="2693" href="graph-theory.universal-reflexive-graph.html#2618" class="Bound">G</a> <a id="2695" href="graph-theory.universal-reflexive-graph.html#2618" class="Bound">G</a>
  <a id="2699" href="graph-theory.universal-reflexive-graph.html#2580" class="Function">refl-universal-Reflexive-Graph</a> <a id="2730" href="graph-theory.universal-reflexive-graph.html#2730" class="Bound">G</a> <a id="2732" class="Symbol">=</a>
    <a id="2738" href="graph-theory.reflexive-graphs.html#1074" class="Function">edge-Reflexive-Graph</a> <a id="2759" href="graph-theory.universal-reflexive-graph.html#2730" class="Bound">G</a>

  <a id="2764" href="graph-theory.universal-reflexive-graph.html#2764" class="Function">directed-graph-universal-Reflexive-Graph</a> <a id="2805" class="Symbol">:</a>
    <a id="2811" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="2826" class="Symbol">(</a><a id="2827" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2832" href="graph-theory.universal-reflexive-graph.html#2230" class="Bound">l1</a> <a id="2835" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2837" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2842" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a><a id="2844" class="Symbol">)</a> <a id="2846" class="Symbol">(</a><a id="2847" href="graph-theory.universal-reflexive-graph.html#2230" class="Bound">l1</a> <a id="2850" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2852" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2857" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a><a id="2859" class="Symbol">)</a>
  <a id="2863" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2867" href="graph-theory.universal-reflexive-graph.html#2764" class="Function">directed-graph-universal-Reflexive-Graph</a> <a id="2908" class="Symbol">=</a>
    <a id="2914" href="graph-theory.universal-reflexive-graph.html#2256" class="Function">vertex-universal-Reflexive-Graph</a>
  <a id="2949" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2953" href="graph-theory.universal-reflexive-graph.html#2764" class="Function">directed-graph-universal-Reflexive-Graph</a> <a id="2994" class="Symbol">=</a>
    <a id="3000" href="graph-theory.universal-reflexive-graph.html#2376" class="Function">edge-universal-Reflexvie-Graph</a>

  <a id="3034" href="graph-theory.universal-reflexive-graph.html#3034" class="Function">universal-Reflexive-Graph</a> <a id="3060" class="Symbol">:</a>
    <a id="3066" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="3082" class="Symbol">(</a><a id="3083" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3088" href="graph-theory.universal-reflexive-graph.html#2230" class="Bound">l1</a> <a id="3091" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3093" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3098" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a><a id="3100" class="Symbol">)</a> <a id="3102" class="Symbol">(</a><a id="3103" href="graph-theory.universal-reflexive-graph.html#2230" class="Bound">l1</a> <a id="3106" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3108" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3113" href="graph-theory.universal-reflexive-graph.html#2233" class="Bound">l2</a><a id="3115" class="Symbol">)</a>
  <a id="3119" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3123" href="graph-theory.universal-reflexive-graph.html#3034" class="Function">universal-Reflexive-Graph</a> <a id="3149" class="Symbol">=</a> <a id="3151" href="graph-theory.universal-reflexive-graph.html#2764" class="Function">directed-graph-universal-Reflexive-Graph</a>
  <a id="3194" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3198" href="graph-theory.universal-reflexive-graph.html#3034" class="Function">universal-Reflexive-Graph</a> <a id="3224" class="Symbol">=</a> <a id="3226" href="graph-theory.universal-reflexive-graph.html#2580" class="Function">refl-universal-Reflexive-Graph</a>
</pre>
### The universal dependent directed graph

<pre class="Agda"><a id="3314" class="Keyword">module</a> <a id="3321" href="graph-theory.universal-reflexive-graph.html#3321" class="Module">_</a>
  <a id="3325" class="Symbol">{</a><a id="3326" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="3329" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a> <a id="3332" class="Symbol">:</a> <a id="3334" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3339" class="Symbol">}</a>
  <a id="3343" class="Keyword">where</a>

  <a id="3352" href="graph-theory.universal-reflexive-graph.html#3352" class="Function">vertex-universal-Dependent-Reflexive-Graph</a> <a id="3395" class="Symbol">:</a>
    <a id="3401" class="Symbol">(</a><a id="3402" href="graph-theory.universal-reflexive-graph.html#3402" class="Bound">G</a> <a id="3404" class="Symbol">:</a> <a id="3406" href="graph-theory.universal-reflexive-graph.html#2256" class="Function">vertex-universal-Reflexive-Graph</a> <a id="3439" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="3442" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a><a id="3444" class="Symbol">)</a> <a id="3446" class="Symbol">→</a> <a id="3448" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3451" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a>
  <a id="3456" href="graph-theory.universal-reflexive-graph.html#3352" class="Function">vertex-universal-Dependent-Reflexive-Graph</a> <a id="3499" href="graph-theory.universal-reflexive-graph.html#3499" class="Bound">G</a> <a id="3501" class="Symbol">=</a>
    <a id="3507" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="3530" href="graph-theory.universal-reflexive-graph.html#3499" class="Bound">G</a>

  <a id="3535" href="graph-theory.universal-reflexive-graph.html#3535" class="Function">edge-universal-Dependent-Reflexive-Graph</a> <a id="3576" class="Symbol">:</a>
    <a id="3582" class="Symbol">(</a><a id="3583" href="graph-theory.universal-reflexive-graph.html#3583" class="Bound">G</a> <a id="3585" href="graph-theory.universal-reflexive-graph.html#3585" class="Bound">H</a> <a id="3587" class="Symbol">:</a> <a id="3589" href="graph-theory.universal-reflexive-graph.html#2256" class="Function">vertex-universal-Reflexive-Graph</a> <a id="3622" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="3625" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a><a id="3627" class="Symbol">)</a>
    <a id="3633" class="Symbol">(</a><a id="3634" href="graph-theory.universal-reflexive-graph.html#3634" class="Bound">R</a> <a id="3636" class="Symbol">:</a> <a id="3638" href="graph-theory.universal-reflexive-graph.html#2376" class="Function">edge-universal-Reflexvie-Graph</a> <a id="3669" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="3672" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a> <a id="3675" href="graph-theory.universal-reflexive-graph.html#3583" class="Bound">G</a> <a id="3677" href="graph-theory.universal-reflexive-graph.html#3585" class="Bound">H</a><a id="3678" class="Symbol">)</a> <a id="3680" class="Symbol">→</a>
    <a id="3686" href="graph-theory.universal-reflexive-graph.html#3352" class="Function">vertex-universal-Dependent-Reflexive-Graph</a> <a id="3729" href="graph-theory.universal-reflexive-graph.html#3583" class="Bound">G</a> <a id="3731" class="Symbol">→</a>
    <a id="3737" href="graph-theory.universal-reflexive-graph.html#3352" class="Function">vertex-universal-Dependent-Reflexive-Graph</a> <a id="3780" href="graph-theory.universal-reflexive-graph.html#3585" class="Bound">H</a> <a id="3782" class="Symbol">→</a> <a id="3784" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3787" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a>
  <a id="3792" href="graph-theory.universal-reflexive-graph.html#3535" class="Function">edge-universal-Dependent-Reflexive-Graph</a> <a id="3833" href="graph-theory.universal-reflexive-graph.html#3833" class="Bound">G</a> <a id="3835" href="graph-theory.universal-reflexive-graph.html#3835" class="Bound">H</a> <a id="3837" href="graph-theory.universal-reflexive-graph.html#3837" class="Bound">R</a> <a id="3839" href="graph-theory.universal-reflexive-graph.html#3839" class="Bound">x</a> <a id="3841" href="graph-theory.universal-reflexive-graph.html#3841" class="Bound">y</a> <a id="3843" class="Symbol">=</a> <a id="3845" href="graph-theory.universal-reflexive-graph.html#3837" class="Bound">R</a> <a id="3847" href="graph-theory.universal-reflexive-graph.html#3839" class="Bound">x</a> <a id="3849" href="graph-theory.universal-reflexive-graph.html#3841" class="Bound">y</a>

  <a id="3854" href="graph-theory.universal-reflexive-graph.html#3854" class="Function">refl-universal-Dependent-Reflexive-Graph</a> <a id="3895" class="Symbol">:</a>
    <a id="3901" class="Symbol">(</a><a id="3902" href="graph-theory.universal-reflexive-graph.html#3902" class="Bound">G</a> <a id="3904" class="Symbol">:</a> <a id="3906" href="graph-theory.universal-reflexive-graph.html#2256" class="Function">vertex-universal-Reflexive-Graph</a> <a id="3939" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="3942" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a><a id="3944" class="Symbol">)</a>
    <a id="3950" class="Symbol">(</a><a id="3951" href="graph-theory.universal-reflexive-graph.html#3951" class="Bound">x</a> <a id="3953" class="Symbol">:</a> <a id="3955" href="graph-theory.universal-reflexive-graph.html#3352" class="Function">vertex-universal-Dependent-Reflexive-Graph</a> <a id="3998" href="graph-theory.universal-reflexive-graph.html#3902" class="Bound">G</a><a id="3999" class="Symbol">)</a> <a id="4001" class="Symbol">→</a>
    <a id="4007" href="graph-theory.universal-reflexive-graph.html#3535" class="Function">edge-universal-Dependent-Reflexive-Graph</a> <a id="4048" href="graph-theory.universal-reflexive-graph.html#3902" class="Bound">G</a> <a id="4050" href="graph-theory.universal-reflexive-graph.html#3902" class="Bound">G</a>
      <a id="4058" class="Symbol">(</a> <a id="4060" href="graph-theory.universal-reflexive-graph.html#2580" class="Function">refl-universal-Reflexive-Graph</a> <a id="4091" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="4094" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a> <a id="4097" href="graph-theory.universal-reflexive-graph.html#3902" class="Bound">G</a><a id="4098" class="Symbol">)</a> <a id="4100" href="graph-theory.universal-reflexive-graph.html#3951" class="Bound">x</a> <a id="4102" href="graph-theory.universal-reflexive-graph.html#3951" class="Bound">x</a>
  <a id="4106" href="graph-theory.universal-reflexive-graph.html#3854" class="Function">refl-universal-Dependent-Reflexive-Graph</a> <a id="4147" href="graph-theory.universal-reflexive-graph.html#4147" class="Bound">G</a> <a id="4149" href="graph-theory.universal-reflexive-graph.html#4149" class="Bound">x</a> <a id="4151" class="Symbol">=</a> <a id="4153" href="graph-theory.reflexive-graphs.html#1232" class="Function">refl-Reflexive-Graph</a> <a id="4174" href="graph-theory.universal-reflexive-graph.html#4147" class="Bound">G</a> <a id="4176" href="graph-theory.universal-reflexive-graph.html#4149" class="Bound">x</a>

  <a id="4181" href="graph-theory.universal-reflexive-graph.html#4181" class="Function">dependent-directed-graph-universal-Dependent-Reflexive-Graph</a> <a id="4242" class="Symbol">:</a>
    <a id="4248" href="graph-theory.dependent-directed-graphs.html#1231" class="Function">Dependent-Directed-Graph</a> <a id="4273" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="4276" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a>
      <a id="4285" class="Symbol">(</a> <a id="4287" href="graph-theory.universal-reflexive-graph.html#2764" class="Function">directed-graph-universal-Reflexive-Graph</a> <a id="4328" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="4331" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a><a id="4333" class="Symbol">)</a>
  <a id="4337" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4341" href="graph-theory.universal-reflexive-graph.html#4181" class="Function">dependent-directed-graph-universal-Dependent-Reflexive-Graph</a> <a id="4402" class="Symbol">=</a>
    <a id="4408" href="graph-theory.universal-reflexive-graph.html#3352" class="Function">vertex-universal-Dependent-Reflexive-Graph</a>
  <a id="4453" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4457" href="graph-theory.universal-reflexive-graph.html#4181" class="Function">dependent-directed-graph-universal-Dependent-Reflexive-Graph</a> <a id="4518" class="Symbol">=</a>
    <a id="4524" href="graph-theory.universal-reflexive-graph.html#3535" class="Function">edge-universal-Dependent-Reflexive-Graph</a>

  <a id="4568" href="graph-theory.universal-reflexive-graph.html#4568" class="Function">universal-Dependent-Reflexive-Graph</a> <a id="4604" class="Symbol">:</a>
    <a id="4610" href="graph-theory.dependent-reflexive-graphs.html#1990" class="Function">Dependent-Reflexive-Graph</a> <a id="4636" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="4639" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a> <a id="4642" class="Symbol">(</a><a id="4643" href="graph-theory.universal-reflexive-graph.html#3034" class="Function">universal-Reflexive-Graph</a> <a id="4669" href="graph-theory.universal-reflexive-graph.html#3326" class="Bound">l1</a> <a id="4672" href="graph-theory.universal-reflexive-graph.html#3329" class="Bound">l2</a><a id="4674" class="Symbol">)</a>
  <a id="4678" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4682" href="graph-theory.universal-reflexive-graph.html#4568" class="Function">universal-Dependent-Reflexive-Graph</a> <a id="4718" class="Symbol">=</a>
    <a id="4724" href="graph-theory.universal-reflexive-graph.html#4181" class="Function">dependent-directed-graph-universal-Dependent-Reflexive-Graph</a>
  <a id="4787" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4791" href="graph-theory.universal-reflexive-graph.html#4568" class="Function">universal-Dependent-Reflexive-Graph</a> <a id="4827" class="Symbol">=</a>
    <a id="4833" href="graph-theory.universal-reflexive-graph.html#3854" class="Function">refl-universal-Dependent-Reflexive-Graph</a>
</pre>
## Formalization target

There is a _reflexive graph duality theorem_, which asserts that for any
reflexive graph `G`, the type of morphisms `hom G 𝒰` from `G` into the universal
reflexive graph is equivalent to the type of pairs `(H , f)` consisting of a
reflexive graph `H` and a morphism `f : hom H G` from `H` into `G`. Such a
result should be formalized in a new file called `reflexive-graph-duality`.

## See also

- [The universal directed graph](graph-theory.universal-directed-graph.md)
