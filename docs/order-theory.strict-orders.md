# Strict orders

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="order-theory.strict-orders.html" class="Module">order-theory.strict-orders</a> <a id="60" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="116" class="Keyword">open</a> <a id="121" class="Keyword">import</a> <a id="128" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="282" class="Keyword">open</a> <a id="287" class="Keyword">import</a> <a id="294" href="foundation.equivalence-relations.html" class="Module">foundation.equivalence-relations</a>
<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="412" class="Keyword">open</a> <a id="417" class="Keyword">import</a> <a id="424" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="444" class="Keyword">open</a> <a id="449" class="Keyword">import</a> <a id="456" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="480" class="Keyword">open</a> <a id="485" class="Keyword">import</a> <a id="492" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="508" class="Keyword">open</a> <a id="513" class="Keyword">import</a> <a id="520" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="548" class="Keyword">open</a> <a id="553" class="Keyword">import</a> <a id="560" href="order-theory.similarity-of-elements-strict-preorders.html" class="Module">order-theory.similarity-of-elements-strict-preorders</a>
<a id="613" class="Keyword">open</a> <a id="618" class="Keyword">import</a> <a id="625" href="order-theory.strict-preorders.html" class="Module">order-theory.strict-preorders</a>
<a id="655" class="Keyword">open</a> <a id="660" class="Keyword">import</a> <a id="667" href="order-theory.strictly-preordered-sets.html" class="Module">order-theory.strictly-preordered-sets</a>
</pre>
</details>

## Idea

A {{#concept "strict order" Agda=Strict-Order}} is a
[strict preorder](order-theory.strict-preorders.md) $A$ satisfying the
{{#concept "extensionality principle" Disambiguation="of strict orders" Agda=extensionality-principle-Strict-Preorder}}
that [similar elements](order-theory.similarity-of-elements-strict-preorders.md)
are [equal](foundation-core.identity-types.md). More concretely, if $x$ and $y$
are such that for every $z$, we have

- $z < x$ [if and only if](foundation.logical-equivalences.md) $z < y$, and
- $x < z$ if and only if $y < z$,

then $x = y$.

The extensionality principle of strict orders is slightly different to that of
[ordinals](order-theory.ordinals.md). For ordinals, elements are equal already
if they are _similar from below_. Namely, only the first of the two conditions
above must be satisfied in order for two elements to be equal.

The extensionality principle of strict orders can be recovered as a special case
of the extensionality principle of
[semicategories](category-theory.nonunital-precategories.md) as considered in
Example 8.16 of _The Univalence Principle_ {{#cite ANST25}}.

## Definitions

### The extensionality principle of strict orders

<pre class="Agda"><a id="extensionality-principle-Strict-Preorder"></a><a id="1932" href="order-theory.strict-orders.html#1932" class="Function">extensionality-principle-Strict-Preorder</a> <a id="1973" class="Symbol">:</a>
  <a id="1977" class="Symbol">{</a><a id="1978" href="order-theory.strict-orders.html#1978" class="Bound">l1</a> <a id="1981" href="order-theory.strict-orders.html#1981" class="Bound">l2</a> <a id="1984" class="Symbol">:</a> <a id="1986" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1991" class="Symbol">}</a> <a id="1993" class="Symbol">→</a> <a id="1995" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="2011" href="order-theory.strict-orders.html#1978" class="Bound">l1</a> <a id="2014" href="order-theory.strict-orders.html#1981" class="Bound">l2</a> <a id="2017" class="Symbol">→</a> <a id="2019" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2022" class="Symbol">(</a><a id="2023" href="order-theory.strict-orders.html#1978" class="Bound">l1</a> <a id="2026" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2028" href="order-theory.strict-orders.html#1981" class="Bound">l2</a><a id="2030" class="Symbol">)</a>
<a id="2032" href="order-theory.strict-orders.html#1932" class="Function">extensionality-principle-Strict-Preorder</a> <a id="2073" href="order-theory.strict-orders.html#2073" class="Bound">P</a> <a id="2075" class="Symbol">=</a>
  <a id="2079" class="Symbol">(</a><a id="2080" href="order-theory.strict-orders.html#2080" class="Bound">x</a> <a id="2082" href="order-theory.strict-orders.html#2082" class="Bound">y</a> <a id="2084" class="Symbol">:</a> <a id="2086" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="2107" href="order-theory.strict-orders.html#2073" class="Bound">P</a><a id="2108" class="Symbol">)</a> <a id="2110" class="Symbol">→</a> <a id="2112" href="order-theory.similarity-of-elements-strict-preorders.html#3465" class="Function">sim-Strict-Preorder</a> <a id="2132" href="order-theory.strict-orders.html#2073" class="Bound">P</a> <a id="2134" href="order-theory.strict-orders.html#2080" class="Bound">x</a> <a id="2136" href="order-theory.strict-orders.html#2082" class="Bound">y</a> <a id="2138" class="Symbol">→</a> <a id="2140" href="order-theory.strict-orders.html#2080" class="Bound">x</a> <a id="2142" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2144" href="order-theory.strict-orders.html#2082" class="Bound">y</a>
</pre>
### The type of strict orders

<pre class="Agda"><a id="Strict-Order"></a><a id="2190" href="order-theory.strict-orders.html#2190" class="Function">Strict-Order</a> <a id="2203" class="Symbol">:</a> <a id="2205" class="Symbol">(</a><a id="2206" href="order-theory.strict-orders.html#2206" class="Bound">l1</a> <a id="2209" href="order-theory.strict-orders.html#2209" class="Bound">l2</a> <a id="2212" class="Symbol">:</a> <a id="2214" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2219" class="Symbol">)</a> <a id="2221" class="Symbol">→</a> <a id="2223" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2226" class="Symbol">(</a><a id="2227" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2232" href="order-theory.strict-orders.html#2206" class="Bound">l1</a> <a id="2235" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2237" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2242" href="order-theory.strict-orders.html#2209" class="Bound">l2</a><a id="2244" class="Symbol">)</a>
<a id="2246" href="order-theory.strict-orders.html#2190" class="Function">Strict-Order</a> <a id="2259" href="order-theory.strict-orders.html#2259" class="Bound">l1</a> <a id="2262" href="order-theory.strict-orders.html#2262" class="Bound">l2</a> <a id="2265" class="Symbol">=</a>
  <a id="2269" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2271" class="Symbol">(</a><a id="2272" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="2288" href="order-theory.strict-orders.html#2259" class="Bound">l1</a> <a id="2291" href="order-theory.strict-orders.html#2262" class="Bound">l2</a><a id="2293" class="Symbol">)</a> <a id="2295" class="Symbol">(</a><a id="2296" href="order-theory.strict-orders.html#1932" class="Function">extensionality-principle-Strict-Preorder</a><a id="2336" class="Symbol">)</a>

<a id="2339" class="Keyword">module</a> <a id="2346" href="order-theory.strict-orders.html#2346" class="Module">_</a>
  <a id="2350" class="Symbol">{</a><a id="2351" href="order-theory.strict-orders.html#2351" class="Bound">l1</a> <a id="2354" href="order-theory.strict-orders.html#2354" class="Bound">l2</a> <a id="2357" class="Symbol">:</a> <a id="2359" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2364" class="Symbol">}</a> <a id="2366" class="Symbol">(</a><a id="2367" href="order-theory.strict-orders.html#2367" class="Bound">A</a> <a id="2369" class="Symbol">:</a> <a id="2371" href="order-theory.strict-orders.html#2190" class="Function">Strict-Order</a> <a id="2384" href="order-theory.strict-orders.html#2351" class="Bound">l1</a> <a id="2387" href="order-theory.strict-orders.html#2354" class="Bound">l2</a><a id="2389" class="Symbol">)</a>
  <a id="2393" class="Keyword">where</a>

  <a id="2402" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a> <a id="2431" class="Symbol">:</a> <a id="2433" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="2449" href="order-theory.strict-orders.html#2351" class="Bound">l1</a> <a id="2452" href="order-theory.strict-orders.html#2354" class="Bound">l2</a>
  <a id="2457" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a> <a id="2486" class="Symbol">=</a> <a id="2488" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2492" href="order-theory.strict-orders.html#2367" class="Bound">A</a>

  <a id="2497" href="order-theory.strict-orders.html#2497" class="Function">extensionality-Strict-Order</a> <a id="2525" class="Symbol">:</a>
    <a id="2531" href="order-theory.strict-orders.html#1932" class="Function">extensionality-principle-Strict-Preorder</a> <a id="2572" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a>
  <a id="2603" href="order-theory.strict-orders.html#2497" class="Function">extensionality-Strict-Order</a> <a id="2631" class="Symbol">=</a> <a id="2633" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2637" href="order-theory.strict-orders.html#2367" class="Bound">A</a>

  <a id="2642" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a> <a id="2660" class="Symbol">:</a> <a id="2662" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2665" href="order-theory.strict-orders.html#2351" class="Bound">l1</a>
  <a id="2670" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a> <a id="2688" class="Symbol">=</a> <a id="2690" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="2711" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a>

  <a id="2743" href="order-theory.strict-orders.html#2743" class="Function">le-Strict-Order</a> <a id="2759" class="Symbol">:</a> <a id="2761" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a> <a id="2779" class="Symbol">→</a> <a id="2781" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a> <a id="2799" class="Symbol">→</a> <a id="2801" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2804" href="order-theory.strict-orders.html#2354" class="Bound">l2</a>
  <a id="2809" href="order-theory.strict-orders.html#2743" class="Function">le-Strict-Order</a> <a id="2825" class="Symbol">=</a> <a id="2827" href="order-theory.strict-preorders.html#1574" class="Function">le-Strict-Preorder</a> <a id="2846" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a>

  <a id="2878" href="order-theory.strict-orders.html#2878" class="Function">is-prop-le-Strict-Order</a> <a id="2902" class="Symbol">:</a>
    <a id="2908" class="Symbol">(</a><a id="2909" href="order-theory.strict-orders.html#2909" class="Bound">x</a> <a id="2911" href="order-theory.strict-orders.html#2911" class="Bound">y</a> <a id="2913" class="Symbol">:</a> <a id="2915" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a><a id="2932" class="Symbol">)</a> <a id="2934" class="Symbol">→</a> <a id="2936" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2944" class="Symbol">(</a><a id="2945" href="order-theory.strict-orders.html#2743" class="Function">le-Strict-Order</a> <a id="2961" href="order-theory.strict-orders.html#2909" class="Bound">x</a> <a id="2963" href="order-theory.strict-orders.html#2911" class="Bound">y</a><a id="2964" class="Symbol">)</a>
  <a id="2968" href="order-theory.strict-orders.html#2878" class="Function">is-prop-le-Strict-Order</a> <a id="2992" class="Symbol">=</a>
    <a id="2998" href="order-theory.strict-preorders.html#1705" class="Function">is-prop-le-Strict-Preorder</a> <a id="3025" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a>

  <a id="3057" href="order-theory.strict-orders.html#3057" class="Function">le-prop-Strict-Order</a> <a id="3078" class="Symbol">:</a> <a id="3080" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a> <a id="3098" class="Symbol">→</a> <a id="3100" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a> <a id="3118" class="Symbol">→</a> <a id="3120" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3125" href="order-theory.strict-orders.html#2354" class="Bound">l2</a>
  <a id="3130" href="order-theory.strict-orders.html#3057" class="Function">le-prop-Strict-Order</a> <a id="3151" class="Symbol">=</a> <a id="3153" href="order-theory.strict-preorders.html#1459" class="Function">le-prop-Strict-Preorder</a> <a id="3177" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a>

  <a id="3209" href="order-theory.strict-orders.html#3209" class="Function">is-irreflexive-le-Strict-Order</a> <a id="3240" class="Symbol">:</a> <a id="3242" href="foundation.binary-relations.html#5565" class="Function">is-irreflexive</a> <a id="3257" href="order-theory.strict-orders.html#2743" class="Function">le-Strict-Order</a>
  <a id="3275" href="order-theory.strict-orders.html#3209" class="Function">is-irreflexive-le-Strict-Order</a> <a id="3306" class="Symbol">=</a>
    <a id="3312" href="order-theory.strict-preorders.html#1895" class="Function">is-irreflexive-le-Strict-Preorder</a> <a id="3346" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a>

  <a id="3378" href="order-theory.strict-orders.html#3378" class="Function">is-transitive-le-Strict-Order</a> <a id="3408" class="Symbol">:</a> <a id="3410" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="3424" href="order-theory.strict-orders.html#2743" class="Function">le-Strict-Order</a>
  <a id="3442" href="order-theory.strict-orders.html#3378" class="Function">is-transitive-le-Strict-Order</a> <a id="3472" class="Symbol">=</a>
    <a id="3478" href="order-theory.strict-preorders.html#2032" class="Function">is-transitive-le-Strict-Preorder</a> <a id="3511" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a>
</pre>
## Properties

### The ordering of a strict order is antisymmetric

<pre class="Agda"><a id="3621" class="Keyword">module</a> <a id="3628" href="order-theory.strict-orders.html#3628" class="Module">_</a>
  <a id="3632" class="Symbol">{</a><a id="3633" href="order-theory.strict-orders.html#3633" class="Bound">l1</a> <a id="3636" href="order-theory.strict-orders.html#3636" class="Bound">l2</a> <a id="3639" class="Symbol">:</a> <a id="3641" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3646" class="Symbol">}</a> <a id="3648" class="Symbol">(</a><a id="3649" href="order-theory.strict-orders.html#3649" class="Bound">A</a> <a id="3651" class="Symbol">:</a> <a id="3653" href="order-theory.strict-orders.html#2190" class="Function">Strict-Order</a> <a id="3666" href="order-theory.strict-orders.html#3633" class="Bound">l1</a> <a id="3669" href="order-theory.strict-orders.html#3636" class="Bound">l2</a><a id="3671" class="Symbol">)</a>
  <a id="3675" class="Keyword">where</a>

  <a id="3684" href="order-theory.strict-orders.html#3684" class="Function">is-antisymmetric-le-Strict-Order</a> <a id="3717" class="Symbol">:</a> <a id="3719" href="foundation.binary-relations.html#6436" class="Function">is-antisymmetric</a> <a id="3736" class="Symbol">(</a><a id="3737" href="order-theory.strict-orders.html#2743" class="Function">le-Strict-Order</a> <a id="3753" href="order-theory.strict-orders.html#3649" class="Bound">A</a><a id="3754" class="Symbol">)</a>
  <a id="3758" href="order-theory.strict-orders.html#3684" class="Function">is-antisymmetric-le-Strict-Order</a> <a id="3791" class="Symbol">=</a>
    <a id="3797" href="order-theory.strict-preorders.html#2313" class="Function">is-antisymmetric-le-Strict-Preorder</a> <a id="3833" class="Symbol">(</a><a id="3834" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a> <a id="3863" href="order-theory.strict-orders.html#3649" class="Bound">A</a><a id="3864" class="Symbol">)</a>
</pre>
### Strict orders are sets

<pre class="Agda"><a id="3907" class="Keyword">module</a> <a id="3914" href="order-theory.strict-orders.html#3914" class="Module">_</a>
  <a id="3918" class="Symbol">{</a><a id="3919" href="order-theory.strict-orders.html#3919" class="Bound">l1</a> <a id="3922" href="order-theory.strict-orders.html#3922" class="Bound">l2</a> <a id="3925" class="Symbol">:</a> <a id="3927" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3932" class="Symbol">}</a> <a id="3934" class="Symbol">(</a><a id="3935" href="order-theory.strict-orders.html#3935" class="Bound">A</a> <a id="3937" class="Symbol">:</a> <a id="3939" href="order-theory.strict-orders.html#2190" class="Function">Strict-Order</a> <a id="3952" href="order-theory.strict-orders.html#3919" class="Bound">l1</a> <a id="3955" href="order-theory.strict-orders.html#3922" class="Bound">l2</a><a id="3957" class="Symbol">)</a>
  <a id="3961" class="Keyword">where</a>

  <a id="3970" href="order-theory.strict-orders.html#3970" class="Function">is-set-type-Strict-Order</a> <a id="3995" class="Symbol">:</a> <a id="3997" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="4004" class="Symbol">(</a><a id="4005" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a> <a id="4023" href="order-theory.strict-orders.html#3935" class="Bound">A</a><a id="4024" class="Symbol">)</a>
  <a id="4028" href="order-theory.strict-orders.html#3970" class="Function">is-set-type-Strict-Order</a> <a id="4053" class="Symbol">=</a>
    <a id="4059" href="foundation-core.sets.html#3983" class="Function">is-set-prop-in-id</a>
      <a id="4083" class="Symbol">(</a> <a id="4085" href="order-theory.similarity-of-elements-strict-preorders.html#3465" class="Function">sim-Strict-Preorder</a> <a id="4105" class="Symbol">(</a><a id="4106" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a> <a id="4135" href="order-theory.strict-orders.html#3935" class="Bound">A</a><a id="4136" class="Symbol">))</a>
      <a id="4145" class="Symbol">(</a> <a id="4147" href="order-theory.similarity-of-elements-strict-preorders.html#3873" class="Function">is-prop-sim-Strict-Preorder</a> <a id="4175" class="Symbol">(</a><a id="4176" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a> <a id="4205" href="order-theory.strict-orders.html#3935" class="Bound">A</a><a id="4206" class="Symbol">))</a>
      <a id="4215" class="Symbol">(</a> <a id="4217" href="order-theory.similarity-of-elements-strict-preorders.html#4487" class="Function">refl-sim-Strict-Preorder</a> <a id="4242" class="Symbol">(</a><a id="4243" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a> <a id="4272" href="order-theory.strict-orders.html#3935" class="Bound">A</a><a id="4273" class="Symbol">))</a>
      <a id="4282" class="Symbol">(</a> <a id="4284" href="order-theory.strict-orders.html#2497" class="Function">extensionality-Strict-Order</a> <a id="4312" href="order-theory.strict-orders.html#3935" class="Bound">A</a><a id="4313" class="Symbol">)</a>

  <a id="4318" href="order-theory.strict-orders.html#4318" class="Function">set-Strict-Order</a> <a id="4335" class="Symbol">:</a> <a id="4337" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="4341" href="order-theory.strict-orders.html#3919" class="Bound">l1</a>
  <a id="4346" href="order-theory.strict-orders.html#4318" class="Function">set-Strict-Order</a> <a id="4363" class="Symbol">=</a> <a id="4365" class="Symbol">(</a><a id="4366" href="order-theory.strict-orders.html#2642" class="Function">type-Strict-Order</a> <a id="4384" href="order-theory.strict-orders.html#3935" class="Bound">A</a> <a id="4386" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4388" href="order-theory.strict-orders.html#3970" class="Function">is-set-type-Strict-Order</a><a id="4412" class="Symbol">)</a>

  <a id="4417" href="order-theory.strict-orders.html#4417" class="Function">strictly-preordered-set-Strict-Order</a> <a id="4454" class="Symbol">:</a> <a id="4456" href="order-theory.strictly-preordered-sets.html#1192" class="Function">Strictly-Preordered-Set</a> <a id="4480" href="order-theory.strict-orders.html#3919" class="Bound">l1</a> <a id="4483" href="order-theory.strict-orders.html#3922" class="Bound">l2</a>
  <a id="4488" href="order-theory.strict-orders.html#4417" class="Function">strictly-preordered-set-Strict-Order</a> <a id="4525" class="Symbol">=</a>
    <a id="4531" href="order-theory.strictly-preordered-sets.html#1440" class="Function">make-Strictly-Preordered-Set</a>
      <a id="4566" class="Symbol">(</a> <a id="4568" href="order-theory.strict-orders.html#2402" class="Function">strict-preorder-Strict-Order</a> <a id="4597" href="order-theory.strict-orders.html#3935" class="Bound">A</a><a id="4598" class="Symbol">)</a>
      <a id="4606" class="Symbol">(</a> <a id="4608" href="order-theory.strict-orders.html#3970" class="Function">is-set-type-Strict-Order</a><a id="4632" class="Symbol">)</a>
</pre>
### The extensionality principle is a proposition

<pre class="Agda"><a id="4698" class="Keyword">module</a> <a id="4705" href="order-theory.strict-orders.html#4705" class="Module">_</a>
  <a id="4709" class="Symbol">{</a><a id="4710" href="order-theory.strict-orders.html#4710" class="Bound">l1</a> <a id="4713" href="order-theory.strict-orders.html#4713" class="Bound">l2</a> <a id="4716" class="Symbol">:</a> <a id="4718" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4723" class="Symbol">}</a> <a id="4725" class="Symbol">(</a><a id="4726" href="order-theory.strict-orders.html#4726" class="Bound">A</a> <a id="4728" class="Symbol">:</a> <a id="4730" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="4746" href="order-theory.strict-orders.html#4710" class="Bound">l1</a> <a id="4749" href="order-theory.strict-orders.html#4713" class="Bound">l2</a><a id="4751" class="Symbol">)</a>
  <a id="4755" class="Keyword">where</a>

  <a id="4764" class="Keyword">abstract</a>
    <a id="4777" href="order-theory.strict-orders.html#4777" class="Function">is-proof-irrelevant-extensionality-principle-Strict-Preorder</a> <a id="4838" class="Symbol">:</a>
      <a id="4846" href="foundation-core.propositions.html#2085" class="Function">is-proof-irrelevant</a> <a id="4866" class="Symbol">(</a><a id="4867" href="order-theory.strict-orders.html#1932" class="Function">extensionality-principle-Strict-Preorder</a> <a id="4908" href="order-theory.strict-orders.html#4726" class="Bound">A</a><a id="4909" class="Symbol">)</a>
    <a id="4915" href="order-theory.strict-orders.html#4777" class="Function">is-proof-irrelevant-extensionality-principle-Strict-Preorder</a> <a id="4976" href="order-theory.strict-orders.html#4976" class="Bound">H</a> <a id="4978" class="Symbol">=</a>
      <a id="4986" class="Symbol">(</a> <a id="4988" href="order-theory.strict-orders.html#4976" class="Bound">H</a> <a id="4990" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
        <a id="5000" class="Symbol">(</a> <a id="5002" class="Symbol">λ</a> <a id="5004" href="order-theory.strict-orders.html#5004" class="Bound">K</a> <a id="5006" class="Symbol">→</a>
          <a id="5018" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a>
            <a id="5038" class="Symbol">(</a> <a id="5040" class="Symbol">λ</a> <a id="5042" href="order-theory.strict-orders.html#5042" class="Bound">x</a> <a id="5044" class="Symbol">→</a>
              <a id="5060" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a>
                <a id="5084" class="Symbol">(</a> <a id="5086" class="Symbol">λ</a> <a id="5088" href="order-theory.strict-orders.html#5088" class="Bound">y</a> <a id="5090" class="Symbol">→</a>
                  <a id="5110" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a>
                    <a id="5138" class="Symbol">(</a> <a id="5140" class="Symbol">λ</a> <a id="5142" href="order-theory.strict-orders.html#5142" class="Bound">_</a> <a id="5144" class="Symbol">→</a>
                      <a id="5168" href="foundation-core.propositions.html#2524" class="Function">eq-is-prop</a> <a id="5179" class="Symbol">(</a><a id="5180" href="order-theory.strict-orders.html#3970" class="Function">is-set-type-Strict-Order</a> <a id="5205" class="Symbol">(</a><a id="5206" href="order-theory.strict-orders.html#4726" class="Bound">A</a> <a id="5208" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5210" href="order-theory.strict-orders.html#4976" class="Bound">H</a><a id="5211" class="Symbol">)</a> <a id="5213" href="order-theory.strict-orders.html#5042" class="Bound">x</a> <a id="5215" href="order-theory.strict-orders.html#5088" class="Bound">y</a><a id="5216" class="Symbol">))))))</a>

  <a id="5226" href="order-theory.strict-orders.html#5226" class="Function">is-prop-extensionality-principle-Strict-Preorder</a> <a id="5275" class="Symbol">:</a>
      <a id="5283" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="5291" class="Symbol">(</a><a id="5292" href="order-theory.strict-orders.html#1932" class="Function">extensionality-principle-Strict-Preorder</a> <a id="5333" href="order-theory.strict-orders.html#4726" class="Bound">A</a><a id="5334" class="Symbol">)</a>
  <a id="5338" href="order-theory.strict-orders.html#5226" class="Function">is-prop-extensionality-principle-Strict-Preorder</a> <a id="5387" class="Symbol">=</a>
    <a id="5393" href="foundation-core.propositions.html#3025" class="Function">is-prop-is-proof-irrelevant</a>
      <a id="5427" class="Symbol">(</a> <a id="5429" href="order-theory.strict-orders.html#4777" class="Function">is-proof-irrelevant-extensionality-principle-Strict-Preorder</a><a id="5489" class="Symbol">)</a>

  <a id="5494" href="order-theory.strict-orders.html#5494" class="Function">extensionality-principle-prop-Strict-Preorder</a> <a id="5540" class="Symbol">:</a> <a id="5542" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="5547" class="Symbol">(</a><a id="5548" href="order-theory.strict-orders.html#4710" class="Bound">l1</a> <a id="5551" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="5553" href="order-theory.strict-orders.html#4713" class="Bound">l2</a><a id="5555" class="Symbol">)</a>
  <a id="5559" href="order-theory.strict-orders.html#5494" class="Function">extensionality-principle-prop-Strict-Preorder</a> <a id="5605" class="Symbol">=</a>
    <a id="5611" class="Symbol">(</a> <a id="5613" href="order-theory.strict-orders.html#1932" class="Function">extensionality-principle-Strict-Preorder</a> <a id="5654" href="order-theory.strict-orders.html#4726" class="Bound">A</a> <a id="5656" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="5664" href="order-theory.strict-orders.html#5226" class="Function">is-prop-extensionality-principle-Strict-Preorder</a><a id="5712" class="Symbol">)</a>
</pre>
## References

{{#bibliography}}

## See also

- [Strictly preordered sets](order-theory.strictly-preordered-sets.md) are
  strict preorders on sets that don't necessarily satisfy the extensionality
  principle.
