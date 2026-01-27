# Large strict orders

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="order-theory.large-strict-orders.html" class="Module">order-theory.large-strict-orders</a> <a id="72" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="foundation.equivalence-relations.html" class="Module">foundation.equivalence-relations</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="386" class="Keyword">open</a> <a id="391" class="Keyword">import</a> <a id="398" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="foundation.large-binary-relations.html" class="Module">foundation.large-binary-relations</a>
<a id="470" class="Keyword">open</a> <a id="475" class="Keyword">import</a> <a id="482" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="502" class="Keyword">open</a> <a id="507" class="Keyword">import</a> <a id="514" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="538" class="Keyword">open</a> <a id="543" class="Keyword">import</a> <a id="550" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="566" class="Keyword">open</a> <a id="571" class="Keyword">import</a> <a id="578" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="606" class="Keyword">open</a> <a id="611" class="Keyword">import</a> <a id="618" href="order-theory.large-strict-preorders.html" class="Module">order-theory.large-strict-preorders</a>
<a id="654" class="Keyword">open</a> <a id="659" class="Keyword">import</a> <a id="666" href="order-theory.similarity-of-elements-large-strict-preorders.html" class="Module">order-theory.similarity-of-elements-large-strict-preorders</a>
<a id="725" class="Keyword">open</a> <a id="730" class="Keyword">import</a> <a id="737" href="order-theory.strict-orders.html" class="Module">order-theory.strict-orders</a>
<a id="764" class="Keyword">open</a> <a id="769" class="Keyword">import</a> <a id="776" href="order-theory.strict-preorders.html" class="Module">order-theory.strict-preorders</a>
<a id="806" class="Keyword">open</a> <a id="811" class="Keyword">import</a> <a id="818" href="order-theory.strictly-preordered-sets.html" class="Module">order-theory.strictly-preordered-sets</a>
</pre>
</details>

## Idea

A {{#concept "large strict order" Agda=Large-Strict-Order}} is a
[large strict preorder](order-theory.large-strict-preorders.md) $A$ satisfying
the
{{#concept "extensionality principle" Disambiguation="of large strict orders" Agda=extensionality-principle-Large-Strict-Preorder}}
that pairs of elements at a universe level that are
[similar](order-theory.similarity-of-elements-large-strict-preorders.md)
relative to that same universe level are
[equal](foundation-core.identity-types.md). More concretely, if $x$ and $y$ are
elements at universe level $l$ such that for every other element $z$ at the same
universe level $l$, we have

- $z < x$ [if and only if](foundation.logical-equivalences.md) $z < y$, and
- $x < z$ if and only if $y < z$,

then $x = y$.

The extensionality principle of large strict orders is slightly different to
that of [ordinals](order-theory.ordinals.md). For ordinals, elements are equal
already if they are _similar from below_. Namely, only the first of the two
conditions above must be satisfied in order for two elements to be equal.

The extensionality principle of large strict orders can be recovered as a
special case of the extensionality principle of
[semicategories](category-theory.nonunital-precategories.md) as considered in
Example 8.16 of _The Univalence Principle_ {{#cite ANST25}}.

## Definitions

### The extensionality principle of large strict orders

<pre class="Agda"><a id="2294" class="Keyword">module</a> <a id="2301" href="order-theory.large-strict-orders.html#2301" class="Module">_</a>
  <a id="2305" class="Symbol">{</a><a id="2306" href="order-theory.large-strict-orders.html#2306" class="Bound">α</a> <a id="2308" class="Symbol">:</a> <a id="2310" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="2316" class="Symbol">→</a> <a id="2318" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2323" class="Symbol">}</a> <a id="2325" class="Symbol">{</a><a id="2326" href="order-theory.large-strict-orders.html#2326" class="Bound">β</a> <a id="2328" class="Symbol">:</a> <a id="2330" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="2336" class="Symbol">→</a> <a id="2338" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="2344" class="Symbol">→</a> <a id="2346" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2351" class="Symbol">}</a>
  <a id="2355" class="Symbol">(</a><a id="2356" href="order-theory.large-strict-orders.html#2356" class="Bound">A</a> <a id="2358" class="Symbol">:</a> <a id="2360" href="order-theory.large-strict-preorders.html#1308" class="Record">Large-Strict-Preorder</a> <a id="2382" href="order-theory.large-strict-orders.html#2306" class="Bound">α</a> <a id="2384" href="order-theory.large-strict-orders.html#2326" class="Bound">β</a><a id="2385" class="Symbol">)</a>
  <a id="2389" class="Keyword">where</a>

  <a id="2398" href="order-theory.large-strict-orders.html#2398" class="Function">extensionality-principle-level-Large-Strict-Preorder</a> <a id="2451" class="Symbol">:</a>
    <a id="2457" class="Symbol">(</a><a id="2458" href="order-theory.large-strict-orders.html#2458" class="Bound">l</a> <a id="2460" class="Symbol">:</a> <a id="2462" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2467" class="Symbol">)</a> <a id="2469" class="Symbol">→</a> <a id="2471" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2474" class="Symbol">(</a><a id="2475" href="order-theory.large-strict-orders.html#2306" class="Bound">α</a> <a id="2477" href="order-theory.large-strict-orders.html#2458" class="Bound">l</a> <a id="2479" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2481" href="order-theory.large-strict-orders.html#2326" class="Bound">β</a> <a id="2483" href="order-theory.large-strict-orders.html#2458" class="Bound">l</a> <a id="2485" href="order-theory.large-strict-orders.html#2458" class="Bound">l</a><a id="2486" class="Symbol">)</a>
  <a id="2490" href="order-theory.large-strict-orders.html#2398" class="Function">extensionality-principle-level-Large-Strict-Preorder</a> <a id="2543" href="order-theory.large-strict-orders.html#2543" class="Bound">l</a> <a id="2545" class="Symbol">=</a>
    <a id="2551" class="Symbol">(</a><a id="2552" href="order-theory.large-strict-orders.html#2552" class="Bound">x</a> <a id="2554" href="order-theory.large-strict-orders.html#2554" class="Bound">y</a> <a id="2556" class="Symbol">:</a> <a id="2558" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a> <a id="2585" href="order-theory.large-strict-orders.html#2356" class="Bound">A</a> <a id="2587" href="order-theory.large-strict-orders.html#2543" class="Bound">l</a><a id="2588" class="Symbol">)</a> <a id="2590" class="Symbol">→</a>
    <a id="2596" href="order-theory.similarity-of-elements-large-strict-preorders.html#5202" class="Function">sim-level-Large-Strict-Preorder</a> <a id="2628" href="order-theory.large-strict-orders.html#2356" class="Bound">A</a> <a id="2630" href="order-theory.large-strict-orders.html#2543" class="Bound">l</a> <a id="2632" href="order-theory.large-strict-orders.html#2552" class="Bound">x</a> <a id="2634" href="order-theory.large-strict-orders.html#2554" class="Bound">y</a> <a id="2636" class="Symbol">→</a>
    <a id="2642" href="order-theory.large-strict-orders.html#2552" class="Bound">x</a> <a id="2644" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2646" href="order-theory.large-strict-orders.html#2554" class="Bound">y</a>

  <a id="2651" href="order-theory.large-strict-orders.html#2651" class="Function">extensionality-principle-Large-Strict-Preorder</a> <a id="2698" class="Symbol">:</a> <a id="2700" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="2706" href="order-theory.large-strict-orders.html#2651" class="Function">extensionality-principle-Large-Strict-Preorder</a> <a id="2753" class="Symbol">=</a>
    <a id="2759" class="Symbol">{</a><a id="2760" href="order-theory.large-strict-orders.html#2760" class="Bound">l</a> <a id="2762" class="Symbol">:</a> <a id="2764" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2769" class="Symbol">}</a> <a id="2771" class="Symbol">→</a> <a id="2773" href="order-theory.large-strict-orders.html#2398" class="Function">extensionality-principle-level-Large-Strict-Preorder</a> <a id="2826" href="order-theory.large-strict-orders.html#2760" class="Bound">l</a>

  <a id="2831" href="order-theory.large-strict-orders.html#2831" class="Function">weak-extensionality-principle-level-Large-Strict-Preorder</a> <a id="2889" class="Symbol">:</a> <a id="2891" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="2897" class="Symbol">→</a> <a id="2899" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="2905" href="order-theory.large-strict-orders.html#2831" class="Function">weak-extensionality-principle-level-Large-Strict-Preorder</a> <a id="2963" href="order-theory.large-strict-orders.html#2963" class="Bound">l</a> <a id="2965" class="Symbol">=</a>
    <a id="2971" class="Symbol">(</a><a id="2972" href="order-theory.large-strict-orders.html#2972" class="Bound">x</a> <a id="2974" href="order-theory.large-strict-orders.html#2974" class="Bound">y</a> <a id="2976" class="Symbol">:</a> <a id="2978" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a> <a id="3005" href="order-theory.large-strict-orders.html#2356" class="Bound">A</a> <a id="3007" href="order-theory.large-strict-orders.html#2963" class="Bound">l</a><a id="3008" class="Symbol">)</a> <a id="3010" class="Symbol">→</a>
    <a id="3016" href="order-theory.similarity-of-elements-large-strict-preorders.html#6301" class="Record">sim-Large-Strict-Preorder</a> <a id="3042" href="order-theory.large-strict-orders.html#2356" class="Bound">A</a> <a id="3044" href="order-theory.large-strict-orders.html#2972" class="Bound">x</a> <a id="3046" href="order-theory.large-strict-orders.html#2974" class="Bound">y</a> <a id="3048" class="Symbol">→</a>
    <a id="3054" href="order-theory.large-strict-orders.html#2972" class="Bound">x</a> <a id="3056" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3058" href="order-theory.large-strict-orders.html#2974" class="Bound">y</a>

  <a id="3063" href="order-theory.large-strict-orders.html#3063" class="Function">weak-extensionality-principle-Large-Strict-Preorder</a> <a id="3115" class="Symbol">:</a> <a id="3117" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="3123" href="order-theory.large-strict-orders.html#3063" class="Function">weak-extensionality-principle-Large-Strict-Preorder</a> <a id="3175" class="Symbol">=</a>
    <a id="3181" class="Symbol">{</a><a id="3182" href="order-theory.large-strict-orders.html#3182" class="Bound">l</a> <a id="3184" class="Symbol">:</a> <a id="3186" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3191" class="Symbol">}</a> <a id="3193" class="Symbol">→</a> <a id="3195" href="order-theory.large-strict-orders.html#2831" class="Function">weak-extensionality-principle-level-Large-Strict-Preorder</a> <a id="3253" href="order-theory.large-strict-orders.html#3182" class="Bound">l</a>
</pre>
The last, "weak", extensionality principle asks that $x$ and $y$ at universe
level $l$ are similar relative to _every_ universe level in order to conclude
they are equal. This principle is likely too weak for practical purposes. For
instance, it is no longer the case for "weakly extensional" large strict
preorders that the underlying strict preorder at a universe level is
extensional, nor can we conclude that the underlying hierarchy of types of a
weakly extensional large strict preorder is a hierarchy of sets without
formalizing the concept of "large propositions", i.e., `Propω`.

### The type of large strict orders

<pre class="Agda"><a id="3894" class="Keyword">record</a> <a id="Large-Strict-Order"></a><a id="3901" href="order-theory.large-strict-orders.html#3901" class="Record">Large-Strict-Order</a> <a id="3920" class="Symbol">(</a><a id="3921" href="order-theory.large-strict-orders.html#3921" class="Bound">α</a> <a id="3923" class="Symbol">:</a> <a id="3925" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="3931" class="Symbol">→</a> <a id="3933" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3938" class="Symbol">)</a> <a id="3940" class="Symbol">(</a><a id="3941" href="order-theory.large-strict-orders.html#3941" class="Bound">β</a> <a id="3943" class="Symbol">:</a> <a id="3945" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="3951" class="Symbol">→</a> <a id="3953" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="3959" class="Symbol">→</a> <a id="3961" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3966" class="Symbol">)</a> <a id="3968" class="Symbol">:</a> <a id="3970" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="3976" class="Keyword">where</a>
  <a id="3984" class="Keyword">constructor</a> <a id="make-Large-Strict-Order"></a><a id="3996" href="order-theory.large-strict-orders.html#3996" class="InductiveConstructor">make-Large-Strict-Order</a>
  <a id="4022" class="Keyword">field</a>
    <a id="Large-Strict-Order.large-strict-preorder-Large-Strict-Order"></a><a id="4032" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a> <a id="4073" class="Symbol">:</a> <a id="4075" href="order-theory.large-strict-preorders.html#1308" class="Record">Large-Strict-Preorder</a> <a id="4097" href="order-theory.large-strict-orders.html#3921" class="Bound">α</a> <a id="4099" href="order-theory.large-strict-orders.html#3941" class="Bound">β</a>

    <a id="Large-Strict-Order.extensionality-Large-Strict-Order"></a><a id="4106" href="order-theory.large-strict-orders.html#4106" class="Field">extensionality-Large-Strict-Order</a> <a id="4140" class="Symbol">:</a>
      <a id="4148" href="order-theory.large-strict-orders.html#2651" class="Function">extensionality-principle-Large-Strict-Preorder</a>
        <a id="4203" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a>

  <a id="Large-Strict-Order.type-Large-Strict-Order"></a><a id="4247" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a> <a id="4271" class="Symbol">:</a> <a id="4273" class="Symbol">(</a><a id="4274" href="order-theory.large-strict-orders.html#4274" class="Bound">l</a> <a id="4276" class="Symbol">:</a> <a id="4278" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4283" class="Symbol">)</a> <a id="4285" class="Symbol">→</a> <a id="4287" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4290" class="Symbol">(</a><a id="4291" href="order-theory.large-strict-orders.html#3921" class="Bound">α</a> <a id="4293" href="order-theory.large-strict-orders.html#4274" class="Bound">l</a><a id="4294" class="Symbol">)</a>
  <a id="4298" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a> <a id="4322" class="Symbol">=</a>
    <a id="4328" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a> <a id="4355" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a>

  <a id="Large-Strict-Order.le-Large-Strict-Order"></a><a id="4399" href="order-theory.large-strict-orders.html#4399" class="Function">le-Large-Strict-Order</a> <a id="4421" class="Symbol">:</a>
    <a id="4427" href="foundation.large-binary-relations.html#1089" class="Function">Large-Relation</a> <a id="4442" href="order-theory.large-strict-orders.html#3941" class="Bound">β</a> <a id="4444" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a>
  <a id="4470" href="order-theory.large-strict-orders.html#4399" class="Function">le-Large-Strict-Order</a> <a id="4492" class="Symbol">=</a>
    <a id="4498" href="order-theory.large-strict-preorders.html#1598" class="Function">le-Large-Strict-Preorder</a> <a id="4523" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a>

  <a id="Large-Strict-Order.is-prop-le-Large-Strict-Order"></a><a id="4567" href="order-theory.large-strict-orders.html#4567" class="Function">is-prop-le-Large-Strict-Order</a> <a id="4597" class="Symbol">:</a>
    <a id="4603" class="Symbol">{</a><a id="4604" href="order-theory.large-strict-orders.html#4604" class="Bound">l1</a> <a id="4607" href="order-theory.large-strict-orders.html#4607" class="Bound">l2</a> <a id="4610" class="Symbol">:</a> <a id="4612" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4617" class="Symbol">}</a>
    <a id="4623" class="Symbol">(</a><a id="4624" href="order-theory.large-strict-orders.html#4624" class="Bound">x</a> <a id="4626" class="Symbol">:</a> <a id="4628" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a> <a id="4652" href="order-theory.large-strict-orders.html#4604" class="Bound">l1</a><a id="4654" class="Symbol">)</a>
    <a id="4660" class="Symbol">(</a><a id="4661" href="order-theory.large-strict-orders.html#4661" class="Bound">y</a> <a id="4663" class="Symbol">:</a> <a id="4665" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a> <a id="4689" href="order-theory.large-strict-orders.html#4607" class="Bound">l2</a><a id="4691" class="Symbol">)</a> <a id="4693" class="Symbol">→</a>
    <a id="4699" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="4707" class="Symbol">(</a><a id="4708" href="order-theory.large-strict-orders.html#4399" class="Function">le-Large-Strict-Order</a> <a id="4730" href="order-theory.large-strict-orders.html#4624" class="Bound">x</a> <a id="4732" href="order-theory.large-strict-orders.html#4661" class="Bound">y</a><a id="4733" class="Symbol">)</a>
  <a id="4737" href="order-theory.large-strict-orders.html#4567" class="Function">is-prop-le-Large-Strict-Order</a> <a id="4767" class="Symbol">=</a>
    <a id="4773" href="order-theory.large-strict-preorders.html#1751" class="Function">is-prop-le-Large-Strict-Preorder</a> <a id="4806" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a>

  <a id="Large-Strict-Order.le-prop-Large-Strict-Order"></a><a id="4850" href="order-theory.large-strict-orders.html#4850" class="Function">le-prop-Large-Strict-Order</a> <a id="4877" class="Symbol">:</a> <a id="4879" href="foundation.large-binary-relations.html#1598" class="Function">Large-Relation-Prop</a> <a id="4899" href="order-theory.large-strict-orders.html#3941" class="Bound">β</a> <a id="4901" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a>
  <a id="4927" href="order-theory.large-strict-orders.html#4850" class="Function">le-prop-Large-Strict-Order</a> <a id="4954" class="Symbol">=</a>
    <a id="4960" href="order-theory.large-strict-preorders.html#1508" class="Field">le-prop-Large-Strict-Preorder</a> <a id="4990" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a>

  <a id="Large-Strict-Order.is-irreflexive-le-Large-Strict-Order"></a><a id="5034" href="order-theory.large-strict-orders.html#5034" class="Function">is-irreflexive-le-Large-Strict-Order</a> <a id="5071" class="Symbol">:</a>
    <a id="5077" href="foundation.large-binary-relations.html#3776" class="Function">is-antireflexive-Large-Relation</a>
      <a id="5115" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a>
      <a id="5145" href="order-theory.large-strict-orders.html#4399" class="Function">le-Large-Strict-Order</a>
  <a id="5169" href="order-theory.large-strict-orders.html#5034" class="Function">is-irreflexive-le-Large-Strict-Order</a> <a id="5206" class="Symbol">=</a>
    <a id="5212" href="order-theory.large-strict-preorders.html#2043" class="Field">is-irreflexive-le-Large-Strict-Preorder</a>
      <a id="5258" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a>

  <a id="Large-Strict-Order.is-transitive-le-Large-Strict-Order"></a><a id="5302" href="order-theory.large-strict-orders.html#5302" class="Function">is-transitive-le-Large-Strict-Order</a> <a id="5338" class="Symbol">:</a>
    <a id="5344" href="foundation.large-binary-relations.html#3481" class="Function">is-transitive-Large-Relation</a> <a id="5373" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a> <a id="5397" href="order-theory.large-strict-orders.html#4399" class="Function">le-Large-Strict-Order</a>
  <a id="5421" href="order-theory.large-strict-orders.html#5302" class="Function">is-transitive-le-Large-Strict-Order</a> <a id="5457" class="Symbol">=</a>
    <a id="5463" href="order-theory.large-strict-preorders.html#2202" class="Field">transitive-le-Large-Strict-Preorder</a> <a id="5499" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a>

<a id="5541" class="Keyword">open</a> <a id="5546" href="order-theory.large-strict-orders.html#3901" class="Module">Large-Strict-Order</a> <a id="5565" class="Keyword">public</a>
</pre>
### The underlying strict order at a universe level

<pre class="Agda"><a id="5638" class="Keyword">module</a> <a id="5645" href="order-theory.large-strict-orders.html#5645" class="Module">_</a>
  <a id="5649" class="Symbol">{</a><a id="5650" href="order-theory.large-strict-orders.html#5650" class="Bound">α</a> <a id="5652" class="Symbol">:</a> <a id="5654" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="5660" class="Symbol">→</a> <a id="5662" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5667" class="Symbol">}</a> <a id="5669" class="Symbol">{</a><a id="5670" href="order-theory.large-strict-orders.html#5670" class="Bound">β</a> <a id="5672" class="Symbol">:</a> <a id="5674" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="5680" class="Symbol">→</a> <a id="5682" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="5688" class="Symbol">→</a> <a id="5690" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5695" class="Symbol">}</a>
  <a id="5699" class="Symbol">(</a><a id="5700" href="order-theory.large-strict-orders.html#5700" class="Bound">A</a> <a id="5702" class="Symbol">:</a> <a id="5704" href="order-theory.large-strict-orders.html#3901" class="Record">Large-Strict-Order</a> <a id="5723" href="order-theory.large-strict-orders.html#5650" class="Bound">α</a> <a id="5725" href="order-theory.large-strict-orders.html#5670" class="Bound">β</a><a id="5726" class="Symbol">)</a>
  <a id="5730" class="Keyword">where</a>

  <a id="5739" href="order-theory.large-strict-orders.html#5739" class="Function">strict-preorder-Large-Strict-Order</a> <a id="5774" class="Symbol">:</a>
    <a id="5780" class="Symbol">(</a><a id="5781" href="order-theory.large-strict-orders.html#5781" class="Bound">l</a> <a id="5783" class="Symbol">:</a> <a id="5785" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5790" class="Symbol">)</a> <a id="5792" class="Symbol">→</a> <a id="5794" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="5810" class="Symbol">(</a><a id="5811" href="order-theory.large-strict-orders.html#5650" class="Bound">α</a> <a id="5813" href="order-theory.large-strict-orders.html#5781" class="Bound">l</a><a id="5814" class="Symbol">)</a> <a id="5816" class="Symbol">(</a><a id="5817" href="order-theory.large-strict-orders.html#5670" class="Bound">β</a> <a id="5819" href="order-theory.large-strict-orders.html#5781" class="Bound">l</a> <a id="5821" href="order-theory.large-strict-orders.html#5781" class="Bound">l</a><a id="5822" class="Symbol">)</a>
  <a id="5826" href="order-theory.large-strict-orders.html#5739" class="Function">strict-preorder-Large-Strict-Order</a> <a id="5861" class="Symbol">=</a>
    <a id="5867" href="order-theory.large-strict-preorders.html#2557" class="Function">strict-preorder-Large-Strict-Preorder</a>
      <a id="5911" class="Symbol">(</a> <a id="5913" href="order-theory.large-strict-orders.html#4032" class="Field">large-strict-preorder-Large-Strict-Order</a> <a id="5954" href="order-theory.large-strict-orders.html#5700" class="Bound">A</a><a id="5955" class="Symbol">)</a>

  <a id="5960" href="order-theory.large-strict-orders.html#5960" class="Function">extensionality-strict-preorder-Large-Strict-Order</a> <a id="6010" class="Symbol">:</a>
    <a id="6016" class="Symbol">(</a><a id="6017" href="order-theory.large-strict-orders.html#6017" class="Bound">l</a> <a id="6019" class="Symbol">:</a> <a id="6021" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6026" class="Symbol">)</a> <a id="6028" class="Symbol">→</a>
    <a id="6034" href="order-theory.strict-orders.html#1932" class="Function">extensionality-principle-Strict-Preorder</a>
      <a id="6081" class="Symbol">(</a> <a id="6083" href="order-theory.large-strict-orders.html#5739" class="Function">strict-preorder-Large-Strict-Order</a> <a id="6118" href="order-theory.large-strict-orders.html#6017" class="Bound">l</a><a id="6119" class="Symbol">)</a>
  <a id="6123" href="order-theory.large-strict-orders.html#5960" class="Function">extensionality-strict-preorder-Large-Strict-Order</a> <a id="6173" href="order-theory.large-strict-orders.html#6173" class="Bound">l</a> <a id="6175" class="Symbol">=</a>
    <a id="6181" href="order-theory.large-strict-orders.html#4106" class="Field">extensionality-Large-Strict-Order</a> <a id="6215" href="order-theory.large-strict-orders.html#5700" class="Bound">A</a>

  <a id="6220" href="order-theory.large-strict-orders.html#6220" class="Function">strict-order-Large-Strict-Order</a> <a id="6252" class="Symbol">:</a>
    <a id="6258" class="Symbol">(</a><a id="6259" href="order-theory.large-strict-orders.html#6259" class="Bound">l</a> <a id="6261" class="Symbol">:</a> <a id="6263" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6268" class="Symbol">)</a> <a id="6270" class="Symbol">→</a> <a id="6272" href="order-theory.strict-orders.html#2190" class="Function">Strict-Order</a> <a id="6285" class="Symbol">(</a><a id="6286" href="order-theory.large-strict-orders.html#5650" class="Bound">α</a> <a id="6288" href="order-theory.large-strict-orders.html#6259" class="Bound">l</a><a id="6289" class="Symbol">)</a> <a id="6291" class="Symbol">(</a><a id="6292" href="order-theory.large-strict-orders.html#5670" class="Bound">β</a> <a id="6294" href="order-theory.large-strict-orders.html#6259" class="Bound">l</a> <a id="6296" href="order-theory.large-strict-orders.html#6259" class="Bound">l</a><a id="6297" class="Symbol">)</a>
  <a id="6301" href="order-theory.large-strict-orders.html#6220" class="Function">strict-order-Large-Strict-Order</a> <a id="6333" href="order-theory.large-strict-orders.html#6333" class="Bound">l</a> <a id="6335" class="Symbol">=</a>
    <a id="6341" class="Symbol">(</a> <a id="6343" href="order-theory.large-strict-orders.html#5739" class="Function">strict-preorder-Large-Strict-Order</a> <a id="6378" href="order-theory.large-strict-orders.html#6333" class="Bound">l</a> <a id="6380" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="6388" href="order-theory.large-strict-orders.html#5960" class="Function">extensionality-strict-preorder-Large-Strict-Order</a> <a id="6438" href="order-theory.large-strict-orders.html#6333" class="Bound">l</a><a id="6439" class="Symbol">)</a>
</pre>
## Properties

### The underlying hierarchy of types is a hierarchy of sets

<pre class="Agda"><a id="6531" class="Keyword">module</a> <a id="6538" href="order-theory.large-strict-orders.html#6538" class="Module">_</a>
  <a id="6542" class="Symbol">{</a><a id="6543" href="order-theory.large-strict-orders.html#6543" class="Bound">α</a> <a id="6545" class="Symbol">:</a> <a id="6547" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="6553" class="Symbol">→</a> <a id="6555" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6560" class="Symbol">}</a> <a id="6562" class="Symbol">{</a><a id="6563" href="order-theory.large-strict-orders.html#6563" class="Bound">β</a> <a id="6565" class="Symbol">:</a> <a id="6567" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="6573" class="Symbol">→</a> <a id="6575" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="6581" class="Symbol">→</a> <a id="6583" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6588" class="Symbol">}</a>
  <a id="6592" class="Symbol">(</a><a id="6593" href="order-theory.large-strict-orders.html#6593" class="Bound">A</a> <a id="6595" class="Symbol">:</a> <a id="6597" href="order-theory.large-strict-orders.html#3901" class="Record">Large-Strict-Order</a> <a id="6616" href="order-theory.large-strict-orders.html#6543" class="Bound">α</a> <a id="6618" href="order-theory.large-strict-orders.html#6563" class="Bound">β</a><a id="6619" class="Symbol">)</a>
  <a id="6623" class="Keyword">where</a>

  <a id="6632" href="order-theory.large-strict-orders.html#6632" class="Function">is-set-type-Large-Strict-Order</a> <a id="6663" class="Symbol">:</a>
    <a id="6669" class="Symbol">{</a><a id="6670" href="order-theory.large-strict-orders.html#6670" class="Bound">l</a> <a id="6672" class="Symbol">:</a> <a id="6674" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6679" class="Symbol">}</a> <a id="6681" class="Symbol">→</a> <a id="6683" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="6690" class="Symbol">(</a><a id="6691" href="order-theory.large-strict-orders.html#4247" class="Function">type-Large-Strict-Order</a> <a id="6715" href="order-theory.large-strict-orders.html#6593" class="Bound">A</a> <a id="6717" href="order-theory.large-strict-orders.html#6670" class="Bound">l</a><a id="6718" class="Symbol">)</a>
  <a id="6722" href="order-theory.large-strict-orders.html#6632" class="Function">is-set-type-Large-Strict-Order</a> <a id="6753" class="Symbol">{</a><a id="6754" href="order-theory.large-strict-orders.html#6754" class="Bound">l</a><a id="6755" class="Symbol">}</a> <a id="6757" class="Symbol">=</a>
    <a id="6763" href="order-theory.strict-orders.html#3970" class="Function">is-set-type-Strict-Order</a> <a id="6788" class="Symbol">(</a><a id="6789" href="order-theory.large-strict-orders.html#6220" class="Function">strict-order-Large-Strict-Order</a> <a id="6821" href="order-theory.large-strict-orders.html#6593" class="Bound">A</a> <a id="6823" href="order-theory.large-strict-orders.html#6754" class="Bound">l</a><a id="6824" class="Symbol">)</a>

  <a id="6829" href="order-theory.large-strict-orders.html#6829" class="Function">set-Large-Strict-Order</a> <a id="6852" class="Symbol">:</a> <a id="6854" class="Symbol">(</a><a id="6855" href="order-theory.large-strict-orders.html#6855" class="Bound">l</a> <a id="6857" class="Symbol">:</a> <a id="6859" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6864" class="Symbol">)</a> <a id="6866" class="Symbol">→</a> <a id="6868" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="6872" class="Symbol">(</a><a id="6873" href="order-theory.large-strict-orders.html#6543" class="Bound">α</a> <a id="6875" href="order-theory.large-strict-orders.html#6855" class="Bound">l</a><a id="6876" class="Symbol">)</a>
  <a id="6880" href="order-theory.large-strict-orders.html#6829" class="Function">set-Large-Strict-Order</a> <a id="6903" href="order-theory.large-strict-orders.html#6903" class="Bound">l</a> <a id="6905" class="Symbol">=</a>
    <a id="6911" href="order-theory.strict-orders.html#4318" class="Function">set-Strict-Order</a> <a id="6928" class="Symbol">(</a><a id="6929" href="order-theory.large-strict-orders.html#6220" class="Function">strict-order-Large-Strict-Order</a> <a id="6961" href="order-theory.large-strict-orders.html#6593" class="Bound">A</a> <a id="6963" href="order-theory.large-strict-orders.html#6903" class="Bound">l</a><a id="6964" class="Symbol">)</a>
</pre>
### The extensionality principle is a proposition at every universe level

<pre class="Agda"><a id="7054" class="Keyword">module</a> <a id="7061" href="order-theory.large-strict-orders.html#7061" class="Module">_</a>
  <a id="7065" class="Symbol">{</a><a id="7066" href="order-theory.large-strict-orders.html#7066" class="Bound">α</a> <a id="7068" class="Symbol">:</a> <a id="7070" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="7076" class="Symbol">→</a> <a id="7078" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7083" class="Symbol">}</a> <a id="7085" class="Symbol">{</a><a id="7086" href="order-theory.large-strict-orders.html#7086" class="Bound">β</a> <a id="7088" class="Symbol">:</a> <a id="7090" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="7096" class="Symbol">→</a> <a id="7098" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="7104" class="Symbol">→</a> <a id="7106" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7111" class="Symbol">}</a>
  <a id="7115" class="Symbol">(</a><a id="7116" href="order-theory.large-strict-orders.html#7116" class="Bound">A</a> <a id="7118" class="Symbol">:</a> <a id="7120" href="order-theory.large-strict-preorders.html#1308" class="Record">Large-Strict-Preorder</a> <a id="7142" href="order-theory.large-strict-orders.html#7066" class="Bound">α</a> <a id="7144" href="order-theory.large-strict-orders.html#7086" class="Bound">β</a><a id="7145" class="Symbol">)</a>
  <a id="7149" class="Keyword">where</a>

  <a id="7158" href="order-theory.large-strict-orders.html#7158" class="Function">is-prop-extensionality-principle-level-Large-Strict-Preorder</a> <a id="7219" class="Symbol">:</a>
    <a id="7225" class="Symbol">{</a><a id="7226" href="order-theory.large-strict-orders.html#7226" class="Bound">l</a> <a id="7228" class="Symbol">:</a> <a id="7230" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7235" class="Symbol">}</a> <a id="7237" class="Symbol">→</a>
    <a id="7243" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="7251" class="Symbol">(</a><a id="7252" href="order-theory.large-strict-orders.html#2398" class="Function">extensionality-principle-level-Large-Strict-Preorder</a> <a id="7305" href="order-theory.large-strict-orders.html#7116" class="Bound">A</a> <a id="7307" href="order-theory.large-strict-orders.html#7226" class="Bound">l</a><a id="7308" class="Symbol">)</a>
  <a id="7312" href="order-theory.large-strict-orders.html#7158" class="Function">is-prop-extensionality-principle-level-Large-Strict-Preorder</a> <a id="7373" class="Symbol">{</a><a id="7374" href="order-theory.large-strict-orders.html#7374" class="Bound">l</a><a id="7375" class="Symbol">}</a> <a id="7377" class="Symbol">=</a>
    <a id="7383" href="order-theory.strict-orders.html#5226" class="Function">is-prop-extensionality-principle-Strict-Preorder</a>
      <a id="7438" class="Symbol">(</a> <a id="7440" href="order-theory.large-strict-preorders.html#2557" class="Function">strict-preorder-Large-Strict-Preorder</a> <a id="7478" href="order-theory.large-strict-orders.html#7116" class="Bound">A</a> <a id="7480" href="order-theory.large-strict-orders.html#7374" class="Bound">l</a><a id="7481" class="Symbol">)</a>

  <a id="7486" href="order-theory.large-strict-orders.html#7486" class="Function">extensionality-principle-level-prop-Large-Strict-Preorder</a> <a id="7544" class="Symbol">:</a>
    <a id="7550" class="Symbol">(</a><a id="7551" href="order-theory.large-strict-orders.html#7551" class="Bound">l</a> <a id="7553" class="Symbol">:</a> <a id="7555" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7560" class="Symbol">)</a> <a id="7562" class="Symbol">→</a> <a id="7564" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="7569" class="Symbol">(</a><a id="7570" href="order-theory.large-strict-orders.html#7066" class="Bound">α</a> <a id="7572" href="order-theory.large-strict-orders.html#7551" class="Bound">l</a> <a id="7574" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="7576" href="order-theory.large-strict-orders.html#7086" class="Bound">β</a> <a id="7578" href="order-theory.large-strict-orders.html#7551" class="Bound">l</a> <a id="7580" href="order-theory.large-strict-orders.html#7551" class="Bound">l</a><a id="7581" class="Symbol">)</a>
  <a id="7585" href="order-theory.large-strict-orders.html#7486" class="Function">extensionality-principle-level-prop-Large-Strict-Preorder</a> <a id="7643" href="order-theory.large-strict-orders.html#7643" class="Bound">l</a> <a id="7645" class="Symbol">=</a>
    <a id="7651" class="Symbol">(</a> <a id="7653" href="order-theory.large-strict-orders.html#2398" class="Function">extensionality-principle-level-Large-Strict-Preorder</a> <a id="7706" href="order-theory.large-strict-orders.html#7116" class="Bound">A</a> <a id="7708" href="order-theory.large-strict-orders.html#7643" class="Bound">l</a> <a id="7710" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="7718" href="order-theory.large-strict-orders.html#7158" class="Function">is-prop-extensionality-principle-level-Large-Strict-Preorder</a><a id="7778" class="Symbol">)</a>
</pre>
## References

{{#bibliography}}
