# Equivalences of species of types

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="species.equivalences-species-of-types.html" class="Module">species.equivalences-species-of-types</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of species of types" Agda=equiv-species-types}}
of [species of types](species.species-of-types.md) from `F` to `G` is a
pointwise [equivalence](foundation-core.equivalences.md).

## Definition

<pre class="Agda"><a id="equiv-species-types"></a><a id="603" href="species.equivalences-species-of-types.html#603" class="Function">equiv-species-types</a> <a id="623" class="Symbol">:</a>
  <a id="627" class="Symbol">{</a><a id="628" href="species.equivalences-species-of-types.html#628" class="Bound">l1</a> <a id="631" href="species.equivalences-species-of-types.html#631" class="Bound">l2</a> <a id="634" href="species.equivalences-species-of-types.html#634" class="Bound">l3</a> <a id="637" class="Symbol">:</a> <a id="639" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="644" class="Symbol">}</a> <a id="646" class="Symbol">→</a> <a id="648" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="662" href="species.equivalences-species-of-types.html#628" class="Bound">l1</a> <a id="665" href="species.equivalences-species-of-types.html#631" class="Bound">l2</a> <a id="668" class="Symbol">→</a> <a id="670" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="684" href="species.equivalences-species-of-types.html#628" class="Bound">l1</a> <a id="687" href="species.equivalences-species-of-types.html#634" class="Bound">l3</a> <a id="690" class="Symbol">→</a>
  <a id="694" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="697" class="Symbol">(</a><a id="698" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="703" href="species.equivalences-species-of-types.html#628" class="Bound">l1</a> <a id="706" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="708" href="species.equivalences-species-of-types.html#631" class="Bound">l2</a> <a id="711" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="713" href="species.equivalences-species-of-types.html#634" class="Bound">l3</a><a id="715" class="Symbol">)</a>
<a id="717" href="species.equivalences-species-of-types.html#603" class="Function">equiv-species-types</a> <a id="737" class="Symbol">{</a><a id="738" href="species.equivalences-species-of-types.html#738" class="Bound">l1</a><a id="740" class="Symbol">}</a> <a id="742" href="species.equivalences-species-of-types.html#742" class="Bound">F</a> <a id="744" href="species.equivalences-species-of-types.html#744" class="Bound">G</a> <a id="746" class="Symbol">=</a> <a id="748" class="Symbol">((</a><a id="750" href="species.equivalences-species-of-types.html#750" class="Bound">X</a> <a id="752" class="Symbol">:</a> <a id="754" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="757" href="species.equivalences-species-of-types.html#738" class="Bound">l1</a><a id="759" class="Symbol">)</a> <a id="761" class="Symbol">→</a> <a id="763" href="species.equivalences-species-of-types.html#742" class="Bound">F</a> <a id="765" href="species.equivalences-species-of-types.html#750" class="Bound">X</a> <a id="767" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="769" href="species.equivalences-species-of-types.html#744" class="Bound">G</a> <a id="771" href="species.equivalences-species-of-types.html#750" class="Bound">X</a><a id="772" class="Symbol">)</a>
</pre>
## Properties

### The identity type of two species of types is equivalent to the type of equivalences between them

<pre class="Agda"><a id="extensionality-species-types"></a><a id="904" href="species.equivalences-species-of-types.html#904" class="Function">extensionality-species-types</a> <a id="933" class="Symbol">:</a>
  <a id="937" class="Symbol">{</a><a id="938" href="species.equivalences-species-of-types.html#938" class="Bound">l1</a> <a id="941" href="species.equivalences-species-of-types.html#941" class="Bound">l2</a> <a id="944" class="Symbol">:</a> <a id="946" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="951" class="Symbol">}</a> <a id="953" class="Symbol">(</a><a id="954" href="species.equivalences-species-of-types.html#954" class="Bound">F</a> <a id="956" href="species.equivalences-species-of-types.html#956" class="Bound">G</a> <a id="958" class="Symbol">:</a> <a id="960" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="974" href="species.equivalences-species-of-types.html#938" class="Bound">l1</a> <a id="977" href="species.equivalences-species-of-types.html#941" class="Bound">l2</a><a id="979" class="Symbol">)</a> <a id="981" class="Symbol">→</a>
  <a id="985" class="Symbol">(</a><a id="986" href="species.equivalences-species-of-types.html#954" class="Bound">F</a> <a id="988" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="990" href="species.equivalences-species-of-types.html#956" class="Bound">G</a><a id="991" class="Symbol">)</a> <a id="993" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="995" class="Symbol">(</a><a id="996" href="species.equivalences-species-of-types.html#603" class="Function">equiv-species-types</a> <a id="1016" href="species.equivalences-species-of-types.html#954" class="Bound">F</a> <a id="1018" href="species.equivalences-species-of-types.html#956" class="Bound">G</a><a id="1019" class="Symbol">)</a>
<a id="1021" href="species.equivalences-species-of-types.html#904" class="Function">extensionality-species-types</a> <a id="1050" class="Symbol">=</a> <a id="1052" href="foundation.univalence.html#5169" class="Function">extensionality-fam</a>
</pre>