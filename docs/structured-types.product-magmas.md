# Products of magmas

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="structured-types.product-magmas.html" class="Module">structured-types.product-magmas</a> <a id="70" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="126" class="Keyword">open</a> <a id="131" class="Keyword">import</a> <a id="138" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="structured-types.magmas.html" class="Module">structured-types.magmas</a>
</pre>
</details>

## Idea

For any pair of [magmas](structured-types.magmas.md) `M` and `N`, their
[cartesian product](foundation.cartesian-product-types.md) `M × N` carries a
natural magma structure.

## Definition

<pre class="Agda"><a id="517" class="Keyword">module</a> <a id="524" href="structured-types.product-magmas.html#524" class="Module">_</a>
  <a id="528" class="Symbol">{</a><a id="529" href="structured-types.product-magmas.html#529" class="Bound">l1</a> <a id="532" href="structured-types.product-magmas.html#532" class="Bound">l2</a> <a id="535" class="Symbol">:</a> <a id="537" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="542" class="Symbol">}</a> <a id="544" class="Symbol">(</a><a id="545" href="structured-types.product-magmas.html#545" class="Bound">M</a> <a id="547" class="Symbol">:</a> <a id="549" href="structured-types.magmas.html#477" class="Function">Magma</a> <a id="555" href="structured-types.product-magmas.html#529" class="Bound">l1</a><a id="557" class="Symbol">)</a> <a id="559" class="Symbol">(</a><a id="560" href="structured-types.product-magmas.html#560" class="Bound">N</a> <a id="562" class="Symbol">:</a> <a id="564" href="structured-types.magmas.html#477" class="Function">Magma</a> <a id="570" href="structured-types.product-magmas.html#532" class="Bound">l2</a><a id="572" class="Symbol">)</a>
  <a id="576" class="Keyword">where</a>

  <a id="585" href="structured-types.product-magmas.html#585" class="Function">product-Magma</a> <a id="599" class="Symbol">:</a> <a id="601" href="structured-types.magmas.html#477" class="Function">Magma</a> <a id="607" class="Symbol">(</a><a id="608" href="structured-types.product-magmas.html#529" class="Bound">l1</a> <a id="611" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="613" href="structured-types.product-magmas.html#532" class="Bound">l2</a><a id="615" class="Symbol">)</a>
  <a id="619" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="623" href="structured-types.product-magmas.html#585" class="Function">product-Magma</a> <a id="637" class="Symbol">=</a> <a id="639" href="structured-types.magmas.html#597" class="Function">type-Magma</a> <a id="650" href="structured-types.product-magmas.html#545" class="Bound">M</a> <a id="652" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="654" href="structured-types.magmas.html#597" class="Function">type-Magma</a> <a id="665" href="structured-types.product-magmas.html#560" class="Bound">N</a>
  <a id="669" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="673" href="structured-types.product-magmas.html#585" class="Function">product-Magma</a> <a id="687" class="Symbol">(</a><a id="688" href="structured-types.product-magmas.html#688" class="Bound">x</a> <a id="690" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="692" href="structured-types.product-magmas.html#692" class="Bound">y</a><a id="693" class="Symbol">)</a> <a id="695" class="Symbol">(</a><a id="696" href="structured-types.product-magmas.html#696" class="Bound">z</a> <a id="698" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="700" href="structured-types.product-magmas.html#700" class="Bound">w</a><a id="701" class="Symbol">)</a> <a id="703" class="Symbol">=</a> <a id="705" href="structured-types.magmas.html#639" class="Function">mul-Magma</a> <a id="715" href="structured-types.product-magmas.html#545" class="Bound">M</a> <a id="717" href="structured-types.product-magmas.html#688" class="Bound">x</a> <a id="719" href="structured-types.product-magmas.html#696" class="Bound">z</a> <a id="721" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="723" href="structured-types.magmas.html#639" class="Function">mul-Magma</a> <a id="733" href="structured-types.product-magmas.html#560" class="Bound">N</a> <a id="735" href="structured-types.product-magmas.html#692" class="Bound">y</a> <a id="737" href="structured-types.product-magmas.html#700" class="Bound">w</a>
</pre>