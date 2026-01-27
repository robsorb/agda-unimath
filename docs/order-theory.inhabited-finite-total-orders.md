# Inhabited finite total orders

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="order-theory.inhabited-finite-total-orders.html" class="Module">order-theory.inhabited-finite-total-orders</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="order-theory.finite-posets.html" class="Module">order-theory.finite-posets</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="order-theory.finite-total-orders.html" class="Module">order-theory.finite-total-orders</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="order-theory.total-orders.html" class="Module">order-theory.total-orders</a>

<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Definitions

An **inhabited finite total order** is a
[finite total order](order-theory.finite-total-orders.md) of which the
underlying type is [inhabited](foundation.inhabited-types.md).

<pre class="Agda"><a id="684" class="Keyword">module</a> <a id="691" href="order-theory.inhabited-finite-total-orders.html#691" class="Module">_</a>
  <a id="695" class="Symbol">{</a><a id="696" href="order-theory.inhabited-finite-total-orders.html#696" class="Bound">l1</a> <a id="699" href="order-theory.inhabited-finite-total-orders.html#699" class="Bound">l2</a> <a id="702" class="Symbol">:</a> <a id="704" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="709" class="Symbol">}</a> <a id="711" class="Symbol">(</a><a id="712" href="order-theory.inhabited-finite-total-orders.html#712" class="Bound">P</a> <a id="714" class="Symbol">:</a> <a id="716" href="order-theory.finite-total-orders.html#1846" class="Function">Finite-Total-Order</a> <a id="735" href="order-theory.inhabited-finite-total-orders.html#696" class="Bound">l1</a> <a id="738" href="order-theory.inhabited-finite-total-orders.html#699" class="Bound">l2</a><a id="740" class="Symbol">)</a>
  <a id="744" class="Keyword">where</a>

  <a id="753" href="order-theory.inhabited-finite-total-orders.html#753" class="Function">is-inhabited-Finite-Total-Order-Prop</a> <a id="790" class="Symbol">:</a> <a id="792" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="797" href="order-theory.inhabited-finite-total-orders.html#696" class="Bound">l1</a>
  <a id="802" href="order-theory.inhabited-finite-total-orders.html#753" class="Function">is-inhabited-Finite-Total-Order-Prop</a> <a id="839" class="Symbol">=</a>
    <a id="845" href="foundation.inhabited-types.html#1261" class="Function">is-inhabited-Prop</a> <a id="863" class="Symbol">(</a><a id="864" href="order-theory.finite-total-orders.html#2719" class="Function">type-Finite-Total-Order</a> <a id="888" href="order-theory.inhabited-finite-total-orders.html#712" class="Bound">P</a><a id="889" class="Symbol">)</a>

  <a id="894" href="order-theory.inhabited-finite-total-orders.html#894" class="Function">is-inhabited-Finite-Total-Order</a> <a id="926" class="Symbol">:</a> <a id="928" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="931" class="Symbol">(</a><a id="932" href="order-theory.inhabited-finite-total-orders.html#696" class="Bound">l1</a> <a id="935" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="937" href="order-theory.inhabited-finite-total-orders.html#699" class="Bound">l2</a><a id="939" class="Symbol">)</a>
  <a id="943" href="order-theory.inhabited-finite-total-orders.html#894" class="Function">is-inhabited-Finite-Total-Order</a> <a id="975" class="Symbol">=</a> <a id="977" href="order-theory.finite-posets.html#904" class="Function">is-finite-Poset</a> <a id="993" class="Symbol">(</a><a id="994" href="order-theory.finite-total-orders.html#2152" class="Function">poset-Finite-Total-Order</a> <a id="1019" href="order-theory.inhabited-finite-total-orders.html#712" class="Bound">P</a><a id="1020" class="Symbol">)</a>

  <a id="1025" href="order-theory.inhabited-finite-total-orders.html#1025" class="Function">is-property-is-inhabited-Finite-Total-Order</a> <a id="1069" class="Symbol">:</a>
    <a id="1075" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1083" href="order-theory.inhabited-finite-total-orders.html#894" class="Function">is-inhabited-Finite-Total-Order</a>
  <a id="1117" href="order-theory.inhabited-finite-total-orders.html#1025" class="Function">is-property-is-inhabited-Finite-Total-Order</a> <a id="1161" class="Symbol">=</a>
    <a id="1167" href="order-theory.finite-posets.html#996" class="Function">is-prop-is-finite-Poset</a> <a id="1191" class="Symbol">(</a><a id="1192" href="order-theory.finite-total-orders.html#2152" class="Function">poset-Finite-Total-Order</a> <a id="1217" href="order-theory.inhabited-finite-total-orders.html#712" class="Bound">P</a><a id="1218" class="Symbol">)</a>

  <a id="1223" href="order-theory.inhabited-finite-total-orders.html#1223" class="Function">is-finite-type-is-inhabited-Finite-Total-Order</a> <a id="1270" class="Symbol">:</a>
    <a id="1276" href="order-theory.inhabited-finite-total-orders.html#894" class="Function">is-inhabited-Finite-Total-Order</a> <a id="1308" class="Symbol">→</a> <a id="1310" href="univalent-combinatorics.finite-types.html#2289" class="Function">is-finite</a> <a id="1320" class="Symbol">(</a><a id="1321" href="order-theory.finite-total-orders.html#2719" class="Function">type-Finite-Total-Order</a> <a id="1345" href="order-theory.inhabited-finite-total-orders.html#712" class="Bound">P</a><a id="1346" class="Symbol">)</a>
  <a id="1350" href="order-theory.inhabited-finite-total-orders.html#1223" class="Function">is-finite-type-is-inhabited-Finite-Total-Order</a> <a id="1397" class="Symbol">=</a>
    <a id="1403" href="order-theory.finite-posets.html#1123" class="Function">is-finite-type-is-finite-Poset</a> <a id="1434" class="Symbol">(</a><a id="1435" href="order-theory.finite-total-orders.html#2152" class="Function">poset-Finite-Total-Order</a> <a id="1460" href="order-theory.inhabited-finite-total-orders.html#712" class="Bound">P</a><a id="1461" class="Symbol">)</a>

<a id="is-inhabited-finite-total-order-Poset-Prop"></a><a id="1464" href="order-theory.inhabited-finite-total-orders.html#1464" class="Function">is-inhabited-finite-total-order-Poset-Prop</a> <a id="1507" class="Symbol">:</a>
  <a id="1511" class="Symbol">{</a><a id="1512" href="order-theory.inhabited-finite-total-orders.html#1512" class="Bound">l1</a> <a id="1515" href="order-theory.inhabited-finite-total-orders.html#1515" class="Bound">l2</a> <a id="1518" class="Symbol">:</a> <a id="1520" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1525" class="Symbol">}</a> <a id="1527" class="Symbol">(</a><a id="1528" href="order-theory.inhabited-finite-total-orders.html#1528" class="Bound">P</a> <a id="1530" class="Symbol">:</a> <a id="1532" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1538" href="order-theory.inhabited-finite-total-orders.html#1512" class="Bound">l1</a> <a id="1541" href="order-theory.inhabited-finite-total-orders.html#1515" class="Bound">l2</a><a id="1543" class="Symbol">)</a> <a id="1545" class="Symbol">→</a> <a id="1547" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1552" class="Symbol">(</a><a id="1553" href="order-theory.inhabited-finite-total-orders.html#1512" class="Bound">l1</a> <a id="1556" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1558" href="order-theory.inhabited-finite-total-orders.html#1515" class="Bound">l2</a><a id="1560" class="Symbol">)</a>
<a id="1562" href="order-theory.inhabited-finite-total-orders.html#1464" class="Function">is-inhabited-finite-total-order-Poset-Prop</a> <a id="1605" href="order-theory.inhabited-finite-total-orders.html#1605" class="Bound">P</a> <a id="1607" class="Symbol">=</a>
  <a id="1611" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
    <a id="1628" class="Symbol">(</a> <a id="1630" href="order-theory.total-orders.html#1795" class="Function">is-total-Poset-Prop</a> <a id="1650" href="order-theory.inhabited-finite-total-orders.html#1605" class="Bound">P</a><a id="1651" class="Symbol">)</a>
    <a id="1657" class="Symbol">(</a> <a id="1659" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="1678" class="Symbol">(</a> <a id="1680" href="order-theory.finite-posets.html#795" class="Function">is-finite-Poset-Prop</a> <a id="1701" href="order-theory.inhabited-finite-total-orders.html#1605" class="Bound">P</a><a id="1702" class="Symbol">)</a>
      <a id="1710" class="Symbol">(</a> <a id="1712" href="foundation.inhabited-types.html#1261" class="Function">is-inhabited-Prop</a> <a id="1730" class="Symbol">(</a><a id="1731" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1742" href="order-theory.inhabited-finite-total-orders.html#1605" class="Bound">P</a><a id="1743" class="Symbol">)))</a>
</pre>