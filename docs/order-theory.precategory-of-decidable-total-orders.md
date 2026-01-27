# The precategory of decidable total orders

<pre class="Agda"><a id="54" class="Keyword">module</a> <a id="61" href="order-theory.precategory-of-decidable-total-orders.html" class="Module">order-theory.precategory-of-decidable-total-orders</a> <a id="112" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="order-theory.decidable-total-orders.html" class="Module">order-theory.decidable-total-orders</a>
<a id="403" class="Keyword">open</a> <a id="408" class="Keyword">import</a> <a id="415" href="order-theory.precategory-of-posets.html" class="Module">order-theory.precategory-of-posets</a>
</pre>
</details>

## Idea

The **(large) precategory of decidable total orders** consists of
[decidable total orders](order-theory.decidable-total-orders.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of decidable total orders

<pre class="Agda"><a id="parametric-Decidable-Total-Order-Full-Large-Subprecategory"></a><a id="922" href="order-theory.precategory-of-decidable-total-orders.html#922" class="Function">parametric-Decidable-Total-Order-Full-Large-Subprecategory</a> <a id="981" class="Symbol">:</a>
  <a id="985" class="Symbol">(</a><a id="986" href="order-theory.precategory-of-decidable-total-orders.html#986" class="Bound">α</a> <a id="988" href="order-theory.precategory-of-decidable-total-orders.html#988" class="Bound">β</a> <a id="990" class="Symbol">:</a> <a id="992" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="998" class="Symbol">→</a> <a id="1000" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1005" class="Symbol">)</a> <a id="1007" class="Symbol">→</a>
  <a id="1011" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a>
    <a id="1041" class="Symbol">(</a> <a id="1043" class="Symbol">λ</a> <a id="1045" href="order-theory.precategory-of-decidable-total-orders.html#1045" class="Bound">l</a> <a id="1047" class="Symbol">→</a> <a id="1049" href="order-theory.precategory-of-decidable-total-orders.html#986" class="Bound">α</a> <a id="1051" href="order-theory.precategory-of-decidable-total-orders.html#1045" class="Bound">l</a> <a id="1053" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1055" href="order-theory.precategory-of-decidable-total-orders.html#988" class="Bound">β</a> <a id="1057" href="order-theory.precategory-of-decidable-total-orders.html#1045" class="Bound">l</a><a id="1058" class="Symbol">)</a>
    <a id="1064" class="Symbol">(</a> <a id="1066" href="order-theory.precategory-of-posets.html#1319" class="Function">parametric-Poset-Large-Precategory</a> <a id="1101" href="order-theory.precategory-of-decidable-total-orders.html#986" class="Bound">α</a> <a id="1103" href="order-theory.precategory-of-decidable-total-orders.html#988" class="Bound">β</a><a id="1104" class="Symbol">)</a>
<a id="1106" href="order-theory.precategory-of-decidable-total-orders.html#922" class="Function">parametric-Decidable-Total-Order-Full-Large-Subprecategory</a> <a id="1165" href="order-theory.precategory-of-decidable-total-orders.html#1165" class="Bound">α</a> <a id="1167" href="order-theory.precategory-of-decidable-total-orders.html#1167" class="Bound">β</a> <a id="1169" class="Symbol">=</a>
  <a id="1173" href="order-theory.decidable-total-orders.html#1401" class="Function">is-decidable-total-prop-Poset</a>

<a id="Decidable-Total-Order-Large-Precategory"></a><a id="1204" href="order-theory.precategory-of-decidable-total-orders.html#1204" class="Function">Decidable-Total-Order-Large-Precategory</a> <a id="1244" class="Symbol">:</a>
  <a id="1248" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1266" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1271" class="Symbol">(</a><a id="1272" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1275" class="Symbol">)</a>
<a id="1277" href="order-theory.precategory-of-decidable-total-orders.html#1204" class="Function">Decidable-Total-Order-Large-Precategory</a> <a id="1317" class="Symbol">=</a>
  <a id="1321" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1369" class="Symbol">(</a> <a id="1371" href="order-theory.precategory-of-posets.html#2115" class="Function">Poset-Large-Precategory</a><a id="1394" class="Symbol">)</a>
    <a id="1400" class="Symbol">(</a> <a id="1402" href="order-theory.precategory-of-decidable-total-orders.html#922" class="Function">parametric-Decidable-Total-Order-Full-Large-Subprecategory</a>
      <a id="1467" class="Symbol">(</a> <a id="1469" class="Symbol">λ</a> <a id="1471" href="order-theory.precategory-of-decidable-total-orders.html#1471" class="Bound">l</a> <a id="1473" class="Symbol">→</a> <a id="1475" href="order-theory.precategory-of-decidable-total-orders.html#1471" class="Bound">l</a><a id="1476" class="Symbol">)</a>
      <a id="1484" class="Symbol">(</a> <a id="1486" class="Symbol">λ</a> <a id="1488" href="order-theory.precategory-of-decidable-total-orders.html#1488" class="Bound">l</a> <a id="1490" class="Symbol">→</a> <a id="1492" href="order-theory.precategory-of-decidable-total-orders.html#1488" class="Bound">l</a><a id="1493" class="Symbol">))</a>
</pre>
### The precategory of total orders at a universe level

<pre class="Agda"><a id="Decidable-Total-Order-Precategory"></a><a id="1566" href="order-theory.precategory-of-decidable-total-orders.html#1566" class="Function">Decidable-Total-Order-Precategory</a> <a id="1600" class="Symbol">:</a> <a id="1602" class="Symbol">(</a><a id="1603" href="order-theory.precategory-of-decidable-total-orders.html#1603" class="Bound">l</a> <a id="1605" class="Symbol">:</a> <a id="1607" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1612" class="Symbol">)</a> <a id="1614" class="Symbol">→</a> <a id="1616" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1628" class="Symbol">(</a><a id="1629" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1634" href="order-theory.precategory-of-decidable-total-orders.html#1603" class="Bound">l</a><a id="1635" class="Symbol">)</a> <a id="1637" href="order-theory.precategory-of-decidable-total-orders.html#1603" class="Bound">l</a>
<a id="1639" href="order-theory.precategory-of-decidable-total-orders.html#1566" class="Function">Decidable-Total-Order-Precategory</a> <a id="1673" class="Symbol">=</a>
  <a id="1677" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1707" href="order-theory.precategory-of-decidable-total-orders.html#1204" class="Function">Decidable-Total-Order-Large-Precategory</a>
</pre>