# The precategory of inhabited finite total orders

<pre class="Agda"><a id="61" class="Keyword">module</a> <a id="68" href="order-theory.precategory-of-inhabited-finite-total-orders.html" class="Module">order-theory.precategory-of-inhabited-finite-total-orders</a> <a id="126" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="order-theory.inhabited-finite-total-orders.html" class="Module">order-theory.inhabited-finite-total-orders</a>
<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="order-theory.precategory-of-posets.html" class="Module">order-theory.precategory-of-posets</a>
</pre>
</details>

## Idea

The **(large) precategory of inhabited finite total orders** consists of
[inhabited finite total orders](order-theory.inhabited-finite-total-orders.md)
and [order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of inhabited finite total orders

<pre class="Agda"><a id="parametric-Inhabited-Finite-Total-Order-Full-Large-Subprecategory"></a><a id="971" href="order-theory.precategory-of-inhabited-finite-total-orders.html#971" class="Function">parametric-Inhabited-Finite-Total-Order-Full-Large-Subprecategory</a> <a id="1037" class="Symbol">:</a>
  <a id="1041" class="Symbol">(</a><a id="1042" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1042" class="Bound">α</a> <a id="1044" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1044" class="Bound">β</a> <a id="1046" class="Symbol">:</a> <a id="1048" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1054" class="Symbol">→</a> <a id="1056" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1061" class="Symbol">)</a> <a id="1063" class="Symbol">→</a>
  <a id="1067" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a>
    <a id="1097" class="Symbol">(</a> <a id="1099" class="Symbol">λ</a> <a id="1101" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1101" class="Bound">l</a> <a id="1103" class="Symbol">→</a> <a id="1105" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1042" class="Bound">α</a> <a id="1107" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1101" class="Bound">l</a> <a id="1109" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1111" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1044" class="Bound">β</a> <a id="1113" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1101" class="Bound">l</a><a id="1114" class="Symbol">)</a>
    <a id="1120" class="Symbol">(</a> <a id="1122" href="order-theory.precategory-of-posets.html#1319" class="Function">parametric-Poset-Large-Precategory</a> <a id="1157" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1042" class="Bound">α</a> <a id="1159" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1044" class="Bound">β</a><a id="1160" class="Symbol">)</a>
<a id="1162" href="order-theory.precategory-of-inhabited-finite-total-orders.html#971" class="Function">parametric-Inhabited-Finite-Total-Order-Full-Large-Subprecategory</a> <a id="1228" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1228" class="Bound">α</a> <a id="1230" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1230" class="Bound">β</a> <a id="1232" class="Symbol">=</a>
  <a id="1236" href="order-theory.inhabited-finite-total-orders.html#1464" class="Function">is-inhabited-finite-total-order-Poset-Prop</a>

<a id="Inhabited-Finite-Total-Order-Large-Precategory"></a><a id="1280" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1280" class="Function">Inhabited-Finite-Total-Order-Large-Precategory</a> <a id="1327" class="Symbol">:</a> <a id="1329" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1347" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1352" class="Symbol">(</a><a id="1353" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1356" class="Symbol">)</a>
<a id="1358" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1280" class="Function">Inhabited-Finite-Total-Order-Large-Precategory</a> <a id="1405" class="Symbol">=</a>
  <a id="1409" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1457" class="Symbol">(</a> <a id="1459" href="order-theory.precategory-of-posets.html#2115" class="Function">Poset-Large-Precategory</a><a id="1482" class="Symbol">)</a>
    <a id="1488" class="Symbol">(</a> <a id="1490" href="order-theory.precategory-of-inhabited-finite-total-orders.html#971" class="Function">parametric-Inhabited-Finite-Total-Order-Full-Large-Subprecategory</a>
      <a id="1562" class="Symbol">(</a> <a id="1564" class="Symbol">λ</a> <a id="1566" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1566" class="Bound">l</a> <a id="1568" class="Symbol">→</a> <a id="1570" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1566" class="Bound">l</a><a id="1571" class="Symbol">)</a>
      <a id="1579" class="Symbol">(</a> <a id="1581" class="Symbol">λ</a> <a id="1583" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1583" class="Bound">l</a> <a id="1585" class="Symbol">→</a> <a id="1587" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1583" class="Bound">l</a><a id="1588" class="Symbol">))</a>
</pre>
### The precategory of finite total orders of universe level `l`

<pre class="Agda"><a id="Inhabited-Finite-Total-Order-Precategory"></a><a id="1670" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1670" class="Function">Inhabited-Finite-Total-Order-Precategory</a> <a id="1711" class="Symbol">:</a> <a id="1713" class="Symbol">(</a><a id="1714" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1714" class="Bound">l</a> <a id="1716" class="Symbol">:</a> <a id="1718" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1723" class="Symbol">)</a> <a id="1725" class="Symbol">→</a> <a id="1727" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1739" class="Symbol">(</a><a id="1740" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1745" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1714" class="Bound">l</a><a id="1746" class="Symbol">)</a> <a id="1748" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1714" class="Bound">l</a>
<a id="1750" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1670" class="Function">Inhabited-Finite-Total-Order-Precategory</a> <a id="1791" class="Symbol">=</a>
  <a id="1795" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1825" href="order-theory.precategory-of-inhabited-finite-total-orders.html#1280" class="Function">Inhabited-Finite-Total-Order-Large-Precategory</a>
</pre>