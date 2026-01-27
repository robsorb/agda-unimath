# The precategory of total orders

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="order-theory.precategory-of-total-orders.html" class="Module">order-theory.precategory-of-total-orders</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="order-theory.precategory-of-posets.html" class="Module">order-theory.precategory-of-posets</a>
<a id="382" class="Keyword">open</a> <a id="387" class="Keyword">import</a> <a id="394" href="order-theory.total-orders.html" class="Module">order-theory.total-orders</a>
</pre>
</details>

## Idea

The **(large) precategory of total orders** consists of
[total orders](order-theory.total-orders.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of total orders

<pre class="Agda"><a id="parametric-Total-Order-Full-Large-Subprecategory"></a><a id="852" href="order-theory.precategory-of-total-orders.html#852" class="Function">parametric-Total-Order-Full-Large-Subprecategory</a> <a id="901" class="Symbol">:</a>
  <a id="905" class="Symbol">(</a><a id="906" href="order-theory.precategory-of-total-orders.html#906" class="Bound">α</a> <a id="908" href="order-theory.precategory-of-total-orders.html#908" class="Bound">β</a> <a id="910" class="Symbol">:</a> <a id="912" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="918" class="Symbol">→</a> <a id="920" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="925" class="Symbol">)</a> <a id="927" class="Symbol">→</a>
  <a id="931" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a>
    <a id="961" class="Symbol">(</a> <a id="963" class="Symbol">λ</a> <a id="965" href="order-theory.precategory-of-total-orders.html#965" class="Bound">l</a> <a id="967" class="Symbol">→</a> <a id="969" href="order-theory.precategory-of-total-orders.html#906" class="Bound">α</a> <a id="971" href="order-theory.precategory-of-total-orders.html#965" class="Bound">l</a> <a id="973" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="975" href="order-theory.precategory-of-total-orders.html#908" class="Bound">β</a> <a id="977" href="order-theory.precategory-of-total-orders.html#965" class="Bound">l</a><a id="978" class="Symbol">)</a>
    <a id="984" class="Symbol">(</a> <a id="986" href="order-theory.precategory-of-posets.html#1319" class="Function">parametric-Poset-Large-Precategory</a> <a id="1021" href="order-theory.precategory-of-total-orders.html#906" class="Bound">α</a> <a id="1023" href="order-theory.precategory-of-total-orders.html#908" class="Bound">β</a><a id="1024" class="Symbol">)</a>
<a id="1026" href="order-theory.precategory-of-total-orders.html#852" class="Function">parametric-Total-Order-Full-Large-Subprecategory</a> <a id="1075" href="order-theory.precategory-of-total-orders.html#1075" class="Bound">α</a> <a id="1077" href="order-theory.precategory-of-total-orders.html#1077" class="Bound">β</a> <a id="1079" class="Symbol">=</a> <a id="1081" href="order-theory.total-orders.html#1795" class="Function">is-total-Poset-Prop</a>

<a id="Total-Order-Large-Precategory"></a><a id="1102" href="order-theory.precategory-of-total-orders.html#1102" class="Function">Total-Order-Large-Precategory</a> <a id="1132" class="Symbol">:</a>
  <a id="1136" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1154" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1159" class="Symbol">(</a><a id="1160" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1163" class="Symbol">)</a>
<a id="1165" href="order-theory.precategory-of-total-orders.html#1102" class="Function">Total-Order-Large-Precategory</a> <a id="1195" class="Symbol">=</a>
  <a id="1199" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1247" class="Symbol">(</a> <a id="1249" href="order-theory.precategory-of-posets.html#2115" class="Function">Poset-Large-Precategory</a><a id="1272" class="Symbol">)</a>
    <a id="1278" class="Symbol">(</a> <a id="1280" href="order-theory.precategory-of-total-orders.html#852" class="Function">parametric-Total-Order-Full-Large-Subprecategory</a> <a id="1329" class="Symbol">(λ</a> <a id="1332" href="order-theory.precategory-of-total-orders.html#1332" class="Bound">l</a> <a id="1334" class="Symbol">→</a> <a id="1336" href="order-theory.precategory-of-total-orders.html#1332" class="Bound">l</a><a id="1337" class="Symbol">)</a> <a id="1339" class="Symbol">(λ</a> <a id="1342" href="order-theory.precategory-of-total-orders.html#1342" class="Bound">l</a> <a id="1344" class="Symbol">→</a> <a id="1346" href="order-theory.precategory-of-total-orders.html#1342" class="Bound">l</a><a id="1347" class="Symbol">))</a>
</pre>
### The precategory of total orders at a universe level

<pre class="Agda"><a id="Total-Order-Precategory"></a><a id="1420" href="order-theory.precategory-of-total-orders.html#1420" class="Function">Total-Order-Precategory</a> <a id="1444" class="Symbol">:</a> <a id="1446" class="Symbol">(</a><a id="1447" href="order-theory.precategory-of-total-orders.html#1447" class="Bound">l</a> <a id="1449" class="Symbol">:</a> <a id="1451" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1456" class="Symbol">)</a> <a id="1458" class="Symbol">→</a> <a id="1460" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1472" class="Symbol">(</a><a id="1473" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1478" href="order-theory.precategory-of-total-orders.html#1447" class="Bound">l</a><a id="1479" class="Symbol">)</a> <a id="1481" href="order-theory.precategory-of-total-orders.html#1447" class="Bound">l</a>
<a id="1483" href="order-theory.precategory-of-total-orders.html#1420" class="Function">Total-Order-Precategory</a> <a id="1507" class="Symbol">=</a>
  <a id="1511" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1541" href="order-theory.precategory-of-total-orders.html#1102" class="Function">Total-Order-Large-Precategory</a>
</pre>