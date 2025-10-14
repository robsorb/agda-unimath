# The precategory of finite total orders

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="order-theory.precategory-of-finite-total-orders.html" class="Module">order-theory.precategory-of-finite-total-orders</a> <a id="106" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="order-theory.finite-total-orders.html" class="Module">order-theory.finite-total-orders</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="order-theory.precategory-of-posets.html" class="Module">order-theory.precategory-of-posets</a>
</pre>
</details>

## Idea

The **(large) precategory of finite total orders** consists of
[finite total orders](order-theory.finite-total-orders.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of finite total orders

<pre class="Agda"><a id="parametric-Finite-Total-Order-Full-Large-Subprecategory"></a><a id="901" href="order-theory.precategory-of-finite-total-orders.html#901" class="Function">parametric-Finite-Total-Order-Full-Large-Subprecategory</a> <a id="957" class="Symbol">:</a>
  <a id="961" class="Symbol">(</a><a id="962" href="order-theory.precategory-of-finite-total-orders.html#962" class="Bound">α</a> <a id="964" href="order-theory.precategory-of-finite-total-orders.html#964" class="Bound">β</a> <a id="966" class="Symbol">:</a> <a id="968" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="974" class="Symbol">→</a> <a id="976" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="981" class="Symbol">)</a> <a id="983" class="Symbol">→</a>
  <a id="987" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a>
    <a id="1017" class="Symbol">(</a> <a id="1019" class="Symbol">λ</a> <a id="1021" href="order-theory.precategory-of-finite-total-orders.html#1021" class="Bound">l</a> <a id="1023" class="Symbol">→</a> <a id="1025" href="order-theory.precategory-of-finite-total-orders.html#962" class="Bound">α</a> <a id="1027" href="order-theory.precategory-of-finite-total-orders.html#1021" class="Bound">l</a> <a id="1029" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1031" href="order-theory.precategory-of-finite-total-orders.html#964" class="Bound">β</a> <a id="1033" href="order-theory.precategory-of-finite-total-orders.html#1021" class="Bound">l</a><a id="1034" class="Symbol">)</a>
    <a id="1040" class="Symbol">(</a> <a id="1042" href="order-theory.precategory-of-posets.html#1319" class="Function">parametric-Poset-Large-Precategory</a> <a id="1077" href="order-theory.precategory-of-finite-total-orders.html#962" class="Bound">α</a> <a id="1079" href="order-theory.precategory-of-finite-total-orders.html#964" class="Bound">β</a><a id="1080" class="Symbol">)</a>
<a id="1082" href="order-theory.precategory-of-finite-total-orders.html#901" class="Function">parametric-Finite-Total-Order-Full-Large-Subprecategory</a> <a id="1138" href="order-theory.precategory-of-finite-total-orders.html#1138" class="Bound">α</a> <a id="1140" href="order-theory.precategory-of-finite-total-orders.html#1140" class="Bound">β</a> <a id="1142" class="Symbol">=</a>
  <a id="1146" href="order-theory.finite-total-orders.html#1646" class="Function">is-finite-total-order-Poset-Prop</a>

<a id="Finite-Total-Order-Large-Precategory"></a><a id="1180" href="order-theory.precategory-of-finite-total-orders.html#1180" class="Function">Finite-Total-Order-Large-Precategory</a> <a id="1217" class="Symbol">:</a> <a id="1219" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1237" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1242" class="Symbol">(</a><a id="1243" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1246" class="Symbol">)</a>
<a id="1248" href="order-theory.precategory-of-finite-total-orders.html#1180" class="Function">Finite-Total-Order-Large-Precategory</a> <a id="1285" class="Symbol">=</a>
  <a id="1289" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1337" class="Symbol">(</a> <a id="1339" href="order-theory.precategory-of-posets.html#2115" class="Function">Poset-Large-Precategory</a><a id="1362" class="Symbol">)</a>
    <a id="1368" class="Symbol">(</a> <a id="1370" href="order-theory.precategory-of-finite-total-orders.html#901" class="Function">parametric-Finite-Total-Order-Full-Large-Subprecategory</a>
      <a id="1432" class="Symbol">(</a> <a id="1434" class="Symbol">λ</a> <a id="1436" href="order-theory.precategory-of-finite-total-orders.html#1436" class="Bound">l</a> <a id="1438" class="Symbol">→</a> <a id="1440" href="order-theory.precategory-of-finite-total-orders.html#1436" class="Bound">l</a><a id="1441" class="Symbol">)</a>
      <a id="1449" class="Symbol">(</a> <a id="1451" class="Symbol">λ</a> <a id="1453" href="order-theory.precategory-of-finite-total-orders.html#1453" class="Bound">l</a> <a id="1455" class="Symbol">→</a> <a id="1457" href="order-theory.precategory-of-finite-total-orders.html#1453" class="Bound">l</a><a id="1458" class="Symbol">))</a>
</pre>
### The precategory of finite total orders of universe level `l`

<pre class="Agda"><a id="Finite-Total-Order-Precategory"></a><a id="1540" href="order-theory.precategory-of-finite-total-orders.html#1540" class="Function">Finite-Total-Order-Precategory</a> <a id="1571" class="Symbol">:</a> <a id="1573" class="Symbol">(</a><a id="1574" href="order-theory.precategory-of-finite-total-orders.html#1574" class="Bound">l</a> <a id="1576" class="Symbol">:</a> <a id="1578" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1583" class="Symbol">)</a> <a id="1585" class="Symbol">→</a> <a id="1587" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1599" class="Symbol">(</a><a id="1600" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1605" href="order-theory.precategory-of-finite-total-orders.html#1574" class="Bound">l</a><a id="1606" class="Symbol">)</a> <a id="1608" href="order-theory.precategory-of-finite-total-orders.html#1574" class="Bound">l</a>
<a id="1610" href="order-theory.precategory-of-finite-total-orders.html#1540" class="Function">Finite-Total-Order-Precategory</a> <a id="1641" class="Symbol">=</a>
  <a id="1645" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1675" href="order-theory.precategory-of-finite-total-orders.html#1180" class="Function">Finite-Total-Order-Large-Precategory</a>
</pre>