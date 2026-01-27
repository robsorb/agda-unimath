# The precategory of finite posets

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="order-theory.precategory-of-finite-posets.html" class="Module">order-theory.precategory-of-finite-posets</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="order-theory.finite-posets.html" class="Module">order-theory.finite-posets</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="order-theory.precategory-of-posets.html" class="Module">order-theory.precategory-of-posets</a>
</pre>
</details>

## Idea

The **(large) precategory of finite posets** consists of
[finite posets](order-theory.finite-posets.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of finite posets

<pre class="Agda"><a id="parametric-Finite-Poset-Full-Large-Subprecategory"></a><a id="859" href="order-theory.precategory-of-finite-posets.html#859" class="Function">parametric-Finite-Poset-Full-Large-Subprecategory</a> <a id="909" class="Symbol">:</a>
  <a id="913" class="Symbol">(</a><a id="914" href="order-theory.precategory-of-finite-posets.html#914" class="Bound">α</a> <a id="916" href="order-theory.precategory-of-finite-posets.html#916" class="Bound">β</a> <a id="918" class="Symbol">:</a> <a id="920" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="926" class="Symbol">→</a> <a id="928" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="933" class="Symbol">)</a> <a id="935" class="Symbol">→</a>
  <a id="939" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a>
    <a id="969" class="Symbol">(</a> <a id="971" class="Symbol">λ</a> <a id="973" href="order-theory.precategory-of-finite-posets.html#973" class="Bound">l</a> <a id="975" class="Symbol">→</a> <a id="977" href="order-theory.precategory-of-finite-posets.html#914" class="Bound">α</a> <a id="979" href="order-theory.precategory-of-finite-posets.html#973" class="Bound">l</a> <a id="981" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="983" href="order-theory.precategory-of-finite-posets.html#916" class="Bound">β</a> <a id="985" href="order-theory.precategory-of-finite-posets.html#973" class="Bound">l</a><a id="986" class="Symbol">)</a>
    <a id="992" class="Symbol">(</a> <a id="994" href="order-theory.precategory-of-posets.html#1319" class="Function">parametric-Poset-Large-Precategory</a> <a id="1029" href="order-theory.precategory-of-finite-posets.html#914" class="Bound">α</a> <a id="1031" href="order-theory.precategory-of-finite-posets.html#916" class="Bound">β</a><a id="1032" class="Symbol">)</a>
<a id="1034" href="order-theory.precategory-of-finite-posets.html#859" class="Function">parametric-Finite-Poset-Full-Large-Subprecategory</a> <a id="1084" href="order-theory.precategory-of-finite-posets.html#1084" class="Bound">α</a> <a id="1086" href="order-theory.precategory-of-finite-posets.html#1086" class="Bound">β</a> <a id="1088" class="Symbol">=</a> <a id="1090" href="order-theory.finite-posets.html#795" class="Function">is-finite-Poset-Prop</a>

<a id="Finite-Poset-Large-Precategory"></a><a id="1112" href="order-theory.precategory-of-finite-posets.html#1112" class="Function">Finite-Poset-Large-Precategory</a> <a id="1143" class="Symbol">:</a>
  <a id="1147" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1165" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1170" class="Symbol">(</a><a id="1171" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1174" class="Symbol">)</a>
<a id="1176" href="order-theory.precategory-of-finite-posets.html#1112" class="Function">Finite-Poset-Large-Precategory</a> <a id="1207" class="Symbol">=</a>
  <a id="1211" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1259" class="Symbol">(</a> <a id="1261" href="order-theory.precategory-of-posets.html#2115" class="Function">Poset-Large-Precategory</a><a id="1284" class="Symbol">)</a>
    <a id="1290" class="Symbol">(</a> <a id="1292" href="order-theory.precategory-of-finite-posets.html#859" class="Function">parametric-Finite-Poset-Full-Large-Subprecategory</a> <a id="1342" class="Symbol">(λ</a> <a id="1345" href="order-theory.precategory-of-finite-posets.html#1345" class="Bound">l</a> <a id="1347" class="Symbol">→</a> <a id="1349" href="order-theory.precategory-of-finite-posets.html#1345" class="Bound">l</a><a id="1350" class="Symbol">)</a> <a id="1352" class="Symbol">(λ</a> <a id="1355" href="order-theory.precategory-of-finite-posets.html#1355" class="Bound">l</a> <a id="1357" class="Symbol">→</a> <a id="1359" href="order-theory.precategory-of-finite-posets.html#1355" class="Bound">l</a><a id="1360" class="Symbol">))</a>
</pre>
### The precategory of finite posets of universe level `l`

<pre class="Agda"><a id="Finite-Poset-Precategory"></a><a id="1436" href="order-theory.precategory-of-finite-posets.html#1436" class="Function">Finite-Poset-Precategory</a> <a id="1461" class="Symbol">:</a> <a id="1463" class="Symbol">(</a><a id="1464" href="order-theory.precategory-of-finite-posets.html#1464" class="Bound">l</a> <a id="1466" class="Symbol">:</a> <a id="1468" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1473" class="Symbol">)</a> <a id="1475" class="Symbol">→</a> <a id="1477" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1489" class="Symbol">(</a><a id="1490" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1495" href="order-theory.precategory-of-finite-posets.html#1464" class="Bound">l</a><a id="1496" class="Symbol">)</a> <a id="1498" href="order-theory.precategory-of-finite-posets.html#1464" class="Bound">l</a>
<a id="1500" href="order-theory.precategory-of-finite-posets.html#1436" class="Function">Finite-Poset-Precategory</a> <a id="1525" class="Symbol">=</a>
  <a id="1529" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1559" href="order-theory.precategory-of-finite-posets.html#1112" class="Function">Finite-Poset-Large-Precategory</a>
</pre>