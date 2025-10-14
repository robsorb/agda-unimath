# Rigid objects in a category

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="category-theory.rigid-objects-categories.html" class="Module">category-theory.rigid-objects-categories</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="category-theory.rigid-objects-precategories.html" class="Module">category-theory.rigid-objects-precategories</a>

<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="276" class="Keyword">open</a> <a id="281" class="Keyword">import</a> <a id="288" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A **rigid object** in a [category](category-theory.categories.md) is an object
whose [automorphism group](group-theory.automorphism-groups.md) is
[trivial](group-theory.trivial-groups.md).

## Definitions

### The predicate of being rigid

<pre class="Agda"><a id="589" class="Keyword">module</a> <a id="596" href="category-theory.rigid-objects-categories.html#596" class="Module">_</a>
  <a id="600" class="Symbol">{</a><a id="601" href="category-theory.rigid-objects-categories.html#601" class="Bound">l1</a> <a id="604" href="category-theory.rigid-objects-categories.html#604" class="Bound">l2</a> <a id="607" class="Symbol">:</a> <a id="609" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="614" class="Symbol">}</a> <a id="616" class="Symbol">(</a><a id="617" href="category-theory.rigid-objects-categories.html#617" class="Bound">C</a> <a id="619" class="Symbol">:</a> <a id="621" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="630" href="category-theory.rigid-objects-categories.html#601" class="Bound">l1</a> <a id="633" href="category-theory.rigid-objects-categories.html#604" class="Bound">l2</a><a id="635" class="Symbol">)</a> <a id="637" class="Symbol">(</a><a id="638" href="category-theory.rigid-objects-categories.html#638" class="Bound">x</a> <a id="640" class="Symbol">:</a> <a id="642" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="655" href="category-theory.rigid-objects-categories.html#617" class="Bound">C</a><a id="656" class="Symbol">)</a>
  <a id="660" class="Keyword">where</a>

  <a id="669" href="category-theory.rigid-objects-categories.html#669" class="Function">is-rigid-obj-prop-Category</a> <a id="696" class="Symbol">:</a> <a id="698" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="703" href="category-theory.rigid-objects-categories.html#604" class="Bound">l2</a>
  <a id="708" href="category-theory.rigid-objects-categories.html#669" class="Function">is-rigid-obj-prop-Category</a> <a id="735" class="Symbol">=</a>
    <a id="741" href="category-theory.rigid-objects-precategories.html#778" class="Function">is-rigid-obj-prop-Precategory</a> <a id="771" class="Symbol">(</a><a id="772" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="793" href="category-theory.rigid-objects-categories.html#617" class="Bound">C</a><a id="794" class="Symbol">)</a> <a id="796" href="category-theory.rigid-objects-categories.html#638" class="Bound">x</a>

  <a id="801" href="category-theory.rigid-objects-categories.html#801" class="Function">is-rigid-obj-Category</a> <a id="823" class="Symbol">:</a> <a id="825" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="828" href="category-theory.rigid-objects-categories.html#604" class="Bound">l2</a>
  <a id="833" href="category-theory.rigid-objects-categories.html#801" class="Function">is-rigid-obj-Category</a> <a id="855" class="Symbol">=</a> <a id="857" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="867" href="category-theory.rigid-objects-categories.html#669" class="Function">is-rigid-obj-prop-Category</a>

  <a id="897" href="category-theory.rigid-objects-categories.html#897" class="Function">is-prop-is-rigid-obj-Category</a> <a id="927" class="Symbol">:</a> <a id="929" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="937" href="category-theory.rigid-objects-categories.html#801" class="Function">is-rigid-obj-Category</a>
  <a id="961" href="category-theory.rigid-objects-categories.html#897" class="Function">is-prop-is-rigid-obj-Category</a> <a id="991" class="Symbol">=</a>
    <a id="997" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1015" href="category-theory.rigid-objects-categories.html#669" class="Function">is-rigid-obj-prop-Category</a>
</pre>
### The type of rigid objects in a category

<pre class="Agda"><a id="rigid-obj-Category"></a><a id="1100" href="category-theory.rigid-objects-categories.html#1100" class="Function">rigid-obj-Category</a> <a id="1119" class="Symbol">:</a> <a id="1121" class="Symbol">{</a><a id="1122" href="category-theory.rigid-objects-categories.html#1122" class="Bound">l1</a> <a id="1125" href="category-theory.rigid-objects-categories.html#1125" class="Bound">l2</a> <a id="1128" class="Symbol">:</a> <a id="1130" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1135" class="Symbol">}</a> <a id="1137" class="Symbol">(</a><a id="1138" href="category-theory.rigid-objects-categories.html#1138" class="Bound">C</a> <a id="1140" class="Symbol">:</a> <a id="1142" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1151" href="category-theory.rigid-objects-categories.html#1122" class="Bound">l1</a> <a id="1154" href="category-theory.rigid-objects-categories.html#1125" class="Bound">l2</a><a id="1156" class="Symbol">)</a> <a id="1158" class="Symbol">→</a> <a id="1160" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1163" class="Symbol">(</a><a id="1164" href="category-theory.rigid-objects-categories.html#1122" class="Bound">l1</a> <a id="1167" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1169" href="category-theory.rigid-objects-categories.html#1125" class="Bound">l2</a><a id="1171" class="Symbol">)</a>
<a id="1173" href="category-theory.rigid-objects-categories.html#1100" class="Function">rigid-obj-Category</a> <a id="1192" href="category-theory.rigid-objects-categories.html#1192" class="Bound">C</a> <a id="1194" class="Symbol">=</a>
    <a id="1200" href="category-theory.rigid-objects-precategories.html#1216" class="Function">rigid-obj-Precategory</a> <a id="1222" class="Symbol">(</a><a id="1223" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1244" href="category-theory.rigid-objects-categories.html#1192" class="Bound">C</a><a id="1245" class="Symbol">)</a>

<a id="1248" class="Keyword">module</a> <a id="1255" href="category-theory.rigid-objects-categories.html#1255" class="Module">_</a>
  <a id="1259" class="Symbol">{</a><a id="1260" href="category-theory.rigid-objects-categories.html#1260" class="Bound">l1</a> <a id="1263" href="category-theory.rigid-objects-categories.html#1263" class="Bound">l2</a> <a id="1266" class="Symbol">:</a> <a id="1268" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1273" class="Symbol">}</a> <a id="1275" class="Symbol">(</a><a id="1276" href="category-theory.rigid-objects-categories.html#1276" class="Bound">C</a> <a id="1278" class="Symbol">:</a> <a id="1280" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1289" href="category-theory.rigid-objects-categories.html#1260" class="Bound">l1</a> <a id="1292" href="category-theory.rigid-objects-categories.html#1263" class="Bound">l2</a><a id="1294" class="Symbol">)</a>
  <a id="1298" class="Keyword">where</a>

  <a id="1307" href="category-theory.rigid-objects-categories.html#1307" class="Function">obj-rigid-obj-Category</a> <a id="1330" class="Symbol">:</a> <a id="1332" href="category-theory.rigid-objects-categories.html#1100" class="Function">rigid-obj-Category</a> <a id="1351" href="category-theory.rigid-objects-categories.html#1276" class="Bound">C</a> <a id="1353" class="Symbol">→</a> <a id="1355" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="1368" href="category-theory.rigid-objects-categories.html#1276" class="Bound">C</a>
  <a id="1372" href="category-theory.rigid-objects-categories.html#1307" class="Function">obj-rigid-obj-Category</a> <a id="1395" class="Symbol">=</a> <a id="1397" href="category-theory.rigid-objects-precategories.html#1435" class="Function">obj-rigid-obj-Precategory</a> <a id="1423" class="Symbol">(</a><a id="1424" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1445" href="category-theory.rigid-objects-categories.html#1276" class="Bound">C</a><a id="1446" class="Symbol">)</a>

  <a id="1451" href="category-theory.rigid-objects-categories.html#1451" class="Function">is-rigid-rigid-obj-Category</a> <a id="1479" class="Symbol">:</a>
    <a id="1485" class="Symbol">(</a><a id="1486" href="category-theory.rigid-objects-categories.html#1486" class="Bound">x</a> <a id="1488" class="Symbol">:</a> <a id="1490" href="category-theory.rigid-objects-categories.html#1100" class="Function">rigid-obj-Category</a> <a id="1509" href="category-theory.rigid-objects-categories.html#1276" class="Bound">C</a><a id="1510" class="Symbol">)</a> <a id="1512" class="Symbol">→</a>
    <a id="1518" href="category-theory.rigid-objects-categories.html#801" class="Function">is-rigid-obj-Category</a> <a id="1540" href="category-theory.rigid-objects-categories.html#1276" class="Bound">C</a> <a id="1542" class="Symbol">(</a><a id="1543" href="category-theory.rigid-objects-categories.html#1307" class="Function">obj-rigid-obj-Category</a> <a id="1566" href="category-theory.rigid-objects-categories.html#1486" class="Bound">x</a><a id="1567" class="Symbol">)</a>
  <a id="1571" href="category-theory.rigid-objects-categories.html#1451" class="Function">is-rigid-rigid-obj-Category</a> <a id="1599" class="Symbol">=</a>
    <a id="1605" href="category-theory.rigid-objects-precategories.html#1544" class="Function">is-rigid-rigid-obj-Precategory</a> <a id="1636" class="Symbol">(</a><a id="1637" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1658" href="category-theory.rigid-objects-categories.html#1276" class="Bound">C</a><a id="1659" class="Symbol">)</a>
</pre>
## See also

- Every object in a category is rigid if and only if it is
  [gaunt](category-theory.gaunt-categories.md).

## External links

- [rigid object](https://ncatlab.org/nlab/show/rigid+object) at $n$Lab
