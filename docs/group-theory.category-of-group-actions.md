# The category of group actions

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="group-theory.category-of-group-actions.html" class="Module">group-theory.category-of-group-actions</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="category-theory.isomorphisms-in-large-precategories.html" class="Module">category-theory.isomorphisms-in-large-precategories</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="427" class="Keyword">open</a> <a id="432" class="Keyword">import</a> <a id="439" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="488" class="Keyword">open</a> <a id="493" class="Keyword">import</a> <a id="500" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="528" class="Keyword">open</a> <a id="533" class="Keyword">import</a> <a id="540" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="567" class="Keyword">open</a> <a id="572" class="Keyword">import</a> <a id="579" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="599" class="Keyword">open</a> <a id="604" class="Keyword">import</a> <a id="611" href="group-theory.homomorphisms-group-actions.html" class="Module">group-theory.homomorphisms-group-actions</a>
<a id="652" class="Keyword">open</a> <a id="657" class="Keyword">import</a> <a id="664" href="group-theory.isomorphisms-group-actions.html" class="Module">group-theory.isomorphisms-group-actions</a>
<a id="704" class="Keyword">open</a> <a id="709" class="Keyword">import</a> <a id="716" href="group-theory.precategory-of-group-actions.html" class="Module">group-theory.precategory-of-group-actions</a>
</pre>
</details>

## Idea

The [large category](category-theory.large-categories.md) of
[group actions](group-theory.group-actions.md) consists of group actions and
[morphisms of group actions](group-theory.homomorphisms-group-actions.md)
between them.

## Definitions

### The large category of `G`-sets

<pre class="Agda"><a id="1071" class="Keyword">module</a> <a id="1078" href="group-theory.category-of-group-actions.html#1078" class="Module">_</a>
  <a id="1082" class="Symbol">{</a><a id="1083" href="group-theory.category-of-group-actions.html#1083" class="Bound">l1</a> <a id="1086" class="Symbol">:</a> <a id="1088" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1093" class="Symbol">}</a> <a id="1095" class="Symbol">(</a><a id="1096" href="group-theory.category-of-group-actions.html#1096" class="Bound">G</a> <a id="1098" class="Symbol">:</a> <a id="1100" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1106" href="group-theory.category-of-group-actions.html#1083" class="Bound">l1</a><a id="1108" class="Symbol">)</a>
  <a id="1112" class="Keyword">where</a>

  <a id="1121" href="group-theory.category-of-group-actions.html#1121" class="Function">is-large-category-action-Group-Large-Category</a> <a id="1167" class="Symbol">:</a>
    <a id="1173" href="category-theory.large-categories.html#1350" class="Function">is-large-category-Large-Precategory</a> <a id="1209" class="Symbol">(</a><a id="1210" href="group-theory.precategory-of-group-actions.html#777" class="Function">action-Group-Large-Precategory</a> <a id="1241" href="group-theory.category-of-group-actions.html#1096" class="Bound">G</a><a id="1242" class="Symbol">)</a>
  <a id="1246" href="group-theory.category-of-group-actions.html#1121" class="Function">is-large-category-action-Group-Large-Category</a> <a id="1292" href="group-theory.category-of-group-actions.html#1292" class="Bound">X</a> <a id="1294" class="Symbol">=</a>
    <a id="1300" href="foundation.fundamental-theorem-of-identity-types.html#2039" class="Function">fundamental-theorem-id</a>
      <a id="1329" class="Symbol">(</a> <a id="1331" href="group-theory.isomorphisms-group-actions.html#9224" class="Function">is-torsorial-iso-action-Group</a> <a id="1361" href="group-theory.category-of-group-actions.html#1096" class="Bound">G</a> <a id="1363" href="group-theory.category-of-group-actions.html#1292" class="Bound">X</a><a id="1364" class="Symbol">)</a>
      <a id="1372" class="Symbol">(</a> <a id="1374" href="category-theory.isomorphisms-in-large-precategories.html#8327" class="Function">iso-eq-Large-Precategory</a> <a id="1399" class="Symbol">(</a><a id="1400" href="group-theory.precategory-of-group-actions.html#777" class="Function">action-Group-Large-Precategory</a> <a id="1431" href="group-theory.category-of-group-actions.html#1096" class="Bound">G</a><a id="1432" class="Symbol">)</a> <a id="1434" href="group-theory.category-of-group-actions.html#1292" class="Bound">X</a><a id="1435" class="Symbol">)</a>

  <a id="1440" href="group-theory.category-of-group-actions.html#1440" class="Function">action-Group-Large-Category</a> <a id="1468" class="Symbol">:</a>
    <a id="1474" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="1489" class="Symbol">(λ</a> <a id="1492" href="group-theory.category-of-group-actions.html#1492" class="Bound">l2</a> <a id="1495" class="Symbol">→</a> <a id="1497" href="group-theory.category-of-group-actions.html#1083" class="Bound">l1</a> <a id="1500" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1502" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1507" href="group-theory.category-of-group-actions.html#1492" class="Bound">l2</a><a id="1509" class="Symbol">)</a> <a id="1511" class="Symbol">(λ</a> <a id="1514" href="group-theory.category-of-group-actions.html#1514" class="Bound">l2</a> <a id="1517" href="group-theory.category-of-group-actions.html#1517" class="Bound">l3</a> <a id="1520" class="Symbol">→</a> <a id="1522" href="group-theory.category-of-group-actions.html#1083" class="Bound">l1</a> <a id="1525" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1527" href="group-theory.category-of-group-actions.html#1514" class="Bound">l2</a> <a id="1530" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1532" href="group-theory.category-of-group-actions.html#1517" class="Bound">l3</a><a id="1534" class="Symbol">)</a>
  <a id="1538" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a> <a id="1571" href="group-theory.category-of-group-actions.html#1440" class="Function">action-Group-Large-Category</a> <a id="1599" class="Symbol">=</a>
      <a id="1607" href="group-theory.precategory-of-group-actions.html#777" class="Function">action-Group-Large-Precategory</a> <a id="1638" href="group-theory.category-of-group-actions.html#1096" class="Bound">G</a>
  <a id="1642" href="category-theory.large-categories.html#1868" class="Field">is-large-category-Large-Category</a> <a id="1675" href="group-theory.category-of-group-actions.html#1440" class="Function">action-Group-Large-Category</a> <a id="1703" class="Symbol">=</a>
    <a id="1709" href="group-theory.category-of-group-actions.html#1121" class="Function">is-large-category-action-Group-Large-Category</a>
</pre>
### The small category of `G`-sets

<pre class="Agda"><a id="1804" class="Keyword">module</a> <a id="1811" href="group-theory.category-of-group-actions.html#1811" class="Module">_</a>
  <a id="1815" class="Symbol">{</a><a id="1816" href="group-theory.category-of-group-actions.html#1816" class="Bound">l1</a> <a id="1819" class="Symbol">:</a> <a id="1821" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1826" class="Symbol">}</a> <a id="1828" class="Symbol">(</a><a id="1829" href="group-theory.category-of-group-actions.html#1829" class="Bound">G</a> <a id="1831" class="Symbol">:</a> <a id="1833" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1839" href="group-theory.category-of-group-actions.html#1816" class="Bound">l1</a><a id="1841" class="Symbol">)</a>
  <a id="1845" class="Keyword">where</a>

  <a id="1854" href="group-theory.category-of-group-actions.html#1854" class="Function">action-Group-Category</a> <a id="1876" class="Symbol">:</a>
    <a id="1882" class="Symbol">(</a><a id="1883" href="group-theory.category-of-group-actions.html#1883" class="Bound">l2</a> <a id="1886" class="Symbol">:</a> <a id="1888" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1893" class="Symbol">)</a> <a id="1895" class="Symbol">→</a> <a id="1897" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1906" class="Symbol">(</a><a id="1907" href="group-theory.category-of-group-actions.html#1816" class="Bound">l1</a> <a id="1910" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1912" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1917" href="group-theory.category-of-group-actions.html#1883" class="Bound">l2</a><a id="1919" class="Symbol">)</a> <a id="1921" class="Symbol">(</a><a id="1922" href="group-theory.category-of-group-actions.html#1816" class="Bound">l1</a> <a id="1925" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1927" href="group-theory.category-of-group-actions.html#1883" class="Bound">l2</a><a id="1929" class="Symbol">)</a>
  <a id="1933" href="group-theory.category-of-group-actions.html#1854" class="Function">action-Group-Category</a> <a id="1955" class="Symbol">=</a>
    <a id="1961" href="category-theory.large-categories.html#7051" class="Function">category-Large-Category</a> <a id="1985" class="Symbol">(</a><a id="1986" href="group-theory.category-of-group-actions.html#1440" class="Function">action-Group-Large-Category</a> <a id="2014" href="group-theory.category-of-group-actions.html#1829" class="Bound">G</a><a id="2015" class="Symbol">)</a>
</pre>