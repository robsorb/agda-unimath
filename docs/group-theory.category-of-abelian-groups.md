# The category of abelian groups

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="group-theory.category-of-abelian-groups.html" class="Module">group-theory.category-of-abelian-groups</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="category-theory.full-large-subcategories.html" class="Module">category-theory.full-large-subcategories</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="category-theory.functors-large-categories.html" class="Module">category-theory.functors-large-categories</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="385" class="Keyword">open</a> <a id="390" class="Keyword">import</a> <a id="397" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="468" class="Keyword">open</a> <a id="473" class="Keyword">import</a> <a id="480" href="group-theory.abelian-groups.html" class="Module">group-theory.abelian-groups</a>
<a id="508" class="Keyword">open</a> <a id="513" class="Keyword">import</a> <a id="520" href="group-theory.category-of-groups.html" class="Module">group-theory.category-of-groups</a>
</pre>
</details>

## Idea

The **category of abelian groups** is the
[full large subcategory](category-theory.full-large-subcategories.md) of the
[category of groups](group-theory.category-of-groups.md) consisting of
[groups](group-theory.groups.md) of which the group operation is
[commutative](group-theory.abelian-groups.md).

## Definitions

### The large category of abelian groups

<pre class="Agda"><a id="Ab-Large-Category"></a><a id="947" href="group-theory.category-of-abelian-groups.html#947" class="Function">Ab-Large-Category</a> <a id="965" class="Symbol">:</a> <a id="967" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="982" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="987" class="Symbol">(</a><a id="988" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="991" class="Symbol">)</a>
<a id="993" href="group-theory.category-of-abelian-groups.html#947" class="Function">Ab-Large-Category</a> <a id="1011" class="Symbol">=</a>
  <a id="1015" href="category-theory.full-large-subcategories.html#6893" class="Function">large-category-Full-Large-Subcategory</a>
    <a id="1057" class="Symbol">(</a> <a id="1059" href="group-theory.category-of-groups.html#907" class="Function">Group-Large-Category</a><a id="1079" class="Symbol">)</a>
    <a id="1085" class="Symbol">(</a> <a id="1087" href="group-theory.abelian-groups.html#1972" class="Function">is-abelian-prop-Group</a><a id="1108" class="Symbol">)</a>
</pre>
### The large precategory of abelian groups

<pre class="Agda"><a id="Ab-Large-Precategory"></a><a id="1168" href="group-theory.category-of-abelian-groups.html#1168" class="Function">Ab-Large-Precategory</a> <a id="1189" class="Symbol">:</a> <a id="1191" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1209" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1214" class="Symbol">(</a><a id="1215" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1218" class="Symbol">)</a>
<a id="1220" href="group-theory.category-of-abelian-groups.html#1168" class="Function">Ab-Large-Precategory</a> <a id="1241" class="Symbol">=</a>
  <a id="1245" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a> <a id="1278" href="group-theory.category-of-abelian-groups.html#947" class="Function">Ab-Large-Category</a>
</pre>
### The category of abelian groups of a given universe level

<pre class="Agda"><a id="Ab-Category"></a><a id="1371" href="group-theory.category-of-abelian-groups.html#1371" class="Function">Ab-Category</a> <a id="1383" class="Symbol">:</a> <a id="1385" class="Symbol">(</a><a id="1386" href="group-theory.category-of-abelian-groups.html#1386" class="Bound">l</a> <a id="1388" class="Symbol">:</a> <a id="1390" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1395" class="Symbol">)</a> <a id="1397" class="Symbol">→</a> <a id="1399" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1408" class="Symbol">(</a><a id="1409" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1414" href="group-theory.category-of-abelian-groups.html#1386" class="Bound">l</a><a id="1415" class="Symbol">)</a> <a id="1417" href="group-theory.category-of-abelian-groups.html#1386" class="Bound">l</a>
<a id="1419" href="group-theory.category-of-abelian-groups.html#1371" class="Function">Ab-Category</a> <a id="1431" class="Symbol">=</a> <a id="1433" href="category-theory.large-categories.html#7051" class="Function">category-Large-Category</a> <a id="1457" href="group-theory.category-of-abelian-groups.html#947" class="Function">Ab-Large-Category</a>
</pre>
### The precategory of abelian groups of a given universe level

<pre class="Agda"><a id="Ab-Precategory"></a><a id="1553" href="group-theory.category-of-abelian-groups.html#1553" class="Function">Ab-Precategory</a> <a id="1568" class="Symbol">:</a> <a id="1570" class="Symbol">(</a><a id="1571" href="group-theory.category-of-abelian-groups.html#1571" class="Bound">l</a> <a id="1573" class="Symbol">:</a> <a id="1575" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1580" class="Symbol">)</a> <a id="1582" class="Symbol">→</a> <a id="1584" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1596" class="Symbol">(</a><a id="1597" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1602" href="group-theory.category-of-abelian-groups.html#1571" class="Bound">l</a><a id="1603" class="Symbol">)</a> <a id="1605" href="group-theory.category-of-abelian-groups.html#1571" class="Bound">l</a>
<a id="1607" href="group-theory.category-of-abelian-groups.html#1553" class="Function">Ab-Precategory</a> <a id="1622" class="Symbol">=</a> <a id="1624" href="category-theory.large-categories.html#6601" class="Function">precategory-Large-Category</a> <a id="1651" href="group-theory.category-of-abelian-groups.html#947" class="Function">Ab-Large-Category</a>
</pre>
### The forgetful functor from abelian groups to groups

<pre class="Agda"><a id="forgetful-functor-Ab"></a><a id="1739" href="group-theory.category-of-abelian-groups.html#1739" class="Function">forgetful-functor-Ab</a> <a id="1760" class="Symbol">:</a>
  <a id="1764" href="category-theory.functors-large-categories.html#1044" class="Function">functor-Large-Category</a> <a id="1787" class="Symbol">(λ</a> <a id="1790" href="group-theory.category-of-abelian-groups.html#1790" class="Bound">l</a> <a id="1792" class="Symbol">→</a> <a id="1794" href="group-theory.category-of-abelian-groups.html#1790" class="Bound">l</a><a id="1795" class="Symbol">)</a> <a id="1797" href="group-theory.category-of-abelian-groups.html#947" class="Function">Ab-Large-Category</a> <a id="1815" href="group-theory.category-of-groups.html#907" class="Function">Group-Large-Category</a>
<a id="1836" href="group-theory.category-of-abelian-groups.html#1739" class="Function">forgetful-functor-Ab</a> <a id="1857" class="Symbol">=</a>
  <a id="1861" href="category-theory.full-large-subcategories.html#7476" class="Function">forgetful-functor-Full-Large-Subcategory</a>
    <a id="1906" class="Symbol">(</a> <a id="1908" href="group-theory.category-of-groups.html#907" class="Function">Group-Large-Category</a><a id="1928" class="Symbol">)</a>
    <a id="1934" class="Symbol">(</a> <a id="1936" href="group-theory.abelian-groups.html#1972" class="Function">is-abelian-prop-Group</a><a id="1957" class="Symbol">)</a>
</pre>