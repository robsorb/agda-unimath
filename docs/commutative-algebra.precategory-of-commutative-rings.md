# The precategory of commutative rings

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="commutative-algebra.precategory-of-commutative-rings.html" class="Module">commutative-algebra.precategory-of-commutative-rings</a> <a id="109" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="165" class="Keyword">open</a> <a id="170" class="Keyword">import</a> <a id="177" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="269" class="Keyword">open</a> <a id="274" class="Keyword">import</a> <a id="281" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="312" class="Keyword">open</a> <a id="317" class="Keyword">import</a> <a id="324" href="commutative-algebra.commutative-rings.html" class="Module">commutative-algebra.commutative-rings</a>

<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="403" class="Keyword">open</a> <a id="408" class="Keyword">import</a> <a id="415" href="ring-theory.precategory-of-rings.html" class="Module">ring-theory.precategory-of-rings</a>
</pre>
</details>

## Idea

The
{{#concept "precategory of commutative rings" Agda=Commutative-Ring-Large-Precategory}}
consists of [commutative rings](commutative-algebra.commutative-rings.md) and
[homomorphisms of commutative rings](commutative-algebra.homomorphisms-commutative-rings.md).

## Definitions

### The precategory of commutative rings as a full subprecategory of rings

<pre class="Agda"><a id="Commutative-Ring-Full-Large-Subprecategory"></a><a id="839" href="commutative-algebra.precategory-of-commutative-rings.html#839" class="Function">Commutative-Ring-Full-Large-Subprecategory</a> <a id="882" class="Symbol">:</a>
  <a id="886" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a> <a id="912" class="Symbol">(λ</a> <a id="915" href="commutative-algebra.precategory-of-commutative-rings.html#915" class="Bound">l</a> <a id="917" class="Symbol">→</a> <a id="919" href="commutative-algebra.precategory-of-commutative-rings.html#915" class="Bound">l</a><a id="920" class="Symbol">)</a> <a id="922" href="ring-theory.precategory-of-rings.html#566" class="Function">Ring-Large-Precategory</a>
<a id="945" href="commutative-algebra.precategory-of-commutative-rings.html#839" class="Function">Commutative-Ring-Full-Large-Subprecategory</a> <a id="988" class="Symbol">=</a> <a id="990" href="commutative-algebra.commutative-rings.html#1951" class="Function">is-commutative-prop-Ring</a>
</pre>
### The large precategory of commutative rings

<pre class="Agda"><a id="Commutative-Ring-Large-Precategory"></a><a id="1076" href="commutative-algebra.precategory-of-commutative-rings.html#1076" class="Function">Commutative-Ring-Large-Precategory</a> <a id="1111" class="Symbol">:</a> <a id="1113" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1131" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1136" class="Symbol">(</a><a id="1137" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1140" class="Symbol">)</a>
<a id="1142" href="commutative-algebra.precategory-of-commutative-rings.html#1076" class="Function">Commutative-Ring-Large-Precategory</a> <a id="1177" class="Symbol">=</a>
  <a id="1181" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1229" class="Symbol">(</a> <a id="1231" href="ring-theory.precategory-of-rings.html#566" class="Function">Ring-Large-Precategory</a><a id="1253" class="Symbol">)</a>
    <a id="1259" class="Symbol">(</a> <a id="1261" href="commutative-algebra.precategory-of-commutative-rings.html#839" class="Function">Commutative-Ring-Full-Large-Subprecategory</a><a id="1303" class="Symbol">)</a>
</pre>
### The precategory of commutative rings of universe level `l`

<pre class="Agda"><a id="Commutative-Ring-Precategory"></a><a id="1382" href="commutative-algebra.precategory-of-commutative-rings.html#1382" class="Function">Commutative-Ring-Precategory</a> <a id="1411" class="Symbol">:</a> <a id="1413" class="Symbol">(</a><a id="1414" href="commutative-algebra.precategory-of-commutative-rings.html#1414" class="Bound">l</a> <a id="1416" class="Symbol">:</a> <a id="1418" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1423" class="Symbol">)</a> <a id="1425" class="Symbol">→</a> <a id="1427" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1439" class="Symbol">(</a><a id="1440" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1445" href="commutative-algebra.precategory-of-commutative-rings.html#1414" class="Bound">l</a><a id="1446" class="Symbol">)</a> <a id="1448" href="commutative-algebra.precategory-of-commutative-rings.html#1414" class="Bound">l</a>
<a id="1450" href="commutative-algebra.precategory-of-commutative-rings.html#1382" class="Function">Commutative-Ring-Precategory</a> <a id="1479" class="Symbol">=</a>
  <a id="1483" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1513" href="commutative-algebra.precategory-of-commutative-rings.html#1076" class="Function">Commutative-Ring-Large-Precategory</a>
</pre>