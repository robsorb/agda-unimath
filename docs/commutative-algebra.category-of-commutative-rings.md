# The category of commutative rings

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="commutative-algebra.category-of-commutative-rings.html" class="Module">commutative-algebra.category-of-commutative-rings</a> <a id="103" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="159" class="Keyword">open</a> <a id="164" class="Keyword">import</a> <a id="171" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>

<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="commutative-algebra.isomorphisms-commutative-rings.html" class="Module">commutative-algebra.isomorphisms-commutative-rings</a>
<a id="307" class="Keyword">open</a> <a id="312" class="Keyword">import</a> <a id="319" href="commutative-algebra.precategory-of-commutative-rings.html" class="Module">commutative-algebra.precategory-of-commutative-rings</a>

<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The [large category](category-theory.large-categories.md)
`Commutative-Ring-Category` of
[commutative rings](commutative-algebra.commutative-rings.md) is the large
category consisting of commutative rings and
[ring homomorphisms](commutative-algebra.homomorphisms-commutative-rings.md).

## Definitions

### The large category of commutative rings

<pre class="Agda"><a id="is-large-category-Commutative-Ring-Large-Category"></a><a id="795" href="commutative-algebra.category-of-commutative-rings.html#795" class="Function">is-large-category-Commutative-Ring-Large-Category</a> <a id="845" class="Symbol">:</a>
  <a id="849" href="category-theory.large-categories.html#1350" class="Function">is-large-category-Large-Precategory</a> <a id="885" href="commutative-algebra.precategory-of-commutative-rings.html#1076" class="Function">Commutative-Ring-Large-Precategory</a>
<a id="920" href="commutative-algebra.category-of-commutative-rings.html#795" class="Function">is-large-category-Commutative-Ring-Large-Category</a> <a id="970" class="Symbol">=</a>
  <a id="974" href="commutative-algebra.isomorphisms-commutative-rings.html#13128" class="Function">is-equiv-iso-eq-Commutative-Ring</a>

<a id="Commutative-Ring-Large-Category"></a><a id="1008" href="commutative-algebra.category-of-commutative-rings.html#1008" class="Function">Commutative-Ring-Large-Category</a> <a id="1040" class="Symbol">:</a> <a id="1042" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="1057" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1062" class="Symbol">(</a><a id="1063" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1066" class="Symbol">)</a>
<a id="1068" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a> <a id="1101" href="commutative-algebra.category-of-commutative-rings.html#1008" class="Function">Commutative-Ring-Large-Category</a> <a id="1133" class="Symbol">=</a>
  <a id="1137" href="commutative-algebra.precategory-of-commutative-rings.html#1076" class="Function">Commutative-Ring-Large-Precategory</a>
<a id="1172" href="category-theory.large-categories.html#1868" class="Field">is-large-category-Large-Category</a> <a id="1205" href="commutative-algebra.category-of-commutative-rings.html#1008" class="Function">Commutative-Ring-Large-Category</a> <a id="1237" class="Symbol">=</a>
  <a id="1241" href="commutative-algebra.category-of-commutative-rings.html#795" class="Function">is-large-category-Commutative-Ring-Large-Category</a>
</pre>
### The small categories of commutative rings

<pre class="Agda"><a id="Commutative-Ring-Category"></a><a id="1351" href="commutative-algebra.category-of-commutative-rings.html#1351" class="Function">Commutative-Ring-Category</a> <a id="1377" class="Symbol">:</a> <a id="1379" class="Symbol">(</a><a id="1380" href="commutative-algebra.category-of-commutative-rings.html#1380" class="Bound">l</a> <a id="1382" class="Symbol">:</a> <a id="1384" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1389" class="Symbol">)</a> <a id="1391" class="Symbol">→</a> <a id="1393" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1402" class="Symbol">(</a><a id="1403" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1408" href="commutative-algebra.category-of-commutative-rings.html#1380" class="Bound">l</a><a id="1409" class="Symbol">)</a> <a id="1411" href="commutative-algebra.category-of-commutative-rings.html#1380" class="Bound">l</a>
<a id="1413" href="commutative-algebra.category-of-commutative-rings.html#1351" class="Function">Commutative-Ring-Category</a> <a id="1439" class="Symbol">=</a>
  <a id="1443" href="category-theory.large-categories.html#7051" class="Function">category-Large-Category</a> <a id="1467" href="commutative-algebra.category-of-commutative-rings.html#1008" class="Function">Commutative-Ring-Large-Category</a>
</pre>