# The category of rings

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="ring-theory.category-of-rings.html" class="Module">ring-theory.category-of-rings</a> <a id="71" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>

<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="ring-theory.isomorphisms-rings.html" class="Module">ring-theory.isomorphisms-rings</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="ring-theory.precategory-of-rings.html" class="Module">ring-theory.precategory-of-rings</a>
</pre>
</details>

## Idea

The [large category](category-theory.large-categories.md) `Ring-Category` of
[rings](ring-theory.rings.md) is the large category consisting of rings and
[ring homomorphisms](ring-theory.homomorphisms-rings.md).

## Definitions

### The large category of rings

<pre class="Agda"><a id="is-large-category-Ring-Large-Category"></a><a id="635" href="ring-theory.category-of-rings.html#635" class="Function">is-large-category-Ring-Large-Category</a> <a id="673" class="Symbol">:</a>
  <a id="677" href="category-theory.large-categories.html#1350" class="Function">is-large-category-Large-Precategory</a> <a id="713" href="ring-theory.precategory-of-rings.html#566" class="Function">Ring-Large-Precategory</a>
<a id="736" href="ring-theory.category-of-rings.html#635" class="Function">is-large-category-Ring-Large-Category</a> <a id="774" class="Symbol">=</a>
  <a id="778" href="ring-theory.isomorphisms-rings.html#17476" class="Function">is-equiv-iso-eq-Ring</a>

<a id="Ring-Large-Category"></a><a id="800" href="ring-theory.category-of-rings.html#800" class="Function">Ring-Large-Category</a> <a id="820" class="Symbol">:</a> <a id="822" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="837" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="842" class="Symbol">(</a><a id="843" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="846" class="Symbol">)</a>
<a id="848" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a> <a id="881" href="ring-theory.category-of-rings.html#800" class="Function">Ring-Large-Category</a> <a id="901" class="Symbol">=</a>
  <a id="905" href="ring-theory.precategory-of-rings.html#566" class="Function">Ring-Large-Precategory</a>
<a id="928" href="category-theory.large-categories.html#1868" class="Field">is-large-category-Large-Category</a> <a id="961" href="ring-theory.category-of-rings.html#800" class="Function">Ring-Large-Category</a> <a id="981" class="Symbol">=</a>
  <a id="985" href="ring-theory.category-of-rings.html#635" class="Function">is-large-category-Ring-Large-Category</a>
</pre>
### The small categories of rings

<pre class="Agda"><a id="Ring-Category"></a><a id="1071" href="ring-theory.category-of-rings.html#1071" class="Function">Ring-Category</a> <a id="1085" class="Symbol">:</a> <a id="1087" class="Symbol">(</a><a id="1088" href="ring-theory.category-of-rings.html#1088" class="Bound">l</a> <a id="1090" class="Symbol">:</a> <a id="1092" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1097" class="Symbol">)</a> <a id="1099" class="Symbol">→</a> <a id="1101" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1110" class="Symbol">(</a><a id="1111" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1116" href="ring-theory.category-of-rings.html#1088" class="Bound">l</a><a id="1117" class="Symbol">)</a> <a id="1119" href="ring-theory.category-of-rings.html#1088" class="Bound">l</a>
<a id="1121" href="ring-theory.category-of-rings.html#1071" class="Function">Ring-Category</a> <a id="1135" class="Symbol">=</a> <a id="1137" href="category-theory.large-categories.html#7051" class="Function">category-Large-Category</a> <a id="1161" href="ring-theory.category-of-rings.html#800" class="Function">Ring-Large-Category</a>
</pre>