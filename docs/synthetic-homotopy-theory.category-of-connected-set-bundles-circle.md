# The category of connected set bundles over the circle

<pre class="Agda"><a id="66" class="Keyword">module</a> <a id="73" href="synthetic-homotopy-theory.category-of-connected-set-bundles-circle.html" class="Module">synthetic-homotopy-theory.category-of-connected-set-bundles-circle</a> <a id="140" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="category-theory.full-large-subcategories.html" class="Module">category-theory.full-large-subcategories</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>

<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.category-of-families-of-sets.html" class="Module">foundation.category-of-families-of-sets</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="synthetic-homotopy-theory.connected-set-bundles-circle.html" class="Module">synthetic-homotopy-theory.connected-set-bundles-circle</a>
</pre>
</details>

## Idea

The
[connected set bundles over the circle](synthetic-homotopy-theory.connected-set-bundles-circle.md)
form a [large category](category-theory.large-categories.md). This large
category is the categorification of the [poset](order-theory.posets.md) of the
[natural numbers ordered by divisibility](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).

## Definitions

### The category of connected set bundles over the circle

<pre class="Agda"><a id="connected-set-bundle-𝕊¹-Large-Category"></a><a id="985" href="synthetic-homotopy-theory.category-of-connected-set-bundles-circle.html#985" class="Function">connected-set-bundle-𝕊¹-Large-Category</a> <a id="1024" class="Symbol">:</a> <a id="1026" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="1041" class="Symbol">(</a><a id="1042" href="Agda.Primitive.html#931" class="Primitive">lsuc</a><a id="1046" class="Symbol">)</a> <a id="1048" class="Symbol">(</a><a id="1049" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1052" class="Symbol">)</a>
<a id="1054" href="synthetic-homotopy-theory.category-of-connected-set-bundles-circle.html#985" class="Function">connected-set-bundle-𝕊¹-Large-Category</a> <a id="1093" class="Symbol">=</a>
  <a id="1097" href="category-theory.full-large-subcategories.html#6893" class="Function">large-category-Full-Large-Subcategory</a>
    <a id="1139" class="Symbol">(</a> <a id="1141" href="foundation.category-of-families-of-sets.html#1441" class="Function">Family-Of-Sets-Large-Category</a> <a id="1171" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a><a id="1173" class="Symbol">)</a>
    <a id="1179" class="Symbol">(</a> <a id="1181" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1526" class="Function">is-connected-prop-set-bundle-𝕊¹</a><a id="1212" class="Symbol">)</a>
</pre>