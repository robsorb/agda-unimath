# Large subcategories

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="category-theory.large-subcategories.html" class="Module">category-theory.large-subcategories</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="category-theory.large-subprecategories.html" class="Module">category-theory.large-subprecategories</a>

<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A **large subcategory** of a
[large category](category-theory.large-categories.md) `C` is a
[large subprecategory](category-theory.large-subprecategories.md) `P` of the
underlying [large precategory](category-theory.large-precategories.md) of `C`.

## Definition

<pre class="Agda"><a id="565" class="Keyword">module</a> <a id="572" href="category-theory.large-subcategories.html#572" class="Module">_</a>
  <a id="576" class="Symbol">{</a><a id="577" href="category-theory.large-subcategories.html#577" class="Bound">α</a> <a id="579" class="Symbol">:</a> <a id="581" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="587" class="Symbol">→</a> <a id="589" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="594" class="Symbol">}</a> <a id="596" class="Symbol">{</a><a id="597" href="category-theory.large-subcategories.html#597" class="Bound">β</a> <a id="599" class="Symbol">:</a> <a id="601" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="607" class="Symbol">→</a> <a id="609" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="615" class="Symbol">→</a> <a id="617" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="622" class="Symbol">}</a>
  <a id="626" class="Symbol">(</a><a id="627" href="category-theory.large-subcategories.html#627" class="Bound">γ</a> <a id="629" class="Symbol">:</a> <a id="631" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="637" class="Symbol">→</a> <a id="639" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="644" class="Symbol">)</a> <a id="646" class="Symbol">(</a><a id="647" href="category-theory.large-subcategories.html#647" class="Bound">δ</a> <a id="649" class="Symbol">:</a> <a id="651" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="657" class="Symbol">→</a> <a id="659" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="665" class="Symbol">→</a> <a id="667" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="672" class="Symbol">)</a>
  <a id="676" class="Symbol">(</a><a id="677" href="category-theory.large-subcategories.html#677" class="Bound">C</a> <a id="679" class="Symbol">:</a> <a id="681" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="696" href="category-theory.large-subcategories.html#577" class="Bound">α</a> <a id="698" href="category-theory.large-subcategories.html#597" class="Bound">β</a><a id="699" class="Symbol">)</a>
  <a id="703" class="Keyword">where</a>

  <a id="712" href="category-theory.large-subcategories.html#712" class="Function">Large-Subcategory</a> <a id="730" class="Symbol">:</a> <a id="732" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="738" href="category-theory.large-subcategories.html#712" class="Function">Large-Subcategory</a> <a id="756" class="Symbol">=</a>
    <a id="762" href="category-theory.large-subprecategories.html#1016" class="Record">Large-Subprecategory</a> <a id="783" href="category-theory.large-subcategories.html#627" class="Bound">γ</a> <a id="785" href="category-theory.large-subcategories.html#647" class="Bound">δ</a> <a id="787" class="Symbol">(</a><a id="788" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a> <a id="821" href="category-theory.large-subcategories.html#677" class="Bound">C</a><a id="822" class="Symbol">)</a>
</pre>