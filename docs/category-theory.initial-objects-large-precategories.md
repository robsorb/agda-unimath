# Initial objects of large precategories

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="category-theory.initial-objects-large-precategories.html" class="Module">category-theory.initial-objects-large-precategories</a> <a id="110" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>

<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An **initial object** in a [large category](category-theory.large-categories.md)
`C` is an object `X` such that `hom X Y` is
[contractible](foundation.contractible-types.md) for any object `Y`.

## Definitions

### Initial objects in large categories

<pre class="Agda"><a id="582" class="Keyword">module</a> <a id="589" href="category-theory.initial-objects-large-precategories.html#589" class="Module">_</a>
  <a id="593" class="Symbol">{</a><a id="594" href="category-theory.initial-objects-large-precategories.html#594" class="Bound">α</a> <a id="596" class="Symbol">:</a> <a id="598" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="604" class="Symbol">→</a> <a id="606" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="611" class="Symbol">}</a> <a id="613" class="Symbol">{</a><a id="614" href="category-theory.initial-objects-large-precategories.html#614" class="Bound">β</a> <a id="616" class="Symbol">:</a> <a id="618" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="624" class="Symbol">→</a> <a id="626" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="632" class="Symbol">→</a> <a id="634" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="639" class="Symbol">}</a>
  <a id="643" class="Symbol">(</a><a id="644" href="category-theory.initial-objects-large-precategories.html#644" class="Bound">C</a> <a id="646" class="Symbol">:</a> <a id="648" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="666" href="category-theory.initial-objects-large-precategories.html#594" class="Bound">α</a> <a id="668" href="category-theory.initial-objects-large-precategories.html#614" class="Bound">β</a><a id="669" class="Symbol">)</a>
  <a id="673" class="Symbol">{</a><a id="674" href="category-theory.initial-objects-large-precategories.html#674" class="Bound">l</a> <a id="676" class="Symbol">:</a> <a id="678" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="683" class="Symbol">}</a> <a id="685" class="Symbol">(</a><a id="686" href="category-theory.initial-objects-large-precategories.html#686" class="Bound">X</a> <a id="688" class="Symbol">:</a> <a id="690" href="category-theory.large-precategories.html#920" class="Field">obj-Large-Precategory</a> <a id="712" href="category-theory.initial-objects-large-precategories.html#644" class="Bound">C</a> <a id="714" href="category-theory.initial-objects-large-precategories.html#674" class="Bound">l</a><a id="715" class="Symbol">)</a>
  <a id="719" class="Keyword">where</a>

  <a id="728" href="category-theory.initial-objects-large-precategories.html#728" class="Function">is-initial-obj-Large-Precategory</a> <a id="761" class="Symbol">:</a> <a id="763" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="769" href="category-theory.initial-objects-large-precategories.html#728" class="Function">is-initial-obj-Large-Precategory</a> <a id="802" class="Symbol">=</a>
    <a id="808" class="Symbol">{</a><a id="809" href="category-theory.initial-objects-large-precategories.html#809" class="Bound">l2</a> <a id="812" class="Symbol">:</a> <a id="814" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="819" class="Symbol">}</a> <a id="821" class="Symbol">(</a><a id="822" href="category-theory.initial-objects-large-precategories.html#822" class="Bound">Y</a> <a id="824" class="Symbol">:</a> <a id="826" href="category-theory.large-precategories.html#920" class="Field">obj-Large-Precategory</a> <a id="848" href="category-theory.initial-objects-large-precategories.html#644" class="Bound">C</a> <a id="850" href="category-theory.initial-objects-large-precategories.html#809" class="Bound">l2</a><a id="852" class="Symbol">)</a> <a id="854" class="Symbol">→</a>
    <a id="860" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="869" class="Symbol">(</a><a id="870" href="category-theory.large-precategories.html#1119" class="Function">hom-Large-Precategory</a> <a id="892" href="category-theory.initial-objects-large-precategories.html#644" class="Bound">C</a> <a id="894" href="category-theory.initial-objects-large-precategories.html#686" class="Bound">X</a> <a id="896" href="category-theory.initial-objects-large-precategories.html#822" class="Bound">Y</a><a id="897" class="Symbol">)</a>
</pre>