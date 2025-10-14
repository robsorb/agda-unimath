# Initial objects of large categories

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="category-theory.initial-objects-large-categories.html" class="Module">category-theory.initial-objects-large-categories</a> <a id="104" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="category-theory.initial-objects-large-precategories.html" class="Module">category-theory.initial-objects-large-precategories</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>

<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An **initial object** in a [large category](category-theory.large-categories.md)
`C` is an object `X` such that `hom X Y` is
[contractible](foundation.contractible-types.md) for any object `Y`.

## Definitions

### Initial objects in large categories

<pre class="Agda"><a id="595" class="Keyword">module</a> <a id="602" href="category-theory.initial-objects-large-categories.html#602" class="Module">_</a>
  <a id="606" class="Symbol">{</a><a id="607" href="category-theory.initial-objects-large-categories.html#607" class="Bound">α</a> <a id="609" class="Symbol">:</a> <a id="611" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="617" class="Symbol">→</a> <a id="619" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="624" class="Symbol">}</a> <a id="626" class="Symbol">{</a><a id="627" href="category-theory.initial-objects-large-categories.html#627" class="Bound">β</a> <a id="629" class="Symbol">:</a> <a id="631" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="637" class="Symbol">→</a> <a id="639" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="645" class="Symbol">→</a> <a id="647" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="652" class="Symbol">}</a>
  <a id="656" class="Symbol">(</a><a id="657" href="category-theory.initial-objects-large-categories.html#657" class="Bound">C</a> <a id="659" class="Symbol">:</a> <a id="661" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="676" href="category-theory.initial-objects-large-categories.html#607" class="Bound">α</a> <a id="678" href="category-theory.initial-objects-large-categories.html#627" class="Bound">β</a><a id="679" class="Symbol">)</a>
  <a id="683" class="Symbol">{</a><a id="684" href="category-theory.initial-objects-large-categories.html#684" class="Bound">l</a> <a id="686" class="Symbol">:</a> <a id="688" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="693" class="Symbol">}</a> <a id="695" class="Symbol">(</a><a id="696" href="category-theory.initial-objects-large-categories.html#696" class="Bound">X</a> <a id="698" class="Symbol">:</a> <a id="700" href="category-theory.large-categories.html#2116" class="Function">obj-Large-Category</a> <a id="719" href="category-theory.initial-objects-large-categories.html#657" class="Bound">C</a> <a id="721" href="category-theory.initial-objects-large-categories.html#684" class="Bound">l</a><a id="722" class="Symbol">)</a>
  <a id="726" class="Keyword">where</a>

  <a id="735" href="category-theory.initial-objects-large-categories.html#735" class="Function">is-initial-obj-Large-Category</a> <a id="765" class="Symbol">:</a> <a id="767" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="773" href="category-theory.initial-objects-large-categories.html#735" class="Function">is-initial-obj-Large-Category</a> <a id="803" class="Symbol">=</a>
    <a id="809" href="category-theory.initial-objects-large-precategories.html#728" class="Function">is-initial-obj-Large-Precategory</a> <a id="842" class="Symbol">(</a><a id="843" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a> <a id="876" href="category-theory.initial-objects-large-categories.html#657" class="Bound">C</a><a id="877" class="Symbol">)</a> <a id="879" href="category-theory.initial-objects-large-categories.html#696" class="Bound">X</a>
</pre>