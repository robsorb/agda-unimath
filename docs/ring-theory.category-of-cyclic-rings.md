# The category of cyclic rings

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="ring-theory.category-of-cyclic-rings.html" class="Module">ring-theory.category-of-cyclic-rings</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>

<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>

<a id="409" class="Keyword">open</a> <a id="414" class="Keyword">import</a> <a id="421" href="ring-theory.category-of-rings.html" class="Module">ring-theory.category-of-rings</a>
<a id="451" class="Keyword">open</a> <a id="456" class="Keyword">import</a> <a id="463" href="ring-theory.cyclic-rings.html" class="Module">ring-theory.cyclic-rings</a>
<a id="488" class="Keyword">open</a> <a id="493" class="Keyword">import</a> <a id="500" href="ring-theory.homomorphisms-cyclic-rings.html" class="Module">ring-theory.homomorphisms-cyclic-rings</a>
<a id="539" class="Keyword">open</a> <a id="544" class="Keyword">import</a> <a id="551" href="ring-theory.precategory-of-rings.html" class="Module">ring-theory.precategory-of-rings</a>
</pre>
</details>

## Idea

The
{{#concept "large category of cyclic rings" Agda=Cyclic-Ring-Large-Category}} is
the [large category](category-theory.large-categories.md) consisting of
[cyclic rings](ring-theory.cyclic-rings.md) and
[ring homomorphisms](ring-theory.homomorphisms-cyclic-rings.md).

Note that we already showed that there is at most one ring homomorphism between
any two cyclic rings, so it follows that the large category of cyclic rings is
in fact a [large poset](order-theory.large-posets.md). The large poset of cyclic
rings is constructed in the file
[`ring-theory.poset-of-cyclic-rings`](ring-theory.poset-of-cyclic-rings.md).

## Definition

### The precategory of cyclic rings as a full subprecategory of the precategory of rings

<pre class="Agda"><a id="Cyclic-Ring-Full-Large-Subprecategory"></a><a id="1345" href="ring-theory.category-of-cyclic-rings.html#1345" class="Function">Cyclic-Ring-Full-Large-Subprecategory</a> <a id="1383" class="Symbol">:</a>
  <a id="1387" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a> <a id="1413" class="Symbol">(λ</a> <a id="1416" href="ring-theory.category-of-cyclic-rings.html#1416" class="Bound">l</a> <a id="1418" class="Symbol">→</a> <a id="1420" href="ring-theory.category-of-cyclic-rings.html#1416" class="Bound">l</a><a id="1421" class="Symbol">)</a> <a id="1423" href="ring-theory.precategory-of-rings.html#566" class="Function">Ring-Large-Precategory</a>
<a id="1446" href="ring-theory.category-of-cyclic-rings.html#1345" class="Function">Cyclic-Ring-Full-Large-Subprecategory</a> <a id="1484" class="Symbol">=</a> <a id="1486" href="ring-theory.cyclic-rings.html#2909" class="Function">is-cyclic-prop-Ring</a>
</pre>
### The large precategory of cyclic rings

<pre class="Agda"><a id="Cyclic-Ring-Large-Precategory"></a><a id="1562" href="ring-theory.category-of-cyclic-rings.html#1562" class="Function">Cyclic-Ring-Large-Precategory</a> <a id="1592" class="Symbol">:</a> <a id="1594" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1612" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1617" class="Symbol">(</a><a id="1618" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1621" class="Symbol">)</a>
<a id="1623" href="ring-theory.category-of-cyclic-rings.html#1562" class="Function">Cyclic-Ring-Large-Precategory</a> <a id="1653" class="Symbol">=</a>
  <a id="1657" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="1705" class="Symbol">(</a> <a id="1707" href="ring-theory.precategory-of-rings.html#566" class="Function">Ring-Large-Precategory</a><a id="1729" class="Symbol">)</a>
    <a id="1735" class="Symbol">(</a> <a id="1737" href="ring-theory.category-of-cyclic-rings.html#1345" class="Function">Cyclic-Ring-Full-Large-Subprecategory</a><a id="1774" class="Symbol">)</a>
</pre>
### The large category of cyclic rings

<pre class="Agda"><a id="1829" class="Keyword">abstract</a>
  <a id="is-large-category-Cyclic-Ring-Large-Category"></a><a id="1840" href="ring-theory.category-of-cyclic-rings.html#1840" class="Function">is-large-category-Cyclic-Ring-Large-Category</a> <a id="1885" class="Symbol">:</a>
    <a id="1891" href="category-theory.large-categories.html#1350" class="Function">is-large-category-Large-Precategory</a> <a id="1927" href="ring-theory.category-of-cyclic-rings.html#1562" class="Function">Cyclic-Ring-Large-Precategory</a>
  <a id="1959" href="ring-theory.category-of-cyclic-rings.html#1840" class="Function">is-large-category-Cyclic-Ring-Large-Category</a> <a id="2004" class="Symbol">=</a>
    <a id="2010" href="category-theory.full-large-subprecategories.html#8647" class="Function">is-large-category-large-precategory-is-large-category-Full-Large-Subprecategory</a>
      <a id="2096" class="Symbol">(</a> <a id="2098" href="ring-theory.precategory-of-rings.html#566" class="Function">Ring-Large-Precategory</a><a id="2120" class="Symbol">)</a>
      <a id="2128" class="Symbol">(</a> <a id="2130" href="ring-theory.category-of-cyclic-rings.html#1345" class="Function">Cyclic-Ring-Full-Large-Subprecategory</a><a id="2167" class="Symbol">)</a>
      <a id="2175" class="Symbol">(</a> <a id="2177" href="ring-theory.category-of-rings.html#635" class="Function">is-large-category-Ring-Large-Category</a><a id="2214" class="Symbol">)</a>

<a id="Cyclic-Ring-Large-Category"></a><a id="2217" href="ring-theory.category-of-cyclic-rings.html#2217" class="Function">Cyclic-Ring-Large-Category</a> <a id="2244" class="Symbol">:</a> <a id="2246" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="2261" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2266" class="Symbol">(</a><a id="2267" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="2270" class="Symbol">)</a>
<a id="2272" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a>
  <a id="2307" href="ring-theory.category-of-cyclic-rings.html#2217" class="Function">Cyclic-Ring-Large-Category</a> <a id="2334" class="Symbol">=</a>
  <a id="2338" href="ring-theory.category-of-cyclic-rings.html#1562" class="Function">Cyclic-Ring-Large-Precategory</a>
<a id="2368" href="category-theory.large-categories.html#1868" class="Field">is-large-category-Large-Category</a>
  <a id="2403" href="ring-theory.category-of-cyclic-rings.html#2217" class="Function">Cyclic-Ring-Large-Category</a> <a id="2430" class="Symbol">=</a>
  <a id="2434" href="ring-theory.category-of-cyclic-rings.html#1840" class="Function">is-large-category-Cyclic-Ring-Large-Category</a>
</pre>
### The small categories of cyclic rings

<pre class="Agda"><a id="Cyclic-Ring-Category"></a><a id="2534" href="ring-theory.category-of-cyclic-rings.html#2534" class="Function">Cyclic-Ring-Category</a> <a id="2555" class="Symbol">:</a> <a id="2557" class="Symbol">(</a><a id="2558" href="ring-theory.category-of-cyclic-rings.html#2558" class="Bound">l</a> <a id="2560" class="Symbol">:</a> <a id="2562" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2567" class="Symbol">)</a> <a id="2569" class="Symbol">→</a> <a id="2571" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="2580" class="Symbol">(</a><a id="2581" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2586" href="ring-theory.category-of-cyclic-rings.html#2558" class="Bound">l</a><a id="2587" class="Symbol">)</a> <a id="2589" href="ring-theory.category-of-cyclic-rings.html#2558" class="Bound">l</a>
<a id="2591" href="ring-theory.category-of-cyclic-rings.html#2534" class="Function">Cyclic-Ring-Category</a> <a id="2612" class="Symbol">=</a> <a id="2614" href="category-theory.large-categories.html#7051" class="Function">category-Large-Category</a> <a id="2638" href="ring-theory.category-of-cyclic-rings.html#2217" class="Function">Cyclic-Ring-Large-Category</a>
</pre>
## Properties

### The large category of cyclic rings is a large poset

<pre class="Agda"><a id="is-large-poset-Cyclic-Ring-Large-Category"></a><a id="2750" href="ring-theory.category-of-cyclic-rings.html#2750" class="Function">is-large-poset-Cyclic-Ring-Large-Category</a> <a id="2792" class="Symbol">:</a>
  <a id="2796" href="order-theory.large-posets.html#3685" class="Function">is-large-poset-Large-Category</a> <a id="2826" href="ring-theory.category-of-cyclic-rings.html#2217" class="Function">Cyclic-Ring-Large-Category</a>
<a id="2853" href="ring-theory.category-of-cyclic-rings.html#2750" class="Function">is-large-poset-Cyclic-Ring-Large-Category</a> <a id="2895" class="Symbol">=</a>
  <a id="2899" href="ring-theory.homomorphisms-cyclic-rings.html#4535" class="Function">is-prop-hom-Cyclic-Ring</a>
</pre>
## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
