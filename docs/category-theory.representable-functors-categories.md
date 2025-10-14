# Representable functors between categories

<pre class="Agda"><a id="54" class="Keyword">module</a> <a id="61" href="category-theory.representable-functors-categories.html" class="Module">category-theory.representable-functors-categories</a> <a id="111" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="category-theory.functors-categories.html" class="Module">category-theory.functors-categories</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="category-theory.natural-transformations-functors-categories.html" class="Module">category-theory.natural-transformations-functors-categories</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="category-theory.representable-functors-precategories.html" class="Module">category-theory.representable-functors-precategories</a>

<a id="392" class="Keyword">open</a> <a id="397" class="Keyword">import</a> <a id="404" href="foundation.category-of-sets.html" class="Module">foundation.category-of-sets</a>
<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Given a [category](category-theory.categories.md) `C` and an object `c`, there
is a [functor](category-theory.functors-categories.md) from `C` to the
[category of sets](foundation.category-of-sets.md) **represented** by `c` that:

- sends an object `x` of `C` to the [set](foundation-core.sets.md) `hom c x` and
- sends a morphism `g : hom x y` of `C` to the function `hom c x → hom c y`
  defined by postcomposition with `g`.

The functoriality axioms follow, by
[function extensionality](foundation.function-extensionality.md), from
associativity and the left unit law for the category `C`.

## Definition

<pre class="Agda"><a id="representable-functor-Category"></a><a id="1114" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="1145" class="Symbol">:</a>
  <a id="1149" class="Symbol">{</a><a id="1150" href="category-theory.representable-functors-categories.html#1150" class="Bound">l1</a> <a id="1153" href="category-theory.representable-functors-categories.html#1153" class="Bound">l2</a> <a id="1156" class="Symbol">:</a> <a id="1158" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1163" class="Symbol">}</a> <a id="1165" class="Symbol">(</a><a id="1166" href="category-theory.representable-functors-categories.html#1166" class="Bound">C</a> <a id="1168" class="Symbol">:</a> <a id="1170" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1179" href="category-theory.representable-functors-categories.html#1150" class="Bound">l1</a> <a id="1182" href="category-theory.representable-functors-categories.html#1153" class="Bound">l2</a><a id="1184" class="Symbol">)</a> <a id="1186" class="Symbol">(</a><a id="1187" href="category-theory.representable-functors-categories.html#1187" class="Bound">c</a> <a id="1189" class="Symbol">:</a> <a id="1191" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="1204" href="category-theory.representable-functors-categories.html#1166" class="Bound">C</a><a id="1205" class="Symbol">)</a> <a id="1207" class="Symbol">→</a>
  <a id="1211" href="category-theory.functors-categories.html#2227" class="Function">functor-Category</a> <a id="1228" href="category-theory.representable-functors-categories.html#1166" class="Bound">C</a> <a id="1230" class="Symbol">(</a><a id="1231" href="foundation.category-of-sets.html#3849" class="Function">Set-Category</a> <a id="1244" href="category-theory.representable-functors-categories.html#1153" class="Bound">l2</a><a id="1246" class="Symbol">)</a>
<a id="1248" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="1279" href="category-theory.representable-functors-categories.html#1279" class="Bound">C</a> <a id="1281" class="Symbol">=</a>
  <a id="1285" href="category-theory.representable-functors-precategories.html#2646" class="Function">representable-functor-Precategory</a> <a id="1319" class="Symbol">(</a><a id="1320" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1341" href="category-theory.representable-functors-categories.html#1279" class="Bound">C</a><a id="1342" class="Symbol">)</a>
</pre>
## Natural transformations between representable functors

A morphism `f : hom b c` in a category `C` defines a
[natural transformation](category-theory.natural-transformations-functors-categories.md)
from the functor represented by `c` to the functor represented by `b`. Its
components `hom c x → hom b x` are defined by precomposition with `f`.

<pre class="Agda"><a id="representable-natural-transformation-Category"></a><a id="1705" href="category-theory.representable-functors-categories.html#1705" class="Function">representable-natural-transformation-Category</a> <a id="1751" class="Symbol">:</a>
  <a id="1755" class="Symbol">{</a><a id="1756" href="category-theory.representable-functors-categories.html#1756" class="Bound">l1</a> <a id="1759" href="category-theory.representable-functors-categories.html#1759" class="Bound">l2</a> <a id="1762" class="Symbol">:</a> <a id="1764" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1769" class="Symbol">}</a> <a id="1771" class="Symbol">(</a><a id="1772" href="category-theory.representable-functors-categories.html#1772" class="Bound">C</a> <a id="1774" class="Symbol">:</a> <a id="1776" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1785" href="category-theory.representable-functors-categories.html#1756" class="Bound">l1</a> <a id="1788" href="category-theory.representable-functors-categories.html#1759" class="Bound">l2</a><a id="1790" class="Symbol">)</a> <a id="1792" class="Symbol">{</a><a id="1793" href="category-theory.representable-functors-categories.html#1793" class="Bound">b</a> <a id="1795" href="category-theory.representable-functors-categories.html#1795" class="Bound">c</a> <a id="1797" class="Symbol">:</a> <a id="1799" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="1812" href="category-theory.representable-functors-categories.html#1772" class="Bound">C</a><a id="1813" class="Symbol">}</a>
  <a id="1817" class="Symbol">(</a><a id="1818" href="category-theory.representable-functors-categories.html#1818" class="Bound">f</a> <a id="1820" class="Symbol">:</a> <a id="1822" href="category-theory.categories.html#2741" class="Function">hom-Category</a> <a id="1835" href="category-theory.representable-functors-categories.html#1772" class="Bound">C</a> <a id="1837" href="category-theory.representable-functors-categories.html#1793" class="Bound">b</a> <a id="1839" href="category-theory.representable-functors-categories.html#1795" class="Bound">c</a><a id="1840" class="Symbol">)</a> <a id="1842" class="Symbol">→</a>
  <a id="1846" href="category-theory.natural-transformations-functors-categories.html#1571" class="Function">natural-transformation-Category</a>
    <a id="1882" class="Symbol">(</a> <a id="1884" href="category-theory.representable-functors-categories.html#1772" class="Bound">C</a><a id="1885" class="Symbol">)</a>
    <a id="1891" class="Symbol">(</a> <a id="1893" href="foundation.category-of-sets.html#3849" class="Function">Set-Category</a> <a id="1906" href="category-theory.representable-functors-categories.html#1759" class="Bound">l2</a><a id="1908" class="Symbol">)</a>
    <a id="1914" class="Symbol">(</a> <a id="1916" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="1947" href="category-theory.representable-functors-categories.html#1772" class="Bound">C</a> <a id="1949" href="category-theory.representable-functors-categories.html#1795" class="Bound">c</a><a id="1950" class="Symbol">)</a>
    <a id="1956" class="Symbol">(</a> <a id="1958" href="category-theory.representable-functors-categories.html#1114" class="Function">representable-functor-Category</a> <a id="1989" href="category-theory.representable-functors-categories.html#1772" class="Bound">C</a> <a id="1991" href="category-theory.representable-functors-categories.html#1793" class="Bound">b</a><a id="1992" class="Symbol">)</a>
<a id="1994" href="category-theory.representable-functors-categories.html#1705" class="Function">representable-natural-transformation-Category</a> <a id="2040" href="category-theory.representable-functors-categories.html#2040" class="Bound">C</a> <a id="2042" class="Symbol">=</a>
  <a id="2046" href="category-theory.representable-functors-precategories.html#4402" class="Function">representable-natural-transformation-Precategory</a> <a id="2095" class="Symbol">(</a><a id="2096" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2117" href="category-theory.representable-functors-categories.html#2040" class="Bound">C</a><a id="2118" class="Symbol">)</a>
</pre>