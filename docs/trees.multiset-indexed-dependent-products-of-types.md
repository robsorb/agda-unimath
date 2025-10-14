# Multiset-indexed dependent products of types

<pre class="Agda"><a id="57" class="Keyword">module</a> <a id="64" href="trees.multiset-indexed-dependent-products-of-types.html" class="Module">trees.multiset-indexed-dependent-products-of-types</a> <a id="115" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="trees.multisets.html" class="Module">trees.multisets</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="trees.w-types.html" class="Module">trees.w-types</a>
</pre>
</details>

## Idea

Consider a [multiset](trees.multisets.md) `M`. Then `M` can be seen as a tower
of type families, via the inclusion from the type of all multisets, which are
the well-founded trees, into the type of all trees.

This leads to the idea that we should be able to take the iterated dependent
product of this tower of type families.

## Definitions

### The iterated dependent product of types indexed by a multiset

<pre class="Agda"><a id="iterated-Π-𝕍"></a><a id="764" href="trees.multiset-indexed-dependent-products-of-types.html#764" class="Function">iterated-Π-𝕍</a> <a id="777" class="Symbol">:</a> <a id="779" class="Symbol">{</a><a id="780" href="trees.multiset-indexed-dependent-products-of-types.html#780" class="Bound">l</a> <a id="782" class="Symbol">:</a> <a id="784" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="789" class="Symbol">}</a> <a id="791" class="Symbol">→</a> <a id="793" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="795" class="Symbol">→</a> <a id="797" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="799" href="trees.multiset-indexed-dependent-products-of-types.html#780" class="Bound">l</a> <a id="801" class="Symbol">→</a> <a id="803" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="806" href="trees.multiset-indexed-dependent-products-of-types.html#780" class="Bound">l</a>
<a id="808" href="trees.multiset-indexed-dependent-products-of-types.html#764" class="Function">iterated-Π-𝕍</a> <a id="821" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="828" class="Symbol">(</a><a id="829" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="836" href="trees.multiset-indexed-dependent-products-of-types.html#836" class="Bound">X</a> <a id="838" href="trees.multiset-indexed-dependent-products-of-types.html#838" class="Bound">Y</a><a id="839" class="Symbol">)</a> <a id="841" class="Symbol">=</a> <a id="843" href="trees.multiset-indexed-dependent-products-of-types.html#836" class="Bound">X</a>
<a id="845" href="trees.multiset-indexed-dependent-products-of-types.html#764" class="Function">iterated-Π-𝕍</a> <a id="858" class="Symbol">(</a><a id="859" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="866" href="trees.multiset-indexed-dependent-products-of-types.html#866" class="Bound">n</a><a id="867" class="Symbol">)</a> <a id="869" class="Symbol">(</a><a id="870" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="877" href="trees.multiset-indexed-dependent-products-of-types.html#877" class="Bound">X</a> <a id="879" href="trees.multiset-indexed-dependent-products-of-types.html#879" class="Bound">Y</a><a id="880" class="Symbol">)</a> <a id="882" class="Symbol">=</a> <a id="884" class="Symbol">(</a><a id="885" href="trees.multiset-indexed-dependent-products-of-types.html#885" class="Bound">x</a> <a id="887" class="Symbol">:</a> <a id="889" href="trees.multiset-indexed-dependent-products-of-types.html#877" class="Bound">X</a><a id="890" class="Symbol">)</a> <a id="892" class="Symbol">→</a> <a id="894" href="trees.multiset-indexed-dependent-products-of-types.html#764" class="Function">iterated-Π-𝕍</a> <a id="907" href="trees.multiset-indexed-dependent-products-of-types.html#866" class="Bound">n</a> <a id="909" class="Symbol">(</a><a id="910" href="trees.multiset-indexed-dependent-products-of-types.html#879" class="Bound">Y</a> <a id="912" href="trees.multiset-indexed-dependent-products-of-types.html#885" class="Bound">x</a><a id="913" class="Symbol">)</a>
</pre>