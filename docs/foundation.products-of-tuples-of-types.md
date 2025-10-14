# Products of tuples of types

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="foundation.products-of-tuples-of-types.html" class="Module">foundation.products-of-tuples-of-types</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.tuples-of-types.html" class="Module">foundation.tuples-of-types</a>
<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The product of an `n`-tuple of types is their dependent product.

## Definition

### Products of `n`-tuples of types

<pre class="Agda"><a id="product-tuple-types"></a><a id="485" href="foundation.products-of-tuples-of-types.html#485" class="Function">product-tuple-types</a> <a id="505" class="Symbol">:</a>
  <a id="509" class="Symbol">{</a><a id="510" href="foundation.products-of-tuples-of-types.html#510" class="Bound">l</a> <a id="512" class="Symbol">:</a> <a id="514" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="519" class="Symbol">}</a> <a id="521" class="Symbol">(</a><a id="522" href="foundation.products-of-tuples-of-types.html#522" class="Bound">n</a> <a id="524" class="Symbol">:</a> <a id="526" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="527" class="Symbol">)</a> <a id="529" class="Symbol">→</a> <a id="531" href="foundation.tuples-of-types.html#373" class="Function">tuple-types</a> <a id="543" href="foundation.products-of-tuples-of-types.html#510" class="Bound">l</a> <a id="545" href="foundation.products-of-tuples-of-types.html#522" class="Bound">n</a> <a id="547" class="Symbol">→</a> <a id="549" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="552" href="foundation.products-of-tuples-of-types.html#510" class="Bound">l</a>
<a id="554" href="foundation.products-of-tuples-of-types.html#485" class="Function">product-tuple-types</a> <a id="574" href="foundation.products-of-tuples-of-types.html#574" class="Bound">n</a> <a id="576" href="foundation.products-of-tuples-of-types.html#576" class="Bound">A</a> <a id="578" class="Symbol">=</a> <a id="580" class="Symbol">(</a><a id="581" href="foundation.products-of-tuples-of-types.html#581" class="Bound">i</a> <a id="583" class="Symbol">:</a> <a id="585" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="589" href="foundation.products-of-tuples-of-types.html#574" class="Bound">n</a><a id="590" class="Symbol">)</a> <a id="592" class="Symbol">→</a> <a id="594" href="foundation.products-of-tuples-of-types.html#576" class="Bound">A</a> <a id="596" href="foundation.products-of-tuples-of-types.html#581" class="Bound">i</a>
</pre>
### The projection maps

<pre class="Agda"><a id="pr-product-tuple-types"></a><a id="636" href="foundation.products-of-tuples-of-types.html#636" class="Function">pr-product-tuple-types</a> <a id="659" class="Symbol">:</a>
  <a id="663" class="Symbol">{</a><a id="664" href="foundation.products-of-tuples-of-types.html#664" class="Bound">l</a> <a id="666" class="Symbol">:</a> <a id="668" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="673" class="Symbol">}</a> <a id="675" class="Symbol">{</a><a id="676" href="foundation.products-of-tuples-of-types.html#676" class="Bound">n</a> <a id="678" class="Symbol">:</a> <a id="680" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="681" class="Symbol">}</a> <a id="683" class="Symbol">(</a><a id="684" href="foundation.products-of-tuples-of-types.html#684" class="Bound">A</a> <a id="686" class="Symbol">:</a> <a id="688" href="foundation.tuples-of-types.html#373" class="Function">tuple-types</a> <a id="700" href="foundation.products-of-tuples-of-types.html#664" class="Bound">l</a> <a id="702" href="foundation.products-of-tuples-of-types.html#676" class="Bound">n</a><a id="703" class="Symbol">)</a> <a id="705" class="Symbol">(</a><a id="706" href="foundation.products-of-tuples-of-types.html#706" class="Bound">i</a> <a id="708" class="Symbol">:</a> <a id="710" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="714" href="foundation.products-of-tuples-of-types.html#676" class="Bound">n</a><a id="715" class="Symbol">)</a> <a id="717" class="Symbol">→</a>
  <a id="721" href="foundation.products-of-tuples-of-types.html#485" class="Function">product-tuple-types</a> <a id="741" href="foundation.products-of-tuples-of-types.html#676" class="Bound">n</a> <a id="743" href="foundation.products-of-tuples-of-types.html#684" class="Bound">A</a> <a id="745" class="Symbol">→</a> <a id="747" href="foundation.products-of-tuples-of-types.html#684" class="Bound">A</a> <a id="749" href="foundation.products-of-tuples-of-types.html#706" class="Bound">i</a>
<a id="751" href="foundation.products-of-tuples-of-types.html#636" class="Function">pr-product-tuple-types</a> <a id="774" href="foundation.products-of-tuples-of-types.html#774" class="Bound">A</a> <a id="776" href="foundation.products-of-tuples-of-types.html#776" class="Bound">i</a> <a id="778" href="foundation.products-of-tuples-of-types.html#778" class="Bound">f</a> <a id="780" class="Symbol">=</a> <a id="782" href="foundation.products-of-tuples-of-types.html#778" class="Bound">f</a> <a id="784" href="foundation.products-of-tuples-of-types.html#776" class="Bound">i</a>
</pre>