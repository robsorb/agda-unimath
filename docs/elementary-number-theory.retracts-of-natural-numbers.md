# Retracts of the type of natural numbers

<pre class="Agda"><a id="52" class="Keyword">module</a> <a id="59" href="elementary-number-theory.retracts-of-natural-numbers.html" class="Module">elementary-number-theory.retracts-of-natural-numbers</a> <a id="112" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a>
<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="foundation.decidable-maps.html" class="Module">foundation.decidable-maps</a>
<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

If `i : A → ℕ` has a retraction, then `i` is a decidable map.

<pre class="Agda"><a id="is-decidable-map-retraction-ℕ"></a><a id="493" href="elementary-number-theory.retracts-of-natural-numbers.html#493" class="Function">is-decidable-map-retraction-ℕ</a> <a id="523" class="Symbol">:</a>
  <a id="527" class="Symbol">{</a><a id="528" href="elementary-number-theory.retracts-of-natural-numbers.html#528" class="Bound">l1</a> <a id="531" class="Symbol">:</a> <a id="533" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="538" class="Symbol">}</a> <a id="540" class="Symbol">{</a><a id="541" href="elementary-number-theory.retracts-of-natural-numbers.html#541" class="Bound">A</a> <a id="543" class="Symbol">:</a> <a id="545" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="548" href="elementary-number-theory.retracts-of-natural-numbers.html#528" class="Bound">l1</a><a id="550" class="Symbol">}</a> <a id="552" class="Symbol">(</a><a id="553" href="elementary-number-theory.retracts-of-natural-numbers.html#553" class="Bound">i</a> <a id="555" class="Symbol">:</a> <a id="557" href="elementary-number-theory.retracts-of-natural-numbers.html#541" class="Bound">A</a> <a id="559" class="Symbol">→</a> <a id="561" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="562" class="Symbol">)</a> <a id="564" class="Symbol">→</a> <a id="566" href="foundation-core.retractions.html#874" class="Function">retraction</a> <a id="577" href="elementary-number-theory.retracts-of-natural-numbers.html#553" class="Bound">i</a> <a id="579" class="Symbol">→</a> <a id="581" href="foundation.decidable-maps.html#1586" class="Function">is-decidable-map</a> <a id="598" href="elementary-number-theory.retracts-of-natural-numbers.html#553" class="Bound">i</a>
<a id="600" href="elementary-number-theory.retracts-of-natural-numbers.html#493" class="Function">is-decidable-map-retraction-ℕ</a> <a id="630" class="Symbol">=</a>
  <a id="634" href="foundation.decidable-maps.html#3793" class="Function">is-decidable-map-retraction</a> <a id="662" href="elementary-number-theory.equality-natural-numbers.html#2869" class="Function">has-decidable-equality-ℕ</a>
</pre>