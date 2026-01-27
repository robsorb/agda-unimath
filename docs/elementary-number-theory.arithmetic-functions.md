# Arithmetic functions

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="elementary-number-theory.arithmetic-functions.html" class="Module">elementary-number-theory.arithmetic-functions</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="elementary-number-theory.nonzero-natural-numbers.html" class="Module">elementary-number-theory.nonzero-natural-numbers</a>

<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

An arithmetic function is a function from the nonzero natural numbers into a
(commutative) ring. The arithmetic functions form a ring under pointwise
addition and dirichlet convolution.

## Definition

<pre class="Agda"><a id="510" class="Keyword">module</a> <a id="517" href="elementary-number-theory.arithmetic-functions.html#517" class="Module">_</a>
  <a id="521" class="Symbol">{</a><a id="522" href="elementary-number-theory.arithmetic-functions.html#522" class="Bound">l</a> <a id="524" class="Symbol">:</a> <a id="526" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="531" class="Symbol">}</a> <a id="533" class="Symbol">(</a><a id="534" href="elementary-number-theory.arithmetic-functions.html#534" class="Bound">R</a> <a id="536" class="Symbol">:</a> <a id="538" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="543" href="elementary-number-theory.arithmetic-functions.html#522" class="Bound">l</a><a id="544" class="Symbol">)</a>
  <a id="548" class="Keyword">where</a>

  <a id="557" href="elementary-number-theory.arithmetic-functions.html#557" class="Function">type-arithmetic-functions-Ring</a> <a id="588" class="Symbol">:</a> <a id="590" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="593" href="elementary-number-theory.arithmetic-functions.html#522" class="Bound">l</a>
  <a id="597" href="elementary-number-theory.arithmetic-functions.html#557" class="Function">type-arithmetic-functions-Ring</a> <a id="628" class="Symbol">=</a> <a id="630" href="elementary-number-theory.nonzero-natural-numbers.html#1455" class="Function">nonzero-ℕ</a> <a id="640" class="Symbol">→</a> <a id="642" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="652" href="elementary-number-theory.arithmetic-functions.html#534" class="Bound">R</a>
</pre>