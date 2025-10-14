# Constant matrices

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="linear-algebra.constant-matrices.html" class="Module">linear-algebra.constant-matrices</a> <a id="70" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="126" class="Keyword">open</a> <a id="131" class="Keyword">import</a> <a id="138" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="linear-algebra.constant-tuples.html" class="Module">linear-algebra.constant-tuples</a>
<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="linear-algebra.matrices.html" class="Module">linear-algebra.matrices</a>
</pre>
</details>

## Idea

Constant matrices are [matrices](linear-algebra.matrices.md) in which all
elements are the same.

## Definition

<pre class="Agda"><a id="constant-matrix"></a><a id="446" href="linear-algebra.constant-matrices.html#446" class="Function">constant-matrix</a> <a id="462" class="Symbol">:</a> <a id="464" class="Symbol">{</a><a id="465" href="linear-algebra.constant-matrices.html#465" class="Bound">l</a> <a id="467" class="Symbol">:</a> <a id="469" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="474" class="Symbol">}</a> <a id="476" class="Symbol">{</a><a id="477" href="linear-algebra.constant-matrices.html#477" class="Bound">A</a> <a id="479" class="Symbol">:</a> <a id="481" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="484" href="linear-algebra.constant-matrices.html#465" class="Bound">l</a><a id="485" class="Symbol">}</a> <a id="487" class="Symbol">{</a><a id="488" href="linear-algebra.constant-matrices.html#488" class="Bound">m</a> <a id="490" href="linear-algebra.constant-matrices.html#490" class="Bound">n</a> <a id="492" class="Symbol">:</a> <a id="494" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="495" class="Symbol">}</a> <a id="497" class="Symbol">→</a> <a id="499" href="linear-algebra.constant-matrices.html#477" class="Bound">A</a> <a id="501" class="Symbol">→</a> <a id="503" href="linear-algebra.matrices.html#788" class="Function">matrix</a> <a id="510" href="linear-algebra.constant-matrices.html#477" class="Bound">A</a> <a id="512" href="linear-algebra.constant-matrices.html#488" class="Bound">m</a> <a id="514" href="linear-algebra.constant-matrices.html#490" class="Bound">n</a>
<a id="516" href="linear-algebra.constant-matrices.html#446" class="Function">constant-matrix</a> <a id="532" href="linear-algebra.constant-matrices.html#532" class="Bound">a</a> <a id="534" class="Symbol">=</a> <a id="536" href="linear-algebra.constant-tuples.html#413" class="Function">constant-tuple</a> <a id="551" class="Symbol">(</a><a id="552" href="linear-algebra.constant-tuples.html#413" class="Function">constant-tuple</a> <a id="567" href="linear-algebra.constant-matrices.html#532" class="Bound">a</a><a id="568" class="Symbol">)</a>
</pre>