# Diagonal tuples

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="linear-algebra.constant-tuples.html" class="Module">linear-algebra.constant-tuples</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="lists.tuples.html" class="Module">lists.tuples</a>
</pre>
</details>

## Idea

Diagonal tuples are [tuples](lists.tuples.md) on the diagonal, i.e., they are
tuples of which all coefficients are equal.

## Definition

<pre class="Agda"><a id="constant-tuple"></a><a id="413" href="linear-algebra.constant-tuples.html#413" class="Function">constant-tuple</a> <a id="428" class="Symbol">:</a> <a id="430" class="Symbol">{</a><a id="431" href="linear-algebra.constant-tuples.html#431" class="Bound">l</a> <a id="433" class="Symbol">:</a> <a id="435" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="440" class="Symbol">}</a> <a id="442" class="Symbol">{</a><a id="443" href="linear-algebra.constant-tuples.html#443" class="Bound">A</a> <a id="445" class="Symbol">:</a> <a id="447" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="450" href="linear-algebra.constant-tuples.html#431" class="Bound">l</a><a id="451" class="Symbol">}</a> <a id="453" class="Symbol">{</a><a id="454" href="linear-algebra.constant-tuples.html#454" class="Bound">n</a> <a id="456" class="Symbol">:</a> <a id="458" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="459" class="Symbol">}</a> <a id="461" class="Symbol">→</a> <a id="463" href="linear-algebra.constant-tuples.html#443" class="Bound">A</a> <a id="465" class="Symbol">→</a> <a id="467" href="lists.tuples.html#1342" class="Datatype">tuple</a> <a id="473" href="linear-algebra.constant-tuples.html#443" class="Bound">A</a> <a id="475" href="linear-algebra.constant-tuples.html#454" class="Bound">n</a>
<a id="477" href="linear-algebra.constant-tuples.html#413" class="Function">constant-tuple</a> <a id="492" class="Symbol">{</a><a id="493" class="Argument">n</a> <a id="495" class="Symbol">=</a> <a id="497" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="503" class="Symbol">}</a> <a id="505" class="Symbol">_</a> <a id="507" class="Symbol">=</a> <a id="509" href="lists.tuples.html#1390" class="InductiveConstructor">empty-tuple</a>
<a id="521" href="linear-algebra.constant-tuples.html#413" class="Function">constant-tuple</a> <a id="536" class="Symbol">{</a><a id="537" class="Argument">n</a> <a id="539" class="Symbol">=</a> <a id="541" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="548" href="linear-algebra.constant-tuples.html#548" class="Bound">n</a><a id="549" class="Symbol">}</a> <a id="551" href="linear-algebra.constant-tuples.html#551" class="Bound">x</a> <a id="553" class="Symbol">=</a> <a id="555" href="linear-algebra.constant-tuples.html#551" class="Bound">x</a> <a id="557" href="lists.tuples.html#1421" class="InductiveConstructor Operator">∷</a> <a id="559" class="Symbol">(</a><a id="560" href="linear-algebra.constant-tuples.html#413" class="Function">constant-tuple</a> <a id="575" href="linear-algebra.constant-tuples.html#551" class="Bound">x</a><a id="576" class="Symbol">)</a>
</pre>