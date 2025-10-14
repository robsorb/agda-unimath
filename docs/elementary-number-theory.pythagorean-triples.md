# Pythagorean triples

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="elementary-number-theory.pythagorean-triples.html" class="Module">elementary-number-theory.pythagorean-triples</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="elementary-number-theory.squares-natural-numbers.html" class="Module">elementary-number-theory.squares-natural-numbers</a>

<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A Pythagorean triple is a triple `(a,b,c)` of natural numbers such that
`a² + b² = c²`.

## Definition

<pre class="Agda"><a id="is-pythagorean-triple"></a><a id="532" href="elementary-number-theory.pythagorean-triples.html#532" class="Function">is-pythagorean-triple</a> <a id="554" class="Symbol">:</a> <a id="556" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="558" class="Symbol">→</a> <a id="560" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="562" class="Symbol">→</a> <a id="564" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="566" class="Symbol">→</a> <a id="568" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="571" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="577" href="elementary-number-theory.pythagorean-triples.html#532" class="Function">is-pythagorean-triple</a> <a id="599" href="elementary-number-theory.pythagorean-triples.html#599" class="Bound">a</a> <a id="601" href="elementary-number-theory.pythagorean-triples.html#601" class="Bound">b</a> <a id="603" href="elementary-number-theory.pythagorean-triples.html#603" class="Bound">c</a> <a id="605" class="Symbol">=</a> <a id="607" class="Symbol">((</a><a id="609" href="elementary-number-theory.squares-natural-numbers.html#1250" class="Function">square-ℕ</a> <a id="618" href="elementary-number-theory.pythagorean-triples.html#599" class="Bound">a</a><a id="619" class="Symbol">)</a> <a id="621" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="624" class="Symbol">(</a><a id="625" href="elementary-number-theory.squares-natural-numbers.html#1250" class="Function">square-ℕ</a> <a id="634" href="elementary-number-theory.pythagorean-triples.html#601" class="Bound">b</a><a id="635" class="Symbol">)</a> <a id="637" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="639" href="elementary-number-theory.squares-natural-numbers.html#1250" class="Function">square-ℕ</a> <a id="648" href="elementary-number-theory.pythagorean-triples.html#603" class="Bound">c</a><a id="649" class="Symbol">)</a>
</pre>