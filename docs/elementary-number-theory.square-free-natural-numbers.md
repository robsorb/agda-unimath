# Square-free natural numbers

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="elementary-number-theory.square-free-natural-numbers.html" class="Module">elementary-number-theory.square-free-natural-numbers</a> <a id="100" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="elementary-number-theory.squares-natural-numbers.html" class="Module">elementary-number-theory.squares-natural-numbers</a>

<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A natural number `n` is said to be square-free if `x² | n ⇒ x = 1` for any
natural number `x`.

## Definition

<pre class="Agda"><a id="is-square-free-ℕ"></a><a id="521" href="elementary-number-theory.square-free-natural-numbers.html#521" class="Function">is-square-free-ℕ</a> <a id="538" class="Symbol">:</a> <a id="540" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="542" class="Symbol">→</a> <a id="544" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="547" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="553" href="elementary-number-theory.square-free-natural-numbers.html#521" class="Function">is-square-free-ℕ</a> <a id="570" href="elementary-number-theory.square-free-natural-numbers.html#570" class="Bound">n</a> <a id="572" class="Symbol">=</a> <a id="574" class="Symbol">(</a><a id="575" href="elementary-number-theory.square-free-natural-numbers.html#575" class="Bound">x</a> <a id="577" class="Symbol">:</a> <a id="579" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="580" class="Symbol">)</a> <a id="582" class="Symbol">→</a> <a id="584" href="elementary-number-theory.divisibility-natural-numbers.html#1683" class="Function">div-ℕ</a> <a id="590" class="Symbol">(</a><a id="591" href="elementary-number-theory.squares-natural-numbers.html#1250" class="Function">square-ℕ</a> <a id="600" href="elementary-number-theory.square-free-natural-numbers.html#575" class="Bound">x</a><a id="601" class="Symbol">)</a> <a id="603" href="elementary-number-theory.square-free-natural-numbers.html#570" class="Bound">n</a> <a id="605" class="Symbol">→</a> <a id="607" href="elementary-number-theory.natural-numbers.html#1544" class="Function">is-one-ℕ</a> <a id="616" href="elementary-number-theory.square-free-natural-numbers.html#575" class="Bound">x</a>
</pre>