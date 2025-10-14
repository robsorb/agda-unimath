# Tuples of types

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="foundation.tuples-of-types.html" class="Module">foundation.tuples-of-types</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

An `n`-tuple of types is a type family `Fin n → UU`.

## Definition

<pre class="Agda"><a id="tuple-types"></a><a id="373" href="foundation.tuples-of-types.html#373" class="Function">tuple-types</a> <a id="385" class="Symbol">:</a> <a id="387" class="Symbol">(</a><a id="388" href="foundation.tuples-of-types.html#388" class="Bound">l</a> <a id="390" class="Symbol">:</a> <a id="392" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="397" class="Symbol">)</a> <a id="399" class="Symbol">(</a><a id="400" href="foundation.tuples-of-types.html#400" class="Bound">n</a> <a id="402" class="Symbol">:</a> <a id="404" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="405" class="Symbol">)</a> <a id="407" class="Symbol">→</a> <a id="409" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="412" class="Symbol">(</a><a id="413" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="418" href="foundation.tuples-of-types.html#388" class="Bound">l</a><a id="419" class="Symbol">)</a>
<a id="421" href="foundation.tuples-of-types.html#373" class="Function">tuple-types</a> <a id="433" href="foundation.tuples-of-types.html#433" class="Bound">l</a> <a id="435" href="foundation.tuples-of-types.html#435" class="Bound">n</a> <a id="437" class="Symbol">=</a> <a id="439" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="443" href="foundation.tuples-of-types.html#435" class="Bound">n</a> <a id="445" class="Symbol">→</a> <a id="447" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="450" href="foundation.tuples-of-types.html#433" class="Bound">l</a>
</pre>
## Properties

### The tuple of types `A j` for `i ≠ j`, given `i`

<pre class="Agda"><a id="533" class="Comment">{-
tuple-types-complement-point :
  {l : Level} {n : ℕ} (A : tuple-types l (succ-ℕ n)) (i : Fin (succ-ℕ n)) →
  tuple-types l n
tuple-types-complement-point A i = {!!}
-}</a>
</pre>