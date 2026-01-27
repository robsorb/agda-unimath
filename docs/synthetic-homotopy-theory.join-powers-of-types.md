# Join powers of types

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="synthetic-homotopy-theory.join-powers-of-types.html" class="Module">synthetic-homotopy-theory.join-powers-of-types</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.iterating-functions.html" class="Module">foundation.iterating-functions</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="synthetic-homotopy-theory.joins-of-types.html" class="Module">synthetic-homotopy-theory.joins-of-types</a>
</pre>
</details>

## Idea

The `n`-th **join power** of a type `A` is defined by taking the
[`n`-fold](foundation.iterating-functions.md)
[join](synthetic-homotopy-theory.joins-of-types.md) of `A` with itself.

## Definitions

### Join powers of types

<pre class="Agda"><a id="join-power"></a><a id="628" href="synthetic-homotopy-theory.join-powers-of-types.html#628" class="Function">join-power</a> <a id="639" class="Symbol">:</a> <a id="641" class="Symbol">{</a><a id="642" href="synthetic-homotopy-theory.join-powers-of-types.html#642" class="Bound">l1</a> <a id="645" class="Symbol">:</a> <a id="647" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="652" class="Symbol">}</a> <a id="654" class="Symbol">→</a> <a id="656" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="658" class="Symbol">→</a> <a id="660" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="663" href="synthetic-homotopy-theory.join-powers-of-types.html#642" class="Bound">l1</a> <a id="666" class="Symbol">→</a> <a id="668" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="671" href="synthetic-homotopy-theory.join-powers-of-types.html#642" class="Bound">l1</a>
<a id="674" href="synthetic-homotopy-theory.join-powers-of-types.html#628" class="Function">join-power</a> <a id="685" href="synthetic-homotopy-theory.join-powers-of-types.html#685" class="Bound">n</a> <a id="687" href="synthetic-homotopy-theory.join-powers-of-types.html#687" class="Bound">A</a> <a id="689" class="Symbol">=</a> <a id="691" href="foundation-core.iterating-functions.html#724" class="Function">iterate</a> <a id="699" href="synthetic-homotopy-theory.join-powers-of-types.html#685" class="Bound">n</a> <a id="701" class="Symbol">(</a><a id="702" href="synthetic-homotopy-theory.joins-of-types.html#1592" class="Function">join</a> <a id="707" href="synthetic-homotopy-theory.join-powers-of-types.html#687" class="Bound">A</a><a id="708" class="Symbol">)</a> <a id="710" class="Symbol">(</a><a id="711" href="foundation.empty-types.html#1140" class="Function">raise-empty</a> <a id="723" class="Symbol">_)</a>
</pre>
### Join powers of type families

<pre class="Agda"><a id="join-power-family-of-types"></a><a id="773" href="synthetic-homotopy-theory.join-powers-of-types.html#773" class="Function">join-power-family-of-types</a> <a id="800" class="Symbol">:</a>
  <a id="804" class="Symbol">{</a><a id="805" href="synthetic-homotopy-theory.join-powers-of-types.html#805" class="Bound">l1</a> <a id="808" href="synthetic-homotopy-theory.join-powers-of-types.html#808" class="Bound">l2</a> <a id="811" class="Symbol">:</a> <a id="813" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="818" class="Symbol">}</a> <a id="820" class="Symbol">→</a> <a id="822" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="824" class="Symbol">→</a> <a id="826" class="Symbol">{</a><a id="827" href="synthetic-homotopy-theory.join-powers-of-types.html#827" class="Bound">A</a> <a id="829" class="Symbol">:</a> <a id="831" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="834" href="synthetic-homotopy-theory.join-powers-of-types.html#805" class="Bound">l1</a><a id="836" class="Symbol">}</a> <a id="838" class="Symbol">→</a> <a id="840" class="Symbol">(</a><a id="841" href="synthetic-homotopy-theory.join-powers-of-types.html#827" class="Bound">A</a> <a id="843" class="Symbol">→</a> <a id="845" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="848" href="synthetic-homotopy-theory.join-powers-of-types.html#808" class="Bound">l2</a><a id="850" class="Symbol">)</a> <a id="852" class="Symbol">→</a> <a id="854" class="Symbol">(</a><a id="855" href="synthetic-homotopy-theory.join-powers-of-types.html#827" class="Bound">A</a> <a id="857" class="Symbol">→</a> <a id="859" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="862" href="synthetic-homotopy-theory.join-powers-of-types.html#808" class="Bound">l2</a><a id="864" class="Symbol">)</a>
<a id="866" href="synthetic-homotopy-theory.join-powers-of-types.html#773" class="Function">join-power-family-of-types</a> <a id="893" href="synthetic-homotopy-theory.join-powers-of-types.html#893" class="Bound">n</a> <a id="895" href="synthetic-homotopy-theory.join-powers-of-types.html#895" class="Bound">B</a> <a id="897" href="synthetic-homotopy-theory.join-powers-of-types.html#897" class="Bound">a</a> <a id="899" class="Symbol">=</a> <a id="901" href="synthetic-homotopy-theory.join-powers-of-types.html#628" class="Function">join-power</a> <a id="912" href="synthetic-homotopy-theory.join-powers-of-types.html#893" class="Bound">n</a> <a id="914" class="Symbol">(</a><a id="915" href="synthetic-homotopy-theory.join-powers-of-types.html#895" class="Bound">B</a> <a id="917" href="synthetic-homotopy-theory.join-powers-of-types.html#897" class="Bound">a</a><a id="918" class="Symbol">)</a>
</pre>