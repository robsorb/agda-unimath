# Scalar multiplication of tuples

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="linear-algebra.scalar-multiplication-tuples.html" class="Module">linear-algebra.scalar-multiplication-tuples</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="lists.functoriality-tuples.html" class="Module">lists.functoriality-tuples</a>
<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="lists.tuples.html" class="Module">lists.tuples</a>
</pre>
</details>

## Idea

Any operation `B → A → A` for some type `B` of formal scalars induces an
operation on [tuples](lists.tuples.md) `B → tuple n A → tuple n A`.

## Definition

<pre class="Agda"><a id="scalar-mul-tuple"></a><a id="500" href="linear-algebra.scalar-multiplication-tuples.html#500" class="Function">scalar-mul-tuple</a> <a id="517" class="Symbol">:</a>
  <a id="521" class="Symbol">{</a><a id="522" href="linear-algebra.scalar-multiplication-tuples.html#522" class="Bound">l1</a> <a id="525" href="linear-algebra.scalar-multiplication-tuples.html#525" class="Bound">l2</a> <a id="528" class="Symbol">:</a> <a id="530" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="535" class="Symbol">}</a> <a id="537" class="Symbol">{</a><a id="538" href="linear-algebra.scalar-multiplication-tuples.html#538" class="Bound">B</a> <a id="540" class="Symbol">:</a> <a id="542" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="545" href="linear-algebra.scalar-multiplication-tuples.html#522" class="Bound">l1</a><a id="547" class="Symbol">}</a> <a id="549" class="Symbol">{</a><a id="550" href="linear-algebra.scalar-multiplication-tuples.html#550" class="Bound">A</a> <a id="552" class="Symbol">:</a> <a id="554" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="557" href="linear-algebra.scalar-multiplication-tuples.html#525" class="Bound">l2</a><a id="559" class="Symbol">}</a> <a id="561" class="Symbol">{</a><a id="562" href="linear-algebra.scalar-multiplication-tuples.html#562" class="Bound">n</a> <a id="564" class="Symbol">:</a> <a id="566" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="567" class="Symbol">}</a> <a id="569" class="Symbol">→</a>
  <a id="573" class="Symbol">(</a><a id="574" href="linear-algebra.scalar-multiplication-tuples.html#538" class="Bound">B</a> <a id="576" class="Symbol">→</a> <a id="578" href="linear-algebra.scalar-multiplication-tuples.html#550" class="Bound">A</a> <a id="580" class="Symbol">→</a> <a id="582" href="linear-algebra.scalar-multiplication-tuples.html#550" class="Bound">A</a><a id="583" class="Symbol">)</a> <a id="585" class="Symbol">→</a> <a id="587" href="linear-algebra.scalar-multiplication-tuples.html#538" class="Bound">B</a> <a id="589" class="Symbol">→</a> <a id="591" href="lists.tuples.html#1342" class="Datatype">tuple</a> <a id="597" href="linear-algebra.scalar-multiplication-tuples.html#550" class="Bound">A</a> <a id="599" href="linear-algebra.scalar-multiplication-tuples.html#562" class="Bound">n</a> <a id="601" class="Symbol">→</a> <a id="603" href="lists.tuples.html#1342" class="Datatype">tuple</a> <a id="609" href="linear-algebra.scalar-multiplication-tuples.html#550" class="Bound">A</a> <a id="611" href="linear-algebra.scalar-multiplication-tuples.html#562" class="Bound">n</a>
<a id="613" href="linear-algebra.scalar-multiplication-tuples.html#500" class="Function">scalar-mul-tuple</a> <a id="630" href="linear-algebra.scalar-multiplication-tuples.html#630" class="Bound">μ</a> <a id="632" href="linear-algebra.scalar-multiplication-tuples.html#632" class="Bound">x</a> <a id="634" class="Symbol">=</a> <a id="636" href="lists.functoriality-tuples.html#952" class="Function">map-tuple</a> <a id="646" class="Symbol">(</a><a id="647" href="linear-algebra.scalar-multiplication-tuples.html#630" class="Bound">μ</a> <a id="649" href="linear-algebra.scalar-multiplication-tuples.html#632" class="Bound">x</a><a id="650" class="Symbol">)</a>
</pre>