# Discrete fields

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="commutative-algebra.discrete-fields.html" class="Module">commutative-algebra.discrete-fields</a> <a id="71" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="commutative-algebra.commutative-rings.html" class="Module">commutative-algebra.commutative-rings</a>

<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="ring-theory.division-rings.html" class="Module">ring-theory.division-rings</a>
</pre>
</details>

## Idea

A **discrete field** is a commutative division ring. They are called discrete,
because only nonzero elements are assumed to be invertible.

## Definition

<pre class="Agda"><a id="is-discrete-field-Commutative-Ring"></a><a id="446" href="commutative-algebra.discrete-fields.html#446" class="Function">is-discrete-field-Commutative-Ring</a> <a id="481" class="Symbol">:</a> <a id="483" class="Symbol">{</a><a id="484" href="commutative-algebra.discrete-fields.html#484" class="Bound">l</a> <a id="486" class="Symbol">:</a> <a id="488" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="493" class="Symbol">}</a> <a id="495" class="Symbol">→</a> <a id="497" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="514" href="commutative-algebra.discrete-fields.html#484" class="Bound">l</a> <a id="516" class="Symbol">→</a> <a id="518" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="521" href="commutative-algebra.discrete-fields.html#484" class="Bound">l</a>
<a id="523" href="commutative-algebra.discrete-fields.html#446" class="Function">is-discrete-field-Commutative-Ring</a> <a id="558" href="commutative-algebra.discrete-fields.html#558" class="Bound">A</a> <a id="560" class="Symbol">=</a>
  <a id="564" href="ring-theory.division-rings.html#494" class="Function">is-division-Ring</a> <a id="581" class="Symbol">(</a><a id="582" href="commutative-algebra.commutative-rings.html#2260" class="Function">ring-Commutative-Ring</a> <a id="604" href="commutative-algebra.discrete-fields.html#558" class="Bound">A</a><a id="605" class="Symbol">)</a>
</pre>