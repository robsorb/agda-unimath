# Boolean rings

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="commutative-algebra.boolean-rings.html" class="Module">commutative-algebra.boolean-rings</a> <a id="67" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="123" class="Keyword">open</a> <a id="128" class="Keyword">import</a> <a id="135" href="commutative-algebra.commutative-rings.html" class="Module">commutative-algebra.commutative-rings</a>

<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="ring-theory.idempotent-elements-rings.html" class="Module">ring-theory.idempotent-elements-rings</a>
</pre>
</details>

## Idea

A **boolean ring** is a commutative ring in which every element is idempotent.

## Definition

<pre class="Agda"><a id="is-boolean-Commutative-Ring"></a><a id="437" href="commutative-algebra.boolean-rings.html#437" class="Function">is-boolean-Commutative-Ring</a> <a id="465" class="Symbol">:</a>
  <a id="469" class="Symbol">{</a><a id="470" href="commutative-algebra.boolean-rings.html#470" class="Bound">l</a> <a id="472" class="Symbol">:</a> <a id="474" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="479" class="Symbol">}</a> <a id="481" class="Symbol">(</a><a id="482" href="commutative-algebra.boolean-rings.html#482" class="Bound">A</a> <a id="484" class="Symbol">:</a> <a id="486" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="503" href="commutative-algebra.boolean-rings.html#470" class="Bound">l</a><a id="504" class="Symbol">)</a> <a id="506" class="Symbol">→</a> <a id="508" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="511" href="commutative-algebra.boolean-rings.html#470" class="Bound">l</a>
<a id="513" href="commutative-algebra.boolean-rings.html#437" class="Function">is-boolean-Commutative-Ring</a> <a id="541" href="commutative-algebra.boolean-rings.html#541" class="Bound">A</a> <a id="543" class="Symbol">=</a>
  <a id="547" class="Symbol">(</a><a id="548" href="commutative-algebra.boolean-rings.html#548" class="Bound">x</a> <a id="550" class="Symbol">:</a> <a id="552" href="commutative-algebra.commutative-rings.html#2498" class="Function">type-Commutative-Ring</a> <a id="574" href="commutative-algebra.boolean-rings.html#541" class="Bound">A</a><a id="575" class="Symbol">)</a> <a id="577" class="Symbol">→</a>
  <a id="581" href="ring-theory.idempotent-elements-rings.html#613" class="Function">is-idempotent-element-Ring</a> <a id="608" class="Symbol">(</a><a id="609" href="commutative-algebra.commutative-rings.html#2260" class="Function">ring-Commutative-Ring</a> <a id="631" href="commutative-algebra.boolean-rings.html#541" class="Bound">A</a><a id="632" class="Symbol">)</a> <a id="634" href="commutative-algebra.boolean-rings.html#548" class="Bound">x</a>

<a id="Boolean-Ring"></a><a id="637" href="commutative-algebra.boolean-rings.html#637" class="Function">Boolean-Ring</a> <a id="650" class="Symbol">:</a> <a id="652" class="Symbol">(</a><a id="653" href="commutative-algebra.boolean-rings.html#653" class="Bound">l</a> <a id="655" class="Symbol">:</a> <a id="657" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="662" class="Symbol">)</a> <a id="664" class="Symbol">→</a> <a id="666" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="669" class="Symbol">(</a><a id="670" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="675" href="commutative-algebra.boolean-rings.html#653" class="Bound">l</a><a id="676" class="Symbol">)</a>
<a id="678" href="commutative-algebra.boolean-rings.html#637" class="Function">Boolean-Ring</a> <a id="691" href="commutative-algebra.boolean-rings.html#691" class="Bound">l</a> <a id="693" class="Symbol">=</a> <a id="695" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="697" class="Symbol">(</a><a id="698" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="715" href="commutative-algebra.boolean-rings.html#691" class="Bound">l</a><a id="716" class="Symbol">)</a> <a id="718" href="commutative-algebra.boolean-rings.html#437" class="Function">is-boolean-Commutative-Ring</a>

<a id="747" class="Keyword">module</a> <a id="754" href="commutative-algebra.boolean-rings.html#754" class="Module">_</a>
  <a id="758" class="Symbol">{</a><a id="759" href="commutative-algebra.boolean-rings.html#759" class="Bound">l</a> <a id="761" class="Symbol">:</a> <a id="763" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="768" class="Symbol">}</a> <a id="770" class="Symbol">(</a><a id="771" href="commutative-algebra.boolean-rings.html#771" class="Bound">A</a> <a id="773" class="Symbol">:</a> <a id="775" href="commutative-algebra.boolean-rings.html#637" class="Function">Boolean-Ring</a> <a id="788" href="commutative-algebra.boolean-rings.html#759" class="Bound">l</a><a id="789" class="Symbol">)</a>
  <a id="793" class="Keyword">where</a>

  <a id="802" href="commutative-algebra.boolean-rings.html#802" class="Function">commutative-ring-Boolean-Ring</a> <a id="832" class="Symbol">:</a> <a id="834" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="851" href="commutative-algebra.boolean-rings.html#759" class="Bound">l</a>
  <a id="855" href="commutative-algebra.boolean-rings.html#802" class="Function">commutative-ring-Boolean-Ring</a> <a id="885" class="Symbol">=</a> <a id="887" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="891" href="commutative-algebra.boolean-rings.html#771" class="Bound">A</a>
</pre>