# Binary operations on unordered pairs of types

<pre class="Agda"><a id="58" class="Keyword">module</a> <a id="65" href="foundation.binary-operations-unordered-pairs-of-types.html" class="Module">foundation.binary-operations-unordered-pairs-of-types</a> <a id="119" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="foundation.products-unordered-pairs-of-types.html" class="Module">foundation.products-unordered-pairs-of-types</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>
</pre>
</details>

## Idea

A binary operation on an unordered pair of types A indexed by a 2-element type I
is a map `((i : I) → A i) → B`.

## Definition

<pre class="Agda"><a id="binary-operation-unordered-pair-types"></a><a id="473" href="foundation.binary-operations-unordered-pairs-of-types.html#473" class="Function">binary-operation-unordered-pair-types</a> <a id="511" class="Symbol">:</a>
  <a id="515" class="Symbol">{</a><a id="516" href="foundation.binary-operations-unordered-pairs-of-types.html#516" class="Bound">l1</a> <a id="519" href="foundation.binary-operations-unordered-pairs-of-types.html#519" class="Bound">l2</a> <a id="522" class="Symbol">:</a> <a id="524" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="529" class="Symbol">}</a> <a id="531" class="Symbol">(</a><a id="532" href="foundation.binary-operations-unordered-pairs-of-types.html#532" class="Bound">A</a> <a id="534" class="Symbol">:</a> <a id="536" href="foundation.unordered-pairs.html#2222" class="Function">unordered-pair</a> <a id="551" class="Symbol">(</a><a id="552" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="555" href="foundation.binary-operations-unordered-pairs-of-types.html#516" class="Bound">l1</a><a id="557" class="Symbol">))</a> <a id="560" class="Symbol">(</a><a id="561" href="foundation.binary-operations-unordered-pairs-of-types.html#561" class="Bound">B</a> <a id="563" class="Symbol">:</a> <a id="565" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="568" href="foundation.binary-operations-unordered-pairs-of-types.html#519" class="Bound">l2</a><a id="570" class="Symbol">)</a> <a id="572" class="Symbol">→</a> <a id="574" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="577" class="Symbol">(</a><a id="578" href="foundation.binary-operations-unordered-pairs-of-types.html#516" class="Bound">l1</a> <a id="581" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="583" href="foundation.binary-operations-unordered-pairs-of-types.html#519" class="Bound">l2</a><a id="585" class="Symbol">)</a>
<a id="587" href="foundation.binary-operations-unordered-pairs-of-types.html#473" class="Function">binary-operation-unordered-pair-types</a> <a id="625" href="foundation.binary-operations-unordered-pairs-of-types.html#625" class="Bound">A</a> <a id="627" href="foundation.binary-operations-unordered-pairs-of-types.html#627" class="Bound">B</a> <a id="629" class="Symbol">=</a> <a id="631" href="foundation.products-unordered-pairs-of-types.html#1065" class="Function">product-unordered-pair-types</a> <a id="660" href="foundation.binary-operations-unordered-pairs-of-types.html#625" class="Bound">A</a> <a id="662" class="Symbol">→</a> <a id="664" href="foundation.binary-operations-unordered-pairs-of-types.html#627" class="Bound">B</a>
</pre>