# The decidable total order of integers

<pre class="Agda"><a id="50" class="Keyword">module</a> <a id="57" href="elementary-number-theory.decidable-total-order-integers.html" class="Module">elementary-number-theory.decidable-total-order-integers</a> <a id="113" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="elementary-number-theory.inequality-integers.html" class="Module">elementary-number-theory.inequality-integers</a>

<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="320" class="Keyword">open</a> <a id="325" class="Keyword">import</a> <a id="332" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="360" class="Keyword">open</a> <a id="365" class="Keyword">import</a> <a id="372" href="order-theory.decidable-total-orders.html" class="Module">order-theory.decidable-total-orders</a>
<a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="order-theory.total-orders.html" class="Module">order-theory.total-orders</a>
</pre>
</details>

## Idea

The type of [integers](elementary-number-theory.integers.md)
[equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-integers.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definition

<pre class="Agda"><a id="is-total-leq-ℤ"></a><a id="753" href="elementary-number-theory.decidable-total-order-integers.html#753" class="Function">is-total-leq-ℤ</a> <a id="768" class="Symbol">:</a> <a id="770" href="order-theory.total-orders.html#1901" class="Function">is-total-Poset</a> <a id="785" href="elementary-number-theory.inequality-integers.html#3653" class="Function">ℤ-Poset</a>
<a id="793" href="elementary-number-theory.decidable-total-order-integers.html#753" class="Function">is-total-leq-ℤ</a> <a id="808" href="elementary-number-theory.decidable-total-order-integers.html#808" class="Bound">x</a> <a id="810" href="elementary-number-theory.decidable-total-order-integers.html#810" class="Bound">y</a> <a id="812" class="Symbol">=</a> <a id="814" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="830" class="Symbol">(</a><a id="831" href="elementary-number-theory.inequality-integers.html#3789" class="Function">linear-leq-ℤ</a> <a id="844" href="elementary-number-theory.decidable-total-order-integers.html#808" class="Bound">x</a> <a id="846" href="elementary-number-theory.decidable-total-order-integers.html#810" class="Bound">y</a><a id="847" class="Symbol">)</a>

<a id="ℤ-Total-Order"></a><a id="850" href="elementary-number-theory.decidable-total-order-integers.html#850" class="Function">ℤ-Total-Order</a> <a id="864" class="Symbol">:</a> <a id="866" href="order-theory.total-orders.html#2153" class="Function">Total-Order</a> <a id="878" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="884" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="890" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="894" href="elementary-number-theory.decidable-total-order-integers.html#850" class="Function">ℤ-Total-Order</a> <a id="908" class="Symbol">=</a> <a id="910" href="elementary-number-theory.inequality-integers.html#3653" class="Function">ℤ-Poset</a>
<a id="918" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="922" href="elementary-number-theory.decidable-total-order-integers.html#850" class="Function">ℤ-Total-Order</a> <a id="936" class="Symbol">=</a> <a id="938" href="elementary-number-theory.decidable-total-order-integers.html#753" class="Function">is-total-leq-ℤ</a>

<a id="ℤ-Decidable-Total-Order"></a><a id="954" href="elementary-number-theory.decidable-total-order-integers.html#954" class="Function">ℤ-Decidable-Total-Order</a> <a id="978" class="Symbol">:</a> <a id="980" href="order-theory.decidable-total-orders.html#1986" class="Function">Decidable-Total-Order</a> <a id="1002" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1008" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1014" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1018" href="elementary-number-theory.decidable-total-order-integers.html#954" class="Function">ℤ-Decidable-Total-Order</a> <a id="1042" class="Symbol">=</a> <a id="1044" href="elementary-number-theory.inequality-integers.html#3653" class="Function">ℤ-Poset</a>
<a id="1052" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1056" class="Symbol">(</a><a id="1057" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1061" href="elementary-number-theory.decidable-total-order-integers.html#954" class="Function">ℤ-Decidable-Total-Order</a><a id="1084" class="Symbol">)</a> <a id="1086" class="Symbol">=</a> <a id="1088" href="elementary-number-theory.decidable-total-order-integers.html#753" class="Function">is-total-leq-ℤ</a>
<a id="1103" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1107" class="Symbol">(</a><a id="1108" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1112" href="elementary-number-theory.decidable-total-order-integers.html#954" class="Function">ℤ-Decidable-Total-Order</a><a id="1135" class="Symbol">)</a> <a id="1137" class="Symbol">=</a> <a id="1139" href="elementary-number-theory.inequality-integers.html#3199" class="Function">is-decidable-leq-ℤ</a>
</pre>