# The decidable total order of rational numbers

<pre class="Agda"><a id="58" class="Keyword">module</a> <a id="65" href="elementary-number-theory.decidable-total-order-rational-numbers.html" class="Module">elementary-number-theory.decidable-total-order-rational-numbers</a> <a id="129" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="elementary-number-theory.inequality-rational-numbers.html" class="Module">elementary-number-theory.inequality-rational-numbers</a>

<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="order-theory.decidable-total-orders.html" class="Module">order-theory.decidable-total-orders</a>
<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="order-theory.total-orders.html" class="Module">order-theory.total-orders</a>
</pre>
</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
[equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-rational-numbers.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definition

<pre class="Agda"><a id="is-total-leq-ℚ"></a><a id="801" href="elementary-number-theory.decidable-total-order-rational-numbers.html#801" class="Function">is-total-leq-ℚ</a> <a id="816" class="Symbol">:</a> <a id="818" href="order-theory.total-orders.html#1901" class="Function">is-total-Poset</a> <a id="833" href="elementary-number-theory.inequality-rational-numbers.html#5448" class="Function">ℚ-Poset</a>
<a id="841" href="elementary-number-theory.decidable-total-order-rational-numbers.html#801" class="Function">is-total-leq-ℚ</a> <a id="856" href="elementary-number-theory.decidable-total-order-rational-numbers.html#856" class="Bound">x</a> <a id="858" href="elementary-number-theory.decidable-total-order-rational-numbers.html#858" class="Bound">y</a> <a id="860" class="Symbol">=</a> <a id="862" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="878" class="Symbol">(</a><a id="879" href="elementary-number-theory.inequality-rational-numbers.html#4567" class="Function">linear-leq-ℚ</a> <a id="892" href="elementary-number-theory.decidable-total-order-rational-numbers.html#856" class="Bound">x</a> <a id="894" href="elementary-number-theory.decidable-total-order-rational-numbers.html#858" class="Bound">y</a><a id="895" class="Symbol">)</a>

<a id="ℚ-Total-Order"></a><a id="898" href="elementary-number-theory.decidable-total-order-rational-numbers.html#898" class="Function">ℚ-Total-Order</a> <a id="912" class="Symbol">:</a> <a id="914" href="order-theory.total-orders.html#2153" class="Function">Total-Order</a> <a id="926" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="932" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="938" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="942" href="elementary-number-theory.decidable-total-order-rational-numbers.html#898" class="Function">ℚ-Total-Order</a> <a id="956" class="Symbol">=</a> <a id="958" href="elementary-number-theory.inequality-rational-numbers.html#5448" class="Function">ℚ-Poset</a>
<a id="966" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="970" href="elementary-number-theory.decidable-total-order-rational-numbers.html#898" class="Function">ℚ-Total-Order</a> <a id="984" class="Symbol">=</a> <a id="986" href="elementary-number-theory.decidable-total-order-rational-numbers.html#801" class="Function">is-total-leq-ℚ</a>

<a id="ℚ-Decidable-Total-Order"></a><a id="1002" href="elementary-number-theory.decidable-total-order-rational-numbers.html#1002" class="Function">ℚ-Decidable-Total-Order</a> <a id="1026" class="Symbol">:</a> <a id="1028" href="order-theory.decidable-total-orders.html#1986" class="Function">Decidable-Total-Order</a> <a id="1050" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1056" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1062" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1066" href="elementary-number-theory.decidable-total-order-rational-numbers.html#1002" class="Function">ℚ-Decidable-Total-Order</a> <a id="1090" class="Symbol">=</a> <a id="1092" href="elementary-number-theory.inequality-rational-numbers.html#5448" class="Function">ℚ-Poset</a>
<a id="1100" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1104" class="Symbol">(</a><a id="1105" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1109" href="elementary-number-theory.decidable-total-order-rational-numbers.html#1002" class="Function">ℚ-Decidable-Total-Order</a><a id="1132" class="Symbol">)</a> <a id="1134" class="Symbol">=</a> <a id="1136" href="elementary-number-theory.decidable-total-order-rational-numbers.html#801" class="Function">is-total-leq-ℚ</a>
<a id="1151" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1155" class="Symbol">(</a><a id="1156" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1160" href="elementary-number-theory.decidable-total-order-rational-numbers.html#1002" class="Function">ℚ-Decidable-Total-Order</a><a id="1183" class="Symbol">)</a> <a id="1185" class="Symbol">=</a> <a id="1187" href="elementary-number-theory.inequality-rational-numbers.html#3377" class="Function">is-decidable-leq-ℚ</a>
</pre>