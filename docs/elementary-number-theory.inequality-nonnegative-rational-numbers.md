# Inequality on the nonnegative rational numbers

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html" class="Module">elementary-number-theory.inequality-nonnegative-rational-numbers</a> <a id="131" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="elementary-number-theory.inequality-rational-numbers.html" class="Module">elementary-number-theory.inequality-rational-numbers</a>
<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="elementary-number-theory.nonnegative-rational-numbers.html" class="Module">elementary-number-theory.nonnegative-rational-numbers</a>

<a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="399" class="Keyword">open</a> <a id="404" class="Keyword">import</a> <a id="411" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="on the nonnegative rational numbers" Agda=leq-ℚ⁰⁺}}
on the
[nonnegative rational numbers](elementary-number-theory.nonnegative-rational-numbers.md)
is inherited from the
[standard ordering](elementary-number-theory.inequality-rational-numbers.md) on
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

<pre class="Agda"><a id="leq-prop-ℚ⁰⁺"></a><a id="855" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#855" class="Function">leq-prop-ℚ⁰⁺</a> <a id="868" class="Symbol">:</a> <a id="870" href="elementary-number-theory.nonnegative-rational-numbers.html#2540" class="Function">ℚ⁰⁺</a> <a id="874" class="Symbol">→</a> <a id="876" href="elementary-number-theory.nonnegative-rational-numbers.html#2540" class="Function">ℚ⁰⁺</a> <a id="880" class="Symbol">→</a> <a id="882" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="887" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="893" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#855" class="Function">leq-prop-ℚ⁰⁺</a> <a id="906" class="Symbol">(</a><a id="907" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#907" class="Bound">p</a> <a id="909" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="911" class="Symbol">_)</a> <a id="914" class="Symbol">(</a><a id="915" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#915" class="Bound">q</a> <a id="917" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="919" class="Symbol">_)</a> <a id="922" class="Symbol">=</a> <a id="924" href="elementary-number-theory.inequality-rational-numbers.html#2832" class="Function">leq-ℚ-Prop</a> <a id="935" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#907" class="Bound">p</a> <a id="937" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#915" class="Bound">q</a>

<a id="leq-ℚ⁰⁺"></a><a id="940" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#940" class="Function">leq-ℚ⁰⁺</a> <a id="948" class="Symbol">:</a> <a id="950" href="elementary-number-theory.nonnegative-rational-numbers.html#2540" class="Function">ℚ⁰⁺</a> <a id="954" class="Symbol">→</a> <a id="956" href="elementary-number-theory.nonnegative-rational-numbers.html#2540" class="Function">ℚ⁰⁺</a> <a id="960" class="Symbol">→</a> <a id="962" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="965" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="971" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#940" class="Function">leq-ℚ⁰⁺</a> <a id="979" class="Symbol">(</a><a id="980" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#980" class="Bound">p</a> <a id="982" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="984" class="Symbol">_)</a> <a id="987" class="Symbol">(</a><a id="988" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#988" class="Bound">q</a> <a id="990" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="992" class="Symbol">_)</a> <a id="995" class="Symbol">=</a> <a id="997" href="elementary-number-theory.inequality-rational-numbers.html#2922" class="Function">leq-ℚ</a> <a id="1003" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#980" class="Bound">p</a> <a id="1005" href="elementary-number-theory.inequality-nonnegative-rational-numbers.html#988" class="Bound">q</a>
</pre>