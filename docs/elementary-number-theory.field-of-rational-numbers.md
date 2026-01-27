# The field of rational numbers

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="elementary-number-theory.field-of-rational-numbers.html" class="Module">elementary-number-theory.field-of-rational-numbers</a> <a id="100" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="commutative-algebra.discrete-fields.html" class="Module">commutative-algebra.discrete-fields</a>

<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="elementary-number-theory.multiplicative-group-of-rational-numbers.html" class="Module">elementary-number-theory.multiplicative-group-of-rational-numbers</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="elementary-number-theory.nonzero-rational-numbers.html" class="Module">elementary-number-theory.nonzero-rational-numbers</a>
<a id="345" class="Keyword">open</a> <a id="350" class="Keyword">import</a> <a id="357" href="elementary-number-theory.ring-of-rational-numbers.html" class="Module">elementary-number-theory.ring-of-rational-numbers</a>

<a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="490" class="Keyword">open</a> <a id="495" class="Keyword">import</a> <a id="502" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>

<a id="529" class="Keyword">open</a> <a id="534" class="Keyword">import</a> <a id="541" href="ring-theory.division-rings.html" class="Module">ring-theory.division-rings</a>
</pre>
</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with [addition](elementary-number-theory.addition-rational-numbers.md)
and
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a [discrete field](commutative-algebra.discrete-fields.md), i.e., a
[commutative ring](commutative-algebra.commutative-rings.md) whose
[nonzero](elementary-number-theory.nonzero-rational-numbers.md) elements are
[invertible](ring-theory.invertible-elements-rings.md).

## Definitions

### The ring of rational numbers is a division ring

<pre class="Agda"><a id="is-division-ring-ℚ"></a><a id="1182" href="elementary-number-theory.field-of-rational-numbers.html#1182" class="Function">is-division-ring-ℚ</a> <a id="1201" class="Symbol">:</a> <a id="1203" href="ring-theory.division-rings.html#494" class="Function">is-division-Ring</a> <a id="1220" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a>
<a id="1227" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1231" href="elementary-number-theory.field-of-rational-numbers.html#1182" class="Function">is-division-ring-ℚ</a> <a id="1250" class="Symbol">=</a> <a id="1252" href="elementary-number-theory.nonzero-rational-numbers.html#2685" class="Function">is-nonzero-one-ℚ</a> <a id="1269" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1271" href="foundation-core.identity-types.html#6358" class="Function">inv</a>
<a id="1275" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1279" href="elementary-number-theory.field-of-rational-numbers.html#1182" class="Function">is-division-ring-ℚ</a> <a id="1298" href="elementary-number-theory.field-of-rational-numbers.html#1298" class="Bound">x</a> <a id="1300" href="elementary-number-theory.field-of-rational-numbers.html#1300" class="Bound">H</a> <a id="1302" class="Symbol">=</a> <a id="1304" href="elementary-number-theory.multiplicative-group-of-rational-numbers.html#3990" class="Function">is-invertible-element-ring-is-nonzero-ℚ</a> <a id="1344" href="elementary-number-theory.field-of-rational-numbers.html#1298" class="Bound">x</a> <a id="1346" class="Symbol">(</a><a id="1347" href="elementary-number-theory.field-of-rational-numbers.html#1300" class="Bound">H</a> <a id="1349" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1351" href="foundation-core.identity-types.html#6358" class="Function">inv</a><a id="1354" class="Symbol">)</a>
</pre>
### The rational numbers form a discrete field

<pre class="Agda"><a id="is-discrete-field-ℚ"></a><a id="1417" href="elementary-number-theory.field-of-rational-numbers.html#1417" class="Function">is-discrete-field-ℚ</a> <a id="1437" class="Symbol">:</a> <a id="1439" href="commutative-algebra.discrete-fields.html#446" class="Function">is-discrete-field-Commutative-Ring</a> <a id="1474" href="elementary-number-theory.ring-of-rational-numbers.html#2056" class="Function">commutative-ring-ℚ</a>
<a id="1493" href="elementary-number-theory.field-of-rational-numbers.html#1417" class="Function">is-discrete-field-ℚ</a> <a id="1513" class="Symbol">=</a> <a id="1515" href="elementary-number-theory.field-of-rational-numbers.html#1182" class="Function">is-division-ring-ℚ</a>
</pre>