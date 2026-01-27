# The multiplicative monoid of rational numbers

<pre class="Agda"><a id="58" class="Symbol">{-#</a> <a id="62" class="Keyword">OPTIONS</a> <a id="70" class="Pragma">--lossy-unification</a> <a id="90" class="Symbol">#-}</a>

<a id="95" class="Keyword">module</a> <a id="102" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html" class="Module">elementary-number-theory.multiplicative-monoid-of-rational-numbers</a> <a id="169" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="elementary-number-theory.multiplication-rational-numbers.html" class="Module">elementary-number-theory.multiplication-rational-numbers</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>

<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="foundation.unital-binary-operations.html" class="Module">foundation.unital-binary-operations</a>
<a id="441" class="Keyword">open</a> <a id="446" class="Keyword">import</a> <a id="453" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="481" class="Keyword">open</a> <a id="486" class="Keyword">import</a> <a id="493" href="group-theory.commutative-monoids.html" class="Module">group-theory.commutative-monoids</a>
<a id="526" class="Keyword">open</a> <a id="531" class="Keyword">import</a> <a id="538" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
<a id="559" class="Keyword">open</a> <a id="564" class="Keyword">import</a> <a id="571" href="group-theory.semigroups.html" class="Module">group-theory.semigroups</a>
</pre>
</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with
[multiplication](elementary-number-theory.addition-rational-numbers.md) is a
[commutative monoid](group-theory.commutative-monoids.md) with unit `one-ℚ`.

## Definitions

### The multiplicative monoid of rational numbers

<pre class="Agda"><a id="semigroup-mul-ℚ"></a><a id="942" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#942" class="Function">semigroup-mul-ℚ</a> <a id="958" class="Symbol">:</a> <a id="960" href="group-theory.semigroups.html#878" class="Function">Semigroup</a> <a id="970" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="976" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="980" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#942" class="Function">semigroup-mul-ℚ</a> <a id="996" class="Symbol">=</a> <a id="998" href="elementary-number-theory.rational-numbers.html#4762" class="Function">ℚ-Set</a>
<a id="1004" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1008" class="Symbol">(</a><a id="1009" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1013" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#942" class="Function">semigroup-mul-ℚ</a><a id="1028" class="Symbol">)</a> <a id="1030" class="Symbol">=</a> <a id="1032" href="elementary-number-theory.multiplication-rational-numbers.html#1667" class="Function">mul-ℚ</a>
<a id="1038" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1042" class="Symbol">(</a><a id="1043" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1047" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#942" class="Function">semigroup-mul-ℚ</a><a id="1062" class="Symbol">)</a> <a id="1064" class="Symbol">=</a> <a id="1066" href="elementary-number-theory.multiplication-rational-numbers.html#5550" class="Function">associative-mul-ℚ</a>

<a id="is-unital-mul-ℚ"></a><a id="1085" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1085" class="Function">is-unital-mul-ℚ</a> <a id="1101" class="Symbol">:</a> <a id="1103" href="foundation.unital-binary-operations.html#1413" class="Function">is-unital</a> <a id="1113" href="elementary-number-theory.multiplication-rational-numbers.html#1667" class="Function">mul-ℚ</a>
<a id="1119" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1123" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1085" class="Function">is-unital-mul-ℚ</a> <a id="1139" class="Symbol">=</a> <a id="1141" href="elementary-number-theory.rational-numbers.html#3674" class="Function">one-ℚ</a>
<a id="1147" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1151" class="Symbol">(</a><a id="1152" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1156" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1085" class="Function">is-unital-mul-ℚ</a><a id="1171" class="Symbol">)</a> <a id="1173" class="Symbol">=</a> <a id="1175" href="elementary-number-theory.multiplication-rational-numbers.html#3936" class="Function">left-unit-law-mul-ℚ</a>
<a id="1195" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1199" class="Symbol">(</a><a id="1200" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1204" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1085" class="Function">is-unital-mul-ℚ</a><a id="1219" class="Symbol">)</a> <a id="1221" class="Symbol">=</a> <a id="1223" href="elementary-number-theory.multiplication-rational-numbers.html#4213" class="Function">right-unit-law-mul-ℚ</a>

<a id="monoid-mul-ℚ"></a><a id="1245" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1245" class="Function">monoid-mul-ℚ</a> <a id="1258" class="Symbol">:</a> <a id="1260" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="1267" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1273" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1277" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1245" class="Function">monoid-mul-ℚ</a> <a id="1290" class="Symbol">=</a> <a id="1292" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#942" class="Function">semigroup-mul-ℚ</a>
<a id="1308" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1312" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1245" class="Function">monoid-mul-ℚ</a> <a id="1325" class="Symbol">=</a> <a id="1327" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1085" class="Function">is-unital-mul-ℚ</a>
</pre>
## Properties

### The multiplicative monoid of rational numbers is commutative

<pre class="Agda"><a id="commutative-monoid-mul-ℚ"></a><a id="1437" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1437" class="Function">commutative-monoid-mul-ℚ</a> <a id="1462" class="Symbol">:</a> <a id="1464" href="group-theory.commutative-monoids.html#1458" class="Function">Commutative-Monoid</a> <a id="1483" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1489" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1493" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1437" class="Function">commutative-monoid-mul-ℚ</a> <a id="1518" class="Symbol">=</a> <a id="1520" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1245" class="Function">monoid-mul-ℚ</a>
<a id="1533" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1537" href="elementary-number-theory.multiplicative-monoid-of-rational-numbers.html#1437" class="Function">commutative-monoid-mul-ℚ</a> <a id="1562" class="Symbol">=</a> <a id="1564" href="elementary-number-theory.multiplication-rational-numbers.html#7012" class="Function">commutative-mul-ℚ</a>
</pre>