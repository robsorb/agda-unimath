# Strict inequality on nonnegative rational numbers

<pre class="Agda"><a id="62" class="Keyword">module</a> <a id="69" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html" class="Module">elementary-number-theory.strict-inequality-nonnegative-rational-numbers</a> <a id="141" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="elementary-number-theory.nonnegative-rational-numbers.html" class="Module">elementary-number-theory.nonnegative-rational-numbers</a>
<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="elementary-number-theory.strict-inequality-rational-numbers.html" class="Module">elementary-number-theory.strict-inequality-rational-numbers</a>

<a id="399" class="Keyword">open</a> <a id="404" class="Keyword">import</a> <a id="411" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="479" class="Keyword">open</a> <a id="484" class="Keyword">import</a> <a id="491" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="on the nonegative rational numbers" Agda=le-ℚ⁰⁺}}
on the
[nonnegative rational numbers](elementary-number-theory.nonnegative-rational-numbers.md)
is inherited from the
[standard strict ordering](elementary-number-theory.strict-inequality-rational-numbers.md)
on [rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

<pre class="Agda"><a id="le-prop-ℚ⁰⁺"></a><a id="954" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#954" class="Function">le-prop-ℚ⁰⁺</a> <a id="966" class="Symbol">:</a> <a id="968" class="Symbol">(</a><a id="969" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#969" class="Bound">p</a> <a id="971" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#971" class="Bound">q</a> <a id="973" class="Symbol">:</a> <a id="975" href="elementary-number-theory.nonnegative-rational-numbers.html#2540" class="Function">ℚ⁰⁺</a><a id="978" class="Symbol">)</a> <a id="980" class="Symbol">→</a> <a id="982" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="987" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="993" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#954" class="Function">le-prop-ℚ⁰⁺</a> <a id="1005" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1005" class="Bound">p</a> <a id="1007" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1007" class="Bound">q</a> <a id="1009" class="Symbol">=</a> <a id="1011" href="elementary-number-theory.strict-inequality-rational-numbers.html#3077" class="Function">le-ℚ-Prop</a> <a id="1021" class="Symbol">(</a><a id="1022" href="elementary-number-theory.nonnegative-rational-numbers.html#2618" class="Function">rational-ℚ⁰⁺</a> <a id="1035" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1005" class="Bound">p</a><a id="1036" class="Symbol">)</a> <a id="1038" class="Symbol">(</a><a id="1039" href="elementary-number-theory.nonnegative-rational-numbers.html#2618" class="Function">rational-ℚ⁰⁺</a> <a id="1052" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1007" class="Bound">q</a><a id="1053" class="Symbol">)</a>

<a id="le-ℚ⁰⁺"></a><a id="1056" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1056" class="Function">le-ℚ⁰⁺</a> <a id="1063" class="Symbol">:</a> <a id="1065" class="Symbol">(</a><a id="1066" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1066" class="Bound">p</a> <a id="1068" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1068" class="Bound">q</a> <a id="1070" class="Symbol">:</a> <a id="1072" href="elementary-number-theory.nonnegative-rational-numbers.html#2540" class="Function">ℚ⁰⁺</a><a id="1075" class="Symbol">)</a> <a id="1077" class="Symbol">→</a> <a id="1079" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1082" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1088" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1056" class="Function">le-ℚ⁰⁺</a> <a id="1095" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1095" class="Bound">p</a> <a id="1097" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1097" class="Bound">q</a> <a id="1099" class="Symbol">=</a> <a id="1101" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1111" class="Symbol">(</a><a id="1112" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#954" class="Function">le-prop-ℚ⁰⁺</a> <a id="1124" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1095" class="Bound">p</a> <a id="1126" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1097" class="Bound">q</a><a id="1127" class="Symbol">)</a>
</pre>
## Properties

### Zero is less than positive rational numbers as nonnegative rational numbers

<pre class="Agda"><a id="1238" class="Keyword">abstract</a>
  <a id="le-zero-nonnegative-ℚ⁰⁺"></a><a id="1249" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1249" class="Function">le-zero-nonnegative-ℚ⁰⁺</a> <a id="1273" class="Symbol">:</a> <a id="1275" class="Symbol">(</a><a id="1276" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1276" class="Bound">q</a> <a id="1278" class="Symbol">:</a> <a id="1280" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="1282" class="Symbol">)</a> <a id="1284" class="Symbol">→</a> <a id="1286" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1056" class="Function">le-ℚ⁰⁺</a> <a id="1293" href="elementary-number-theory.nonnegative-rational-numbers.html#3466" class="Function">zero-ℚ⁰⁺</a> <a id="1302" class="Symbol">(</a><a id="1303" href="elementary-number-theory.nonnegative-rational-numbers.html#3921" class="Function">nonnegative-ℚ⁺</a> <a id="1318" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1276" class="Bound">q</a><a id="1319" class="Symbol">)</a>
  <a id="1323" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1249" class="Function">le-zero-nonnegative-ℚ⁰⁺</a> <a id="1347" class="Symbol">(</a><a id="1348" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1348" class="Bound">q</a> <a id="1350" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1352" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1352" class="Bound">pos-q</a><a id="1357" class="Symbol">)</a> <a id="1359" class="Symbol">=</a> <a id="1361" href="elementary-number-theory.positive-rational-numbers.html#7370" class="Function">le-zero-is-positive-ℚ</a> <a id="1383" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1348" class="Bound">q</a> <a id="1385" href="elementary-number-theory.strict-inequality-nonnegative-rational-numbers.html#1352" class="Bound">pos-q</a>
</pre>