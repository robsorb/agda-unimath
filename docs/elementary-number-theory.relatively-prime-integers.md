# Relatively prime integers

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="elementary-number-theory.relatively-prime-integers.html" class="Module">elementary-number-theory.relatively-prime-integers</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="elementary-number-theory.absolute-value-integers.html" class="Module">elementary-number-theory.absolute-value-integers</a>
<a id="213" class="Keyword">open</a> <a id="218" class="Keyword">import</a> <a id="225" href="elementary-number-theory.greatest-common-divisor-integers.html" class="Module">elementary-number-theory.greatest-common-divisor-integers</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="elementary-number-theory.relatively-prime-natural-numbers.html" class="Module">elementary-number-theory.relatively-prime-natural-numbers</a>

<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="459" class="Keyword">open</a> <a id="464" class="Keyword">import</a> <a id="471" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Two integers are said to be relatively prime if their greatest common divisor
is 1.

## Definition

<pre class="Agda"><a id="is-relative-prime-ℤ"></a><a id="668" href="elementary-number-theory.relatively-prime-integers.html#668" class="Function">is-relative-prime-ℤ</a> <a id="688" class="Symbol">:</a> <a id="690" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a> <a id="692" class="Symbol">→</a> <a id="694" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a> <a id="696" class="Symbol">→</a> <a id="698" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="701" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="707" href="elementary-number-theory.relatively-prime-integers.html#668" class="Function">is-relative-prime-ℤ</a> <a id="727" href="elementary-number-theory.relatively-prime-integers.html#727" class="Bound">x</a> <a id="729" href="elementary-number-theory.relatively-prime-integers.html#729" class="Bound">y</a> <a id="731" class="Symbol">=</a> <a id="733" href="elementary-number-theory.integers.html#1887" class="Function">is-one-ℤ</a> <a id="742" class="Symbol">(</a><a id="743" href="elementary-number-theory.greatest-common-divisor-integers.html#1741" class="Function">gcd-ℤ</a> <a id="749" href="elementary-number-theory.relatively-prime-integers.html#727" class="Bound">x</a> <a id="751" href="elementary-number-theory.relatively-prime-integers.html#729" class="Bound">y</a><a id="752" class="Symbol">)</a>
</pre>
## Properties

### Being relatively prime is a proposition

<pre class="Agda"><a id="is-prop-is-relative-prime-ℤ"></a><a id="827" href="elementary-number-theory.relatively-prime-integers.html#827" class="Function">is-prop-is-relative-prime-ℤ</a> <a id="855" class="Symbol">:</a> <a id="857" class="Symbol">(</a><a id="858" href="elementary-number-theory.relatively-prime-integers.html#858" class="Bound">x</a> <a id="860" href="elementary-number-theory.relatively-prime-integers.html#860" class="Bound">y</a> <a id="862" class="Symbol">:</a> <a id="864" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a><a id="865" class="Symbol">)</a> <a id="867" class="Symbol">→</a> <a id="869" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="877" class="Symbol">(</a><a id="878" href="elementary-number-theory.relatively-prime-integers.html#668" class="Function">is-relative-prime-ℤ</a> <a id="898" href="elementary-number-theory.relatively-prime-integers.html#858" class="Bound">x</a> <a id="900" href="elementary-number-theory.relatively-prime-integers.html#860" class="Bound">y</a><a id="901" class="Symbol">)</a>
<a id="903" href="elementary-number-theory.relatively-prime-integers.html#827" class="Function">is-prop-is-relative-prime-ℤ</a> <a id="931" href="elementary-number-theory.relatively-prime-integers.html#931" class="Bound">x</a> <a id="933" href="elementary-number-theory.relatively-prime-integers.html#933" class="Bound">y</a> <a id="935" class="Symbol">=</a> <a id="937" href="elementary-number-theory.integers.html#3529" class="Function">is-set-ℤ</a> <a id="946" class="Symbol">(</a><a id="947" href="elementary-number-theory.greatest-common-divisor-integers.html#1741" class="Function">gcd-ℤ</a> <a id="953" href="elementary-number-theory.relatively-prime-integers.html#931" class="Bound">x</a> <a id="955" href="elementary-number-theory.relatively-prime-integers.html#933" class="Bound">y</a><a id="956" class="Symbol">)</a> <a id="958" href="elementary-number-theory.integers.html#1852" class="Function">one-ℤ</a>
</pre>
### Two integers are relatively prime if and only if their absolute values are relatively prime natural numbers

<pre class="Agda"><a id="is-relatively-prime-abs-is-relatively-prime-ℤ"></a><a id="1090" href="elementary-number-theory.relatively-prime-integers.html#1090" class="Function">is-relatively-prime-abs-is-relatively-prime-ℤ</a> <a id="1136" class="Symbol">:</a>
  <a id="1140" class="Symbol">{</a><a id="1141" href="elementary-number-theory.relatively-prime-integers.html#1141" class="Bound">a</a> <a id="1143" href="elementary-number-theory.relatively-prime-integers.html#1143" class="Bound">b</a> <a id="1145" class="Symbol">:</a> <a id="1147" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a><a id="1148" class="Symbol">}</a> <a id="1150" class="Symbol">→</a> <a id="1152" href="elementary-number-theory.relatively-prime-integers.html#668" class="Function">is-relative-prime-ℤ</a> <a id="1172" href="elementary-number-theory.relatively-prime-integers.html#1141" class="Bound">a</a> <a id="1174" href="elementary-number-theory.relatively-prime-integers.html#1143" class="Bound">b</a> <a id="1176" class="Symbol">→</a>
  <a id="1180" href="elementary-number-theory.relatively-prime-natural-numbers.html#1030" class="Function">is-relatively-prime-ℕ</a> <a id="1202" class="Symbol">(</a><a id="1203" href="elementary-number-theory.absolute-value-integers.html#1126" class="Function">abs-ℤ</a> <a id="1209" href="elementary-number-theory.relatively-prime-integers.html#1141" class="Bound">a</a><a id="1210" class="Symbol">)</a> <a id="1212" class="Symbol">(</a><a id="1213" href="elementary-number-theory.absolute-value-integers.html#1126" class="Function">abs-ℤ</a> <a id="1219" href="elementary-number-theory.relatively-prime-integers.html#1143" class="Bound">b</a><a id="1220" class="Symbol">)</a>
<a id="1222" href="elementary-number-theory.relatively-prime-integers.html#1090" class="Function">is-relatively-prime-abs-is-relatively-prime-ℤ</a> <a id="1268" class="Symbol">{</a><a id="1269" href="elementary-number-theory.relatively-prime-integers.html#1269" class="Bound">a</a><a id="1270" class="Symbol">}</a> <a id="1272" class="Symbol">{</a><a id="1273" href="elementary-number-theory.relatively-prime-integers.html#1273" class="Bound">b</a><a id="1274" class="Symbol">}</a> <a id="1276" href="elementary-number-theory.relatively-prime-integers.html#1276" class="Bound">H</a> <a id="1278" class="Symbol">=</a> <a id="1280" href="elementary-number-theory.integers.html#2054" class="Function">is-injective-int-ℕ</a> <a id="1299" href="elementary-number-theory.relatively-prime-integers.html#1276" class="Bound">H</a>

<a id="is-relatively-prime-is-relatively-prime-abs-ℤ"></a><a id="1302" href="elementary-number-theory.relatively-prime-integers.html#1302" class="Function">is-relatively-prime-is-relatively-prime-abs-ℤ</a> <a id="1348" class="Symbol">:</a>
  <a id="1352" class="Symbol">{</a><a id="1353" href="elementary-number-theory.relatively-prime-integers.html#1353" class="Bound">a</a> <a id="1355" href="elementary-number-theory.relatively-prime-integers.html#1355" class="Bound">b</a> <a id="1357" class="Symbol">:</a> <a id="1359" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a><a id="1360" class="Symbol">}</a> <a id="1362" class="Symbol">→</a> <a id="1364" href="elementary-number-theory.relatively-prime-natural-numbers.html#1030" class="Function">is-relatively-prime-ℕ</a> <a id="1386" class="Symbol">(</a><a id="1387" href="elementary-number-theory.absolute-value-integers.html#1126" class="Function">abs-ℤ</a> <a id="1393" href="elementary-number-theory.relatively-prime-integers.html#1353" class="Bound">a</a><a id="1394" class="Symbol">)</a> <a id="1396" class="Symbol">(</a><a id="1397" href="elementary-number-theory.absolute-value-integers.html#1126" class="Function">abs-ℤ</a> <a id="1403" href="elementary-number-theory.relatively-prime-integers.html#1355" class="Bound">b</a><a id="1404" class="Symbol">)</a> <a id="1406" class="Symbol">→</a>
  <a id="1410" href="elementary-number-theory.relatively-prime-integers.html#668" class="Function">is-relative-prime-ℤ</a> <a id="1430" href="elementary-number-theory.relatively-prime-integers.html#1353" class="Bound">a</a> <a id="1432" href="elementary-number-theory.relatively-prime-integers.html#1355" class="Bound">b</a>
<a id="1434" href="elementary-number-theory.relatively-prime-integers.html#1302" class="Function">is-relatively-prime-is-relatively-prime-abs-ℤ</a> <a id="1480" class="Symbol">{</a><a id="1481" href="elementary-number-theory.relatively-prime-integers.html#1481" class="Bound">a</a><a id="1482" class="Symbol">}</a> <a id="1484" class="Symbol">{</a><a id="1485" href="elementary-number-theory.relatively-prime-integers.html#1485" class="Bound">b</a><a id="1486" class="Symbol">}</a> <a id="1488" href="elementary-number-theory.relatively-prime-integers.html#1488" class="Bound">H</a> <a id="1490" class="Symbol">=</a> <a id="1492" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="1495" href="elementary-number-theory.integers.html#1987" class="Function">int-ℕ</a> <a id="1501" href="elementary-number-theory.relatively-prime-integers.html#1488" class="Bound">H</a>
</pre>
### For any two integers `a` and `b` that are not both `0`, the integers `a/gcd(a,b)` and `b/gcd(a,b)` are relatively prime

<pre class="Agda"><a id="1641" class="Comment">{-
relatively-prime-quotient-div-ℤ :
  {a b : ℤ} → (is-nonzero-ℤ a + is-nonzero-ℤ b) →
  is-relative-prime-ℤ
    ( quotient-div-ℤ (gcd-ℤ a b) a (div-left-gcd-ℤ a b))
    ( quotient-div-ℤ (gcd-ℤ a b) b (div-right-gcd-ℤ a b))
relatively-prime-quotient-div-ℤ H =
  is-relatively-prime-is-relatively-prime-abs-ℤ
    {!!}
-}</a>
</pre>