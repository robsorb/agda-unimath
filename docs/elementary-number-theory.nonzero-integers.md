# Nonzero integers

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="elementary-number-theory.nonzero-integers.html" class="Module">elementary-number-theory.nonzero-integers</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="234" class="Keyword">open</a> <a id="239" class="Keyword">import</a> <a id="246" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="423" class="Keyword">open</a> <a id="428" class="Keyword">import</a> <a id="435" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="455" class="Keyword">open</a> <a id="460" class="Keyword">import</a> <a id="467" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An [integer](elementary-number-theory.integers.md) `k` is said to be **nonzero**
if the [proposition](foundation.propositions.md)

```text
  k ≠ 0
```

holds.

## Definition

### The predicate of being a nonzero integer

<pre class="Agda"><a id="is-nonzero-prop-ℤ"></a><a id="749" href="elementary-number-theory.nonzero-integers.html#749" class="Function">is-nonzero-prop-ℤ</a> <a id="767" class="Symbol">:</a> <a id="769" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a> <a id="771" class="Symbol">→</a> <a id="773" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="778" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="784" href="elementary-number-theory.nonzero-integers.html#749" class="Function">is-nonzero-prop-ℤ</a> <a id="802" href="elementary-number-theory.nonzero-integers.html#802" class="Bound">k</a> <a id="804" class="Symbol">=</a> <a id="806" href="foundation.negation.html#897" class="Function">neg-type-Prop</a> <a id="820" class="Symbol">(</a><a id="821" href="elementary-number-theory.nonzero-integers.html#802" class="Bound">k</a> <a id="823" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="825" href="elementary-number-theory.integers.html#1569" class="Function">zero-ℤ</a><a id="831" class="Symbol">)</a>

<a id="is-nonzero-ℤ"></a><a id="834" href="elementary-number-theory.nonzero-integers.html#834" class="Function">is-nonzero-ℤ</a> <a id="847" class="Symbol">:</a> <a id="849" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a> <a id="851" class="Symbol">→</a> <a id="853" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="856" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="862" href="elementary-number-theory.nonzero-integers.html#834" class="Function">is-nonzero-ℤ</a> <a id="875" href="elementary-number-theory.nonzero-integers.html#875" class="Bound">k</a> <a id="877" class="Symbol">=</a> <a id="879" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="889" class="Symbol">(</a><a id="890" href="elementary-number-theory.nonzero-integers.html#749" class="Function">is-nonzero-prop-ℤ</a> <a id="908" href="elementary-number-theory.nonzero-integers.html#875" class="Bound">k</a><a id="909" class="Symbol">)</a>

<a id="is-prop-is-nonzero-ℤ"></a><a id="912" href="elementary-number-theory.nonzero-integers.html#912" class="Function">is-prop-is-nonzero-ℤ</a> <a id="933" class="Symbol">:</a> <a id="935" class="Symbol">(</a><a id="936" href="elementary-number-theory.nonzero-integers.html#936" class="Bound">k</a> <a id="938" class="Symbol">:</a> <a id="940" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a><a id="941" class="Symbol">)</a> <a id="943" class="Symbol">→</a> <a id="945" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="953" class="Symbol">(</a><a id="954" href="elementary-number-theory.nonzero-integers.html#834" class="Function">is-nonzero-ℤ</a> <a id="967" href="elementary-number-theory.nonzero-integers.html#936" class="Bound">k</a><a id="968" class="Symbol">)</a>
<a id="970" href="elementary-number-theory.nonzero-integers.html#912" class="Function">is-prop-is-nonzero-ℤ</a> <a id="991" href="elementary-number-theory.nonzero-integers.html#991" class="Bound">k</a> <a id="993" class="Symbol">=</a> <a id="995" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1013" class="Symbol">(</a><a id="1014" href="elementary-number-theory.nonzero-integers.html#749" class="Function">is-nonzero-prop-ℤ</a> <a id="1032" href="elementary-number-theory.nonzero-integers.html#991" class="Bound">k</a><a id="1033" class="Symbol">)</a>
</pre>
### The nonzero integers

<pre class="Agda"><a id="nonzero-ℤ"></a><a id="1074" href="elementary-number-theory.nonzero-integers.html#1074" class="Function">nonzero-ℤ</a> <a id="1084" class="Symbol">:</a> <a id="1086" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1089" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1095" href="elementary-number-theory.nonzero-integers.html#1074" class="Function">nonzero-ℤ</a> <a id="1105" class="Symbol">=</a> <a id="1107" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="1120" href="elementary-number-theory.nonzero-integers.html#749" class="Function">is-nonzero-prop-ℤ</a>

<a id="1139" class="Keyword">module</a> <a id="1146" href="elementary-number-theory.nonzero-integers.html#1146" class="Module">_</a>
  <a id="1150" class="Symbol">(</a><a id="1151" href="elementary-number-theory.nonzero-integers.html#1151" class="Bound">k</a> <a id="1153" class="Symbol">:</a> <a id="1155" href="elementary-number-theory.nonzero-integers.html#1074" class="Function">nonzero-ℤ</a><a id="1164" class="Symbol">)</a>
  <a id="1168" class="Keyword">where</a>

  <a id="1177" href="elementary-number-theory.nonzero-integers.html#1177" class="Function">int-nonzero-ℤ</a> <a id="1191" class="Symbol">:</a> <a id="1193" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a>
  <a id="1197" href="elementary-number-theory.nonzero-integers.html#1177" class="Function">int-nonzero-ℤ</a> <a id="1211" class="Symbol">=</a> <a id="1213" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1217" href="elementary-number-theory.nonzero-integers.html#1151" class="Bound">k</a>

  <a id="1222" href="elementary-number-theory.nonzero-integers.html#1222" class="Function">is-nonzero-nonzero-ℤ</a> <a id="1243" class="Symbol">:</a> <a id="1245" href="elementary-number-theory.nonzero-integers.html#834" class="Function">is-nonzero-ℤ</a> <a id="1258" href="elementary-number-theory.nonzero-integers.html#1177" class="Function">int-nonzero-ℤ</a>
  <a id="1274" href="elementary-number-theory.nonzero-integers.html#1222" class="Function">is-nonzero-nonzero-ℤ</a> <a id="1295" class="Symbol">=</a> <a id="1297" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1301" href="elementary-number-theory.nonzero-integers.html#1151" class="Bound">k</a>
</pre>
### The nonzero integer `1`

<pre class="Agda"><a id="is-nonzero-one-ℤ"></a><a id="1345" href="elementary-number-theory.nonzero-integers.html#1345" class="Function">is-nonzero-one-ℤ</a> <a id="1362" class="Symbol">:</a> <a id="1364" href="elementary-number-theory.nonzero-integers.html#834" class="Function">is-nonzero-ℤ</a> <a id="1377" href="elementary-number-theory.integers.html#1852" class="Function">one-ℤ</a>
<a id="1383" href="elementary-number-theory.nonzero-integers.html#1345" class="Function">is-nonzero-one-ℤ</a> <a id="1400" class="Symbol">()</a>

<a id="one-nonzero-ℤ"></a><a id="1404" href="elementary-number-theory.nonzero-integers.html#1404" class="Function">one-nonzero-ℤ</a> <a id="1418" class="Symbol">:</a> <a id="1420" href="elementary-number-theory.nonzero-integers.html#1074" class="Function">nonzero-ℤ</a>
<a id="1430" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1434" href="elementary-number-theory.nonzero-integers.html#1404" class="Function">one-nonzero-ℤ</a> <a id="1448" class="Symbol">=</a> <a id="1450" href="elementary-number-theory.integers.html#1852" class="Function">one-ℤ</a>
<a id="1456" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1460" href="elementary-number-theory.nonzero-integers.html#1404" class="Function">one-nonzero-ℤ</a> <a id="1474" class="Symbol">=</a> <a id="1476" href="elementary-number-theory.nonzero-integers.html#1345" class="Function">is-nonzero-one-ℤ</a>
</pre>
## Properties

### The integer image of a nonzero natural number is nonzero

<pre class="Agda"><a id="is-nonzero-int-ℕ"></a><a id="1583" href="elementary-number-theory.nonzero-integers.html#1583" class="Function">is-nonzero-int-ℕ</a> <a id="1600" class="Symbol">:</a> <a id="1602" class="Symbol">(</a><a id="1603" href="elementary-number-theory.nonzero-integers.html#1603" class="Bound">n</a> <a id="1605" class="Symbol">:</a> <a id="1607" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1608" class="Symbol">)</a> <a id="1610" class="Symbol">→</a> <a id="1612" href="elementary-number-theory.natural-numbers.html#1482" class="Function">is-nonzero-ℕ</a> <a id="1625" href="elementary-number-theory.nonzero-integers.html#1603" class="Bound">n</a> <a id="1627" class="Symbol">→</a> <a id="1629" href="elementary-number-theory.nonzero-integers.html#834" class="Function">is-nonzero-ℤ</a> <a id="1642" class="Symbol">(</a><a id="1643" href="elementary-number-theory.integers.html#1987" class="Function">int-ℕ</a> <a id="1649" href="elementary-number-theory.nonzero-integers.html#1603" class="Bound">n</a><a id="1650" class="Symbol">)</a>
<a id="1652" href="elementary-number-theory.nonzero-integers.html#1583" class="Function">is-nonzero-int-ℕ</a> <a id="1669" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1676" href="elementary-number-theory.nonzero-integers.html#1676" class="Bound">H</a> <a id="1678" href="elementary-number-theory.nonzero-integers.html#1678" class="Bound">p</a> <a id="1680" class="Symbol">=</a> <a id="1682" href="elementary-number-theory.nonzero-integers.html#1676" class="Bound">H</a> <a id="1684" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### The negative of a nonzero integer is nonzero

<pre class="Agda"><a id="is-nonzero-neg-nonzero-ℤ"></a><a id="1752" href="elementary-number-theory.nonzero-integers.html#1752" class="Function">is-nonzero-neg-nonzero-ℤ</a> <a id="1777" class="Symbol">:</a> <a id="1779" class="Symbol">(</a><a id="1780" href="elementary-number-theory.nonzero-integers.html#1780" class="Bound">x</a> <a id="1782" class="Symbol">:</a> <a id="1784" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a><a id="1785" class="Symbol">)</a> <a id="1787" class="Symbol">→</a> <a id="1789" href="elementary-number-theory.nonzero-integers.html#834" class="Function">is-nonzero-ℤ</a> <a id="1802" href="elementary-number-theory.nonzero-integers.html#1780" class="Bound">x</a> <a id="1804" class="Symbol">→</a> <a id="1806" href="elementary-number-theory.nonzero-integers.html#834" class="Function">is-nonzero-ℤ</a> <a id="1819" class="Symbol">(</a><a id="1820" href="elementary-number-theory.integers.html#3345" class="Function">neg-ℤ</a> <a id="1826" href="elementary-number-theory.nonzero-integers.html#1780" class="Bound">x</a><a id="1827" class="Symbol">)</a>
<a id="1829" href="elementary-number-theory.nonzero-integers.html#1752" class="Function">is-nonzero-neg-nonzero-ℤ</a> <a id="1854" href="elementary-number-theory.nonzero-integers.html#1854" class="Bound">x</a> <a id="1856" href="elementary-number-theory.nonzero-integers.html#1856" class="Bound">H</a> <a id="1858" href="elementary-number-theory.nonzero-integers.html#1858" class="Bound">K</a> <a id="1860" class="Symbol">=</a> <a id="1862" href="elementary-number-theory.nonzero-integers.html#1856" class="Bound">H</a> <a id="1864" class="Symbol">(</a><a id="1865" href="elementary-number-theory.integers.html#7108" class="Function">is-zero-is-zero-neg-ℤ</a> <a id="1887" href="elementary-number-theory.nonzero-integers.html#1854" class="Bound">x</a> <a id="1889" href="elementary-number-theory.nonzero-integers.html#1858" class="Bound">K</a><a id="1890" class="Symbol">)</a>
</pre>