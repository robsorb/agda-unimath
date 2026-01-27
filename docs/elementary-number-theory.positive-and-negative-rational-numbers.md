# The positive, negative, and nonnegative rational numbers

<pre class="Agda"><a id="69" class="Keyword">module</a> <a id="76" href="elementary-number-theory.positive-and-negative-rational-numbers.html" class="Module">elementary-number-theory.positive-and-negative-rational-numbers</a> <a id="140" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="elementary-number-theory.inequality-rational-numbers.html" class="Module">elementary-number-theory.inequality-rational-numbers</a>
<a id="261" class="Keyword">open</a> <a id="266" class="Keyword">import</a> <a id="273" href="elementary-number-theory.negative-rational-numbers.html" class="Module">elementary-number-theory.negative-rational-numbers</a>
<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="elementary-number-theory.nonnegative-rational-numbers.html" class="Module">elementary-number-theory.nonnegative-rational-numbers</a>
<a id="390" class="Keyword">open</a> <a id="395" class="Keyword">import</a> <a id="402" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>
<a id="453" class="Keyword">open</a> <a id="458" class="Keyword">import</a> <a id="465" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>
<a id="507" class="Keyword">open</a> <a id="512" class="Keyword">import</a> <a id="519" href="elementary-number-theory.strict-inequality-rational-numbers.html" class="Module">elementary-number-theory.strict-inequality-rational-numbers</a>

<a id="580" class="Keyword">open</a> <a id="585" class="Keyword">import</a> <a id="592" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="619" class="Keyword">open</a> <a id="624" class="Keyword">import</a> <a id="631" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="672" class="Keyword">open</a> <a id="677" class="Keyword">import</a> <a id="684" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="710" class="Keyword">open</a> <a id="715" class="Keyword">import</a> <a id="722" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

In this file, we outline basic relations between
[negative](elementary-number-theory.negative-rational-numbers.md),
[nonnegative](elementary-number-theory.nonnegative-rational-numbers.md), and
[positive](elementary-number-theory.positive-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md).

## Properties

### Dichotomies

#### A rational number is either negative or nonnegative

<pre class="Agda"><a id="1199" class="Keyword">abstract</a>
  <a id="decide-is-negative-is-nonnegative-ℚ"></a><a id="1210" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1210" class="Function">decide-is-negative-is-nonnegative-ℚ</a> <a id="1246" class="Symbol">:</a>
    <a id="1252" class="Symbol">(</a><a id="1253" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1253" class="Bound">q</a> <a id="1255" class="Symbol">:</a> <a id="1257" href="elementary-number-theory.rational-numbers.html#2278" class="Function">ℚ</a><a id="1258" class="Symbol">)</a> <a id="1260" class="Symbol">→</a>
    <a id="1266" href="elementary-number-theory.negative-rational-numbers.html#2102" class="Function">is-negative-ℚ</a> <a id="1280" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1253" class="Bound">q</a> <a id="1282" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="1284" href="elementary-number-theory.nonnegative-rational-numbers.html#2041" class="Function">is-nonnegative-ℚ</a> <a id="1301" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1253" class="Bound">q</a>
  <a id="1305" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1210" class="Function">decide-is-negative-is-nonnegative-ℚ</a> <a id="1341" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1341" class="Bound">q</a> <a id="1343" class="Symbol">=</a>
    <a id="1349" href="foundation.functoriality-coproduct-types.html#2021" class="Function">map-coproduct</a>
      <a id="1369" class="Symbol">(</a> <a id="1371" href="elementary-number-theory.negative-rational-numbers.html#5083" class="Function">is-negative-le-zero-ℚ</a> <a id="1393" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1341" class="Bound">q</a><a id="1394" class="Symbol">)</a>
      <a id="1402" class="Symbol">(</a> <a id="1404" href="elementary-number-theory.nonnegative-rational-numbers.html#5141" class="Function">is-nonnegative-leq-zero-ℚ</a> <a id="1430" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1341" class="Bound">q</a><a id="1431" class="Symbol">)</a>
      <a id="1439" class="Symbol">(</a> <a id="1441" href="elementary-number-theory.strict-inequality-rational-numbers.html#12264" class="Function">decide-le-leq-ℚ</a> <a id="1457" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1341" class="Bound">q</a> <a id="1459" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="1465" class="Symbol">)</a>
</pre>
### Trichotomies

#### A rational number is either negative, zero, or positive

<pre class="Agda"><a id="1560" class="Keyword">abstract</a>
  <a id="trichotomy-sign-ℚ"></a><a id="1571" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1571" class="Function">trichotomy-sign-ℚ</a> <a id="1589" class="Symbol">:</a>
    <a id="1595" class="Symbol">{</a><a id="1596" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1596" class="Bound">l</a> <a id="1598" class="Symbol">:</a> <a id="1600" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1605" class="Symbol">}</a> <a id="1607" class="Symbol">{</a><a id="1608" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1608" class="Bound">A</a> <a id="1610" class="Symbol">:</a> <a id="1612" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1615" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1596" class="Bound">l</a><a id="1616" class="Symbol">}</a> <a id="1618" class="Symbol">(</a><a id="1619" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1619" class="Bound">x</a> <a id="1621" class="Symbol">:</a> <a id="1623" href="elementary-number-theory.rational-numbers.html#2278" class="Function">ℚ</a><a id="1624" class="Symbol">)</a> <a id="1626" class="Symbol">→</a>
    <a id="1632" class="Symbol">(</a> <a id="1634" href="elementary-number-theory.negative-rational-numbers.html#2102" class="Function">is-negative-ℚ</a> <a id="1648" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1619" class="Bound">x</a> <a id="1650" class="Symbol">→</a> <a id="1652" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1608" class="Bound">A</a><a id="1653" class="Symbol">)</a> <a id="1655" class="Symbol">→</a>
    <a id="1661" class="Symbol">(</a> <a id="1663" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1619" class="Bound">x</a> <a id="1665" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1667" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a> <a id="1674" class="Symbol">→</a> <a id="1676" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1608" class="Bound">A</a><a id="1677" class="Symbol">)</a> <a id="1679" class="Symbol">→</a>
    <a id="1685" class="Symbol">(</a> <a id="1687" href="elementary-number-theory.positive-rational-numbers.html#4173" class="Function">is-positive-ℚ</a> <a id="1701" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1619" class="Bound">x</a> <a id="1703" class="Symbol">→</a> <a id="1705" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1608" class="Bound">A</a><a id="1706" class="Symbol">)</a> <a id="1708" class="Symbol">→</a>
    <a id="1714" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1608" class="Bound">A</a>
  <a id="1718" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1571" class="Function">trichotomy-sign-ℚ</a> <a id="1736" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1736" class="Bound">x</a> <a id="1738" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1738" class="Bound">neg</a> <a id="1742" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1742" class="Bound">zero</a> <a id="1747" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1747" class="Bound">pos</a> <a id="1751" class="Symbol">=</a>
    <a id="1757" href="elementary-number-theory.strict-inequality-rational-numbers.html#12998" class="Function">trichotomy-le-ℚ</a>
      <a id="1779" class="Symbol">(</a> <a id="1781" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1736" class="Bound">x</a><a id="1782" class="Symbol">)</a>
      <a id="1790" class="Symbol">(</a> <a id="1792" href="elementary-number-theory.rational-numbers.html#3520" class="Function">zero-ℚ</a><a id="1798" class="Symbol">)</a>
      <a id="1806" class="Symbol">(</a> <a id="1808" class="Symbol">λ</a> <a id="1810" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1810" class="Bound">x&lt;0</a> <a id="1814" class="Symbol">→</a> <a id="1816" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1738" class="Bound">neg</a> <a id="1820" class="Symbol">(</a><a id="1821" href="elementary-number-theory.negative-rational-numbers.html#5083" class="Function">is-negative-le-zero-ℚ</a> <a id="1843" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1736" class="Bound">x</a> <a id="1845" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1810" class="Bound">x&lt;0</a><a id="1848" class="Symbol">))</a>
      <a id="1857" class="Symbol">(</a> <a id="1859" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1742" class="Bound">zero</a><a id="1863" class="Symbol">)</a>
      <a id="1871" class="Symbol">(</a> <a id="1873" class="Symbol">λ</a> <a id="1875" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1875" class="Bound">0&lt;x</a> <a id="1879" class="Symbol">→</a> <a id="1881" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1747" class="Bound">pos</a> <a id="1885" class="Symbol">(</a><a id="1886" href="elementary-number-theory.positive-rational-numbers.html#7536" class="Function">is-positive-le-zero-ℚ</a> <a id="1908" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1736" class="Bound">x</a> <a id="1910" href="elementary-number-theory.positive-and-negative-rational-numbers.html#1875" class="Bound">0&lt;x</a><a id="1913" class="Symbol">))</a>
</pre>