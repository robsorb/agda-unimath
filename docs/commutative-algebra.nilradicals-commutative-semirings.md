# The nilradical of a commutative semiring

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="commutative-algebra.nilradicals-commutative-semirings.html" class="Module">commutative-algebra.nilradicals-commutative-semirings</a> <a id="114" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="commutative-algebra.commutative-semirings.html" class="Module">commutative-algebra.commutative-semirings</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="commutative-algebra.subsets-commutative-semirings.html" class="Module">commutative-algebra.subsets-commutative-semirings</a>

<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="ring-theory.nilpotent-elements-semirings.html" class="Module">ring-theory.nilpotent-elements-semirings</a>
</pre>
</details>

## Idea

The **nilradical** of a commutative semiring is the ideal consisting of all
nilpotent elements.

## Definitions

<pre class="Agda"><a id="subset-nilradical-Commutative-Semiring"></a><a id="615" href="commutative-algebra.nilradicals-commutative-semirings.html#615" class="Function">subset-nilradical-Commutative-Semiring</a> <a id="654" class="Symbol">:</a>
  <a id="658" class="Symbol">{</a><a id="659" href="commutative-algebra.nilradicals-commutative-semirings.html#659" class="Bound">l</a> <a id="661" class="Symbol">:</a> <a id="663" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="668" class="Symbol">}</a> <a id="670" class="Symbol">(</a><a id="671" href="commutative-algebra.nilradicals-commutative-semirings.html#671" class="Bound">A</a> <a id="673" class="Symbol">:</a> <a id="675" href="commutative-algebra.commutative-semirings.html#1570" class="Function">Commutative-Semiring</a> <a id="696" href="commutative-algebra.nilradicals-commutative-semirings.html#659" class="Bound">l</a><a id="697" class="Symbol">)</a> <a id="699" class="Symbol">→</a> <a id="701" href="commutative-algebra.subsets-commutative-semirings.html#593" class="Function">subset-Commutative-Semiring</a> <a id="729" href="commutative-algebra.nilradicals-commutative-semirings.html#659" class="Bound">l</a> <a id="731" href="commutative-algebra.nilradicals-commutative-semirings.html#671" class="Bound">A</a>
<a id="733" href="commutative-algebra.nilradicals-commutative-semirings.html#615" class="Function">subset-nilradical-Commutative-Semiring</a> <a id="772" href="commutative-algebra.nilradicals-commutative-semirings.html#772" class="Bound">A</a> <a id="774" class="Symbol">=</a>
  <a id="778" href="ring-theory.nilpotent-elements-semirings.html#913" class="Function">is-nilpotent-element-semiring-Prop</a> <a id="813" class="Symbol">(</a><a id="814" href="commutative-algebra.commutative-semirings.html#1818" class="Function">semiring-Commutative-Semiring</a> <a id="844" href="commutative-algebra.nilradicals-commutative-semirings.html#772" class="Bound">A</a><a id="845" class="Symbol">)</a>
</pre>
## Properties

### The nilradical contains zero

<pre class="Agda"><a id="contains-zero-nilradical-Commutative-Semiring"></a><a id="909" href="commutative-algebra.nilradicals-commutative-semirings.html#909" class="Function">contains-zero-nilradical-Commutative-Semiring</a> <a id="955" class="Symbol">:</a>
  <a id="959" class="Symbol">{</a><a id="960" href="commutative-algebra.nilradicals-commutative-semirings.html#960" class="Bound">l</a> <a id="962" class="Symbol">:</a> <a id="964" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="969" class="Symbol">}</a> <a id="971" class="Symbol">(</a><a id="972" href="commutative-algebra.nilradicals-commutative-semirings.html#972" class="Bound">A</a> <a id="974" class="Symbol">:</a> <a id="976" href="commutative-algebra.commutative-semirings.html#1570" class="Function">Commutative-Semiring</a> <a id="997" href="commutative-algebra.nilradicals-commutative-semirings.html#960" class="Bound">l</a><a id="998" class="Symbol">)</a> <a id="1000" class="Symbol">→</a>
  <a id="1004" href="commutative-algebra.subsets-commutative-semirings.html#2868" class="Function">contains-zero-subset-Commutative-Semiring</a> <a id="1046" href="commutative-algebra.nilradicals-commutative-semirings.html#972" class="Bound">A</a>
    <a id="1052" class="Symbol">(</a> <a id="1054" href="commutative-algebra.nilradicals-commutative-semirings.html#615" class="Function">subset-nilradical-Commutative-Semiring</a> <a id="1093" href="commutative-algebra.nilradicals-commutative-semirings.html#972" class="Bound">A</a><a id="1094" class="Symbol">)</a>
<a id="1096" href="commutative-algebra.nilradicals-commutative-semirings.html#909" class="Function">contains-zero-nilradical-Commutative-Semiring</a> <a id="1142" href="commutative-algebra.nilradicals-commutative-semirings.html#1142" class="Bound">A</a> <a id="1144" class="Symbol">=</a> <a id="1146" href="foundation.existential-quantification.html#4482" class="Function">intro-exists</a> <a id="1159" class="Number">1</a> <a id="1161" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### The nilradical is closed under addition

<pre class="Agda"><a id="is-closed-under-add-nilradical-Commutative-Semiring"></a><a id="1224" href="commutative-algebra.nilradicals-commutative-semirings.html#1224" class="Function">is-closed-under-add-nilradical-Commutative-Semiring</a> <a id="1276" class="Symbol">:</a>
  <a id="1280" class="Symbol">{</a><a id="1281" href="commutative-algebra.nilradicals-commutative-semirings.html#1281" class="Bound">l</a> <a id="1283" class="Symbol">:</a> <a id="1285" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1290" class="Symbol">}</a> <a id="1292" class="Symbol">(</a><a id="1293" href="commutative-algebra.nilradicals-commutative-semirings.html#1293" class="Bound">A</a> <a id="1295" class="Symbol">:</a> <a id="1297" href="commutative-algebra.commutative-semirings.html#1570" class="Function">Commutative-Semiring</a> <a id="1318" href="commutative-algebra.nilradicals-commutative-semirings.html#1281" class="Bound">l</a><a id="1319" class="Symbol">)</a> <a id="1321" class="Symbol">→</a>
  <a id="1325" href="commutative-algebra.subsets-commutative-semirings.html#3331" class="Function">is-closed-under-addition-subset-Commutative-Semiring</a> <a id="1378" href="commutative-algebra.nilradicals-commutative-semirings.html#1293" class="Bound">A</a>
    <a id="1384" class="Symbol">(</a> <a id="1386" href="commutative-algebra.nilradicals-commutative-semirings.html#615" class="Function">subset-nilradical-Commutative-Semiring</a> <a id="1425" href="commutative-algebra.nilradicals-commutative-semirings.html#1293" class="Bound">A</a><a id="1426" class="Symbol">)</a>
<a id="1428" href="commutative-algebra.nilradicals-commutative-semirings.html#1224" class="Function">is-closed-under-add-nilradical-Commutative-Semiring</a> <a id="1480" href="commutative-algebra.nilradicals-commutative-semirings.html#1480" class="Bound">A</a> <a id="1482" href="commutative-algebra.nilradicals-commutative-semirings.html#1482" class="Bound">x</a> <a id="1484" href="commutative-algebra.nilradicals-commutative-semirings.html#1484" class="Bound">y</a> <a id="1486" class="Symbol">=</a>
  <a id="1490" href="ring-theory.nilpotent-elements-semirings.html#1854" class="Function">is-nilpotent-add-Semiring</a>
    <a id="1520" class="Symbol">(</a> <a id="1522" href="commutative-algebra.commutative-semirings.html#1818" class="Function">semiring-Commutative-Semiring</a> <a id="1552" href="commutative-algebra.nilradicals-commutative-semirings.html#1480" class="Bound">A</a><a id="1553" class="Symbol">)</a>
    <a id="1559" class="Symbol">(</a> <a id="1561" href="commutative-algebra.nilradicals-commutative-semirings.html#1482" class="Bound">x</a><a id="1562" class="Symbol">)</a>
    <a id="1568" class="Symbol">(</a> <a id="1570" href="commutative-algebra.nilradicals-commutative-semirings.html#1484" class="Bound">y</a><a id="1571" class="Symbol">)</a>
    <a id="1577" class="Symbol">(</a> <a id="1579" href="commutative-algebra.commutative-semirings.html#8301" class="Function">commutative-mul-Commutative-Semiring</a> <a id="1616" href="commutative-algebra.nilradicals-commutative-semirings.html#1480" class="Bound">A</a> <a id="1618" href="commutative-algebra.nilradicals-commutative-semirings.html#1482" class="Bound">x</a> <a id="1620" href="commutative-algebra.nilradicals-commutative-semirings.html#1484" class="Bound">y</a><a id="1621" class="Symbol">)</a>
</pre>
### The nilradical is closed under multiplication with ring elements

<pre class="Agda"><a id="1706" class="Keyword">module</a> <a id="1713" href="commutative-algebra.nilradicals-commutative-semirings.html#1713" class="Module">_</a>
  <a id="1717" class="Symbol">{</a><a id="1718" href="commutative-algebra.nilradicals-commutative-semirings.html#1718" class="Bound">l</a> <a id="1720" class="Symbol">:</a> <a id="1722" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1727" class="Symbol">}</a> <a id="1729" class="Symbol">(</a><a id="1730" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a> <a id="1732" class="Symbol">:</a> <a id="1734" href="commutative-algebra.commutative-semirings.html#1570" class="Function">Commutative-Semiring</a> <a id="1755" href="commutative-algebra.nilradicals-commutative-semirings.html#1718" class="Bound">l</a><a id="1756" class="Symbol">)</a>
  <a id="1760" class="Keyword">where</a>

  <a id="1769" href="commutative-algebra.nilradicals-commutative-semirings.html#1769" class="Function">is-closed-under-right-multiplication-nilradical-Commutative-Semiring</a> <a id="1838" class="Symbol">:</a>
    <a id="1844" href="commutative-algebra.subsets-commutative-semirings.html#4346" class="Function">is-closed-under-right-multiplication-subset-Commutative-Semiring</a> <a id="1909" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a>
      <a id="1917" class="Symbol">(</a> <a id="1919" href="commutative-algebra.nilradicals-commutative-semirings.html#615" class="Function">subset-nilradical-Commutative-Semiring</a> <a id="1958" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a><a id="1959" class="Symbol">)</a>
  <a id="1963" href="commutative-algebra.nilradicals-commutative-semirings.html#1769" class="Function">is-closed-under-right-multiplication-nilradical-Commutative-Semiring</a> <a id="2032" href="commutative-algebra.nilradicals-commutative-semirings.html#2032" class="Bound">x</a> <a id="2034" href="commutative-algebra.nilradicals-commutative-semirings.html#2034" class="Bound">y</a> <a id="2036" class="Symbol">=</a>
    <a id="2042" href="ring-theory.nilpotent-elements-semirings.html#2994" class="Function">is-nilpotent-element-mul-Semiring</a>
      <a id="2082" class="Symbol">(</a> <a id="2084" href="commutative-algebra.commutative-semirings.html#1818" class="Function">semiring-Commutative-Semiring</a> <a id="2114" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a><a id="2115" class="Symbol">)</a>
      <a id="2123" class="Symbol">(</a> <a id="2125" href="commutative-algebra.nilradicals-commutative-semirings.html#2032" class="Bound">x</a><a id="2126" class="Symbol">)</a>
      <a id="2134" class="Symbol">(</a> <a id="2136" href="commutative-algebra.nilradicals-commutative-semirings.html#2034" class="Bound">y</a><a id="2137" class="Symbol">)</a>
      <a id="2145" class="Symbol">(</a> <a id="2147" href="commutative-algebra.commutative-semirings.html#8301" class="Function">commutative-mul-Commutative-Semiring</a> <a id="2184" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a> <a id="2186" href="commutative-algebra.nilradicals-commutative-semirings.html#2032" class="Bound">x</a> <a id="2188" href="commutative-algebra.nilradicals-commutative-semirings.html#2034" class="Bound">y</a><a id="2189" class="Symbol">)</a>

  <a id="2194" href="commutative-algebra.nilradicals-commutative-semirings.html#2194" class="Function">is-closed-under-left-multiplication-nilradical-Commutative-Semiring</a> <a id="2262" class="Symbol">:</a>
    <a id="2268" href="commutative-algebra.subsets-commutative-semirings.html#3973" class="Function">is-closed-under-left-multiplication-subset-Commutative-Semiring</a> <a id="2332" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a>
      <a id="2340" class="Symbol">(</a> <a id="2342" href="commutative-algebra.nilradicals-commutative-semirings.html#615" class="Function">subset-nilradical-Commutative-Semiring</a> <a id="2381" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a><a id="2382" class="Symbol">)</a>
  <a id="2386" href="commutative-algebra.nilradicals-commutative-semirings.html#2194" class="Function">is-closed-under-left-multiplication-nilradical-Commutative-Semiring</a> <a id="2454" href="commutative-algebra.nilradicals-commutative-semirings.html#2454" class="Bound">x</a> <a id="2456" href="commutative-algebra.nilradicals-commutative-semirings.html#2456" class="Bound">y</a> <a id="2458" class="Symbol">=</a>
    <a id="2464" href="ring-theory.nilpotent-elements-semirings.html#3613" class="Function">is-nilpotent-element-mul-Semiring&#39;</a>
      <a id="2505" class="Symbol">(</a> <a id="2507" href="commutative-algebra.commutative-semirings.html#1818" class="Function">semiring-Commutative-Semiring</a> <a id="2537" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a><a id="2538" class="Symbol">)</a>
      <a id="2546" class="Symbol">(</a> <a id="2548" href="commutative-algebra.nilradicals-commutative-semirings.html#2456" class="Bound">y</a><a id="2549" class="Symbol">)</a>
      <a id="2557" class="Symbol">(</a> <a id="2559" href="commutative-algebra.nilradicals-commutative-semirings.html#2454" class="Bound">x</a><a id="2560" class="Symbol">)</a>
      <a id="2568" class="Symbol">(</a> <a id="2570" href="commutative-algebra.commutative-semirings.html#8301" class="Function">commutative-mul-Commutative-Semiring</a> <a id="2607" href="commutative-algebra.nilradicals-commutative-semirings.html#1730" class="Bound">A</a> <a id="2609" href="commutative-algebra.nilradicals-commutative-semirings.html#2456" class="Bound">y</a> <a id="2611" href="commutative-algebra.nilradicals-commutative-semirings.html#2454" class="Bound">x</a><a id="2612" class="Symbol">)</a>
</pre>