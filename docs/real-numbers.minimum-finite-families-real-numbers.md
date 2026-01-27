# The minimum of finite families of real numbers

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="real-numbers.minimum-finite-families-real-numbers.html" class="Module">real-numbers.minimum-finite-families-real-numbers</a> <a id="116" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="lists.finite-sequences.html" class="Module">lists.finite-sequences</a>

<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="order-theory.greatest-lower-bounds-large-posets.html" class="Module">order-theory.greatest-lower-bounds-large-posets</a>

<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="real-numbers.dedekind-real-numbers.html" class="Module">real-numbers.dedekind-real-numbers</a>
<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="real-numbers.inequality-real-numbers.html" class="Module">real-numbers.inequality-real-numbers</a>
<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="real-numbers.infima-families-real-numbers.html" class="Module">real-numbers.infima-families-real-numbers</a>
<a id="551" class="Keyword">open</a> <a id="556" class="Keyword">import</a> <a id="563" href="real-numbers.maximum-finite-families-real-numbers.html" class="Module">real-numbers.maximum-finite-families-real-numbers</a>
<a id="613" class="Keyword">open</a> <a id="618" class="Keyword">import</a> <a id="625" href="real-numbers.negation-real-numbers.html" class="Module">real-numbers.negation-real-numbers</a>

<a id="661" class="Keyword">open</a> <a id="666" class="Keyword">import</a> <a id="673" href="univalent-combinatorics.inhabited-finite-types.html" class="Module">univalent-combinatorics.inhabited-finite-types</a>
</pre>
</details>

## Idea

The
{{#concept "minimum" Disambiguation="inhabited finite family, Dedekind real numbers" Agda=min-finite-family-ℝ WD="minimum" WDID=Q10578722}}
of a family of [Dedekind real numbers](real-numbers.dedekind-real-numbers.md)
indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md) is
their
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md).

## Definition

### The minimum of a nonempty finite sequence of real numbers

<pre class="Agda"><a id="1229" class="Keyword">module</a> <a id="1236" href="real-numbers.minimum-finite-families-real-numbers.html#1236" class="Module">_</a>
  <a id="1240" class="Symbol">{</a><a id="1241" href="real-numbers.minimum-finite-families-real-numbers.html#1241" class="Bound">l</a> <a id="1243" class="Symbol">:</a> <a id="1245" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1250" class="Symbol">}</a> <a id="1252" class="Symbol">(</a><a id="1253" href="real-numbers.minimum-finite-families-real-numbers.html#1253" class="Bound">n</a> <a id="1255" class="Symbol">:</a> <a id="1257" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1258" class="Symbol">)</a> <a id="1260" class="Symbol">(</a><a id="1261" href="real-numbers.minimum-finite-families-real-numbers.html#1261" class="Bound">x</a> <a id="1263" class="Symbol">:</a> <a id="1265" href="lists.finite-sequences.html#1256" class="Function">fin-sequence</a> <a id="1278" class="Symbol">(</a><a id="1279" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1281" href="real-numbers.minimum-finite-families-real-numbers.html#1241" class="Bound">l</a><a id="1282" class="Symbol">)</a> <a id="1284" class="Symbol">(</a><a id="1285" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1292" href="real-numbers.minimum-finite-families-real-numbers.html#1253" class="Bound">n</a><a id="1293" class="Symbol">))</a>
  <a id="1298" class="Keyword">where</a>

  <a id="1307" class="Keyword">opaque</a>
    <a id="1318" href="real-numbers.minimum-finite-families-real-numbers.html#1318" class="Function">min-fin-sequence-ℝ</a> <a id="1337" class="Symbol">:</a> <a id="1339" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1341" href="real-numbers.minimum-finite-families-real-numbers.html#1241" class="Bound">l</a>
    <a id="1347" href="real-numbers.minimum-finite-families-real-numbers.html#1318" class="Function">min-fin-sequence-ℝ</a> <a id="1366" class="Symbol">=</a> <a id="1368" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="1374" class="Symbol">(</a><a id="1375" href="real-numbers.maximum-finite-families-real-numbers.html#2433" class="Function">max-fin-sequence-ℝ</a> <a id="1394" href="real-numbers.minimum-finite-families-real-numbers.html#1253" class="Bound">n</a> <a id="1396" class="Symbol">(</a><a id="1397" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="1403" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1405" href="real-numbers.minimum-finite-families-real-numbers.html#1261" class="Bound">x</a><a id="1406" class="Symbol">))</a>
</pre>
### The minimum of an inhabited finite family of real numbers

<pre class="Agda"><a id="1485" class="Keyword">module</a> <a id="1492" href="real-numbers.minimum-finite-families-real-numbers.html#1492" class="Module">_</a>
  <a id="1496" class="Symbol">{</a><a id="1497" href="real-numbers.minimum-finite-families-real-numbers.html#1497" class="Bound">l1</a> <a id="1500" href="real-numbers.minimum-finite-families-real-numbers.html#1500" class="Bound">l2</a> <a id="1503" class="Symbol">:</a> <a id="1505" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1510" class="Symbol">}</a> <a id="1512" class="Symbol">(</a><a id="1513" href="real-numbers.minimum-finite-families-real-numbers.html#1513" class="Bound">I</a> <a id="1515" class="Symbol">:</a> <a id="1517" href="univalent-combinatorics.inhabited-finite-types.html#1273" class="Function">Inhabited-Finite-Type</a> <a id="1539" href="real-numbers.minimum-finite-families-real-numbers.html#1497" class="Bound">l1</a><a id="1541" class="Symbol">)</a>
  <a id="1545" class="Symbol">(</a><a id="1546" href="real-numbers.minimum-finite-families-real-numbers.html#1546" class="Bound">f</a> <a id="1548" class="Symbol">:</a> <a id="1550" href="univalent-combinatorics.inhabited-finite-types.html#1573" class="Function">type-Inhabited-Finite-Type</a> <a id="1577" href="real-numbers.minimum-finite-families-real-numbers.html#1513" class="Bound">I</a> <a id="1579" class="Symbol">→</a> <a id="1581" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1583" href="real-numbers.minimum-finite-families-real-numbers.html#1500" class="Bound">l2</a><a id="1585" class="Symbol">)</a>
  <a id="1589" class="Keyword">where</a>

  <a id="1598" class="Keyword">opaque</a>
    <a id="1609" href="real-numbers.minimum-finite-families-real-numbers.html#1609" class="Function">min-finite-family-ℝ</a> <a id="1629" class="Symbol">:</a> <a id="1631" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1633" href="real-numbers.minimum-finite-families-real-numbers.html#1500" class="Bound">l2</a>
    <a id="1640" href="real-numbers.minimum-finite-families-real-numbers.html#1609" class="Function">min-finite-family-ℝ</a> <a id="1660" class="Symbol">=</a> <a id="1662" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="1668" class="Symbol">(</a><a id="1669" href="real-numbers.maximum-finite-families-real-numbers.html#3178" class="Function">max-finite-family-ℝ</a> <a id="1689" href="real-numbers.minimum-finite-families-real-numbers.html#1513" class="Bound">I</a> <a id="1691" class="Symbol">(</a><a id="1692" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="1698" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1700" href="real-numbers.minimum-finite-families-real-numbers.html#1546" class="Bound">f</a><a id="1701" class="Symbol">))</a>
</pre>
## Properties

### The minimum of a finite sequence is its infimum

<pre class="Agda"><a id="1785" class="Keyword">opaque</a>
  <a id="1794" class="Keyword">unfolding</a> <a id="1804" href="real-numbers.minimum-finite-families-real-numbers.html#1318" class="Function">min-fin-sequence-ℝ</a>

  <a id="is-infimum-min-fin-sequence-ℝ"></a><a id="1826" href="real-numbers.minimum-finite-families-real-numbers.html#1826" class="Function">is-infimum-min-fin-sequence-ℝ</a> <a id="1856" class="Symbol">:</a>
    <a id="1862" class="Symbol">{</a><a id="1863" href="real-numbers.minimum-finite-families-real-numbers.html#1863" class="Bound">l</a> <a id="1865" class="Symbol">:</a> <a id="1867" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1872" class="Symbol">}</a> <a id="1874" class="Symbol">(</a><a id="1875" href="real-numbers.minimum-finite-families-real-numbers.html#1875" class="Bound">n</a> <a id="1877" class="Symbol">:</a> <a id="1879" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1880" class="Symbol">)</a> <a id="1882" class="Symbol">(</a><a id="1883" href="real-numbers.minimum-finite-families-real-numbers.html#1883" class="Bound">x</a> <a id="1885" class="Symbol">:</a> <a id="1887" href="lists.finite-sequences.html#1256" class="Function">fin-sequence</a> <a id="1900" class="Symbol">(</a><a id="1901" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1903" href="real-numbers.minimum-finite-families-real-numbers.html#1863" class="Bound">l</a><a id="1904" class="Symbol">)</a> <a id="1906" class="Symbol">(</a><a id="1907" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1914" href="real-numbers.minimum-finite-families-real-numbers.html#1875" class="Bound">n</a><a id="1915" class="Symbol">))</a> <a id="1918" class="Symbol">→</a>
    <a id="1924" href="real-numbers.infima-families-real-numbers.html#3089" class="Function">is-infimum-family-ℝ</a> <a id="1944" href="real-numbers.minimum-finite-families-real-numbers.html#1883" class="Bound">x</a> <a id="1946" class="Symbol">(</a><a id="1947" href="real-numbers.minimum-finite-families-real-numbers.html#1318" class="Function">min-fin-sequence-ℝ</a> <a id="1966" href="real-numbers.minimum-finite-families-real-numbers.html#1875" class="Bound">n</a> <a id="1968" href="real-numbers.minimum-finite-families-real-numbers.html#1883" class="Bound">x</a><a id="1969" class="Symbol">)</a>
  <a id="1973" href="real-numbers.minimum-finite-families-real-numbers.html#1826" class="Function">is-infimum-min-fin-sequence-ℝ</a> <a id="2003" href="real-numbers.minimum-finite-families-real-numbers.html#2003" class="Bound">n</a> <a id="2005" href="real-numbers.minimum-finite-families-real-numbers.html#2005" class="Bound">x</a> <a id="2007" class="Symbol">=</a>
    <a id="2013" href="real-numbers.infima-families-real-numbers.html#9511" class="Function">is-infimum-neg-supremum-neg-family-ℝ</a>
      <a id="2056" class="Symbol">(</a> <a id="2058" href="real-numbers.minimum-finite-families-real-numbers.html#2005" class="Bound">x</a><a id="2059" class="Symbol">)</a>
      <a id="2067" class="Symbol">(</a> <a id="2069" href="real-numbers.maximum-finite-families-real-numbers.html#2433" class="Function">max-fin-sequence-ℝ</a> <a id="2088" href="real-numbers.minimum-finite-families-real-numbers.html#2003" class="Bound">n</a> <a id="2090" class="Symbol">(</a><a id="2091" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="2097" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2099" href="real-numbers.minimum-finite-families-real-numbers.html#2005" class="Bound">x</a><a id="2100" class="Symbol">))</a>
      <a id="2109" class="Symbol">(</a> <a id="2111" href="real-numbers.maximum-finite-families-real-numbers.html#6298" class="Function">is-supremum-max-fin-sequence-ℝ</a> <a id="2142" href="real-numbers.minimum-finite-families-real-numbers.html#2003" class="Bound">n</a> <a id="2144" class="Symbol">(</a><a id="2145" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="2151" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2153" href="real-numbers.minimum-finite-families-real-numbers.html#2005" class="Bound">x</a><a id="2154" class="Symbol">))</a>
</pre>
### The minimum of a finite family is its infimum

<pre class="Agda"><a id="2221" class="Keyword">module</a> <a id="2228" href="real-numbers.minimum-finite-families-real-numbers.html#2228" class="Module">_</a>
  <a id="2232" class="Symbol">{</a><a id="2233" href="real-numbers.minimum-finite-families-real-numbers.html#2233" class="Bound">l1</a> <a id="2236" href="real-numbers.minimum-finite-families-real-numbers.html#2236" class="Bound">l2</a> <a id="2239" class="Symbol">:</a> <a id="2241" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2246" class="Symbol">}</a> <a id="2248" class="Symbol">(</a><a id="2249" href="real-numbers.minimum-finite-families-real-numbers.html#2249" class="Bound">I</a> <a id="2251" class="Symbol">:</a> <a id="2253" href="univalent-combinatorics.inhabited-finite-types.html#1273" class="Function">Inhabited-Finite-Type</a> <a id="2275" href="real-numbers.minimum-finite-families-real-numbers.html#2233" class="Bound">l1</a><a id="2277" class="Symbol">)</a>
  <a id="2281" class="Symbol">(</a><a id="2282" href="real-numbers.minimum-finite-families-real-numbers.html#2282" class="Bound">x</a> <a id="2284" class="Symbol">:</a> <a id="2286" href="univalent-combinatorics.inhabited-finite-types.html#1573" class="Function">type-Inhabited-Finite-Type</a> <a id="2313" href="real-numbers.minimum-finite-families-real-numbers.html#2249" class="Bound">I</a> <a id="2315" class="Symbol">→</a> <a id="2317" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="2319" href="real-numbers.minimum-finite-families-real-numbers.html#2236" class="Bound">l2</a><a id="2321" class="Symbol">)</a>
  <a id="2325" class="Keyword">where</a>

  <a id="2334" class="Keyword">opaque</a>
    <a id="2345" class="Keyword">unfolding</a> <a id="2355" href="real-numbers.minimum-finite-families-real-numbers.html#1609" class="Function">min-finite-family-ℝ</a>

    <a id="2380" href="real-numbers.minimum-finite-families-real-numbers.html#2380" class="Function">is-infimum-min-finite-family-ℝ</a> <a id="2411" class="Symbol">:</a>
      <a id="2419" href="real-numbers.infima-families-real-numbers.html#3089" class="Function">is-infimum-family-ℝ</a> <a id="2439" href="real-numbers.minimum-finite-families-real-numbers.html#2282" class="Bound">x</a> <a id="2441" class="Symbol">(</a><a id="2442" href="real-numbers.minimum-finite-families-real-numbers.html#1609" class="Function">min-finite-family-ℝ</a> <a id="2462" href="real-numbers.minimum-finite-families-real-numbers.html#2249" class="Bound">I</a> <a id="2464" href="real-numbers.minimum-finite-families-real-numbers.html#2282" class="Bound">x</a><a id="2465" class="Symbol">)</a>
    <a id="2471" href="real-numbers.minimum-finite-families-real-numbers.html#2380" class="Function">is-infimum-min-finite-family-ℝ</a> <a id="2502" class="Symbol">=</a>
      <a id="2510" href="real-numbers.infima-families-real-numbers.html#9511" class="Function">is-infimum-neg-supremum-neg-family-ℝ</a>
        <a id="2555" class="Symbol">(</a> <a id="2557" href="real-numbers.minimum-finite-families-real-numbers.html#2282" class="Bound">x</a><a id="2558" class="Symbol">)</a>
        <a id="2568" class="Symbol">(</a> <a id="2570" href="real-numbers.maximum-finite-families-real-numbers.html#3178" class="Function">max-finite-family-ℝ</a> <a id="2590" href="real-numbers.minimum-finite-families-real-numbers.html#2249" class="Bound">I</a> <a id="2592" class="Symbol">(</a><a id="2593" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="2599" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2601" href="real-numbers.minimum-finite-families-real-numbers.html#2282" class="Bound">x</a><a id="2602" class="Symbol">))</a>
        <a id="2613" class="Symbol">(</a> <a id="2615" href="real-numbers.maximum-finite-families-real-numbers.html#8890" class="Function">is-supremum-max-finite-family-ℝ</a> <a id="2647" href="real-numbers.minimum-finite-families-real-numbers.html#2249" class="Bound">I</a> <a id="2649" class="Symbol">(</a><a id="2650" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="2656" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2658" href="real-numbers.minimum-finite-families-real-numbers.html#2282" class="Bound">x</a><a id="2659" class="Symbol">))</a>
</pre>
### The minimum of a finite family is its greatest lower bound

<pre class="Agda"><a id="2739" class="Keyword">module</a> <a id="2746" href="real-numbers.minimum-finite-families-real-numbers.html#2746" class="Module">_</a>
  <a id="2750" class="Symbol">{</a><a id="2751" href="real-numbers.minimum-finite-families-real-numbers.html#2751" class="Bound">l1</a> <a id="2754" href="real-numbers.minimum-finite-families-real-numbers.html#2754" class="Bound">l2</a> <a id="2757" class="Symbol">:</a> <a id="2759" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2764" class="Symbol">}</a> <a id="2766" class="Symbol">(</a><a id="2767" href="real-numbers.minimum-finite-families-real-numbers.html#2767" class="Bound">I</a> <a id="2769" class="Symbol">:</a> <a id="2771" href="univalent-combinatorics.inhabited-finite-types.html#1273" class="Function">Inhabited-Finite-Type</a> <a id="2793" href="real-numbers.minimum-finite-families-real-numbers.html#2751" class="Bound">l1</a><a id="2795" class="Symbol">)</a>
  <a id="2799" class="Symbol">(</a><a id="2800" href="real-numbers.minimum-finite-families-real-numbers.html#2800" class="Bound">x</a> <a id="2802" class="Symbol">:</a> <a id="2804" href="univalent-combinatorics.inhabited-finite-types.html#1573" class="Function">type-Inhabited-Finite-Type</a> <a id="2831" href="real-numbers.minimum-finite-families-real-numbers.html#2767" class="Bound">I</a> <a id="2833" class="Symbol">→</a> <a id="2835" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="2837" href="real-numbers.minimum-finite-families-real-numbers.html#2754" class="Bound">l2</a><a id="2839" class="Symbol">)</a>
  <a id="2843" class="Keyword">where</a>

  <a id="2852" class="Keyword">abstract</a>
    <a id="2865" href="real-numbers.minimum-finite-families-real-numbers.html#2865" class="Function">is-greatest-lower-bound-min-finite-family-ℝ</a> <a id="2909" class="Symbol">:</a>
      <a id="2917" href="order-theory.greatest-lower-bounds-large-posets.html#1568" class="Function">is-greatest-lower-bound-family-of-elements-Large-Poset</a>
        <a id="2980" class="Symbol">(</a> <a id="2982" href="real-numbers.inequality-real-numbers.html#5939" class="Function">ℝ-Large-Poset</a><a id="2995" class="Symbol">)</a>
        <a id="3005" class="Symbol">(</a> <a id="3007" href="real-numbers.minimum-finite-families-real-numbers.html#2800" class="Bound">x</a><a id="3008" class="Symbol">)</a>
        <a id="3018" class="Symbol">(</a> <a id="3020" href="real-numbers.minimum-finite-families-real-numbers.html#1609" class="Function">min-finite-family-ℝ</a> <a id="3040" href="real-numbers.minimum-finite-families-real-numbers.html#2767" class="Bound">I</a> <a id="3042" href="real-numbers.minimum-finite-families-real-numbers.html#2800" class="Bound">x</a><a id="3043" class="Symbol">)</a>
    <a id="3049" href="real-numbers.minimum-finite-families-real-numbers.html#2865" class="Function">is-greatest-lower-bound-min-finite-family-ℝ</a> <a id="3093" class="Symbol">=</a>
      <a id="3101" href="real-numbers.infima-families-real-numbers.html#4228" class="Function">is-greatest-lower-bound-is-infimum-family-ℝ</a>
        <a id="3153" class="Symbol">(</a> <a id="3155" href="real-numbers.minimum-finite-families-real-numbers.html#2800" class="Bound">x</a><a id="3156" class="Symbol">)</a>
        <a id="3166" class="Symbol">(</a> <a id="3168" href="real-numbers.minimum-finite-families-real-numbers.html#1609" class="Function">min-finite-family-ℝ</a> <a id="3188" href="real-numbers.minimum-finite-families-real-numbers.html#2767" class="Bound">I</a> <a id="3190" href="real-numbers.minimum-finite-families-real-numbers.html#2800" class="Bound">x</a><a id="3191" class="Symbol">)</a>
        <a id="3201" class="Symbol">(</a> <a id="3203" href="real-numbers.minimum-finite-families-real-numbers.html#2380" class="Function">is-infimum-min-finite-family-ℝ</a> <a id="3234" href="real-numbers.minimum-finite-families-real-numbers.html#2767" class="Bound">I</a> <a id="3236" href="real-numbers.minimum-finite-families-real-numbers.html#2800" class="Bound">x</a><a id="3237" class="Symbol">)</a>
</pre>