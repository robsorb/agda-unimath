# The negation isometry on real numbers

<pre class="Agda"><a id="50" class="Symbol">{-#</a> <a id="54" class="Keyword">OPTIONS</a> <a id="62" class="Pragma">--lossy-unification</a> <a id="82" class="Symbol">#-}</a>

<a id="87" class="Keyword">module</a> <a id="94" href="real-numbers.isometry-negation-real-numbers.html" class="Module">real-numbers.isometry-negation-real-numbers</a> <a id="138" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>

<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.binary-transport.html" class="Module">foundation.binary-transport</a>
<a id="298" class="Keyword">open</a> <a id="303" class="Keyword">import</a> <a id="310" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="458" class="Keyword">open</a> <a id="463" class="Keyword">import</a> <a id="470" href="metric-spaces.isometries-metric-spaces.html" class="Module">metric-spaces.isometries-metric-spaces</a>
<a id="509" class="Keyword">open</a> <a id="514" class="Keyword">import</a> <a id="521" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>

<a id="550" class="Keyword">open</a> <a id="555" class="Keyword">import</a> <a id="562" href="real-numbers.dedekind-real-numbers.html" class="Module">real-numbers.dedekind-real-numbers</a>
<a id="597" class="Keyword">open</a> <a id="602" class="Keyword">import</a> <a id="609" href="real-numbers.inequality-real-numbers.html" class="Module">real-numbers.inequality-real-numbers</a>
<a id="646" class="Keyword">open</a> <a id="651" class="Keyword">import</a> <a id="658" href="real-numbers.metric-space-of-real-numbers.html" class="Module">real-numbers.metric-space-of-real-numbers</a>
<a id="700" class="Keyword">open</a> <a id="705" class="Keyword">import</a> <a id="712" href="real-numbers.negation-real-numbers.html" class="Module">real-numbers.negation-real-numbers</a>
</pre>
</details>

## Idea

[Negation](real-numbers.negation-real-numbers.md) of real numbers is an
[isometry](metric-spaces.isometries-metric-spaces.md) of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definitions

### Negation of a real number preserves neighborhoods

<pre class="Agda"><a id="1064" class="Keyword">module</a> <a id="1071" href="real-numbers.isometry-negation-real-numbers.html#1071" class="Module">_</a>
  <a id="1075" class="Symbol">{</a><a id="1076" href="real-numbers.isometry-negation-real-numbers.html#1076" class="Bound">l1</a> <a id="1079" class="Symbol">:</a> <a id="1081" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1086" class="Symbol">}</a>
  <a id="1090" class="Keyword">where</a>

  <a id="1099" class="Keyword">abstract</a>
    <a id="1112" href="real-numbers.isometry-negation-real-numbers.html#1112" class="Function">neg-neighborhood-ℝ</a> <a id="1131" class="Symbol">:</a> <a id="1133" class="Symbol">(</a><a id="1134" href="real-numbers.isometry-negation-real-numbers.html#1134" class="Bound">d</a> <a id="1136" class="Symbol">:</a> <a id="1138" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a><a id="1140" class="Symbol">)</a> <a id="1142" class="Symbol">(</a><a id="1143" href="real-numbers.isometry-negation-real-numbers.html#1143" class="Bound">x</a> <a id="1145" href="real-numbers.isometry-negation-real-numbers.html#1145" class="Bound">y</a> <a id="1147" class="Symbol">:</a> <a id="1149" href="real-numbers.dedekind-real-numbers.html#4019" class="Function">ℝ</a> <a id="1151" href="real-numbers.isometry-negation-real-numbers.html#1076" class="Bound">l1</a><a id="1153" class="Symbol">)</a> <a id="1155" class="Symbol">→</a>
      <a id="1163" href="real-numbers.metric-space-of-real-numbers.html#3296" class="Function">neighborhood-ℝ</a> <a id="1178" href="real-numbers.isometry-negation-real-numbers.html#1076" class="Bound">l1</a> <a id="1181" href="real-numbers.isometry-negation-real-numbers.html#1134" class="Bound">d</a> <a id="1183" href="real-numbers.isometry-negation-real-numbers.html#1143" class="Bound">x</a> <a id="1185" href="real-numbers.isometry-negation-real-numbers.html#1145" class="Bound">y</a> <a id="1187" class="Symbol">→</a>
      <a id="1195" href="real-numbers.metric-space-of-real-numbers.html#3296" class="Function">neighborhood-ℝ</a> <a id="1210" href="real-numbers.isometry-negation-real-numbers.html#1076" class="Bound">l1</a> <a id="1213" href="real-numbers.isometry-negation-real-numbers.html#1134" class="Bound">d</a> <a id="1215" class="Symbol">(</a><a id="1216" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="1222" href="real-numbers.isometry-negation-real-numbers.html#1143" class="Bound">x</a><a id="1223" class="Symbol">)</a> <a id="1225" class="Symbol">(</a><a id="1226" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="1232" href="real-numbers.isometry-negation-real-numbers.html#1145" class="Bound">y</a><a id="1233" class="Symbol">)</a>
    <a id="1239" href="real-numbers.isometry-negation-real-numbers.html#1112" class="Function">neg-neighborhood-ℝ</a> <a id="1258" href="real-numbers.isometry-negation-real-numbers.html#1258" class="Bound">d</a> <a id="1260" href="real-numbers.isometry-negation-real-numbers.html#1260" class="Bound">x</a> <a id="1262" href="real-numbers.isometry-negation-real-numbers.html#1262" class="Bound">y</a> <a id="1264" href="real-numbers.isometry-negation-real-numbers.html#1264" class="Bound">H</a> <a id="1266" class="Symbol">=</a>
      <a id="1274" href="real-numbers.metric-space-of-real-numbers.html#10249" class="Function">neighborhood-real-bound-each-leq-ℝ</a>
        <a id="1317" class="Symbol">(</a> <a id="1319" href="real-numbers.isometry-negation-real-numbers.html#1258" class="Bound">d</a><a id="1320" class="Symbol">)</a>
        <a id="1330" class="Symbol">(</a> <a id="1332" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="1338" href="real-numbers.isometry-negation-real-numbers.html#1260" class="Bound">x</a><a id="1339" class="Symbol">)</a>
        <a id="1349" class="Symbol">(</a> <a id="1351" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="1357" href="real-numbers.isometry-negation-real-numbers.html#1262" class="Bound">y</a><a id="1358" class="Symbol">)</a>
        <a id="1368" class="Symbol">(</a> <a id="1370" href="real-numbers.inequality-real-numbers.html#14516" class="Function">reverses-lower-neighborhood-neg-ℝ</a>
          <a id="1414" class="Symbol">(</a> <a id="1416" href="real-numbers.isometry-negation-real-numbers.html#1258" class="Bound">d</a><a id="1417" class="Symbol">)</a>
          <a id="1429" class="Symbol">(</a> <a id="1431" href="real-numbers.isometry-negation-real-numbers.html#1262" class="Bound">y</a><a id="1432" class="Symbol">)</a>
          <a id="1444" class="Symbol">(</a> <a id="1446" href="real-numbers.isometry-negation-real-numbers.html#1260" class="Bound">x</a><a id="1447" class="Symbol">)</a>
          <a id="1459" class="Symbol">(</a> <a id="1461" href="real-numbers.metric-space-of-real-numbers.html#10752" class="Function">right-leq-real-bound-neighborhood-ℝ</a> <a id="1497" href="real-numbers.isometry-negation-real-numbers.html#1258" class="Bound">d</a> <a id="1499" href="real-numbers.isometry-negation-real-numbers.html#1260" class="Bound">x</a> <a id="1501" href="real-numbers.isometry-negation-real-numbers.html#1262" class="Bound">y</a> <a id="1503" href="real-numbers.isometry-negation-real-numbers.html#1264" class="Bound">H</a><a id="1504" class="Symbol">))</a>
        <a id="1515" class="Symbol">(</a> <a id="1517" href="real-numbers.inequality-real-numbers.html#14516" class="Function">reverses-lower-neighborhood-neg-ℝ</a>
          <a id="1561" class="Symbol">(</a> <a id="1563" href="real-numbers.isometry-negation-real-numbers.html#1258" class="Bound">d</a><a id="1564" class="Symbol">)</a>
          <a id="1576" class="Symbol">(</a> <a id="1578" href="real-numbers.isometry-negation-real-numbers.html#1260" class="Bound">x</a><a id="1579" class="Symbol">)</a>
          <a id="1591" class="Symbol">(</a> <a id="1593" href="real-numbers.isometry-negation-real-numbers.html#1262" class="Bound">y</a><a id="1594" class="Symbol">)</a>
          <a id="1606" class="Symbol">(</a> <a id="1608" href="real-numbers.metric-space-of-real-numbers.html#10555" class="Function">left-leq-real-bound-neighborhood-ℝ</a> <a id="1643" href="real-numbers.isometry-negation-real-numbers.html#1258" class="Bound">d</a> <a id="1645" href="real-numbers.isometry-negation-real-numbers.html#1260" class="Bound">x</a> <a id="1647" href="real-numbers.isometry-negation-real-numbers.html#1262" class="Bound">y</a> <a id="1649" href="real-numbers.isometry-negation-real-numbers.html#1264" class="Bound">H</a><a id="1650" class="Symbol">))</a>
</pre>
### Negation on the real numbers is an isometry

<pre class="Agda"><a id="1715" class="Keyword">module</a> <a id="1722" href="real-numbers.isometry-negation-real-numbers.html#1722" class="Module">_</a>
  <a id="1726" class="Symbol">{</a><a id="1727" href="real-numbers.isometry-negation-real-numbers.html#1727" class="Bound">l1</a> <a id="1730" class="Symbol">:</a> <a id="1732" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1737" class="Symbol">}</a>
  <a id="1741" class="Keyword">where</a>

  <a id="1750" class="Keyword">abstract</a>
    <a id="1763" href="real-numbers.isometry-negation-real-numbers.html#1763" class="Function">is-isometry-neg-ℝ</a> <a id="1781" class="Symbol">:</a>
      <a id="1789" href="metric-spaces.isometries-metric-spaces.html#2158" class="Function">is-isometry-Metric-Space</a>
        <a id="1822" class="Symbol">(</a> <a id="1824" href="real-numbers.metric-space-of-real-numbers.html#8513" class="Function">metric-space-ℝ</a> <a id="1839" href="real-numbers.isometry-negation-real-numbers.html#1727" class="Bound">l1</a><a id="1841" class="Symbol">)</a>
        <a id="1851" class="Symbol">(</a> <a id="1853" href="real-numbers.metric-space-of-real-numbers.html#8513" class="Function">metric-space-ℝ</a> <a id="1868" href="real-numbers.isometry-negation-real-numbers.html#1727" class="Bound">l1</a><a id="1870" class="Symbol">)</a>
        <a id="1880" class="Symbol">(</a> <a id="1882" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a><a id="1887" class="Symbol">)</a>
    <a id="1893" href="real-numbers.isometry-negation-real-numbers.html#1763" class="Function">is-isometry-neg-ℝ</a> <a id="1911" href="real-numbers.isometry-negation-real-numbers.html#1911" class="Bound">d</a> <a id="1913" href="real-numbers.isometry-negation-real-numbers.html#1913" class="Bound">x</a> <a id="1915" href="real-numbers.isometry-negation-real-numbers.html#1915" class="Bound">y</a> <a id="1917" class="Symbol">=</a>
      <a id="1925" class="Symbol">(</a> <a id="1927" href="real-numbers.isometry-negation-real-numbers.html#1112" class="Function">neg-neighborhood-ℝ</a> <a id="1946" href="real-numbers.isometry-negation-real-numbers.html#1911" class="Bound">d</a> <a id="1948" href="real-numbers.isometry-negation-real-numbers.html#1913" class="Bound">x</a> <a id="1950" href="real-numbers.isometry-negation-real-numbers.html#1915" class="Bound">y</a><a id="1951" class="Symbol">)</a> <a id="1953" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="1961" class="Symbol">(</a> <a id="1963" class="Symbol">(</a> <a id="1965" href="foundation.binary-transport.html#801" class="Function">binary-tr</a>
          <a id="1985" class="Symbol">(</a> <a id="1987" href="real-numbers.metric-space-of-real-numbers.html#3296" class="Function">neighborhood-ℝ</a> <a id="2002" href="real-numbers.isometry-negation-real-numbers.html#1727" class="Bound">l1</a> <a id="2005" href="real-numbers.isometry-negation-real-numbers.html#1911" class="Bound">d</a><a id="2006" class="Symbol">)</a>
          <a id="2018" class="Symbol">(</a> <a id="2020" href="real-numbers.negation-real-numbers.html#3138" class="Function">neg-neg-ℝ</a> <a id="2030" href="real-numbers.isometry-negation-real-numbers.html#1913" class="Bound">x</a><a id="2031" class="Symbol">)</a>
          <a id="2043" class="Symbol">(</a> <a id="2045" href="real-numbers.negation-real-numbers.html#3138" class="Function">neg-neg-ℝ</a> <a id="2055" href="real-numbers.isometry-negation-real-numbers.html#1915" class="Bound">y</a><a id="2056" class="Symbol">))</a> <a id="2059" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
        <a id="2069" class="Symbol">(</a> <a id="2071" href="real-numbers.isometry-negation-real-numbers.html#1112" class="Function">neg-neighborhood-ℝ</a>
          <a id="2100" class="Symbol">(</a> <a id="2102" href="real-numbers.isometry-negation-real-numbers.html#1911" class="Bound">d</a><a id="2103" class="Symbol">)</a>
          <a id="2115" class="Symbol">(</a> <a id="2117" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="2123" href="real-numbers.isometry-negation-real-numbers.html#1913" class="Bound">x</a><a id="2124" class="Symbol">)</a>
          <a id="2136" class="Symbol">(</a> <a id="2138" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="2144" href="real-numbers.isometry-negation-real-numbers.html#1915" class="Bound">y</a><a id="2145" class="Symbol">)))</a>

  <a id="2152" href="real-numbers.isometry-negation-real-numbers.html#2152" class="Function">isometry-neg-ℝ</a> <a id="2167" class="Symbol">:</a>
    <a id="2173" href="metric-spaces.isometries-metric-spaces.html#2787" class="Function">isometry-Metric-Space</a>
      <a id="2201" class="Symbol">(</a> <a id="2203" href="real-numbers.metric-space-of-real-numbers.html#8513" class="Function">metric-space-ℝ</a> <a id="2218" href="real-numbers.isometry-negation-real-numbers.html#1727" class="Bound">l1</a><a id="2220" class="Symbol">)</a>
      <a id="2228" class="Symbol">(</a> <a id="2230" href="real-numbers.metric-space-of-real-numbers.html#8513" class="Function">metric-space-ℝ</a> <a id="2245" href="real-numbers.isometry-negation-real-numbers.html#1727" class="Bound">l1</a><a id="2247" class="Symbol">)</a>
  <a id="2251" href="real-numbers.isometry-negation-real-numbers.html#2152" class="Function">isometry-neg-ℝ</a> <a id="2266" class="Symbol">=</a> <a id="2268" class="Symbol">(</a><a id="2269" href="real-numbers.negation-real-numbers.html#2840" class="Function">neg-ℝ</a> <a id="2275" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2277" href="real-numbers.isometry-negation-real-numbers.html#1763" class="Function">is-isometry-neg-ℝ</a><a id="2294" class="Symbol">)</a>
</pre>