# Symmetric globular types

<pre class="Agda"><a id="37" class="Symbol">{-#</a> <a id="41" class="Keyword">OPTIONS</a> <a id="49" class="Pragma">--guardedness</a> <a id="63" class="Symbol">#-}</a>

<a id="68" class="Keyword">module</a> <a id="75" href="globular-types.symmetric-globular-types.html" class="Module">globular-types.symmetric-globular-types</a> <a id="115" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

We say a [globular type](globular-types.globular-types.md) is
{{#concept "symmetric" Disambiguation="globular type" Agda=is-symmetric-Globular-Type}}
if there is a symmetry action on its $n$-cells for positive $n$, mapping
$n$-cells from `x` to `y` to $n$-cells from `y` to `x`.

## Definition

### Symmetry structure on a globular type

<pre class="Agda"><a id="747" class="Keyword">record</a>
  <a id="is-symmetric-Globular-Type"></a><a id="756" href="globular-types.symmetric-globular-types.html#756" class="Record">is-symmetric-Globular-Type</a>
    <a id="787" class="Symbol">{</a><a id="788" href="globular-types.symmetric-globular-types.html#788" class="Bound">l1</a> <a id="791" href="globular-types.symmetric-globular-types.html#791" class="Bound">l2</a> <a id="794" class="Symbol">:</a> <a id="796" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="801" class="Symbol">}</a> <a id="803" class="Symbol">(</a><a id="804" href="globular-types.symmetric-globular-types.html#804" class="Bound">G</a> <a id="806" class="Symbol">:</a> <a id="808" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="822" href="globular-types.symmetric-globular-types.html#788" class="Bound">l1</a> <a id="825" href="globular-types.symmetric-globular-types.html#791" class="Bound">l2</a><a id="827" class="Symbol">)</a> <a id="829" class="Symbol">:</a> <a id="831" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="834" class="Symbol">(</a><a id="835" href="globular-types.symmetric-globular-types.html#788" class="Bound">l1</a> <a id="838" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="840" href="globular-types.symmetric-globular-types.html#791" class="Bound">l2</a><a id="842" class="Symbol">)</a>
  <a id="846" class="Keyword">where</a>
  <a id="854" class="Keyword">coinductive</a>

  <a id="869" class="Keyword">field</a>
    <a id="is-symmetric-Globular-Type.is-symmetric-1-cell-is-symmetric-Globular-Type"></a><a id="879" href="globular-types.symmetric-globular-types.html#879" class="Field">is-symmetric-1-cell-is-symmetric-Globular-Type</a> <a id="926" class="Symbol">:</a>
      <a id="934" href="foundation.binary-relations.html#3402" class="Function">is-symmetric</a> <a id="947" class="Symbol">(</a><a id="948" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="969" href="globular-types.symmetric-globular-types.html#804" class="Bound">G</a><a id="970" class="Symbol">)</a>

  <a id="975" class="Keyword">field</a>
    <a id="is-symmetric-Globular-Type.is-symmetric-1-cell-globular-type-is-symmetric-Globular-Type"></a><a id="985" href="globular-types.symmetric-globular-types.html#985" class="Field">is-symmetric-1-cell-globular-type-is-symmetric-Globular-Type</a> <a id="1046" class="Symbol">:</a>
      <a id="1054" class="Symbol">(</a><a id="1055" href="globular-types.symmetric-globular-types.html#1055" class="Bound">x</a> <a id="1057" href="globular-types.symmetric-globular-types.html#1057" class="Bound">y</a> <a id="1059" class="Symbol">:</a> <a id="1061" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1082" href="globular-types.symmetric-globular-types.html#804" class="Bound">G</a><a id="1083" class="Symbol">)</a> <a id="1085" class="Symbol">→</a>
      <a id="1093" href="globular-types.symmetric-globular-types.html#756" class="Record">is-symmetric-Globular-Type</a> <a id="1120" class="Symbol">(</a><a id="1121" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1156" href="globular-types.symmetric-globular-types.html#804" class="Bound">G</a> <a id="1158" href="globular-types.symmetric-globular-types.html#1055" class="Bound">x</a> <a id="1160" href="globular-types.symmetric-globular-types.html#1057" class="Bound">y</a><a id="1161" class="Symbol">)</a>

<a id="1164" class="Keyword">open</a> <a id="1169" href="globular-types.symmetric-globular-types.html#756" class="Module">is-symmetric-Globular-Type</a> <a id="1196" class="Keyword">public</a>
</pre>
### Symmetric globular types

<pre class="Agda"><a id="1246" class="Keyword">record</a>
  <a id="Symmetric-Globular-Type"></a><a id="1255" href="globular-types.symmetric-globular-types.html#1255" class="Record">Symmetric-Globular-Type</a>
    <a id="1283" class="Symbol">(</a><a id="1284" href="globular-types.symmetric-globular-types.html#1284" class="Bound">l1</a> <a id="1287" href="globular-types.symmetric-globular-types.html#1287" class="Bound">l2</a> <a id="1290" class="Symbol">:</a> <a id="1292" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1297" class="Symbol">)</a> <a id="1299" class="Symbol">:</a> <a id="1301" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1304" class="Symbol">(</a><a id="1305" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1310" href="globular-types.symmetric-globular-types.html#1284" class="Bound">l1</a> <a id="1313" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1315" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1320" href="globular-types.symmetric-globular-types.html#1287" class="Bound">l2</a><a id="1322" class="Symbol">)</a>
  <a id="1326" class="Keyword">where</a>

  <a id="1335" class="Keyword">field</a>
    <a id="Symmetric-Globular-Type.globular-type-Symmetric-Globular-Type"></a><a id="1345" href="globular-types.symmetric-globular-types.html#1345" class="Field">globular-type-Symmetric-Globular-Type</a> <a id="1383" class="Symbol">:</a> <a id="1385" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1399" href="globular-types.symmetric-globular-types.html#1284" class="Bound">l1</a> <a id="1402" href="globular-types.symmetric-globular-types.html#1287" class="Bound">l2</a>

  <a id="Symmetric-Globular-Type.0-cell-Symmetric-Globular-Type"></a><a id="1408" href="globular-types.symmetric-globular-types.html#1408" class="Function">0-cell-Symmetric-Globular-Type</a> <a id="1439" class="Symbol">:</a> <a id="1441" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1444" href="globular-types.symmetric-globular-types.html#1284" class="Bound">l1</a>
  <a id="1449" href="globular-types.symmetric-globular-types.html#1408" class="Function">0-cell-Symmetric-Globular-Type</a> <a id="1480" class="Symbol">=</a>
    <a id="1486" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1507" href="globular-types.symmetric-globular-types.html#1345" class="Field">globular-type-Symmetric-Globular-Type</a>

  <a id="Symmetric-Globular-Type.1-cell-globular-type-Symmetric-Globular-Type"></a><a id="1548" href="globular-types.symmetric-globular-types.html#1548" class="Function">1-cell-globular-type-Symmetric-Globular-Type</a> <a id="1593" class="Symbol">:</a>
    <a id="1599" class="Symbol">(</a><a id="1600" href="globular-types.symmetric-globular-types.html#1600" class="Bound">x</a> <a id="1602" href="globular-types.symmetric-globular-types.html#1602" class="Bound">y</a> <a id="1604" class="Symbol">:</a> <a id="1606" href="globular-types.symmetric-globular-types.html#1408" class="Function">0-cell-Symmetric-Globular-Type</a><a id="1636" class="Symbol">)</a> <a id="1638" class="Symbol">→</a>
    <a id="1644" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1658" href="globular-types.symmetric-globular-types.html#1287" class="Bound">l2</a> <a id="1661" href="globular-types.symmetric-globular-types.html#1287" class="Bound">l2</a>
  <a id="1666" href="globular-types.symmetric-globular-types.html#1548" class="Function">1-cell-globular-type-Symmetric-Globular-Type</a> <a id="1711" class="Symbol">=</a>
    <a id="1717" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1752" href="globular-types.symmetric-globular-types.html#1345" class="Field">globular-type-Symmetric-Globular-Type</a>

  <a id="Symmetric-Globular-Type.1-cell-Symmetric-Globular-Type"></a><a id="1793" href="globular-types.symmetric-globular-types.html#1793" class="Function">1-cell-Symmetric-Globular-Type</a> <a id="1824" class="Symbol">:</a>
    <a id="1830" class="Symbol">(</a><a id="1831" href="globular-types.symmetric-globular-types.html#1831" class="Bound">x</a> <a id="1833" href="globular-types.symmetric-globular-types.html#1833" class="Bound">y</a> <a id="1835" class="Symbol">:</a> <a id="1837" href="globular-types.symmetric-globular-types.html#1408" class="Function">0-cell-Symmetric-Globular-Type</a><a id="1867" class="Symbol">)</a> <a id="1869" class="Symbol">→</a> <a id="1871" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1874" href="globular-types.symmetric-globular-types.html#1287" class="Bound">l2</a>
  <a id="1879" href="globular-types.symmetric-globular-types.html#1793" class="Function">1-cell-Symmetric-Globular-Type</a> <a id="1910" class="Symbol">=</a>
    <a id="1916" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="1937" href="globular-types.symmetric-globular-types.html#1345" class="Field">globular-type-Symmetric-Globular-Type</a>

  <a id="1978" class="Keyword">field</a>
    <a id="Symmetric-Globular-Type.is-symmetric-Symmetric-Globular-Type"></a><a id="1988" href="globular-types.symmetric-globular-types.html#1988" class="Field">is-symmetric-Symmetric-Globular-Type</a> <a id="2025" class="Symbol">:</a>
      <a id="2033" href="globular-types.symmetric-globular-types.html#756" class="Record">is-symmetric-Globular-Type</a> <a id="2060" href="globular-types.symmetric-globular-types.html#1345" class="Field">globular-type-Symmetric-Globular-Type</a>

  <a id="Symmetric-Globular-Type.inv-1-cell-Symmetric-Globular-Type"></a><a id="2101" href="globular-types.symmetric-globular-types.html#2101" class="Function">inv-1-cell-Symmetric-Globular-Type</a> <a id="2136" class="Symbol">:</a>
    <a id="2142" class="Symbol">{</a><a id="2143" href="globular-types.symmetric-globular-types.html#2143" class="Bound">x</a> <a id="2145" href="globular-types.symmetric-globular-types.html#2145" class="Bound">y</a> <a id="2147" class="Symbol">:</a> <a id="2149" href="globular-types.symmetric-globular-types.html#1408" class="Function">0-cell-Symmetric-Globular-Type</a><a id="2179" class="Symbol">}</a> <a id="2181" class="Symbol">→</a>
    <a id="2187" href="globular-types.symmetric-globular-types.html#1793" class="Function">1-cell-Symmetric-Globular-Type</a> <a id="2218" href="globular-types.symmetric-globular-types.html#2143" class="Bound">x</a> <a id="2220" href="globular-types.symmetric-globular-types.html#2145" class="Bound">y</a> <a id="2222" class="Symbol">→</a> <a id="2224" href="globular-types.symmetric-globular-types.html#1793" class="Function">1-cell-Symmetric-Globular-Type</a> <a id="2255" href="globular-types.symmetric-globular-types.html#2145" class="Bound">y</a> <a id="2257" href="globular-types.symmetric-globular-types.html#2143" class="Bound">x</a>
  <a id="2261" href="globular-types.symmetric-globular-types.html#2101" class="Function">inv-1-cell-Symmetric-Globular-Type</a> <a id="2296" class="Symbol">=</a>
    <a id="2302" href="globular-types.symmetric-globular-types.html#879" class="Field">is-symmetric-1-cell-is-symmetric-Globular-Type</a>
      <a id="2355" href="globular-types.symmetric-globular-types.html#1988" class="Field">is-symmetric-Symmetric-Globular-Type</a>
      <a id="2398" class="Symbol">_</a>
      <a id="2406" class="Symbol">_</a>

  <a id="Symmetric-Globular-Type.is-symmetric-1-cell-globular-type-Symmetric-Globular-Type"></a><a id="2411" href="globular-types.symmetric-globular-types.html#2411" class="Function">is-symmetric-1-cell-globular-type-Symmetric-Globular-Type</a> <a id="2469" class="Symbol">:</a>
    <a id="2475" class="Symbol">(</a><a id="2476" href="globular-types.symmetric-globular-types.html#2476" class="Bound">x</a> <a id="2478" href="globular-types.symmetric-globular-types.html#2478" class="Bound">y</a> <a id="2480" class="Symbol">:</a> <a id="2482" href="globular-types.symmetric-globular-types.html#1408" class="Function">0-cell-Symmetric-Globular-Type</a><a id="2512" class="Symbol">)</a> <a id="2514" class="Symbol">→</a>
    <a id="2520" href="globular-types.symmetric-globular-types.html#756" class="Record">is-symmetric-Globular-Type</a>
      <a id="2553" class="Symbol">(</a> <a id="2555" href="globular-types.symmetric-globular-types.html#1548" class="Function">1-cell-globular-type-Symmetric-Globular-Type</a> <a id="2600" href="globular-types.symmetric-globular-types.html#2476" class="Bound">x</a> <a id="2602" href="globular-types.symmetric-globular-types.html#2478" class="Bound">y</a><a id="2603" class="Symbol">)</a>
  <a id="2607" href="globular-types.symmetric-globular-types.html#2411" class="Function">is-symmetric-1-cell-globular-type-Symmetric-Globular-Type</a> <a id="2665" class="Symbol">=</a>
    <a id="2671" href="globular-types.symmetric-globular-types.html#985" class="Field">is-symmetric-1-cell-globular-type-is-symmetric-Globular-Type</a>
      <a id="2738" href="globular-types.symmetric-globular-types.html#1988" class="Field">is-symmetric-Symmetric-Globular-Type</a>

  <a id="Symmetric-Globular-Type.1-cell-symmetric-globular-type-Symmetric-Globular-Type"></a><a id="2778" href="globular-types.symmetric-globular-types.html#2778" class="Function">1-cell-symmetric-globular-type-Symmetric-Globular-Type</a> <a id="2833" class="Symbol">:</a>
    <a id="2839" class="Symbol">(</a><a id="2840" href="globular-types.symmetric-globular-types.html#2840" class="Bound">x</a> <a id="2842" href="globular-types.symmetric-globular-types.html#2842" class="Bound">y</a> <a id="2844" class="Symbol">:</a> <a id="2846" href="globular-types.symmetric-globular-types.html#1408" class="Function">0-cell-Symmetric-Globular-Type</a><a id="2876" class="Symbol">)</a> <a id="2878" class="Symbol">→</a>
    <a id="2884" href="globular-types.symmetric-globular-types.html#1255" class="Record">Symmetric-Globular-Type</a> <a id="2908" href="globular-types.symmetric-globular-types.html#1287" class="Bound">l2</a> <a id="2911" href="globular-types.symmetric-globular-types.html#1287" class="Bound">l2</a>
  <a id="2916" href="globular-types.symmetric-globular-types.html#1345" class="Field">globular-type-Symmetric-Globular-Type</a>
    <a id="2958" class="Symbol">(</a> <a id="2960" href="globular-types.symmetric-globular-types.html#2778" class="Function">1-cell-symmetric-globular-type-Symmetric-Globular-Type</a> <a id="3015" href="globular-types.symmetric-globular-types.html#3015" class="Bound">x</a> <a id="3017" href="globular-types.symmetric-globular-types.html#3017" class="Bound">y</a><a id="3018" class="Symbol">)</a> <a id="3020" class="Symbol">=</a>
    <a id="3026" href="globular-types.symmetric-globular-types.html#1548" class="Function">1-cell-globular-type-Symmetric-Globular-Type</a> <a id="3071" href="globular-types.symmetric-globular-types.html#3015" class="Bound">x</a> <a id="3073" href="globular-types.symmetric-globular-types.html#3017" class="Bound">y</a>
  <a id="3077" href="globular-types.symmetric-globular-types.html#1988" class="Field">is-symmetric-Symmetric-Globular-Type</a>
    <a id="3118" class="Symbol">(</a> <a id="3120" href="globular-types.symmetric-globular-types.html#2778" class="Function">1-cell-symmetric-globular-type-Symmetric-Globular-Type</a> <a id="3175" href="globular-types.symmetric-globular-types.html#3175" class="Bound">x</a> <a id="3177" href="globular-types.symmetric-globular-types.html#3177" class="Bound">y</a><a id="3178" class="Symbol">)</a> <a id="3180" class="Symbol">=</a>
    <a id="3186" href="globular-types.symmetric-globular-types.html#2411" class="Function">is-symmetric-1-cell-globular-type-Symmetric-Globular-Type</a> <a id="3244" href="globular-types.symmetric-globular-types.html#3175" class="Bound">x</a> <a id="3246" href="globular-types.symmetric-globular-types.html#3177" class="Bound">y</a>

<a id="3249" class="Keyword">open</a> <a id="3254" href="globular-types.symmetric-globular-types.html#1255" class="Module">Symmetric-Globular-Type</a> <a id="3278" class="Keyword">public</a>
</pre>