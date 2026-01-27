# Sequences in partially ordered sets

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="order-theory.sequences-posets.html" class="Module">order-theory.sequences-posets</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="195" class="Keyword">open</a> <a id="200" class="Keyword">import</a> <a id="207" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="440" class="Keyword">open</a> <a id="445" class="Keyword">import</a> <a id="452" href="lists.sequences.html" class="Module">lists.sequences</a>

<a id="469" class="Keyword">open</a> <a id="474" class="Keyword">import</a> <a id="481" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="501" class="Keyword">open</a> <a id="506" class="Keyword">import</a> <a id="513" href="order-theory.sequences-preorders.html" class="Module">order-theory.sequences-preorders</a>
</pre>
</details>

## Idea

A {{#concept "sequence" Disambiguation="in a poset" Agda=sequence-type-Poset}}
in a [poset](order-theory.posets.md) is a [sequence](lists.sequences.md) in its
underlying type.

## Definitions

### Sequences in partially ordered sets

<pre class="Agda"><a id="814" class="Keyword">module</a> <a id="821" href="order-theory.sequences-posets.html#821" class="Module">_</a>
  <a id="825" class="Symbol">{</a><a id="826" href="order-theory.sequences-posets.html#826" class="Bound">l1</a> <a id="829" href="order-theory.sequences-posets.html#829" class="Bound">l2</a> <a id="832" class="Symbol">:</a> <a id="834" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="839" class="Symbol">}</a> <a id="841" class="Symbol">(</a><a id="842" href="order-theory.sequences-posets.html#842" class="Bound">P</a> <a id="844" class="Symbol">:</a> <a id="846" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="852" href="order-theory.sequences-posets.html#826" class="Bound">l1</a> <a id="855" href="order-theory.sequences-posets.html#829" class="Bound">l2</a><a id="857" class="Symbol">)</a>
  <a id="861" class="Keyword">where</a>

  <a id="870" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="890" class="Symbol">:</a> <a id="892" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="895" href="order-theory.sequences-posets.html#826" class="Bound">l1</a>
  <a id="900" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="920" class="Symbol">=</a> <a id="922" href="order-theory.sequences-preorders.html#820" class="Function">sequence-type-Preorder</a> <a id="945" class="Symbol">(</a><a id="946" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="961" href="order-theory.sequences-posets.html#842" class="Bound">P</a><a id="962" class="Symbol">)</a>
</pre>
### Pointwise comparison on sequences in partially ordered sets

<pre class="Agda"><a id="1042" class="Keyword">module</a> <a id="1049" href="order-theory.sequences-posets.html#1049" class="Module">_</a>
  <a id="1053" class="Symbol">{</a><a id="1054" href="order-theory.sequences-posets.html#1054" class="Bound">l1</a> <a id="1057" href="order-theory.sequences-posets.html#1057" class="Bound">l2</a> <a id="1060" class="Symbol">:</a> <a id="1062" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1067" class="Symbol">}</a> <a id="1069" class="Symbol">(</a><a id="1070" href="order-theory.sequences-posets.html#1070" class="Bound">P</a> <a id="1072" class="Symbol">:</a> <a id="1074" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1080" href="order-theory.sequences-posets.html#1054" class="Bound">l1</a> <a id="1083" href="order-theory.sequences-posets.html#1057" class="Bound">l2</a><a id="1085" class="Symbol">)</a>
  <a id="1089" class="Keyword">where</a>

  <a id="1098" href="order-theory.sequences-posets.html#1098" class="Function">leq-value-prop-sequence-Poset</a> <a id="1128" class="Symbol">:</a>
    <a id="1134" class="Symbol">(</a><a id="1135" href="order-theory.sequences-posets.html#1135" class="Bound">u</a> <a id="1137" href="order-theory.sequences-posets.html#1137" class="Bound">v</a> <a id="1139" class="Symbol">:</a> <a id="1141" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="1161" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1162" class="Symbol">)</a> <a id="1164" class="Symbol">→</a> <a id="1166" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1168" class="Symbol">→</a> <a id="1170" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1175" href="order-theory.sequences-posets.html#1057" class="Bound">l2</a>
  <a id="1180" href="order-theory.sequences-posets.html#1098" class="Function">leq-value-prop-sequence-Poset</a> <a id="1210" class="Symbol">=</a>
    <a id="1216" href="order-theory.sequences-preorders.html#1062" class="Function">leq-value-prop-sequence-Preorder</a> <a id="1249" class="Symbol">(</a><a id="1250" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1265" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1266" class="Symbol">)</a>

  <a id="1271" href="order-theory.sequences-posets.html#1271" class="Function">leq-value-sequence-Poset</a> <a id="1296" class="Symbol">:</a>
    <a id="1302" class="Symbol">(</a><a id="1303" href="order-theory.sequences-posets.html#1303" class="Bound">u</a> <a id="1305" href="order-theory.sequences-posets.html#1305" class="Bound">v</a> <a id="1307" class="Symbol">:</a> <a id="1309" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="1329" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1330" class="Symbol">)</a> <a id="1332" class="Symbol">→</a> <a id="1334" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1336" class="Symbol">→</a> <a id="1338" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1341" href="order-theory.sequences-posets.html#1057" class="Bound">l2</a>
  <a id="1346" href="order-theory.sequences-posets.html#1271" class="Function">leq-value-sequence-Poset</a> <a id="1371" class="Symbol">=</a>
    <a id="1377" href="order-theory.sequences-preorders.html#1183" class="Function">leq-value-sequence-Preorder</a> <a id="1405" class="Symbol">(</a><a id="1406" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1421" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1422" class="Symbol">)</a>

  <a id="1427" href="order-theory.sequences-posets.html#1427" class="Function">leq-prop-sequence-Poset</a> <a id="1451" class="Symbol">:</a> <a id="1453" class="Symbol">(</a><a id="1454" href="order-theory.sequences-posets.html#1454" class="Bound">u</a> <a id="1456" href="order-theory.sequences-posets.html#1456" class="Bound">v</a> <a id="1458" class="Symbol">:</a> <a id="1460" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="1480" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1481" class="Symbol">)</a> <a id="1483" class="Symbol">→</a> <a id="1485" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1490" href="order-theory.sequences-posets.html#1057" class="Bound">l2</a>
  <a id="1495" href="order-theory.sequences-posets.html#1427" class="Function">leq-prop-sequence-Poset</a> <a id="1519" class="Symbol">=</a>
    <a id="1525" href="order-theory.sequences-preorders.html#1303" class="Function">leq-prop-sequence-Preorder</a> <a id="1552" class="Symbol">(</a><a id="1553" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1568" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1569" class="Symbol">)</a>

  <a id="1574" href="order-theory.sequences-posets.html#1574" class="Function">leq-sequence-Poset</a> <a id="1593" class="Symbol">:</a> <a id="1595" class="Symbol">(</a><a id="1596" href="order-theory.sequences-posets.html#1596" class="Bound">u</a> <a id="1598" href="order-theory.sequences-posets.html#1598" class="Bound">v</a> <a id="1600" class="Symbol">:</a> <a id="1602" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="1622" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1623" class="Symbol">)</a> <a id="1625" class="Symbol">→</a> <a id="1627" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1630" href="order-theory.sequences-posets.html#1057" class="Bound">l2</a>
  <a id="1635" href="order-theory.sequences-posets.html#1574" class="Function">leq-sequence-Poset</a> <a id="1654" class="Symbol">=</a>
    <a id="1660" href="order-theory.sequences-preorders.html#1416" class="Function">leq-sequence-Preorder</a> <a id="1682" class="Symbol">(</a><a id="1683" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1698" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1699" class="Symbol">)</a>

  <a id="1704" href="order-theory.sequences-posets.html#1704" class="Function">is-prop-leq-sequence-Poset</a> <a id="1731" class="Symbol">:</a>
    <a id="1737" class="Symbol">(</a><a id="1738" href="order-theory.sequences-posets.html#1738" class="Bound">u</a> <a id="1740" href="order-theory.sequences-posets.html#1740" class="Bound">v</a> <a id="1742" class="Symbol">:</a> <a id="1744" href="order-theory.sequences-posets.html#870" class="Function">sequence-type-Poset</a> <a id="1764" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1765" class="Symbol">)</a> <a id="1767" class="Symbol">→</a>
    <a id="1773" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1781" class="Symbol">(</a><a id="1782" href="order-theory.sequences-posets.html#1574" class="Function">leq-sequence-Poset</a> <a id="1801" href="order-theory.sequences-posets.html#1738" class="Bound">u</a> <a id="1803" href="order-theory.sequences-posets.html#1740" class="Bound">v</a><a id="1804" class="Symbol">)</a>
  <a id="1808" href="order-theory.sequences-posets.html#1704" class="Function">is-prop-leq-sequence-Poset</a> <a id="1835" class="Symbol">=</a>
    <a id="1841" href="order-theory.sequences-preorders.html#1512" class="Function">is-prop-leq-sequence-Preorder</a> <a id="1871" class="Symbol">(</a><a id="1872" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1887" href="order-theory.sequences-posets.html#1070" class="Bound">P</a><a id="1888" class="Symbol">)</a>
</pre>
## Properties

### The type of sequences in a poset is a poset ordered by pointwise comparison

<pre class="Agda"><a id="1999" class="Keyword">module</a> <a id="2006" href="order-theory.sequences-posets.html#2006" class="Module">_</a>
  <a id="2010" class="Symbol">{</a><a id="2011" href="order-theory.sequences-posets.html#2011" class="Bound">l1</a> <a id="2014" href="order-theory.sequences-posets.html#2014" class="Bound">l2</a> <a id="2017" class="Symbol">:</a> <a id="2019" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2024" class="Symbol">}</a> <a id="2026" class="Symbol">(</a><a id="2027" href="order-theory.sequences-posets.html#2027" class="Bound">P</a> <a id="2029" class="Symbol">:</a> <a id="2031" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2037" href="order-theory.sequences-posets.html#2011" class="Bound">l1</a> <a id="2040" href="order-theory.sequences-posets.html#2014" class="Bound">l2</a><a id="2042" class="Symbol">)</a>
  <a id="2046" class="Keyword">where</a>

  <a id="2055" href="order-theory.sequences-posets.html#2055" class="Function">antisymmetric-leq-sequence-Poset</a> <a id="2088" class="Symbol">:</a> <a id="2090" href="foundation.binary-relations.html#6436" class="Function">is-antisymmetric</a> <a id="2107" class="Symbol">(</a><a id="2108" href="order-theory.sequences-posets.html#1574" class="Function">leq-sequence-Poset</a> <a id="2127" href="order-theory.sequences-posets.html#2027" class="Bound">P</a><a id="2128" class="Symbol">)</a>
  <a id="2132" href="order-theory.sequences-posets.html#2055" class="Function">antisymmetric-leq-sequence-Poset</a> <a id="2165" href="order-theory.sequences-posets.html#2165" class="Bound">u</a> <a id="2167" href="order-theory.sequences-posets.html#2167" class="Bound">v</a> <a id="2169" href="order-theory.sequences-posets.html#2169" class="Bound">I</a> <a id="2171" href="order-theory.sequences-posets.html#2171" class="Bound">J</a> <a id="2173" class="Symbol">=</a>
    <a id="2179" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a> <a id="2187" class="Symbol">(λ</a> <a id="2190" href="order-theory.sequences-posets.html#2190" class="Bound">n</a> <a id="2192" class="Symbol">→</a> <a id="2194" href="order-theory.posets.html#3131" class="Function">antisymmetric-leq-Poset</a> <a id="2218" href="order-theory.sequences-posets.html#2027" class="Bound">P</a> <a id="2220" class="Symbol">(</a><a id="2221" href="order-theory.sequences-posets.html#2165" class="Bound">u</a> <a id="2223" href="order-theory.sequences-posets.html#2190" class="Bound">n</a><a id="2224" class="Symbol">)</a> <a id="2226" class="Symbol">(</a><a id="2227" href="order-theory.sequences-posets.html#2167" class="Bound">v</a> <a id="2229" href="order-theory.sequences-posets.html#2190" class="Bound">n</a><a id="2230" class="Symbol">)</a> <a id="2232" class="Symbol">(</a><a id="2233" href="order-theory.sequences-posets.html#2169" class="Bound">I</a> <a id="2235" href="order-theory.sequences-posets.html#2190" class="Bound">n</a><a id="2236" class="Symbol">)</a> <a id="2238" class="Symbol">(</a><a id="2239" href="order-theory.sequences-posets.html#2171" class="Bound">J</a> <a id="2241" href="order-theory.sequences-posets.html#2190" class="Bound">n</a><a id="2242" class="Symbol">))</a>

  <a id="2248" href="order-theory.sequences-posets.html#2248" class="Function">sequence-Poset</a> <a id="2263" class="Symbol">:</a> <a id="2265" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2271" href="order-theory.sequences-posets.html#2011" class="Bound">l1</a> <a id="2274" href="order-theory.sequences-posets.html#2014" class="Bound">l2</a>
  <a id="2279" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2283" href="order-theory.sequences-posets.html#2248" class="Function">sequence-Poset</a> <a id="2298" class="Symbol">=</a> <a id="2300" href="order-theory.sequences-preorders.html#2146" class="Function">sequence-Preorder</a> <a id="2318" class="Symbol">(</a><a id="2319" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2334" href="order-theory.sequences-posets.html#2027" class="Bound">P</a><a id="2335" class="Symbol">)</a>
  <a id="2339" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2343" href="order-theory.sequences-posets.html#2248" class="Function">sequence-Poset</a> <a id="2358" class="Symbol">=</a> <a id="2360" href="order-theory.sequences-posets.html#2055" class="Function">antisymmetric-leq-sequence-Poset</a>

  <a id="2396" href="order-theory.sequences-posets.html#2396" class="Function">refl-leq-sequence-Poset</a> <a id="2420" class="Symbol">:</a> <a id="2422" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="2435" class="Symbol">(</a><a id="2436" href="order-theory.sequences-posets.html#1574" class="Function">leq-sequence-Poset</a> <a id="2455" href="order-theory.sequences-posets.html#2027" class="Bound">P</a><a id="2456" class="Symbol">)</a>
  <a id="2460" href="order-theory.sequences-posets.html#2396" class="Function">refl-leq-sequence-Poset</a> <a id="2484" class="Symbol">=</a>
    <a id="2490" href="order-theory.posets.html#2603" class="Function">refl-leq-Poset</a> <a id="2505" href="order-theory.sequences-posets.html#2248" class="Function">sequence-Poset</a>

  <a id="2523" href="order-theory.sequences-posets.html#2523" class="Function">transitive-leq-sequence-Poset</a> <a id="2553" class="Symbol">:</a> <a id="2555" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2569" class="Symbol">(</a><a id="2570" href="order-theory.sequences-posets.html#1574" class="Function">leq-sequence-Poset</a> <a id="2589" href="order-theory.sequences-posets.html#2027" class="Bound">P</a><a id="2590" class="Symbol">)</a>
  <a id="2594" href="order-theory.sequences-posets.html#2523" class="Function">transitive-leq-sequence-Poset</a> <a id="2624" class="Symbol">=</a>
    <a id="2630" href="order-theory.posets.html#2698" class="Function">transitive-leq-Poset</a> <a id="2651" href="order-theory.sequences-posets.html#2248" class="Function">sequence-Poset</a>
</pre>