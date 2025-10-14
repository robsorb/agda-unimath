# Subfinite types

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="univalent-combinatorics.subfinite-types.html" class="Module">univalent-combinatorics.subfinite-types</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="foundation.discrete-types.html" class="Module">foundation.discrete-types</a>
<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="466" class="Keyword">open</a> <a id="471" class="Keyword">import</a> <a id="478" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="502" class="Keyword">open</a> <a id="507" class="Keyword">import</a> <a id="514" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="530" class="Keyword">open</a> <a id="535" class="Keyword">import</a> <a id="542" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="570" class="Keyword">open</a> <a id="575" class="Keyword">import</a> <a id="582" href="univalent-combinatorics.dedekind-finite-types.html" class="Module">univalent-combinatorics.dedekind-finite-types</a>
<a id="628" class="Keyword">open</a> <a id="633" class="Keyword">import</a> <a id="640" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a>
<a id="695" class="Keyword">open</a> <a id="700" class="Keyword">import</a> <a id="707" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
<a id="753" class="Keyword">open</a> <a id="758" class="Keyword">import</a> <a id="765" href="univalent-combinatorics.subcounting.html" class="Module">univalent-combinatorics.subcounting</a>
</pre>
</details>

## Idea

A type `X` is {{#concept "subfinite" Agda=is-subfinite Agda=Subfinite-Type}} if
there [exists](foundation.existential-quantification.md) an
[embedding](foundation-core.embeddings.md) into a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definitions

### The predicate of being subfinite

<pre class="Agda"><a id="is-subfinite-Prop"></a><a id="1154" href="univalent-combinatorics.subfinite-types.html#1154" class="Function">is-subfinite-Prop</a> <a id="1172" class="Symbol">:</a> <a id="1174" class="Symbol">{</a><a id="1175" href="univalent-combinatorics.subfinite-types.html#1175" class="Bound">l</a> <a id="1177" class="Symbol">:</a> <a id="1179" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1184" class="Symbol">}</a> <a id="1186" class="Symbol">→</a> <a id="1188" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1191" href="univalent-combinatorics.subfinite-types.html#1175" class="Bound">l</a> <a id="1193" class="Symbol">→</a> <a id="1195" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1200" href="univalent-combinatorics.subfinite-types.html#1175" class="Bound">l</a>
<a id="1202" href="univalent-combinatorics.subfinite-types.html#1154" class="Function">is-subfinite-Prop</a> <a id="1220" href="univalent-combinatorics.subfinite-types.html#1220" class="Bound">X</a> <a id="1222" class="Symbol">=</a> <a id="1224" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="1235" class="Symbol">(</a><a id="1236" href="univalent-combinatorics.subcounting.html#1878" class="Function">subcount</a> <a id="1245" href="univalent-combinatorics.subfinite-types.html#1220" class="Bound">X</a><a id="1246" class="Symbol">)</a>

<a id="is-subfinite"></a><a id="1249" href="univalent-combinatorics.subfinite-types.html#1249" class="Function">is-subfinite</a> <a id="1262" class="Symbol">:</a> <a id="1264" class="Symbol">{</a><a id="1265" href="univalent-combinatorics.subfinite-types.html#1265" class="Bound">l</a> <a id="1267" class="Symbol">:</a> <a id="1269" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1274" class="Symbol">}</a> <a id="1276" class="Symbol">→</a> <a id="1278" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1281" href="univalent-combinatorics.subfinite-types.html#1265" class="Bound">l</a> <a id="1283" class="Symbol">→</a> <a id="1285" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1288" href="univalent-combinatorics.subfinite-types.html#1265" class="Bound">l</a>
<a id="1290" href="univalent-combinatorics.subfinite-types.html#1249" class="Function">is-subfinite</a> <a id="1303" href="univalent-combinatorics.subfinite-types.html#1303" class="Bound">X</a> <a id="1305" class="Symbol">=</a> <a id="1307" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1317" class="Symbol">(</a><a id="1318" href="univalent-combinatorics.subfinite-types.html#1154" class="Function">is-subfinite-Prop</a> <a id="1336" href="univalent-combinatorics.subfinite-types.html#1303" class="Bound">X</a><a id="1337" class="Symbol">)</a>

<a id="is-prop-is-subfinite"></a><a id="1340" href="univalent-combinatorics.subfinite-types.html#1340" class="Function">is-prop-is-subfinite</a> <a id="1361" class="Symbol">:</a> <a id="1363" class="Symbol">{</a><a id="1364" href="univalent-combinatorics.subfinite-types.html#1364" class="Bound">l</a> <a id="1366" class="Symbol">:</a> <a id="1368" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1373" class="Symbol">}</a> <a id="1375" class="Symbol">{</a><a id="1376" href="univalent-combinatorics.subfinite-types.html#1376" class="Bound">X</a> <a id="1378" class="Symbol">:</a> <a id="1380" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1383" href="univalent-combinatorics.subfinite-types.html#1364" class="Bound">l</a><a id="1384" class="Symbol">}</a> <a id="1386" class="Symbol">→</a> <a id="1388" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1396" class="Symbol">(</a><a id="1397" href="univalent-combinatorics.subfinite-types.html#1249" class="Function">is-subfinite</a> <a id="1410" href="univalent-combinatorics.subfinite-types.html#1376" class="Bound">X</a><a id="1411" class="Symbol">)</a>
<a id="1413" href="univalent-combinatorics.subfinite-types.html#1340" class="Function">is-prop-is-subfinite</a> <a id="1434" class="Symbol">{</a><a id="1435" class="Argument">X</a> <a id="1437" class="Symbol">=</a> <a id="1439" href="univalent-combinatorics.subfinite-types.html#1439" class="Bound">X</a><a id="1440" class="Symbol">}</a> <a id="1442" class="Symbol">=</a> <a id="1444" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1462" class="Symbol">(</a><a id="1463" href="univalent-combinatorics.subfinite-types.html#1154" class="Function">is-subfinite-Prop</a> <a id="1481" href="univalent-combinatorics.subfinite-types.html#1439" class="Bound">X</a><a id="1482" class="Symbol">)</a>
</pre>
### The subuniverse of subfinite types

<pre class="Agda"><a id="Subfinite-Type"></a><a id="1537" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="1552" class="Symbol">:</a> <a id="1554" class="Symbol">(</a><a id="1555" href="univalent-combinatorics.subfinite-types.html#1555" class="Bound">l</a> <a id="1557" class="Symbol">:</a> <a id="1559" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1564" class="Symbol">)</a> <a id="1566" class="Symbol">→</a> <a id="1568" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1571" class="Symbol">(</a><a id="1572" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1577" href="univalent-combinatorics.subfinite-types.html#1555" class="Bound">l</a><a id="1578" class="Symbol">)</a>
<a id="1580" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="1595" href="univalent-combinatorics.subfinite-types.html#1595" class="Bound">l</a> <a id="1597" class="Symbol">=</a> <a id="1599" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1601" class="Symbol">(</a><a id="1602" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1605" href="univalent-combinatorics.subfinite-types.html#1595" class="Bound">l</a><a id="1606" class="Symbol">)</a> <a id="1608" class="Symbol">(</a><a id="1609" href="univalent-combinatorics.subfinite-types.html#1249" class="Function">is-subfinite</a><a id="1621" class="Symbol">)</a>

<a id="1624" class="Keyword">module</a> <a id="1631" href="univalent-combinatorics.subfinite-types.html#1631" class="Module">_</a>
  <a id="1635" class="Symbol">{</a><a id="1636" href="univalent-combinatorics.subfinite-types.html#1636" class="Bound">l</a> <a id="1638" class="Symbol">:</a> <a id="1640" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1645" class="Symbol">}</a> <a id="1647" class="Symbol">(</a><a id="1648" href="univalent-combinatorics.subfinite-types.html#1648" class="Bound">X</a> <a id="1650" class="Symbol">:</a> <a id="1652" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="1667" href="univalent-combinatorics.subfinite-types.html#1636" class="Bound">l</a><a id="1668" class="Symbol">)</a>
  <a id="1672" class="Keyword">where</a>

  <a id="1681" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="1701" class="Symbol">:</a> <a id="1703" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1706" href="univalent-combinatorics.subfinite-types.html#1636" class="Bound">l</a>
  <a id="1710" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="1730" class="Symbol">=</a> <a id="1732" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1736" href="univalent-combinatorics.subfinite-types.html#1648" class="Bound">X</a>

  <a id="1741" href="univalent-combinatorics.subfinite-types.html#1741" class="Function">is-subfinite-type-Subfinite-Type</a> <a id="1774" class="Symbol">:</a> <a id="1776" href="univalent-combinatorics.subfinite-types.html#1249" class="Function">is-subfinite</a> <a id="1789" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a>
  <a id="1811" href="univalent-combinatorics.subfinite-types.html#1741" class="Function">is-subfinite-type-Subfinite-Type</a> <a id="1844" class="Symbol">=</a> <a id="1846" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1850" href="univalent-combinatorics.subfinite-types.html#1648" class="Bound">X</a>
</pre>
## Properties

### The standard finite types are subfinite

<pre class="Agda"><a id="Fin-Subfinite-Type"></a><a id="1925" href="univalent-combinatorics.subfinite-types.html#1925" class="Function">Fin-Subfinite-Type</a> <a id="1944" class="Symbol">:</a> <a id="1946" class="Symbol">(</a><a id="1947" href="univalent-combinatorics.subfinite-types.html#1947" class="Bound">n</a> <a id="1949" class="Symbol">:</a> <a id="1951" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1952" class="Symbol">)</a> <a id="1954" class="Symbol">→</a> <a id="1956" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="1971" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1977" href="univalent-combinatorics.subfinite-types.html#1925" class="Function">Fin-Subfinite-Type</a> <a id="1996" href="univalent-combinatorics.subfinite-types.html#1996" class="Bound">n</a> <a id="1998" class="Symbol">=</a> <a id="2000" class="Symbol">(</a><a id="2001" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="2005" href="univalent-combinatorics.subfinite-types.html#1996" class="Bound">n</a> <a id="2007" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2009" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="2025" class="Symbol">(</a><a id="2026" href="univalent-combinatorics.subcounting.html#3088" class="Function">subcount-Fin</a> <a id="2039" href="univalent-combinatorics.subfinite-types.html#1996" class="Bound">n</a><a id="2040" class="Symbol">))</a>
</pre>
### Subfinite types are discrete

<pre class="Agda"><a id="2090" class="Keyword">module</a> <a id="2097" href="univalent-combinatorics.subfinite-types.html#2097" class="Module">_</a>
  <a id="2101" class="Symbol">{</a><a id="2102" href="univalent-combinatorics.subfinite-types.html#2102" class="Bound">l</a> <a id="2104" class="Symbol">:</a> <a id="2106" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2111" class="Symbol">}</a> <a id="2113" class="Symbol">(</a><a id="2114" href="univalent-combinatorics.subfinite-types.html#2114" class="Bound">X</a> <a id="2116" class="Symbol">:</a> <a id="2118" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="2133" href="univalent-combinatorics.subfinite-types.html#2102" class="Bound">l</a><a id="2134" class="Symbol">)</a>
  <a id="2138" class="Keyword">where</a>

  <a id="2147" href="univalent-combinatorics.subfinite-types.html#2147" class="Function">has-decidable-equality-type-Subfinite-Type</a> <a id="2190" class="Symbol">:</a>
    <a id="2196" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="2219" class="Symbol">(</a><a id="2220" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="2240" href="univalent-combinatorics.subfinite-types.html#2114" class="Bound">X</a><a id="2241" class="Symbol">)</a>
  <a id="2245" href="univalent-combinatorics.subfinite-types.html#2147" class="Function">has-decidable-equality-type-Subfinite-Type</a> <a id="2288" class="Symbol">=</a>
    <a id="2294" href="foundation.propositional-truncations.html#4671" class="Function">rec-trunc-Prop</a>
      <a id="2315" class="Symbol">(</a> <a id="2317" href="foundation.decidable-equality.html#8014" class="Function">has-decidable-equality-Prop</a> <a id="2345" class="Symbol">(</a><a id="2346" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="2366" href="univalent-combinatorics.subfinite-types.html#2114" class="Bound">X</a><a id="2367" class="Symbol">))</a>
      <a id="2376" class="Symbol">(</a> <a id="2378" class="Symbol">λ</a> <a id="2380" class="Symbol">(</a><a id="2381" href="univalent-combinatorics.subfinite-types.html#2381" class="Bound">k</a> <a id="2383" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2385" href="univalent-combinatorics.subfinite-types.html#2385" class="Bound">f</a><a id="2386" class="Symbol">)</a> <a id="2388" class="Symbol">→</a> <a id="2390" href="foundation.decidable-equality.html#4376" class="Function">has-decidable-equality-emb</a> <a id="2417" href="univalent-combinatorics.subfinite-types.html#2385" class="Bound">f</a> <a id="2419" class="Symbol">(</a><a id="2420" href="univalent-combinatorics.equality-standard-finite-types.html#3037" class="Function">has-decidable-equality-Fin</a> <a id="2447" href="univalent-combinatorics.subfinite-types.html#2381" class="Bound">k</a><a id="2448" class="Symbol">))</a>
      <a id="2457" class="Symbol">(</a> <a id="2459" href="univalent-combinatorics.subfinite-types.html#1741" class="Function">is-subfinite-type-Subfinite-Type</a> <a id="2492" href="univalent-combinatorics.subfinite-types.html#2114" class="Bound">X</a><a id="2493" class="Symbol">)</a>

  <a id="2498" href="univalent-combinatorics.subfinite-types.html#2498" class="Function">discrete-type-Subfinite-Type</a> <a id="2527" class="Symbol">:</a> <a id="2529" href="foundation-core.discrete-types.html#542" class="Function">Discrete-Type</a> <a id="2543" href="univalent-combinatorics.subfinite-types.html#2102" class="Bound">l</a>
  <a id="2547" href="univalent-combinatorics.subfinite-types.html#2498" class="Function">discrete-type-Subfinite-Type</a> <a id="2576" class="Symbol">=</a>
    <a id="2582" class="Symbol">(</a> <a id="2584" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="2604" href="univalent-combinatorics.subfinite-types.html#2114" class="Bound">X</a> <a id="2606" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2608" href="univalent-combinatorics.subfinite-types.html#2147" class="Function">has-decidable-equality-type-Subfinite-Type</a><a id="2650" class="Symbol">)</a>
</pre>
### Subfinite types are sets

<pre class="Agda"><a id="2695" class="Keyword">module</a> <a id="2702" href="univalent-combinatorics.subfinite-types.html#2702" class="Module">_</a>
  <a id="2706" class="Symbol">{</a><a id="2707" href="univalent-combinatorics.subfinite-types.html#2707" class="Bound">l</a> <a id="2709" class="Symbol">:</a> <a id="2711" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2716" class="Symbol">}</a> <a id="2718" class="Symbol">(</a><a id="2719" href="univalent-combinatorics.subfinite-types.html#2719" class="Bound">X</a> <a id="2721" class="Symbol">:</a> <a id="2723" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="2738" href="univalent-combinatorics.subfinite-types.html#2707" class="Bound">l</a><a id="2739" class="Symbol">)</a>
  <a id="2743" class="Keyword">where</a>

  <a id="2752" href="univalent-combinatorics.subfinite-types.html#2752" class="Function">is-set-type-Subfinite-Type</a> <a id="2779" class="Symbol">:</a> <a id="2781" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="2788" class="Symbol">(</a><a id="2789" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="2809" href="univalent-combinatorics.subfinite-types.html#2719" class="Bound">X</a><a id="2810" class="Symbol">)</a>
  <a id="2814" href="univalent-combinatorics.subfinite-types.html#2752" class="Function">is-set-type-Subfinite-Type</a> <a id="2841" class="Symbol">=</a>
    <a id="2847" href="foundation.decidable-equality.html#7205" class="Function">is-set-has-decidable-equality</a> <a id="2877" class="Symbol">(</a><a id="2878" href="univalent-combinatorics.subfinite-types.html#2147" class="Function">has-decidable-equality-type-Subfinite-Type</a> <a id="2921" href="univalent-combinatorics.subfinite-types.html#2719" class="Bound">X</a><a id="2922" class="Symbol">)</a>

  <a id="2927" href="univalent-combinatorics.subfinite-types.html#2927" class="Function">set-Subfinite-Type</a> <a id="2946" class="Symbol">:</a> <a id="2948" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="2952" href="univalent-combinatorics.subfinite-types.html#2707" class="Bound">l</a>
  <a id="2956" href="univalent-combinatorics.subfinite-types.html#2927" class="Function">set-Subfinite-Type</a> <a id="2975" class="Symbol">=</a> <a id="2977" class="Symbol">(</a><a id="2978" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="2998" href="univalent-combinatorics.subfinite-types.html#2719" class="Bound">X</a> <a id="3000" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3002" href="univalent-combinatorics.subfinite-types.html#2752" class="Function">is-set-type-Subfinite-Type</a><a id="3028" class="Symbol">)</a>
</pre>
### Subfinite types are Dedekind finite

We reproduce a proof given by
[Gro-Tsen](https://mathoverflow.net/users/17064/gro-tsen) in this MathOverflow
answer: <https://mathoverflow.net/a/433318>.

**Proof.** Let $X$ be a subfinite type witnessed by $ι : X ↪ Fin n$, and let
$f : X ↪ X$ be an arbitrary self-embedding. It suffices to prove $f$ is
surjective, so assume given an $x : X$ where we want to show there exists
$z : X$ such that $f(z) ＝ x$. The mapping $i ↦ fⁱ(x)$ defines an $ℕ$-indexed
sequence of elements of $X$. Since the
[standard pigeonhole principle](univalent-combinatorics.pigeonhole-principle.md)
applies to $\operatorname{Fin}n$ there has to be $i < j$ in
$\operatorname{Fin}n$ such that $ι(fⁱ(x)) = ι(fʲ(x))$. Since $ι$ is an embedding
we in particular have $fⁱ(x) = fʲ(x)$ . By injectivity of $f$ we can cancel $i$
applications on both sides of the equation to obtain $x = f(f^{j-i-1}(x))$, and
so $f^{j-i-1}(x)$ is our desired preimage of $x$. ∎

<pre class="Agda"><a id="4013" class="Keyword">module</a> <a id="4020" href="univalent-combinatorics.subfinite-types.html#4020" class="Module">_</a>
  <a id="4024" class="Symbol">{</a><a id="4025" href="univalent-combinatorics.subfinite-types.html#4025" class="Bound">l</a> <a id="4027" class="Symbol">:</a> <a id="4029" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4034" class="Symbol">}</a> <a id="4036" class="Symbol">(</a><a id="4037" href="univalent-combinatorics.subfinite-types.html#4037" class="Bound">X</a> <a id="4039" class="Symbol">:</a> <a id="4041" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="4056" href="univalent-combinatorics.subfinite-types.html#4025" class="Bound">l</a><a id="4057" class="Symbol">)</a>
  <a id="4061" class="Keyword">where</a>

  <a id="4070" href="univalent-combinatorics.subfinite-types.html#4070" class="Function">is-dedekind-finite-type-Subfinite-Type&#39;</a> <a id="4110" class="Symbol">:</a>
    <a id="4116" class="Symbol">(</a><a id="4117" href="univalent-combinatorics.subfinite-types.html#4117" class="Bound">f</a> <a id="4119" class="Symbol">:</a> <a id="4121" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="4141" href="univalent-combinatorics.subfinite-types.html#4037" class="Bound">X</a> <a id="4143" class="Symbol">→</a> <a id="4145" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="4165" href="univalent-combinatorics.subfinite-types.html#4037" class="Bound">X</a><a id="4166" class="Symbol">)</a> <a id="4168" class="Symbol">→</a>
    <a id="4174" href="foundation-core.injective-maps.html#1182" class="Function">is-injective</a> <a id="4187" href="univalent-combinatorics.subfinite-types.html#4117" class="Bound">f</a> <a id="4189" class="Symbol">→</a> <a id="4191" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="4200" href="univalent-combinatorics.subfinite-types.html#4117" class="Bound">f</a>
  <a id="4204" href="univalent-combinatorics.subfinite-types.html#4070" class="Function">is-dedekind-finite-type-Subfinite-Type&#39;</a> <a id="4244" href="univalent-combinatorics.subfinite-types.html#4244" class="Bound">f</a> <a id="4246" href="univalent-combinatorics.subfinite-types.html#4246" class="Bound">is-injective-f</a> <a id="4261" class="Symbol">=</a>
    <a id="4267" href="foundation.propositional-truncations.html#4671" class="Function">rec-trunc-Prop</a>
      <a id="4288" class="Symbol">(</a> <a id="4290" href="foundation.equivalences.html#5072" class="Function">is-equiv-Prop</a> <a id="4304" href="univalent-combinatorics.subfinite-types.html#4244" class="Bound">f</a><a id="4305" class="Symbol">)</a>
      <a id="4313" class="Symbol">(</a> <a id="4315" class="Symbol">λ</a> <a id="4317" href="univalent-combinatorics.subfinite-types.html#4317" class="Bound">j</a> <a id="4319" class="Symbol">→</a> <a id="4321" href="univalent-combinatorics.subcounting.html#8709" class="Function">is-dedekind-finite-subcount&#39;</a> <a id="4350" href="univalent-combinatorics.subfinite-types.html#4317" class="Bound">j</a> <a id="4352" href="univalent-combinatorics.subfinite-types.html#4244" class="Bound">f</a> <a id="4354" href="univalent-combinatorics.subfinite-types.html#4246" class="Bound">is-injective-f</a><a id="4368" class="Symbol">)</a>
      <a id="4376" class="Symbol">(</a> <a id="4378" href="univalent-combinatorics.subfinite-types.html#1741" class="Function">is-subfinite-type-Subfinite-Type</a> <a id="4411" href="univalent-combinatorics.subfinite-types.html#4037" class="Bound">X</a><a id="4412" class="Symbol">)</a>

  <a id="4417" href="univalent-combinatorics.subfinite-types.html#4417" class="Function">is-dedekind-finite-type-Subfinite-Type</a> <a id="4456" class="Symbol">:</a>
    <a id="4462" href="univalent-combinatorics.dedekind-finite-types.html#1241" class="Function">is-dedekind-finite</a> <a id="4481" class="Symbol">(</a><a id="4482" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="4502" href="univalent-combinatorics.subfinite-types.html#4037" class="Bound">X</a><a id="4503" class="Symbol">)</a>
  <a id="4507" href="univalent-combinatorics.subfinite-types.html#4417" class="Function">is-dedekind-finite-type-Subfinite-Type</a> <a id="4546" href="univalent-combinatorics.subfinite-types.html#4546" class="Bound">f</a> <a id="4548" href="univalent-combinatorics.subfinite-types.html#4548" class="Bound">is-emb-f</a> <a id="4557" class="Symbol">=</a>
    <a id="4563" href="univalent-combinatorics.subfinite-types.html#4070" class="Function">is-dedekind-finite-type-Subfinite-Type&#39;</a> <a id="4603" href="univalent-combinatorics.subfinite-types.html#4546" class="Bound">f</a> <a id="4605" class="Symbol">(</a><a id="4606" href="foundation-core.injective-maps.html#3323" class="Function">is-injective-is-emb</a> <a id="4626" href="univalent-combinatorics.subfinite-types.html#4548" class="Bound">is-emb-f</a><a id="4634" class="Symbol">)</a>

  <a id="4639" href="univalent-combinatorics.subfinite-types.html#4639" class="Function">dedekind-finite-type-Subfinite-Type</a> <a id="4675" class="Symbol">:</a> <a id="4677" href="univalent-combinatorics.dedekind-finite-types.html#1408" class="Function">Dedekind-Finite-Type</a> <a id="4698" href="univalent-combinatorics.subfinite-types.html#4025" class="Bound">l</a>
  <a id="4702" href="univalent-combinatorics.subfinite-types.html#4639" class="Function">dedekind-finite-type-Subfinite-Type</a> <a id="4738" class="Symbol">=</a>
    <a id="4744" class="Symbol">(</a> <a id="4746" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="4766" href="univalent-combinatorics.subfinite-types.html#4037" class="Bound">X</a> <a id="4768" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4770" href="univalent-combinatorics.subfinite-types.html#4417" class="Function">is-dedekind-finite-type-Subfinite-Type</a><a id="4808" class="Symbol">)</a>
</pre>
### The Cantor–Schröder–Bernstein theorem for subfinite types

If two subfinite types `X` and `Y` mutually embed, `X ↪ Y` and `Y ↪ X`, then
`X ≃ Y`.

<pre class="Agda"><a id="4973" class="Keyword">module</a> <a id="4980" href="univalent-combinatorics.subfinite-types.html#4980" class="Module">_</a>
  <a id="4984" class="Symbol">{</a><a id="4985" href="univalent-combinatorics.subfinite-types.html#4985" class="Bound">l1</a> <a id="4988" href="univalent-combinatorics.subfinite-types.html#4988" class="Bound">l2</a> <a id="4991" class="Symbol">:</a> <a id="4993" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4998" class="Symbol">}</a> <a id="5000" class="Symbol">(</a><a id="5001" href="univalent-combinatorics.subfinite-types.html#5001" class="Bound">X</a> <a id="5003" class="Symbol">:</a> <a id="5005" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="5020" href="univalent-combinatorics.subfinite-types.html#4985" class="Bound">l1</a><a id="5022" class="Symbol">)</a> <a id="5024" class="Symbol">(</a><a id="5025" href="univalent-combinatorics.subfinite-types.html#5025" class="Bound">Y</a> <a id="5027" class="Symbol">:</a> <a id="5029" href="univalent-combinatorics.subfinite-types.html#1537" class="Function">Subfinite-Type</a> <a id="5044" href="univalent-combinatorics.subfinite-types.html#4988" class="Bound">l2</a><a id="5046" class="Symbol">)</a>
  <a id="5050" class="Keyword">where</a>

  <a id="5059" href="univalent-combinatorics.subfinite-types.html#5059" class="Function">Cantor-Schröder-Bernstein-Subfinite-Type</a> <a id="5100" class="Symbol">:</a>
    <a id="5106" class="Symbol">(</a><a id="5107" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="5127" href="univalent-combinatorics.subfinite-types.html#5001" class="Bound">X</a> <a id="5129" href="foundation-core.embeddings.html#1627" class="Function Operator">↪</a> <a id="5131" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="5151" href="univalent-combinatorics.subfinite-types.html#5025" class="Bound">Y</a><a id="5152" class="Symbol">)</a> <a id="5154" class="Symbol">→</a>
    <a id="5160" class="Symbol">(</a><a id="5161" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="5181" href="univalent-combinatorics.subfinite-types.html#5025" class="Bound">Y</a> <a id="5183" href="foundation-core.embeddings.html#1627" class="Function Operator">↪</a> <a id="5185" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="5205" href="univalent-combinatorics.subfinite-types.html#5001" class="Bound">X</a><a id="5206" class="Symbol">)</a> <a id="5208" class="Symbol">→</a>
    <a id="5214" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="5234" href="univalent-combinatorics.subfinite-types.html#5001" class="Bound">X</a> <a id="5236" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="5238" href="univalent-combinatorics.subfinite-types.html#1681" class="Function">type-Subfinite-Type</a> <a id="5258" href="univalent-combinatorics.subfinite-types.html#5025" class="Bound">Y</a>
  <a id="5262" href="univalent-combinatorics.subfinite-types.html#5059" class="Function">Cantor-Schröder-Bernstein-Subfinite-Type</a> <a id="5303" class="Symbol">=</a>
    <a id="5309" href="univalent-combinatorics.dedekind-finite-types.html#3193" class="Function">Cantor-Schröder-Bernstein-Dedekind-Finite-Type</a>
      <a id="5362" class="Symbol">(</a> <a id="5364" href="univalent-combinatorics.subfinite-types.html#4639" class="Function">dedekind-finite-type-Subfinite-Type</a> <a id="5400" href="univalent-combinatorics.subfinite-types.html#5001" class="Bound">X</a><a id="5401" class="Symbol">)</a>
      <a id="5409" class="Symbol">(</a> <a id="5411" href="univalent-combinatorics.subfinite-types.html#4639" class="Function">dedekind-finite-type-Subfinite-Type</a> <a id="5447" href="univalent-combinatorics.subfinite-types.html#5025" class="Bound">Y</a><a id="5448" class="Symbol">)</a>
</pre>
## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Kuratowski`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Kuratowski.html)
  at TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia
