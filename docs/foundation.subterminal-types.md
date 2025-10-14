# Subterminal types

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="foundation.subterminal-types.html" class="Module">foundation.subterminal-types</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="467" class="Keyword">open</a> <a id="472" class="Keyword">import</a> <a id="479" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A type is said to be {{#concept "subterminal" Agda=is-subterminal}} if it
[embeds](foundation-core.embeddings.md) into the
[unit type](foundation.unit-type.md). A type is subterminal if and only if it is
a [proposition](foundation-core.propositions.md).

## Definition

<pre class="Agda"><a id="812" class="Keyword">module</a> <a id="819" href="foundation.subterminal-types.html#819" class="Module">_</a>
  <a id="823" class="Symbol">{</a><a id="824" href="foundation.subterminal-types.html#824" class="Bound">l</a> <a id="826" class="Symbol">:</a> <a id="828" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="833" class="Symbol">}</a> <a id="835" class="Symbol">(</a><a id="836" href="foundation.subterminal-types.html#836" class="Bound">A</a> <a id="838" class="Symbol">:</a> <a id="840" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="843" href="foundation.subterminal-types.html#824" class="Bound">l</a><a id="844" class="Symbol">)</a>
  <a id="848" class="Keyword">where</a>

  <a id="857" href="foundation.subterminal-types.html#857" class="Function">is-subterminal</a> <a id="872" class="Symbol">:</a> <a id="874" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="877" href="foundation.subterminal-types.html#824" class="Bound">l</a>
  <a id="881" href="foundation.subterminal-types.html#857" class="Function">is-subterminal</a> <a id="896" class="Symbol">=</a> <a id="898" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="905" class="Symbol">(</a><a id="906" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="919" href="foundation.subterminal-types.html#836" class="Bound">A</a><a id="920" class="Symbol">)</a>
</pre>
## Properties

### A type is subterminal if and only if it is a proposition

<pre class="Agda"><a id="1012" class="Keyword">module</a> <a id="1019" href="foundation.subterminal-types.html#1019" class="Module">_</a>
  <a id="1023" class="Symbol">{</a><a id="1024" href="foundation.subterminal-types.html#1024" class="Bound">l</a> <a id="1026" class="Symbol">:</a> <a id="1028" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1033" class="Symbol">}</a> <a id="1035" class="Symbol">{</a><a id="1036" href="foundation.subterminal-types.html#1036" class="Bound">A</a> <a id="1038" class="Symbol">:</a> <a id="1040" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1043" href="foundation.subterminal-types.html#1024" class="Bound">l</a><a id="1044" class="Symbol">}</a>
  <a id="1048" class="Keyword">where</a>

  <a id="1057" class="Keyword">abstract</a>
    <a id="1070" href="foundation.subterminal-types.html#1070" class="Function">is-subterminal-is-proof-irrelevant</a> <a id="1105" class="Symbol">:</a>
      <a id="1113" href="foundation-core.propositions.html#2085" class="Function">is-proof-irrelevant</a> <a id="1133" href="foundation.subterminal-types.html#1036" class="Bound">A</a> <a id="1135" class="Symbol">→</a> <a id="1137" href="foundation.subterminal-types.html#857" class="Function">is-subterminal</a> <a id="1152" href="foundation.subterminal-types.html#1036" class="Bound">A</a>
    <a id="1158" href="foundation.subterminal-types.html#1070" class="Function">is-subterminal-is-proof-irrelevant</a> <a id="1193" href="foundation.subterminal-types.html#1193" class="Bound">H</a> <a id="1195" class="Symbol">=</a>
      <a id="1203" href="foundation-core.embeddings.html#3033" class="Function">is-emb-is-emb</a>
        <a id="1225" class="Symbol">(</a> <a id="1227" class="Symbol">λ</a> <a id="1229" href="foundation.subterminal-types.html#1229" class="Bound">x</a> <a id="1231" class="Symbol">→</a> <a id="1233" href="foundation-core.equivalences.html#20409" class="Function">is-emb-is-equiv</a> <a id="1249" class="Symbol">(</a><a id="1250" href="foundation-core.contractible-types.html#3139" class="Function">is-equiv-is-contr</a> <a id="1268" class="Symbol">_</a> <a id="1270" class="Symbol">(</a><a id="1271" href="foundation.subterminal-types.html#1193" class="Bound">H</a> <a id="1273" href="foundation.subterminal-types.html#1229" class="Bound">x</a><a id="1274" class="Symbol">)</a> <a id="1276" href="foundation.unit-type.html#2082" class="Function">is-contr-unit</a><a id="1289" class="Symbol">))</a>

  <a id="1295" class="Keyword">abstract</a>
    <a id="1308" href="foundation.subterminal-types.html#1308" class="Function">is-subterminal-all-elements-equal</a> <a id="1342" class="Symbol">:</a> <a id="1344" href="foundation-core.propositions.html#2015" class="Function">all-elements-equal</a> <a id="1363" href="foundation.subterminal-types.html#1036" class="Bound">A</a> <a id="1365" class="Symbol">→</a> <a id="1367" href="foundation.subterminal-types.html#857" class="Function">is-subterminal</a> <a id="1382" href="foundation.subterminal-types.html#1036" class="Bound">A</a>
    <a id="1388" href="foundation.subterminal-types.html#1308" class="Function">is-subterminal-all-elements-equal</a> <a id="1422" class="Symbol">=</a>
      <a id="1430" href="foundation.subterminal-types.html#1070" class="Function">is-subterminal-is-proof-irrelevant</a> <a id="1465" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
      <a id="1473" href="foundation-core.propositions.html#2628" class="Function">is-proof-irrelevant-all-elements-equal</a>

  <a id="1515" class="Keyword">abstract</a>
    <a id="1528" href="foundation.subterminal-types.html#1528" class="Function">is-subterminal-is-prop</a> <a id="1551" class="Symbol">:</a> <a id="1553" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1561" href="foundation.subterminal-types.html#1036" class="Bound">A</a> <a id="1563" class="Symbol">→</a> <a id="1565" href="foundation.subterminal-types.html#857" class="Function">is-subterminal</a> <a id="1580" href="foundation.subterminal-types.html#1036" class="Bound">A</a>
    <a id="1586" href="foundation.subterminal-types.html#1528" class="Function">is-subterminal-is-prop</a> <a id="1609" class="Symbol">=</a> <a id="1611" href="foundation.subterminal-types.html#1308" class="Function">is-subterminal-all-elements-equal</a> <a id="1645" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1647" href="foundation-core.propositions.html#2425" class="Function">eq-is-prop&#39;</a>

  <a id="1662" class="Keyword">abstract</a>
    <a id="1675" href="foundation.subterminal-types.html#1675" class="Function">is-prop-is-subterminal</a> <a id="1698" class="Symbol">:</a> <a id="1700" href="foundation.subterminal-types.html#857" class="Function">is-subterminal</a> <a id="1715" href="foundation.subterminal-types.html#1036" class="Bound">A</a> <a id="1717" class="Symbol">→</a> <a id="1719" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1727" href="foundation.subterminal-types.html#1036" class="Bound">A</a>
    <a id="1733" href="foundation.subterminal-types.html#1675" class="Function">is-prop-is-subterminal</a> <a id="1756" href="foundation.subterminal-types.html#1756" class="Bound">H</a> <a id="1758" href="foundation.subterminal-types.html#1758" class="Bound">x</a> <a id="1760" href="foundation.subterminal-types.html#1760" class="Bound">y</a> <a id="1762" class="Symbol">=</a>
      <a id="1770" href="foundation-core.contractible-types.html#2210" class="Function">is-contr-is-equiv</a>
        <a id="1796" class="Symbol">(</a> <a id="1798" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a> <a id="1803" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1805" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1809" class="Symbol">)</a>
        <a id="1819" class="Symbol">(</a> <a id="1821" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="1824" class="Symbol">(</a><a id="1825" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="1838" href="foundation.subterminal-types.html#1036" class="Bound">A</a><a id="1839" class="Symbol">))</a>
        <a id="1850" class="Symbol">(</a> <a id="1852" href="foundation.subterminal-types.html#1756" class="Bound">H</a> <a id="1854" href="foundation.subterminal-types.html#1758" class="Bound">x</a> <a id="1856" href="foundation.subterminal-types.html#1760" class="Bound">y</a><a id="1857" class="Symbol">)</a>
        <a id="1867" class="Symbol">(</a> <a id="1869" href="foundation.unit-type.html#4543" class="Function">is-prop-unit</a> <a id="1882" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a> <a id="1887" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1891" class="Symbol">)</a>

  <a id="1896" class="Keyword">abstract</a>
    <a id="1909" href="foundation.subterminal-types.html#1909" class="Function">eq-is-subterminal</a> <a id="1927" class="Symbol">:</a> <a id="1929" href="foundation.subterminal-types.html#857" class="Function">is-subterminal</a> <a id="1944" href="foundation.subterminal-types.html#1036" class="Bound">A</a> <a id="1946" class="Symbol">→</a> <a id="1948" href="foundation-core.propositions.html#2015" class="Function">all-elements-equal</a> <a id="1967" href="foundation.subterminal-types.html#1036" class="Bound">A</a>
    <a id="1973" href="foundation.subterminal-types.html#1909" class="Function">eq-is-subterminal</a> <a id="1991" class="Symbol">=</a> <a id="1993" href="foundation-core.propositions.html#2425" class="Function">eq-is-prop&#39;</a> <a id="2005" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2007" href="foundation.subterminal-types.html#1675" class="Function">is-prop-is-subterminal</a>

  <a id="2033" class="Keyword">abstract</a>
    <a id="2046" href="foundation.subterminal-types.html#2046" class="Function">is-proof-irrelevant-is-subterminal</a> <a id="2081" class="Symbol">:</a>
      <a id="2089" href="foundation.subterminal-types.html#857" class="Function">is-subterminal</a> <a id="2104" href="foundation.subterminal-types.html#1036" class="Bound">A</a> <a id="2106" class="Symbol">→</a> <a id="2108" href="foundation-core.propositions.html#2085" class="Function">is-proof-irrelevant</a> <a id="2128" href="foundation.subterminal-types.html#1036" class="Bound">A</a>
    <a id="2134" href="foundation.subterminal-types.html#2046" class="Function">is-proof-irrelevant-is-subterminal</a> <a id="2169" href="foundation.subterminal-types.html#2169" class="Bound">H</a> <a id="2171" class="Symbol">=</a>
      <a id="2179" href="foundation-core.propositions.html#2628" class="Function">is-proof-irrelevant-all-elements-equal</a> <a id="2218" class="Symbol">(</a><a id="2219" href="foundation.subterminal-types.html#1909" class="Function">eq-is-subterminal</a> <a id="2237" href="foundation.subterminal-types.html#2169" class="Bound">H</a><a id="2238" class="Symbol">)</a>
</pre>
## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
