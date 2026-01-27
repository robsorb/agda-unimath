# Markovian types

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="logic.markovian-types.html" class="Module">logic.markovian-types</a> <a id="57" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="113" class="Keyword">open</a> <a id="118" class="Keyword">import</a> <a id="125" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="307" class="Keyword">open</a> <a id="312" class="Keyword">import</a> <a id="319" href="foundation.universal-quantification.html" class="Module">foundation.universal-quantification</a>
<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A type `A` is {{#concept "Markovian" Disambiguation="type" Agda=is-markovian}}
if, for every [decidable subtype](foundation.decidable-subtypes.md) `𝒫` of `A`,
if `𝒫` is [not](foundation-core.negation.md) [full](foundation.full-subtypes.md)
then there is an element of `A` that is
[not in](foundation.complements-subtypes.md) `𝒫`.

## Definitions

### The predicate of being Markovian

We phrase the condition using the [type of booleans](foundation.booleans.md) so
that the predicate is small.

<pre class="Agda"><a id="is-markovian"></a><a id="965" href="logic.markovian-types.html#965" class="Function">is-markovian</a> <a id="978" class="Symbol">:</a> <a id="980" class="Symbol">{</a><a id="981" href="logic.markovian-types.html#981" class="Bound">l</a> <a id="983" class="Symbol">:</a> <a id="985" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="990" class="Symbol">}</a> <a id="992" class="Symbol">→</a> <a id="994" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="997" href="logic.markovian-types.html#981" class="Bound">l</a> <a id="999" class="Symbol">→</a> <a id="1001" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1004" href="logic.markovian-types.html#981" class="Bound">l</a>
<a id="1006" href="logic.markovian-types.html#965" class="Function">is-markovian</a> <a id="1019" href="logic.markovian-types.html#1019" class="Bound">A</a> <a id="1021" class="Symbol">=</a>
  <a id="1025" class="Symbol">(</a><a id="1026" href="logic.markovian-types.html#1026" class="Bound">𝒫</a> <a id="1028" class="Symbol">:</a> <a id="1030" href="logic.markovian-types.html#1019" class="Bound">A</a> <a id="1032" class="Symbol">→</a> <a id="1034" href="foundation.booleans.html#1556" class="Datatype">bool</a><a id="1038" class="Symbol">)</a> <a id="1040" class="Symbol">→</a>
  <a id="1044" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1046" class="Symbol">((</a><a id="1048" href="logic.markovian-types.html#1048" class="Bound">x</a> <a id="1050" class="Symbol">:</a> <a id="1052" href="logic.markovian-types.html#1019" class="Bound">A</a><a id="1053" class="Symbol">)</a> <a id="1055" class="Symbol">→</a> <a id="1057" href="foundation.booleans.html#5155" class="Function">is-true</a> <a id="1065" class="Symbol">(</a><a id="1066" href="logic.markovian-types.html#1026" class="Bound">𝒫</a> <a id="1068" href="logic.markovian-types.html#1048" class="Bound">x</a><a id="1069" class="Symbol">))</a> <a id="1072" class="Symbol">→</a>
  <a id="1076" href="foundation.existential-quantification.html#4151" class="Function">exists</a> <a id="1083" href="logic.markovian-types.html#1019" class="Bound">A</a> <a id="1085" class="Symbol">(λ</a> <a id="1088" href="logic.markovian-types.html#1088" class="Bound">x</a> <a id="1090" class="Symbol">→</a> <a id="1092" href="foundation.booleans.html#5856" class="Function">is-false-Prop</a> <a id="1106" class="Symbol">(</a><a id="1107" href="logic.markovian-types.html#1026" class="Bound">𝒫</a> <a id="1109" href="logic.markovian-types.html#1088" class="Bound">x</a><a id="1110" class="Symbol">))</a>

<a id="is-prop-is-markovian"></a><a id="1114" href="logic.markovian-types.html#1114" class="Function">is-prop-is-markovian</a> <a id="1135" class="Symbol">:</a> <a id="1137" class="Symbol">{</a><a id="1138" href="logic.markovian-types.html#1138" class="Bound">l</a> <a id="1140" class="Symbol">:</a> <a id="1142" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1147" class="Symbol">}</a> <a id="1149" class="Symbol">(</a><a id="1150" href="logic.markovian-types.html#1150" class="Bound">A</a> <a id="1152" class="Symbol">:</a> <a id="1154" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1157" href="logic.markovian-types.html#1138" class="Bound">l</a><a id="1158" class="Symbol">)</a> <a id="1160" class="Symbol">→</a> <a id="1162" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1170" class="Symbol">(</a><a id="1171" href="logic.markovian-types.html#965" class="Function">is-markovian</a> <a id="1184" href="logic.markovian-types.html#1150" class="Bound">A</a><a id="1185" class="Symbol">)</a>
<a id="1187" href="logic.markovian-types.html#1114" class="Function">is-prop-is-markovian</a> <a id="1208" href="logic.markovian-types.html#1208" class="Bound">A</a> <a id="1210" class="Symbol">=</a>
  <a id="1214" href="foundation-core.propositions.html#6443" class="Function">is-prop-Π</a> <a id="1224" class="Symbol">(λ</a> <a id="1227" href="logic.markovian-types.html#1227" class="Bound">𝒫</a> <a id="1229" class="Symbol">→</a> <a id="1231" href="foundation-core.propositions.html#7883" class="Function">is-prop-function-type</a> <a id="1253" class="Symbol">(</a><a id="1254" href="foundation.existential-quantification.html#4222" class="Function">is-prop-exists</a> <a id="1269" href="logic.markovian-types.html#1208" class="Bound">A</a> <a id="1271" class="Symbol">(</a><a id="1272" href="foundation.booleans.html#5856" class="Function">is-false-Prop</a> <a id="1286" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1288" href="logic.markovian-types.html#1227" class="Bound">𝒫</a><a id="1289" class="Symbol">)))</a>
</pre>
### The predicate of being Markovian at a universe level

<pre class="Agda"><a id="1364" class="Keyword">module</a> <a id="1371" href="logic.markovian-types.html#1371" class="Module">_</a>
  <a id="1375" class="Symbol">{</a><a id="1376" href="logic.markovian-types.html#1376" class="Bound">l1</a> <a id="1379" class="Symbol">:</a> <a id="1381" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1386" class="Symbol">}</a> <a id="1388" class="Symbol">(</a><a id="1389" href="logic.markovian-types.html#1389" class="Bound">l2</a> <a id="1392" class="Symbol">:</a> <a id="1394" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1399" class="Symbol">)</a> <a id="1401" class="Symbol">(</a><a id="1402" href="logic.markovian-types.html#1402" class="Bound">A</a> <a id="1404" class="Symbol">:</a> <a id="1406" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1409" href="logic.markovian-types.html#1376" class="Bound">l1</a><a id="1411" class="Symbol">)</a>
  <a id="1415" class="Keyword">where</a>

  <a id="1424" href="logic.markovian-types.html#1424" class="Function">is-markovian-prop-Level</a> <a id="1448" class="Symbol">:</a> <a id="1450" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1455" class="Symbol">(</a><a id="1456" href="logic.markovian-types.html#1376" class="Bound">l1</a> <a id="1459" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1461" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1466" href="logic.markovian-types.html#1389" class="Bound">l2</a><a id="1468" class="Symbol">)</a>
  <a id="1472" href="logic.markovian-types.html#1424" class="Function">is-markovian-prop-Level</a> <a id="1496" class="Symbol">=</a>
    <a id="1502" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1515" class="Symbol">(</a> <a id="1517" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="1535" href="logic.markovian-types.html#1389" class="Bound">l2</a> <a id="1538" href="logic.markovian-types.html#1402" class="Bound">A</a><a id="1539" class="Symbol">)</a>
      <a id="1547" class="Symbol">(</a> <a id="1549" class="Symbol">λ</a> <a id="1551" href="logic.markovian-types.html#1551" class="Bound">P</a> <a id="1553" class="Symbol">→</a>
        <a id="1563" href="foundation.negation.html#1170" class="Function Operator">¬&#39;</a> <a id="1566" class="Symbol">(</a><a id="1567" href="foundation.universal-quantification.html#1971" class="Function">∀&#39;</a> <a id="1570" href="logic.markovian-types.html#1402" class="Bound">A</a> <a id="1572" class="Symbol">(</a><a id="1573" href="foundation.decidable-subtypes.html#2991" class="Function">subtype-decidable-subtype</a> <a id="1599" href="logic.markovian-types.html#1551" class="Bound">P</a><a id="1600" class="Symbol">))</a> <a id="1603" href="foundation-core.propositions.html#8926" class="Function Operator">⇒</a>
        <a id="1613" href="foundation.existential-quantification.html#4308" class="Function">∃</a> <a id="1615" href="logic.markovian-types.html#1402" class="Bound">A</a> <a id="1617" class="Symbol">(</a><a id="1618" href="foundation.negation.html#1170" class="Function Operator">¬&#39;_</a> <a id="1622" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1624" href="foundation.decidable-subtypes.html#2991" class="Function">subtype-decidable-subtype</a> <a id="1650" href="logic.markovian-types.html#1551" class="Bound">P</a><a id="1651" class="Symbol">))</a>

  <a id="1657" href="logic.markovian-types.html#1657" class="Function">is-markovian-Level</a> <a id="1676" class="Symbol">:</a> <a id="1678" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1681" class="Symbol">(</a><a id="1682" href="logic.markovian-types.html#1376" class="Bound">l1</a> <a id="1685" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1687" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1692" href="logic.markovian-types.html#1389" class="Bound">l2</a><a id="1694" class="Symbol">)</a>
  <a id="1698" href="logic.markovian-types.html#1657" class="Function">is-markovian-Level</a> <a id="1717" class="Symbol">=</a>
      <a id="1725" class="Symbol">(</a><a id="1726" href="logic.markovian-types.html#1726" class="Bound">P</a> <a id="1728" class="Symbol">:</a> <a id="1730" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="1748" href="logic.markovian-types.html#1389" class="Bound">l2</a> <a id="1751" href="logic.markovian-types.html#1402" class="Bound">A</a><a id="1752" class="Symbol">)</a> <a id="1754" class="Symbol">→</a>
      <a id="1762" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1764" class="Symbol">((</a><a id="1766" href="logic.markovian-types.html#1766" class="Bound">x</a> <a id="1768" class="Symbol">:</a> <a id="1770" href="logic.markovian-types.html#1402" class="Bound">A</a><a id="1771" class="Symbol">)</a> <a id="1773" class="Symbol">→</a> <a id="1775" href="foundation.decidable-subtypes.html#3255" class="Function">is-in-decidable-subtype</a> <a id="1799" href="logic.markovian-types.html#1726" class="Bound">P</a> <a id="1801" href="logic.markovian-types.html#1766" class="Bound">x</a><a id="1802" class="Symbol">)</a> <a id="1804" class="Symbol">→</a>
      <a id="1812" href="foundation.existential-quantification.html#4151" class="Function">exists</a> <a id="1819" href="logic.markovian-types.html#1402" class="Bound">A</a> <a id="1821" class="Symbol">(</a><a id="1822" href="foundation.negation.html#1170" class="Function Operator">¬&#39;_</a> <a id="1826" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1828" href="foundation.decidable-subtypes.html#2991" class="Function">subtype-decidable-subtype</a> <a id="1854" href="logic.markovian-types.html#1726" class="Bound">P</a><a id="1855" class="Symbol">)</a>

  <a id="1860" href="logic.markovian-types.html#1860" class="Function">is-prop-is-markovian-Level</a> <a id="1887" class="Symbol">:</a> <a id="1889" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1897" href="logic.markovian-types.html#1657" class="Function">is-markovian-Level</a>
  <a id="1918" href="logic.markovian-types.html#1860" class="Function">is-prop-is-markovian-Level</a> <a id="1945" class="Symbol">=</a> <a id="1947" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1965" href="logic.markovian-types.html#1424" class="Function">is-markovian-prop-Level</a>
</pre>
## Properties

### A type is Markovian if and only if it is Markovian at any universe level

> This remains to be formalized.

### A type is Markovian if and only if it is Markovian at all universe levels

> This remains to be formalized.

### Types with decidability search are Markovian

> This remains to be formalized.

## See also

- [Markov's principle](logic.markovs-principle.md)

## External links

- [limited principle of omniscience](https://ncatlab.org/nlab/show/limited+principle+of+omniscience)
  at $n$Lab
