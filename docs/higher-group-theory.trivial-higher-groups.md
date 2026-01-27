# Trivial higher groups

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="higher-group-theory.trivial-higher-groups.html" class="Module">higher-group-theory.trivial-higher-groups</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.0-connected-types.html" class="Module">foundation.0-connected-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>
</pre>
</details>

## Idea

A [higher group](higher-group-theory.higher-groups.md) `G` is **trivial** if its
underlying type is contractible.

## Definitions

### Trivial higher groups

<pre class="Agda"><a id="613" class="Keyword">module</a> <a id="620" href="higher-group-theory.trivial-higher-groups.html#620" class="Module">_</a>
  <a id="624" class="Symbol">{</a><a id="625" href="higher-group-theory.trivial-higher-groups.html#625" class="Bound">l</a> <a id="627" class="Symbol">:</a> <a id="629" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="634" class="Symbol">}</a> <a id="636" class="Symbol">(</a><a id="637" href="higher-group-theory.trivial-higher-groups.html#637" class="Bound">G</a> <a id="639" class="Symbol">:</a> <a id="641" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="649" href="higher-group-theory.trivial-higher-groups.html#625" class="Bound">l</a><a id="650" class="Symbol">)</a>
  <a id="654" class="Keyword">where</a>

  <a id="663" href="higher-group-theory.trivial-higher-groups.html#663" class="Function">is-trivial-prop-∞-Group</a> <a id="687" class="Symbol">:</a> <a id="689" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="694" href="higher-group-theory.trivial-higher-groups.html#625" class="Bound">l</a>
  <a id="698" href="higher-group-theory.trivial-higher-groups.html#663" class="Function">is-trivial-prop-∞-Group</a> <a id="722" class="Symbol">=</a> <a id="724" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="738" class="Symbol">(</a><a id="739" href="higher-group-theory.higher-groups.html#3080" class="Function">type-∞-Group</a> <a id="752" href="higher-group-theory.trivial-higher-groups.html#637" class="Bound">G</a><a id="753" class="Symbol">)</a>

  <a id="758" href="higher-group-theory.trivial-higher-groups.html#758" class="Function">is-trivial-∞-Group</a> <a id="777" class="Symbol">:</a> <a id="779" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="782" href="higher-group-theory.trivial-higher-groups.html#625" class="Bound">l</a>
  <a id="786" href="higher-group-theory.trivial-higher-groups.html#758" class="Function">is-trivial-∞-Group</a> <a id="805" class="Symbol">=</a> <a id="807" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="817" href="higher-group-theory.trivial-higher-groups.html#663" class="Function">is-trivial-prop-∞-Group</a>

  <a id="844" href="higher-group-theory.trivial-higher-groups.html#844" class="Function">is-property-is-trivial-∞-Group</a> <a id="875" class="Symbol">:</a> <a id="877" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="885" class="Symbol">(</a><a id="886" href="higher-group-theory.trivial-higher-groups.html#758" class="Function">is-trivial-∞-Group</a><a id="904" class="Symbol">)</a>
  <a id="908" href="higher-group-theory.trivial-higher-groups.html#844" class="Function">is-property-is-trivial-∞-Group</a> <a id="939" class="Symbol">=</a> <a id="941" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="959" href="higher-group-theory.trivial-higher-groups.html#663" class="Function">is-trivial-prop-∞-Group</a>
</pre>
### Higher groups with contractible classifying type

<pre class="Agda"><a id="1050" class="Keyword">module</a> <a id="1057" href="higher-group-theory.trivial-higher-groups.html#1057" class="Module">_</a>
  <a id="1061" class="Symbol">{</a><a id="1062" href="higher-group-theory.trivial-higher-groups.html#1062" class="Bound">l</a> <a id="1064" class="Symbol">:</a> <a id="1066" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1071" class="Symbol">}</a> <a id="1073" class="Symbol">(</a><a id="1074" href="higher-group-theory.trivial-higher-groups.html#1074" class="Bound">G</a> <a id="1076" class="Symbol">:</a> <a id="1078" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="1086" href="higher-group-theory.trivial-higher-groups.html#1062" class="Bound">l</a><a id="1087" class="Symbol">)</a>
  <a id="1091" class="Keyword">where</a>

  <a id="1100" href="higher-group-theory.trivial-higher-groups.html#1100" class="Function">has-contractible-classifying-type-prop-∞-Group</a> <a id="1147" class="Symbol">:</a> <a id="1149" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1154" href="higher-group-theory.trivial-higher-groups.html#1062" class="Bound">l</a>
  <a id="1158" href="higher-group-theory.trivial-higher-groups.html#1100" class="Function">has-contractible-classifying-type-prop-∞-Group</a> <a id="1205" class="Symbol">=</a>
    <a id="1211" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="1225" class="Symbol">(</a><a id="1226" href="higher-group-theory.higher-groups.html#1252" class="Function">classifying-type-∞-Group</a> <a id="1251" href="higher-group-theory.trivial-higher-groups.html#1074" class="Bound">G</a><a id="1252" class="Symbol">)</a>

  <a id="1257" href="higher-group-theory.trivial-higher-groups.html#1257" class="Function">has-contractible-classifying-type-∞-Group</a> <a id="1299" class="Symbol">:</a> <a id="1301" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1304" href="higher-group-theory.trivial-higher-groups.html#1062" class="Bound">l</a>
  <a id="1308" href="higher-group-theory.trivial-higher-groups.html#1257" class="Function">has-contractible-classifying-type-∞-Group</a> <a id="1350" class="Symbol">=</a>
    <a id="1356" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1366" href="higher-group-theory.trivial-higher-groups.html#1100" class="Function">has-contractible-classifying-type-prop-∞-Group</a>

  <a id="1416" href="higher-group-theory.trivial-higher-groups.html#1416" class="Function">is-property-has-contractible-classifying-type-∞-Group</a> <a id="1470" class="Symbol">:</a>
    <a id="1476" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1484" class="Symbol">(</a><a id="1485" href="higher-group-theory.trivial-higher-groups.html#1257" class="Function">has-contractible-classifying-type-∞-Group</a><a id="1526" class="Symbol">)</a>
  <a id="1530" href="higher-group-theory.trivial-higher-groups.html#1416" class="Function">is-property-has-contractible-classifying-type-∞-Group</a> <a id="1584" class="Symbol">=</a>
    <a id="1590" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1608" href="higher-group-theory.trivial-higher-groups.html#1100" class="Function">has-contractible-classifying-type-prop-∞-Group</a>
</pre>
### The trivial higher group

<pre class="Agda"><a id="trivial-∞-Group"></a><a id="1698" href="higher-group-theory.trivial-higher-groups.html#1698" class="Function">trivial-∞-Group</a> <a id="1714" class="Symbol">:</a> <a id="1716" class="Symbol">{</a><a id="1717" href="higher-group-theory.trivial-higher-groups.html#1717" class="Bound">l</a> <a id="1719" class="Symbol">:</a> <a id="1721" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1726" class="Symbol">}</a> <a id="1728" class="Symbol">→</a> <a id="1730" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="1738" href="higher-group-theory.trivial-higher-groups.html#1717" class="Bound">l</a>
<a id="1740" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1744" class="Symbol">(</a><a id="1745" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1749" class="Symbol">(</a><a id="1750" href="higher-group-theory.trivial-higher-groups.html#1698" class="Function">trivial-∞-Group</a> <a id="1766" class="Symbol">{</a><a id="1767" href="higher-group-theory.trivial-higher-groups.html#1767" class="Bound">l</a><a id="1768" class="Symbol">}))</a> <a id="1772" class="Symbol">=</a> <a id="1774" href="foundation.unit-type.html#1545" class="Function">raise-unit</a> <a id="1785" href="higher-group-theory.trivial-higher-groups.html#1767" class="Bound">l</a>
<a id="1787" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1791" class="Symbol">(</a><a id="1792" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1796" href="higher-group-theory.trivial-higher-groups.html#1698" class="Function">trivial-∞-Group</a><a id="1811" class="Symbol">)</a> <a id="1813" class="Symbol">=</a> <a id="1815" href="foundation.unit-type.html#1606" class="Function">raise-star</a>
<a id="1826" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1830" class="Symbol">(</a><a id="1831" href="higher-group-theory.trivial-higher-groups.html#1698" class="Function">trivial-∞-Group</a> <a id="1847" class="Symbol">{</a><a id="1848" href="higher-group-theory.trivial-higher-groups.html#1848" class="Bound">l</a><a id="1849" class="Symbol">})</a> <a id="1852" class="Symbol">=</a>
  <a id="1856" href="foundation.0-connected-types.html#7024" class="Function">is-0-connected-is-contr</a> <a id="1880" class="Symbol">(</a><a id="1881" href="foundation.unit-type.html#1545" class="Function">raise-unit</a> <a id="1892" href="higher-group-theory.trivial-higher-groups.html#1848" class="Bound">l</a><a id="1893" class="Symbol">)</a> <a id="1895" href="foundation.unit-type.html#2180" class="Function">is-contr-raise-unit</a>

<a id="has-contractible-classifying-type-trivial-∞-Group"></a><a id="1916" href="higher-group-theory.trivial-higher-groups.html#1916" class="Function">has-contractible-classifying-type-trivial-∞-Group</a> <a id="1966" class="Symbol">:</a>
  <a id="1970" class="Symbol">{</a><a id="1971" href="higher-group-theory.trivial-higher-groups.html#1971" class="Bound">l</a> <a id="1973" class="Symbol">:</a> <a id="1975" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1980" class="Symbol">}</a> <a id="1982" class="Symbol">→</a> <a id="1984" href="higher-group-theory.trivial-higher-groups.html#1257" class="Function">has-contractible-classifying-type-∞-Group</a> <a id="2026" class="Symbol">(</a><a id="2027" href="higher-group-theory.trivial-higher-groups.html#1698" class="Function">trivial-∞-Group</a> <a id="2043" class="Symbol">{</a><a id="2044" href="higher-group-theory.trivial-higher-groups.html#1971" class="Bound">l</a><a id="2045" class="Symbol">})</a>
<a id="2048" href="higher-group-theory.trivial-higher-groups.html#1916" class="Function">has-contractible-classifying-type-trivial-∞-Group</a> <a id="2098" class="Symbol">=</a> <a id="2100" href="foundation.unit-type.html#2180" class="Function">is-contr-raise-unit</a>
</pre>
## Properties

### Having contractible classifying type is equivalent to having contractible underlying type

This remains to be formalized.
