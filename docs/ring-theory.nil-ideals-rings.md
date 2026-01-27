# Nil ideals of rings

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="ring-theory.nil-ideals-rings.html" class="Module">ring-theory.nil-ideals-rings</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="ring-theory.ideals-rings.html" class="Module">ring-theory.ideals-rings</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="ring-theory.left-ideals-rings.html" class="Module">ring-theory.left-ideals-rings</a>
<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="ring-theory.nilpotent-elements-rings.html" class="Module">ring-theory.nilpotent-elements-rings</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="ring-theory.right-ideals-rings.html" class="Module">ring-theory.right-ideals-rings</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

A nil ideal in a ring is an ideal in which every element is nilpotent

## Definition

### Nil left ideals

<pre class="Agda"><a id="542" class="Keyword">module</a> <a id="549" href="ring-theory.nil-ideals-rings.html#549" class="Module">_</a>
  <a id="553" class="Symbol">{</a><a id="554" href="ring-theory.nil-ideals-rings.html#554" class="Bound">l1</a> <a id="557" href="ring-theory.nil-ideals-rings.html#557" class="Bound">l2</a> <a id="560" class="Symbol">:</a> <a id="562" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="567" class="Symbol">}</a> <a id="569" class="Symbol">(</a><a id="570" href="ring-theory.nil-ideals-rings.html#570" class="Bound">R</a> <a id="572" class="Symbol">:</a> <a id="574" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="579" href="ring-theory.nil-ideals-rings.html#554" class="Bound">l1</a><a id="581" class="Symbol">)</a> <a id="583" class="Symbol">(</a><a id="584" href="ring-theory.nil-ideals-rings.html#584" class="Bound">I</a> <a id="586" class="Symbol">:</a> <a id="588" href="ring-theory.left-ideals-rings.html#1338" class="Function">left-ideal-Ring</a> <a id="604" href="ring-theory.nil-ideals-rings.html#557" class="Bound">l2</a> <a id="607" href="ring-theory.nil-ideals-rings.html#570" class="Bound">R</a><a id="608" class="Symbol">)</a>
  <a id="612" class="Keyword">where</a>

  <a id="621" href="ring-theory.nil-ideals-rings.html#621" class="Function">is-nil-left-ideal-ring-Prop</a> <a id="649" class="Symbol">:</a> <a id="651" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="656" class="Symbol">(</a><a id="657" href="ring-theory.nil-ideals-rings.html#554" class="Bound">l1</a> <a id="660" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="662" href="ring-theory.nil-ideals-rings.html#557" class="Bound">l2</a><a id="664" class="Symbol">)</a>
  <a id="668" href="ring-theory.nil-ideals-rings.html#621" class="Function">is-nil-left-ideal-ring-Prop</a> <a id="696" class="Symbol">=</a>
    <a id="702" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="715" class="Symbol">(</a> <a id="717" href="ring-theory.left-ideals-rings.html#1758" class="Function">type-left-ideal-Ring</a> <a id="738" href="ring-theory.nil-ideals-rings.html#570" class="Bound">R</a> <a id="740" href="ring-theory.nil-ideals-rings.html#584" class="Bound">I</a><a id="741" class="Symbol">)</a>
      <a id="749" class="Symbol">(</a> <a id="751" class="Symbol">λ</a> <a id="753" href="ring-theory.nil-ideals-rings.html#753" class="Bound">x</a> <a id="755" class="Symbol">→</a>
        <a id="765" href="ring-theory.nilpotent-elements-rings.html#832" class="Function">is-nilpotent-element-ring-Prop</a> <a id="796" href="ring-theory.nil-ideals-rings.html#570" class="Bound">R</a> <a id="798" class="Symbol">(</a><a id="799" href="ring-theory.left-ideals-rings.html#1864" class="Function">inclusion-left-ideal-Ring</a> <a id="825" href="ring-theory.nil-ideals-rings.html#570" class="Bound">R</a> <a id="827" href="ring-theory.nil-ideals-rings.html#584" class="Bound">I</a> <a id="829" href="ring-theory.nil-ideals-rings.html#753" class="Bound">x</a><a id="830" class="Symbol">))</a>

  <a id="836" href="ring-theory.nil-ideals-rings.html#836" class="Function">is-nil-left-ideal-Ring</a> <a id="859" class="Symbol">:</a> <a id="861" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="864" class="Symbol">(</a><a id="865" href="ring-theory.nil-ideals-rings.html#554" class="Bound">l1</a> <a id="868" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="870" href="ring-theory.nil-ideals-rings.html#557" class="Bound">l2</a><a id="872" class="Symbol">)</a>
  <a id="876" href="ring-theory.nil-ideals-rings.html#836" class="Function">is-nil-left-ideal-Ring</a> <a id="899" class="Symbol">=</a> <a id="901" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="911" href="ring-theory.nil-ideals-rings.html#621" class="Function">is-nil-left-ideal-ring-Prop</a>

  <a id="942" href="ring-theory.nil-ideals-rings.html#942" class="Function">is-prop-is-nil-left-ideal-Ring</a> <a id="973" class="Symbol">:</a> <a id="975" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="983" href="ring-theory.nil-ideals-rings.html#836" class="Function">is-nil-left-ideal-Ring</a>
  <a id="1008" href="ring-theory.nil-ideals-rings.html#942" class="Function">is-prop-is-nil-left-ideal-Ring</a> <a id="1039" class="Symbol">=</a>
    <a id="1045" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1063" href="ring-theory.nil-ideals-rings.html#621" class="Function">is-nil-left-ideal-ring-Prop</a>
</pre>
### Nil right ideals

<pre class="Agda"><a id="1126" class="Keyword">module</a> <a id="1133" href="ring-theory.nil-ideals-rings.html#1133" class="Module">_</a>
  <a id="1137" class="Symbol">{</a><a id="1138" href="ring-theory.nil-ideals-rings.html#1138" class="Bound">l1</a> <a id="1141" href="ring-theory.nil-ideals-rings.html#1141" class="Bound">l2</a> <a id="1144" class="Symbol">:</a> <a id="1146" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1151" class="Symbol">}</a> <a id="1153" class="Symbol">(</a><a id="1154" href="ring-theory.nil-ideals-rings.html#1154" class="Bound">R</a> <a id="1156" class="Symbol">:</a> <a id="1158" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1163" href="ring-theory.nil-ideals-rings.html#1138" class="Bound">l1</a><a id="1165" class="Symbol">)</a> <a id="1167" class="Symbol">(</a><a id="1168" href="ring-theory.nil-ideals-rings.html#1168" class="Bound">I</a> <a id="1170" class="Symbol">:</a> <a id="1172" href="ring-theory.right-ideals-rings.html#1350" class="Function">right-ideal-Ring</a> <a id="1189" href="ring-theory.nil-ideals-rings.html#1141" class="Bound">l2</a> <a id="1192" href="ring-theory.nil-ideals-rings.html#1154" class="Bound">R</a><a id="1193" class="Symbol">)</a>
  <a id="1197" class="Keyword">where</a>

  <a id="1206" href="ring-theory.nil-ideals-rings.html#1206" class="Function">is-nil-right-ideal-ring-Prop</a> <a id="1235" class="Symbol">:</a> <a id="1237" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1242" class="Symbol">(</a><a id="1243" href="ring-theory.nil-ideals-rings.html#1138" class="Bound">l1</a> <a id="1246" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1248" href="ring-theory.nil-ideals-rings.html#1141" class="Bound">l2</a><a id="1250" class="Symbol">)</a>
  <a id="1254" href="ring-theory.nil-ideals-rings.html#1206" class="Function">is-nil-right-ideal-ring-Prop</a> <a id="1283" class="Symbol">=</a>
    <a id="1289" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1302" class="Symbol">(</a> <a id="1304" href="ring-theory.right-ideals-rings.html#1779" class="Function">type-right-ideal-Ring</a> <a id="1326" href="ring-theory.nil-ideals-rings.html#1154" class="Bound">R</a> <a id="1328" href="ring-theory.nil-ideals-rings.html#1168" class="Bound">I</a><a id="1329" class="Symbol">)</a>
      <a id="1337" class="Symbol">(</a> <a id="1339" class="Symbol">λ</a> <a id="1341" href="ring-theory.nil-ideals-rings.html#1341" class="Bound">x</a> <a id="1343" class="Symbol">→</a>
        <a id="1353" href="ring-theory.nilpotent-elements-rings.html#832" class="Function">is-nilpotent-element-ring-Prop</a> <a id="1384" href="ring-theory.nil-ideals-rings.html#1154" class="Bound">R</a> <a id="1386" class="Symbol">(</a><a id="1387" href="ring-theory.right-ideals-rings.html#1888" class="Function">inclusion-right-ideal-Ring</a> <a id="1414" href="ring-theory.nil-ideals-rings.html#1154" class="Bound">R</a> <a id="1416" href="ring-theory.nil-ideals-rings.html#1168" class="Bound">I</a> <a id="1418" href="ring-theory.nil-ideals-rings.html#1341" class="Bound">x</a><a id="1419" class="Symbol">))</a>

  <a id="1425" href="ring-theory.nil-ideals-rings.html#1425" class="Function">is-nil-right-ideal-Ring</a> <a id="1449" class="Symbol">:</a> <a id="1451" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1454" class="Symbol">(</a><a id="1455" href="ring-theory.nil-ideals-rings.html#1138" class="Bound">l1</a> <a id="1458" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1460" href="ring-theory.nil-ideals-rings.html#1141" class="Bound">l2</a><a id="1462" class="Symbol">)</a>
  <a id="1466" href="ring-theory.nil-ideals-rings.html#1425" class="Function">is-nil-right-ideal-Ring</a> <a id="1490" class="Symbol">=</a> <a id="1492" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1502" href="ring-theory.nil-ideals-rings.html#1206" class="Function">is-nil-right-ideal-ring-Prop</a>

  <a id="1534" href="ring-theory.nil-ideals-rings.html#1534" class="Function">is-prop-is-nil-right-ideal-Ring</a> <a id="1566" class="Symbol">:</a> <a id="1568" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1576" href="ring-theory.nil-ideals-rings.html#1425" class="Function">is-nil-right-ideal-Ring</a>
  <a id="1602" href="ring-theory.nil-ideals-rings.html#1534" class="Function">is-prop-is-nil-right-ideal-Ring</a> <a id="1634" class="Symbol">=</a>
    <a id="1640" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1658" href="ring-theory.nil-ideals-rings.html#1206" class="Function">is-nil-right-ideal-ring-Prop</a>
</pre>
### Nil ideals

<pre class="Agda"><a id="1716" class="Keyword">module</a> <a id="1723" href="ring-theory.nil-ideals-rings.html#1723" class="Module">_</a>
  <a id="1727" class="Symbol">{</a><a id="1728" href="ring-theory.nil-ideals-rings.html#1728" class="Bound">l1</a> <a id="1731" href="ring-theory.nil-ideals-rings.html#1731" class="Bound">l2</a> <a id="1734" class="Symbol">:</a> <a id="1736" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1741" class="Symbol">}</a> <a id="1743" class="Symbol">(</a><a id="1744" href="ring-theory.nil-ideals-rings.html#1744" class="Bound">R</a> <a id="1746" class="Symbol">:</a> <a id="1748" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1753" href="ring-theory.nil-ideals-rings.html#1728" class="Bound">l1</a><a id="1755" class="Symbol">)</a> <a id="1757" class="Symbol">(</a><a id="1758" href="ring-theory.nil-ideals-rings.html#1758" class="Bound">I</a> <a id="1760" class="Symbol">:</a> <a id="1762" href="ring-theory.ideals-rings.html#1957" class="Function">ideal-Ring</a> <a id="1773" href="ring-theory.nil-ideals-rings.html#1731" class="Bound">l2</a> <a id="1776" href="ring-theory.nil-ideals-rings.html#1744" class="Bound">R</a><a id="1777" class="Symbol">)</a>
  <a id="1781" class="Keyword">where</a>

  <a id="1790" href="ring-theory.nil-ideals-rings.html#1790" class="Function">is-nil-ideal-ring-Prop</a> <a id="1813" class="Symbol">:</a> <a id="1815" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1820" class="Symbol">(</a><a id="1821" href="ring-theory.nil-ideals-rings.html#1728" class="Bound">l1</a> <a id="1824" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1826" href="ring-theory.nil-ideals-rings.html#1731" class="Bound">l2</a><a id="1828" class="Symbol">)</a>
  <a id="1832" href="ring-theory.nil-ideals-rings.html#1790" class="Function">is-nil-ideal-ring-Prop</a> <a id="1855" class="Symbol">=</a>
    <a id="1861" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1874" class="Symbol">(</a> <a id="1876" href="ring-theory.ideals-rings.html#2334" class="Function">type-ideal-Ring</a> <a id="1892" href="ring-theory.nil-ideals-rings.html#1744" class="Bound">R</a> <a id="1894" href="ring-theory.nil-ideals-rings.html#1758" class="Bound">I</a><a id="1895" class="Symbol">)</a>
      <a id="1903" class="Symbol">(</a> <a id="1905" class="Symbol">λ</a> <a id="1907" href="ring-theory.nil-ideals-rings.html#1907" class="Bound">x</a> <a id="1909" class="Symbol">→</a>
        <a id="1919" href="ring-theory.nilpotent-elements-rings.html#832" class="Function">is-nilpotent-element-ring-Prop</a> <a id="1950" href="ring-theory.nil-ideals-rings.html#1744" class="Bound">R</a> <a id="1952" class="Symbol">(</a><a id="1953" href="ring-theory.ideals-rings.html#2425" class="Function">inclusion-ideal-Ring</a> <a id="1974" href="ring-theory.nil-ideals-rings.html#1744" class="Bound">R</a> <a id="1976" href="ring-theory.nil-ideals-rings.html#1758" class="Bound">I</a> <a id="1978" href="ring-theory.nil-ideals-rings.html#1907" class="Bound">x</a><a id="1979" class="Symbol">))</a>

  <a id="1985" href="ring-theory.nil-ideals-rings.html#1985" class="Function">is-nil-ideal-Ring</a> <a id="2003" class="Symbol">:</a> <a id="2005" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2008" class="Symbol">(</a><a id="2009" href="ring-theory.nil-ideals-rings.html#1728" class="Bound">l1</a> <a id="2012" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2014" href="ring-theory.nil-ideals-rings.html#1731" class="Bound">l2</a><a id="2016" class="Symbol">)</a>
  <a id="2020" href="ring-theory.nil-ideals-rings.html#1985" class="Function">is-nil-ideal-Ring</a> <a id="2038" class="Symbol">=</a> <a id="2040" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2050" href="ring-theory.nil-ideals-rings.html#1790" class="Function">is-nil-ideal-ring-Prop</a>

  <a id="2076" href="ring-theory.nil-ideals-rings.html#2076" class="Function">is-prop-is-nil-ideal-Ring</a> <a id="2102" class="Symbol">:</a> <a id="2104" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2112" href="ring-theory.nil-ideals-rings.html#1985" class="Function">is-nil-ideal-Ring</a>
  <a id="2132" href="ring-theory.nil-ideals-rings.html#2076" class="Function">is-prop-is-nil-ideal-Ring</a> <a id="2158" class="Symbol">=</a>
    <a id="2164" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2182" href="ring-theory.nil-ideals-rings.html#1790" class="Function">is-nil-ideal-ring-Prop</a>
</pre>