# Central elements of monoids

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="group-theory.central-elements-monoids.html" class="Module">group-theory.central-elements-monoids</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="group-theory.central-elements-semigroups.html" class="Module">group-theory.central-elements-semigroups</a>
<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
</pre>
</details>

## Idea

An element `x` of a monoid `M` is said to be central if `xy ＝ yx` for every
`y : M`.

## Definition

<pre class="Agda"><a id="476" class="Keyword">module</a> <a id="483" href="group-theory.central-elements-monoids.html#483" class="Module">_</a>
  <a id="487" class="Symbol">{</a><a id="488" href="group-theory.central-elements-monoids.html#488" class="Bound">l</a> <a id="490" class="Symbol">:</a> <a id="492" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="497" class="Symbol">}</a> <a id="499" class="Symbol">(</a><a id="500" href="group-theory.central-elements-monoids.html#500" class="Bound">M</a> <a id="502" class="Symbol">:</a> <a id="504" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="511" href="group-theory.central-elements-monoids.html#488" class="Bound">l</a><a id="512" class="Symbol">)</a>
  <a id="516" class="Keyword">where</a>

  <a id="525" href="group-theory.central-elements-monoids.html#525" class="Function">is-central-element-prop-Monoid</a> <a id="556" class="Symbol">:</a> <a id="558" href="group-theory.monoids.html#1116" class="Function">type-Monoid</a> <a id="570" href="group-theory.central-elements-monoids.html#500" class="Bound">M</a> <a id="572" class="Symbol">→</a> <a id="574" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="579" href="group-theory.central-elements-monoids.html#488" class="Bound">l</a>
  <a id="583" href="group-theory.central-elements-monoids.html#525" class="Function">is-central-element-prop-Monoid</a> <a id="614" class="Symbol">=</a>
    <a id="620" href="group-theory.central-elements-semigroups.html#573" class="Function">is-central-element-prop-Semigroup</a> <a id="654" class="Symbol">(</a><a id="655" href="group-theory.monoids.html#969" class="Function">semigroup-Monoid</a> <a id="672" href="group-theory.central-elements-monoids.html#500" class="Bound">M</a><a id="673" class="Symbol">)</a>

  <a id="678" href="group-theory.central-elements-monoids.html#678" class="Function">is-central-element-Monoid</a> <a id="704" class="Symbol">:</a> <a id="706" href="group-theory.monoids.html#1116" class="Function">type-Monoid</a> <a id="718" href="group-theory.central-elements-monoids.html#500" class="Bound">M</a> <a id="720" class="Symbol">→</a> <a id="722" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="725" href="group-theory.central-elements-monoids.html#488" class="Bound">l</a>
  <a id="729" href="group-theory.central-elements-monoids.html#678" class="Function">is-central-element-Monoid</a> <a id="755" class="Symbol">=</a>
    <a id="761" href="group-theory.central-elements-semigroups.html#841" class="Function">is-central-element-Semigroup</a> <a id="790" class="Symbol">(</a><a id="791" href="group-theory.monoids.html#969" class="Function">semigroup-Monoid</a> <a id="808" href="group-theory.central-elements-monoids.html#500" class="Bound">M</a><a id="809" class="Symbol">)</a>

  <a id="814" href="group-theory.central-elements-monoids.html#814" class="Function">is-prop-is-central-element-Monoid</a> <a id="848" class="Symbol">:</a>
    <a id="854" class="Symbol">(</a><a id="855" href="group-theory.central-elements-monoids.html#855" class="Bound">x</a> <a id="857" class="Symbol">:</a> <a id="859" href="group-theory.monoids.html#1116" class="Function">type-Monoid</a> <a id="871" href="group-theory.central-elements-monoids.html#500" class="Bound">M</a><a id="872" class="Symbol">)</a> <a id="874" class="Symbol">→</a> <a id="876" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="884" class="Symbol">(</a><a id="885" href="group-theory.central-elements-monoids.html#678" class="Function">is-central-element-Monoid</a> <a id="911" href="group-theory.central-elements-monoids.html#855" class="Bound">x</a><a id="912" class="Symbol">)</a>
  <a id="916" href="group-theory.central-elements-monoids.html#814" class="Function">is-prop-is-central-element-Monoid</a> <a id="950" class="Symbol">=</a>
    <a id="956" href="group-theory.central-elements-semigroups.html#986" class="Function">is-prop-is-central-element-Semigroup</a> <a id="993" class="Symbol">(</a><a id="994" href="group-theory.monoids.html#969" class="Function">semigroup-Monoid</a> <a id="1011" href="group-theory.central-elements-monoids.html#500" class="Bound">M</a><a id="1012" class="Symbol">)</a>
</pre>
## Properties

### The unit element is central

<pre class="Agda"><a id="1075" class="Keyword">module</a> <a id="1082" href="group-theory.central-elements-monoids.html#1082" class="Module">_</a>
  <a id="1086" class="Symbol">{</a><a id="1087" href="group-theory.central-elements-monoids.html#1087" class="Bound">l</a> <a id="1089" class="Symbol">:</a> <a id="1091" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1096" class="Symbol">}</a> <a id="1098" class="Symbol">(</a><a id="1099" href="group-theory.central-elements-monoids.html#1099" class="Bound">M</a> <a id="1101" class="Symbol">:</a> <a id="1103" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="1110" href="group-theory.central-elements-monoids.html#1087" class="Bound">l</a><a id="1111" class="Symbol">)</a>
  <a id="1115" class="Keyword">where</a>

  <a id="1124" href="group-theory.central-elements-monoids.html#1124" class="Function">is-central-element-unit-Monoid</a> <a id="1155" class="Symbol">:</a> <a id="1157" href="group-theory.central-elements-monoids.html#678" class="Function">is-central-element-Monoid</a> <a id="1183" href="group-theory.central-elements-monoids.html#1099" class="Bound">M</a> <a id="1185" class="Symbol">(</a><a id="1186" href="group-theory.monoids.html#1972" class="Function">unit-Monoid</a> <a id="1198" href="group-theory.central-elements-monoids.html#1099" class="Bound">M</a><a id="1199" class="Symbol">)</a>
  <a id="1203" href="group-theory.central-elements-monoids.html#1124" class="Function">is-central-element-unit-Monoid</a> <a id="1234" href="group-theory.central-elements-monoids.html#1234" class="Bound">y</a> <a id="1236" class="Symbol">=</a>
    <a id="1242" href="group-theory.monoids.html#2218" class="Function">left-unit-law-mul-Monoid</a> <a id="1267" href="group-theory.central-elements-monoids.html#1099" class="Bound">M</a> <a id="1269" href="group-theory.central-elements-monoids.html#1234" class="Bound">y</a> <a id="1271" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a> <a id="1273" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="1277" class="Symbol">(</a><a id="1278" href="group-theory.monoids.html#2352" class="Function">right-unit-law-mul-Monoid</a> <a id="1304" href="group-theory.central-elements-monoids.html#1099" class="Bound">M</a> <a id="1306" href="group-theory.central-elements-monoids.html#1234" class="Bound">y</a><a id="1307" class="Symbol">)</a>
</pre>
### The product of two central elements is central

<pre class="Agda"><a id="1374" class="Keyword">module</a> <a id="1381" href="group-theory.central-elements-monoids.html#1381" class="Module">_</a>
  <a id="1385" class="Symbol">{</a><a id="1386" href="group-theory.central-elements-monoids.html#1386" class="Bound">l</a> <a id="1388" class="Symbol">:</a> <a id="1390" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1395" class="Symbol">}</a> <a id="1397" class="Symbol">(</a><a id="1398" href="group-theory.central-elements-monoids.html#1398" class="Bound">M</a> <a id="1400" class="Symbol">:</a> <a id="1402" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="1409" href="group-theory.central-elements-monoids.html#1386" class="Bound">l</a><a id="1410" class="Symbol">)</a>
  <a id="1414" class="Keyword">where</a>

  <a id="1423" href="group-theory.central-elements-monoids.html#1423" class="Function">is-central-element-mul-Monoid</a> <a id="1453" class="Symbol">:</a>
    <a id="1459" class="Symbol">(</a><a id="1460" href="group-theory.central-elements-monoids.html#1460" class="Bound">x</a> <a id="1462" href="group-theory.central-elements-monoids.html#1462" class="Bound">y</a> <a id="1464" class="Symbol">:</a> <a id="1466" href="group-theory.monoids.html#1116" class="Function">type-Monoid</a> <a id="1478" href="group-theory.central-elements-monoids.html#1398" class="Bound">M</a><a id="1479" class="Symbol">)</a> <a id="1481" class="Symbol">→</a>
    <a id="1487" href="group-theory.central-elements-monoids.html#678" class="Function">is-central-element-Monoid</a> <a id="1513" href="group-theory.central-elements-monoids.html#1398" class="Bound">M</a> <a id="1515" href="group-theory.central-elements-monoids.html#1460" class="Bound">x</a> <a id="1517" class="Symbol">→</a> <a id="1519" href="group-theory.central-elements-monoids.html#678" class="Function">is-central-element-Monoid</a> <a id="1545" href="group-theory.central-elements-monoids.html#1398" class="Bound">M</a> <a id="1547" href="group-theory.central-elements-monoids.html#1462" class="Bound">y</a> <a id="1549" class="Symbol">→</a>
    <a id="1555" href="group-theory.central-elements-monoids.html#678" class="Function">is-central-element-Monoid</a> <a id="1581" href="group-theory.central-elements-monoids.html#1398" class="Bound">M</a> <a id="1583" class="Symbol">(</a><a id="1584" href="group-theory.monoids.html#1359" class="Function">mul-Monoid</a> <a id="1595" href="group-theory.central-elements-monoids.html#1398" class="Bound">M</a> <a id="1597" href="group-theory.central-elements-monoids.html#1460" class="Bound">x</a> <a id="1599" href="group-theory.central-elements-monoids.html#1462" class="Bound">y</a><a id="1600" class="Symbol">)</a>
  <a id="1604" href="group-theory.central-elements-monoids.html#1423" class="Function">is-central-element-mul-Monoid</a> <a id="1634" class="Symbol">=</a>
    <a id="1640" href="group-theory.central-elements-semigroups.html#1330" class="Function">is-central-element-mul-Semigroup</a> <a id="1673" class="Symbol">(</a><a id="1674" href="group-theory.monoids.html#969" class="Function">semigroup-Monoid</a> <a id="1691" href="group-theory.central-elements-monoids.html#1398" class="Bound">M</a><a id="1692" class="Symbol">)</a>
</pre>