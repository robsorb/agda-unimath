# Center of a monoid

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="group-theory.centers-monoids.html" class="Module">group-theory.centers-monoids</a> <a id="67" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="123" class="Keyword">open</a> <a id="128" class="Keyword">import</a> <a id="135" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="group-theory.central-elements-monoids.html" class="Module">group-theory.central-elements-monoids</a>
<a id="331" class="Keyword">open</a> <a id="336" class="Keyword">import</a> <a id="343" href="group-theory.homomorphisms-monoids.html" class="Module">group-theory.homomorphisms-monoids</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
<a id="411" class="Keyword">open</a> <a id="416" class="Keyword">import</a> <a id="423" href="group-theory.submonoids.html" class="Module">group-theory.submonoids</a>
</pre>
</details>

## Idea

The **center** of a [monoid](group-theory.monoids.md) consists of those elements
that are central.

## Definition

<pre class="Agda"><a id="596" class="Keyword">module</a> <a id="603" href="group-theory.centers-monoids.html#603" class="Module">_</a>
  <a id="607" class="Symbol">{</a><a id="608" href="group-theory.centers-monoids.html#608" class="Bound">l</a> <a id="610" class="Symbol">:</a> <a id="612" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="617" class="Symbol">}</a> <a id="619" class="Symbol">(</a><a id="620" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="622" class="Symbol">:</a> <a id="624" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="631" href="group-theory.centers-monoids.html#608" class="Bound">l</a><a id="632" class="Symbol">)</a>
  <a id="636" class="Keyword">where</a>

  <a id="645" href="group-theory.centers-monoids.html#645" class="Function">subtype-center-Monoid</a> <a id="667" class="Symbol">:</a> <a id="669" href="group-theory.monoids.html#1116" class="Function">type-Monoid</a> <a id="681" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="683" class="Symbol">→</a> <a id="685" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="690" href="group-theory.centers-monoids.html#608" class="Bound">l</a>
  <a id="694" href="group-theory.centers-monoids.html#645" class="Function">subtype-center-Monoid</a> <a id="716" class="Symbol">=</a> <a id="718" href="group-theory.central-elements-monoids.html#525" class="Function">is-central-element-prop-Monoid</a> <a id="749" href="group-theory.centers-monoids.html#620" class="Bound">M</a>

  <a id="754" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a> <a id="768" class="Symbol">:</a> <a id="770" href="group-theory.submonoids.html#1247" class="Function">Submonoid</a> <a id="780" href="group-theory.centers-monoids.html#608" class="Bound">l</a> <a id="782" href="group-theory.centers-monoids.html#620" class="Bound">M</a>
  <a id="786" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="790" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a> <a id="804" class="Symbol">=</a> <a id="806" href="group-theory.centers-monoids.html#645" class="Function">subtype-center-Monoid</a>
  <a id="830" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="834" class="Symbol">(</a><a id="835" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="839" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a><a id="852" class="Symbol">)</a> <a id="854" class="Symbol">=</a> <a id="856" href="group-theory.central-elements-monoids.html#1124" class="Function">is-central-element-unit-Monoid</a> <a id="887" href="group-theory.centers-monoids.html#620" class="Bound">M</a>
  <a id="891" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="895" class="Symbol">(</a><a id="896" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="900" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a><a id="913" class="Symbol">)</a> <a id="915" class="Symbol">=</a> <a id="917" href="group-theory.central-elements-monoids.html#1423" class="Function">is-central-element-mul-Monoid</a> <a id="947" href="group-theory.centers-monoids.html#620" class="Bound">M</a>

  <a id="952" href="group-theory.centers-monoids.html#952" class="Function">monoid-center-Monoid</a> <a id="973" class="Symbol">:</a> <a id="975" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="982" href="group-theory.centers-monoids.html#608" class="Bound">l</a>
  <a id="986" href="group-theory.centers-monoids.html#952" class="Function">monoid-center-Monoid</a> <a id="1007" class="Symbol">=</a> <a id="1009" href="group-theory.submonoids.html#4945" class="Function">monoid-Submonoid</a> <a id="1026" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="1028" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a>

  <a id="1045" href="group-theory.centers-monoids.html#1045" class="Function">type-center-Monoid</a> <a id="1064" class="Symbol">:</a> <a id="1066" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1069" href="group-theory.centers-monoids.html#608" class="Bound">l</a>
  <a id="1073" href="group-theory.centers-monoids.html#1045" class="Function">type-center-Monoid</a> <a id="1092" class="Symbol">=</a>
    <a id="1098" href="group-theory.submonoids.html#2339" class="Function">type-Submonoid</a> <a id="1113" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="1115" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a>

  <a id="1132" href="group-theory.centers-monoids.html#1132" class="Function">mul-center-Monoid</a> <a id="1150" class="Symbol">:</a>
    <a id="1156" class="Symbol">(</a><a id="1157" href="group-theory.centers-monoids.html#1157" class="Bound">x</a> <a id="1159" href="group-theory.centers-monoids.html#1159" class="Bound">y</a> <a id="1161" class="Symbol">:</a> <a id="1163" href="group-theory.centers-monoids.html#1045" class="Function">type-center-Monoid</a><a id="1181" class="Symbol">)</a> <a id="1183" class="Symbol">→</a> <a id="1185" href="group-theory.centers-monoids.html#1045" class="Function">type-center-Monoid</a>
  <a id="1206" href="group-theory.centers-monoids.html#1132" class="Function">mul-center-Monoid</a> <a id="1224" class="Symbol">=</a> <a id="1226" href="group-theory.submonoids.html#3595" class="Function">mul-Submonoid</a> <a id="1240" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="1242" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a>

  <a id="1259" href="group-theory.centers-monoids.html#1259" class="Function">associative-mul-center-Monoid</a> <a id="1289" class="Symbol">:</a>
    <a id="1295" class="Symbol">(</a><a id="1296" href="group-theory.centers-monoids.html#1296" class="Bound">x</a> <a id="1298" href="group-theory.centers-monoids.html#1298" class="Bound">y</a> <a id="1300" href="group-theory.centers-monoids.html#1300" class="Bound">z</a> <a id="1302" class="Symbol">:</a> <a id="1304" href="group-theory.centers-monoids.html#1045" class="Function">type-center-Monoid</a><a id="1322" class="Symbol">)</a> <a id="1324" class="Symbol">→</a>
    <a id="1330" href="group-theory.centers-monoids.html#1132" class="Function">mul-center-Monoid</a> <a id="1348" class="Symbol">(</a><a id="1349" href="group-theory.centers-monoids.html#1132" class="Function">mul-center-Monoid</a> <a id="1367" href="group-theory.centers-monoids.html#1296" class="Bound">x</a> <a id="1369" href="group-theory.centers-monoids.html#1298" class="Bound">y</a><a id="1370" class="Symbol">)</a> <a id="1372" href="group-theory.centers-monoids.html#1300" class="Bound">z</a> <a id="1374" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="1380" href="group-theory.centers-monoids.html#1132" class="Function">mul-center-Monoid</a> <a id="1398" href="group-theory.centers-monoids.html#1296" class="Bound">x</a> <a id="1400" class="Symbol">(</a><a id="1401" href="group-theory.centers-monoids.html#1132" class="Function">mul-center-Monoid</a> <a id="1419" href="group-theory.centers-monoids.html#1298" class="Bound">y</a> <a id="1421" href="group-theory.centers-monoids.html#1300" class="Bound">z</a><a id="1422" class="Symbol">)</a>
  <a id="1426" href="group-theory.centers-monoids.html#1259" class="Function">associative-mul-center-Monoid</a> <a id="1456" class="Symbol">=</a>
    <a id="1462" href="group-theory.submonoids.html#3914" class="Function">associative-mul-Submonoid</a> <a id="1488" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="1490" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a>

  <a id="1507" href="group-theory.centers-monoids.html#1507" class="Function">inclusion-center-Monoid</a> <a id="1531" class="Symbol">:</a>
    <a id="1537" href="group-theory.centers-monoids.html#1045" class="Function">type-center-Monoid</a> <a id="1556" class="Symbol">→</a> <a id="1558" href="group-theory.monoids.html#1116" class="Function">type-Monoid</a> <a id="1570" href="group-theory.centers-monoids.html#620" class="Bound">M</a>
  <a id="1574" href="group-theory.centers-monoids.html#1507" class="Function">inclusion-center-Monoid</a> <a id="1598" class="Symbol">=</a>
    <a id="1604" href="group-theory.submonoids.html#2637" class="Function">inclusion-Submonoid</a> <a id="1624" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="1626" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a>

  <a id="1643" href="group-theory.centers-monoids.html#1643" class="Function">preserves-mul-inclusion-center-Monoid</a> <a id="1681" class="Symbol">:</a>
    <a id="1687" class="Symbol">{</a><a id="1688" href="group-theory.centers-monoids.html#1688" class="Bound">x</a> <a id="1690" href="group-theory.centers-monoids.html#1690" class="Bound">y</a> <a id="1692" class="Symbol">:</a> <a id="1694" href="group-theory.centers-monoids.html#1045" class="Function">type-center-Monoid</a><a id="1712" class="Symbol">}</a> <a id="1714" class="Symbol">→</a>
    <a id="1720" href="group-theory.centers-monoids.html#1507" class="Function">inclusion-center-Monoid</a> <a id="1744" class="Symbol">(</a><a id="1745" href="group-theory.centers-monoids.html#1132" class="Function">mul-center-Monoid</a> <a id="1763" href="group-theory.centers-monoids.html#1688" class="Bound">x</a> <a id="1765" href="group-theory.centers-monoids.html#1690" class="Bound">y</a><a id="1766" class="Symbol">)</a> <a id="1768" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="1774" href="group-theory.monoids.html#1359" class="Function">mul-Monoid</a> <a id="1785" href="group-theory.centers-monoids.html#620" class="Bound">M</a>
      <a id="1793" class="Symbol">(</a> <a id="1795" href="group-theory.centers-monoids.html#1507" class="Function">inclusion-center-Monoid</a> <a id="1819" href="group-theory.centers-monoids.html#1688" class="Bound">x</a><a id="1820" class="Symbol">)</a>
      <a id="1828" class="Symbol">(</a> <a id="1830" href="group-theory.centers-monoids.html#1507" class="Function">inclusion-center-Monoid</a> <a id="1854" href="group-theory.centers-monoids.html#1690" class="Bound">y</a><a id="1855" class="Symbol">)</a>
  <a id="1859" href="group-theory.centers-monoids.html#1643" class="Function">preserves-mul-inclusion-center-Monoid</a> <a id="1897" class="Symbol">{</a><a id="1898" href="group-theory.centers-monoids.html#1898" class="Bound">x</a><a id="1899" class="Symbol">}</a> <a id="1901" class="Symbol">{</a><a id="1902" href="group-theory.centers-monoids.html#1902" class="Bound">y</a><a id="1903" class="Symbol">}</a> <a id="1905" class="Symbol">=</a>
    <a id="1911" href="group-theory.submonoids.html#5345" class="Function">preserves-mul-inclusion-Submonoid</a> <a id="1945" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="1947" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a> <a id="1961" class="Symbol">{</a><a id="1962" href="group-theory.centers-monoids.html#1898" class="Bound">x</a><a id="1963" class="Symbol">}</a> <a id="1965" class="Symbol">{</a><a id="1966" href="group-theory.centers-monoids.html#1902" class="Bound">y</a><a id="1967" class="Symbol">}</a>

  <a id="1972" href="group-theory.centers-monoids.html#1972" class="Function">hom-inclusion-center-Monoid</a> <a id="2000" class="Symbol">:</a>
    <a id="2006" href="group-theory.homomorphisms-monoids.html#2364" class="Function">hom-Monoid</a> <a id="2017" href="group-theory.centers-monoids.html#952" class="Function">monoid-center-Monoid</a> <a id="2038" href="group-theory.centers-monoids.html#620" class="Bound">M</a>
  <a id="2042" href="group-theory.centers-monoids.html#1972" class="Function">hom-inclusion-center-Monoid</a> <a id="2070" class="Symbol">=</a>
    <a id="2076" href="group-theory.submonoids.html#5567" class="Function">hom-inclusion-Submonoid</a> <a id="2100" href="group-theory.centers-monoids.html#620" class="Bound">M</a> <a id="2102" href="group-theory.centers-monoids.html#754" class="Function">center-Monoid</a>
</pre>