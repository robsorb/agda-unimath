# Conjugation on concrete groups

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="group-theory.conjugation-concrete-groups.html" class="Module">group-theory.conjugation-concrete-groups</a> <a id="91" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="147" class="Keyword">open</a> <a id="152" class="Keyword">import</a> <a id="159" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="group-theory.conjugation.html" class="Module">group-theory.conjugation</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="group-theory.homomorphisms-concrete-groups.html" class="Module">group-theory.homomorphisms-concrete-groups</a>

<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="higher-group-theory.conjugation.html" class="Module">higher-group-theory.conjugation</a>
</pre>
</details>

## Idea

The **conjugation operation** on a
[concrete group](group-theory.concrete-groups.md) `G` can be seen as a
[homomorphism](group-theory.homomorphisms-concrete-groups.md) of concrete groups
and as a [concrete group action](group-theory.concrete-group-actions.md).

Note that the delooping of the
[conjugation homomorphism](structured-types.conjugation-pointed-types.md) can be
defined directly for [pointed types](structured-types.pointed-types.md), which
applies also to the case of [∞-groups](higher-group-theory.higher-groups.md).

## Definitions

### The conjugation homomorphism on concrete groups

<pre class="Agda"><a id="1072" class="Keyword">module</a> <a id="1079" href="group-theory.conjugation-concrete-groups.html#1079" class="Module">_</a>
  <a id="1083" class="Symbol">{</a><a id="1084" href="group-theory.conjugation-concrete-groups.html#1084" class="Bound">l</a> <a id="1086" class="Symbol">:</a> <a id="1088" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1093" class="Symbol">}</a> <a id="1095" class="Symbol">(</a><a id="1096" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="1098" class="Symbol">:</a> <a id="1100" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="1115" href="group-theory.conjugation-concrete-groups.html#1084" class="Bound">l</a><a id="1116" class="Symbol">)</a> <a id="1118" class="Symbol">(</a><a id="1119" href="group-theory.conjugation-concrete-groups.html#1119" class="Bound">g</a> <a id="1121" class="Symbol">:</a> <a id="1123" href="group-theory.concrete-groups.html#2510" class="Function">type-Concrete-Group</a> <a id="1143" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a><a id="1144" class="Symbol">)</a>
  <a id="1148" class="Keyword">where</a>

  <a id="1157" href="group-theory.conjugation-concrete-groups.html#1157" class="Function">conjugation-Concrete-Group</a> <a id="1184" class="Symbol">:</a> <a id="1186" href="group-theory.homomorphisms-concrete-groups.html#678" class="Function">hom-Concrete-Group</a> <a id="1205" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="1207" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a>
  <a id="1211" href="group-theory.conjugation-concrete-groups.html#1157" class="Function">conjugation-Concrete-Group</a> <a id="1238" class="Symbol">=</a> <a id="1240" href="higher-group-theory.conjugation.html#826" class="Function">conjugation-∞-Group</a> <a id="1260" class="Symbol">(</a><a id="1261" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="1284" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a><a id="1285" class="Symbol">)</a> <a id="1287" href="group-theory.conjugation-concrete-groups.html#1119" class="Bound">g</a>

  <a id="1292" href="group-theory.conjugation-concrete-groups.html#1292" class="Function">classifying-map-conjugation-Concrete-Group</a> <a id="1335" class="Symbol">:</a>
    <a id="1341" href="group-theory.concrete-groups.html#1503" class="Function">classifying-type-Concrete-Group</a> <a id="1373" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="1375" class="Symbol">→</a> <a id="1377" href="group-theory.concrete-groups.html#1503" class="Function">classifying-type-Concrete-Group</a> <a id="1409" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a>
  <a id="1413" href="group-theory.conjugation-concrete-groups.html#1292" class="Function">classifying-map-conjugation-Concrete-Group</a> <a id="1456" class="Symbol">=</a>
    <a id="1462" href="group-theory.homomorphisms-concrete-groups.html#1274" class="Function">classifying-map-hom-Concrete-Group</a> <a id="1497" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="1499" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="1501" href="group-theory.conjugation-concrete-groups.html#1157" class="Function">conjugation-Concrete-Group</a>

  <a id="1531" href="group-theory.conjugation-concrete-groups.html#1531" class="Function">preserves-point-classifying-map-conjugation-Concrete-Group</a> <a id="1590" class="Symbol">:</a>
    <a id="1596" href="group-theory.conjugation-concrete-groups.html#1292" class="Function">classifying-map-conjugation-Concrete-Group</a> <a id="1639" class="Symbol">(</a><a id="1640" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="1661" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a><a id="1662" class="Symbol">)</a> <a id="1664" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="1670" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="1691" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a>
  <a id="1695" href="group-theory.conjugation-concrete-groups.html#1531" class="Function">preserves-point-classifying-map-conjugation-Concrete-Group</a> <a id="1754" class="Symbol">=</a>
    <a id="1760" href="group-theory.homomorphisms-concrete-groups.html#1552" class="Function">preserves-point-classifying-map-hom-Concrete-Group</a> <a id="1811" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="1813" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a>
      <a id="1821" class="Symbol">(</a> <a id="1823" href="group-theory.conjugation-concrete-groups.html#1157" class="Function">conjugation-Concrete-Group</a><a id="1849" class="Symbol">)</a>

  <a id="1854" href="group-theory.conjugation-concrete-groups.html#1854" class="Function">map-conjugation-Concrete-Group</a> <a id="1885" class="Symbol">:</a>
    <a id="1891" href="group-theory.concrete-groups.html#2510" class="Function">type-Concrete-Group</a> <a id="1911" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="1913" class="Symbol">→</a> <a id="1915" href="group-theory.concrete-groups.html#2510" class="Function">type-Concrete-Group</a> <a id="1935" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a>
  <a id="1939" href="group-theory.conjugation-concrete-groups.html#1854" class="Function">map-conjugation-Concrete-Group</a> <a id="1970" class="Symbol">=</a>
    <a id="1976" href="group-theory.homomorphisms-concrete-groups.html#1920" class="Function">map-hom-Concrete-Group</a> <a id="1999" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="2001" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a> <a id="2003" href="group-theory.conjugation-concrete-groups.html#1157" class="Function">conjugation-Concrete-Group</a>

  <a id="2033" href="group-theory.conjugation-concrete-groups.html#2033" class="Function">compute-map-conjugation-Concrete-Group</a> <a id="2072" class="Symbol">:</a>
    <a id="2078" href="group-theory.conjugation.html#2564" class="Function">conjugation-Group&#39;</a> <a id="2097" class="Symbol">(</a><a id="2098" href="group-theory.concrete-groups.html#7049" class="Function">group-Concrete-Group</a> <a id="2119" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a><a id="2120" class="Symbol">)</a> <a id="2122" href="group-theory.conjugation-concrete-groups.html#1119" class="Bound">g</a> <a id="2124" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="2130" href="group-theory.conjugation-concrete-groups.html#1854" class="Function">map-conjugation-Concrete-Group</a>
  <a id="2163" href="group-theory.conjugation-concrete-groups.html#2033" class="Function">compute-map-conjugation-Concrete-Group</a> <a id="2202" href="group-theory.conjugation-concrete-groups.html#2202" class="Bound">x</a> <a id="2204" class="Symbol">=</a>
    <a id="2210" class="Symbol">(</a> <a id="2212" href="foundation-core.identity-types.html#7454" class="Function">assoc</a> <a id="2218" class="Symbol">(</a><a id="2219" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="2223" href="group-theory.conjugation-concrete-groups.html#1119" class="Bound">g</a><a id="2224" class="Symbol">)</a> <a id="2226" href="group-theory.conjugation-concrete-groups.html#2202" class="Bound">x</a> <a id="2228" href="group-theory.conjugation-concrete-groups.html#1119" class="Bound">g</a><a id="2229" class="Symbol">)</a> <a id="2231" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="2237" class="Symbol">(</a> <a id="2239" href="higher-group-theory.conjugation.html#1546" class="Function">compute-map-conjugation-∞-Group</a> <a id="2271" class="Symbol">(</a><a id="2272" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="2295" href="group-theory.conjugation-concrete-groups.html#1096" class="Bound">G</a><a id="2296" class="Symbol">)</a> <a id="2298" href="group-theory.conjugation-concrete-groups.html#1119" class="Bound">g</a> <a id="2300" href="group-theory.conjugation-concrete-groups.html#2202" class="Bound">x</a><a id="2301" class="Symbol">)</a>
</pre>