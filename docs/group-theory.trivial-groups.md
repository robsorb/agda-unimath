# Trivial groups

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="group-theory.trivial-groups.html" class="Module">group-theory.trivial-groups</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="420" class="Keyword">open</a> <a id="425" class="Keyword">import</a> <a id="432" href="foundation.structure-identity-principle.html" class="Module">foundation.structure-identity-principle</a>
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="505" class="Keyword">open</a> <a id="510" class="Keyword">import</a> <a id="517" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="545" class="Keyword">open</a> <a id="550" class="Keyword">import</a> <a id="557" href="group-theory.abelian-groups.html" class="Module">group-theory.abelian-groups</a>
<a id="585" class="Keyword">open</a> <a id="590" class="Keyword">import</a> <a id="597" href="group-theory.full-subgroups.html" class="Module">group-theory.full-subgroups</a>
<a id="625" class="Keyword">open</a> <a id="630" class="Keyword">import</a> <a id="637" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="657" class="Keyword">open</a> <a id="662" class="Keyword">import</a> <a id="669" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
<a id="692" class="Keyword">open</a> <a id="697" class="Keyword">import</a> <a id="704" href="group-theory.trivial-subgroups.html" class="Module">group-theory.trivial-subgroups</a>
</pre>
</details>

## Idea

A [group](group-theory.groups.md) is said to be **trivial** if its underlying
type is [contractible](foundation-core.contractible-types.md). In other words, a
group is trivial if it consists only of the unit element.

## Definitions

### The predicate of being a trivial group

<pre class="Agda"><a id="1047" class="Keyword">module</a> <a id="1054" href="group-theory.trivial-groups.html#1054" class="Module">_</a>
  <a id="1058" class="Symbol">{</a><a id="1059" href="group-theory.trivial-groups.html#1059" class="Bound">l1</a> <a id="1062" class="Symbol">:</a> <a id="1064" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1069" class="Symbol">}</a> <a id="1071" class="Symbol">(</a><a id="1072" href="group-theory.trivial-groups.html#1072" class="Bound">G</a> <a id="1074" class="Symbol">:</a> <a id="1076" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1082" href="group-theory.trivial-groups.html#1059" class="Bound">l1</a><a id="1084" class="Symbol">)</a>
  <a id="1088" class="Keyword">where</a>

  <a id="1097" href="group-theory.trivial-groups.html#1097" class="Function">is-trivial-prop-Group</a> <a id="1119" class="Symbol">:</a> <a id="1121" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1126" href="group-theory.trivial-groups.html#1059" class="Bound">l1</a>
  <a id="1131" href="group-theory.trivial-groups.html#1097" class="Function">is-trivial-prop-Group</a> <a id="1153" class="Symbol">=</a> <a id="1155" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="1169" class="Symbol">(</a><a id="1170" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1181" href="group-theory.trivial-groups.html#1072" class="Bound">G</a><a id="1182" class="Symbol">)</a>

  <a id="1187" href="group-theory.trivial-groups.html#1187" class="Function">is-trivial-Group</a> <a id="1204" class="Symbol">:</a> <a id="1206" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1209" href="group-theory.trivial-groups.html#1059" class="Bound">l1</a>
  <a id="1214" href="group-theory.trivial-groups.html#1187" class="Function">is-trivial-Group</a> <a id="1231" class="Symbol">=</a> <a id="1233" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1243" href="group-theory.trivial-groups.html#1097" class="Function">is-trivial-prop-Group</a>
</pre>
### The type of trivial groups

<pre class="Agda"><a id="Trivial-Group"></a><a id="1310" href="group-theory.trivial-groups.html#1310" class="Function">Trivial-Group</a> <a id="1324" class="Symbol">:</a> <a id="1326" class="Symbol">(</a><a id="1327" href="group-theory.trivial-groups.html#1327" class="Bound">l</a> <a id="1329" class="Symbol">:</a> <a id="1331" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1336" class="Symbol">)</a> <a id="1338" class="Symbol">→</a> <a id="1340" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1343" class="Symbol">(</a><a id="1344" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1349" href="group-theory.trivial-groups.html#1327" class="Bound">l</a><a id="1350" class="Symbol">)</a>
<a id="1352" href="group-theory.trivial-groups.html#1310" class="Function">Trivial-Group</a> <a id="1366" href="group-theory.trivial-groups.html#1366" class="Bound">l</a> <a id="1368" class="Symbol">=</a> <a id="1370" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1372" class="Symbol">(</a><a id="1373" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1379" href="group-theory.trivial-groups.html#1366" class="Bound">l</a><a id="1380" class="Symbol">)</a> <a id="1382" href="group-theory.trivial-groups.html#1187" class="Function">is-trivial-Group</a>
</pre>
### The trivial group

<pre class="Agda"><a id="trivial-Group"></a><a id="1435" href="group-theory.trivial-groups.html#1435" class="Function">trivial-Group</a> <a id="1449" class="Symbol">:</a> <a id="1451" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1457" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1463" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1467" class="Symbol">(</a><a id="1468" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1472" href="group-theory.trivial-groups.html#1435" class="Function">trivial-Group</a><a id="1485" class="Symbol">)</a> <a id="1487" class="Symbol">=</a> <a id="1489" href="foundation.unit-type.html#5066" class="Function">unit-Set</a>
<a id="1498" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1502" class="Symbol">(</a><a id="1503" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1507" class="Symbol">(</a><a id="1508" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1512" href="group-theory.trivial-groups.html#1435" class="Function">trivial-Group</a><a id="1525" class="Symbol">))</a> <a id="1528" href="group-theory.trivial-groups.html#1528" class="Bound">x</a> <a id="1530" href="group-theory.trivial-groups.html#1530" class="Bound">y</a> <a id="1532" class="Symbol">=</a> <a id="1534" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a>
<a id="1539" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1543" class="Symbol">(</a><a id="1544" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1548" class="Symbol">(</a><a id="1549" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1553" href="group-theory.trivial-groups.html#1435" class="Function">trivial-Group</a><a id="1566" class="Symbol">))</a> <a id="1569" href="group-theory.trivial-groups.html#1569" class="Bound">x</a> <a id="1571" href="group-theory.trivial-groups.html#1571" class="Bound">y</a> <a id="1573" href="group-theory.trivial-groups.html#1573" class="Bound">z</a> <a id="1575" class="Symbol">=</a> <a id="1577" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
<a id="1582" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1586" class="Symbol">(</a><a id="1587" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1591" href="group-theory.trivial-groups.html#1435" class="Function">trivial-Group</a><a id="1604" class="Symbol">)</a> <a id="1606" class="Symbol">=</a> <a id="1608" class="Symbol">(</a><a id="1609" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a> <a id="1614" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1616" class="Symbol">(</a><a id="1617" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a> <a id="1627" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1629" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="1638" class="Symbol">))</a>
<a id="1641" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1645" class="Symbol">(</a><a id="1646" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1650" href="group-theory.trivial-groups.html#1435" class="Function">trivial-Group</a><a id="1663" class="Symbol">)</a> <a id="1665" class="Symbol">=</a> <a id="1667" class="Symbol">((λ</a> <a id="1671" href="group-theory.trivial-groups.html#1671" class="Bound">x</a> <a id="1673" class="Symbol">→</a> <a id="1675" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1679" class="Symbol">)</a> <a id="1681" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1683" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a> <a id="1693" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1695" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="1704" class="Symbol">)</a>
</pre>
## Properties

### The type of subgroups of a trivial group is contractible

<pre class="Agda"><a id="1796" class="Keyword">module</a> <a id="1803" href="group-theory.trivial-groups.html#1803" class="Module">_</a>
  <a id="1807" class="Symbol">{</a><a id="1808" href="group-theory.trivial-groups.html#1808" class="Bound">l1</a> <a id="1811" class="Symbol">:</a> <a id="1813" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1818" class="Symbol">}</a> <a id="1820" class="Symbol">(</a><a id="1821" href="group-theory.trivial-groups.html#1821" class="Bound">G</a> <a id="1823" class="Symbol">:</a> <a id="1825" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1831" href="group-theory.trivial-groups.html#1808" class="Bound">l1</a><a id="1833" class="Symbol">)</a>
  <a id="1837" class="Keyword">where</a>

  <a id="1846" class="Keyword">abstract</a>
    <a id="1859" href="group-theory.trivial-groups.html#1859" class="Function">is-contr-subgroup-is-trivial-Group</a> <a id="1894" class="Symbol">:</a>
      <a id="1902" href="group-theory.trivial-groups.html#1187" class="Function">is-trivial-Group</a> <a id="1919" href="group-theory.trivial-groups.html#1821" class="Bound">G</a> <a id="1921" class="Symbol">→</a> <a id="1923" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="1932" class="Symbol">(</a><a id="1933" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="1942" href="group-theory.trivial-groups.html#1808" class="Bound">l1</a> <a id="1945" href="group-theory.trivial-groups.html#1821" class="Bound">G</a><a id="1946" class="Symbol">)</a>
    <a id="1952" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1956" class="Symbol">(</a><a id="1957" href="group-theory.trivial-groups.html#1859" class="Function">is-contr-subgroup-is-trivial-Group</a> <a id="1992" href="group-theory.trivial-groups.html#1992" class="Bound">H</a><a id="1993" class="Symbol">)</a> <a id="1995" class="Symbol">=</a>
      <a id="2003" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a> <a id="2020" href="group-theory.trivial-groups.html#1821" class="Bound">G</a>
    <a id="2026" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2030" class="Symbol">(</a><a id="2031" href="group-theory.trivial-groups.html#1859" class="Function">is-contr-subgroup-is-trivial-Group</a> <a id="2066" href="group-theory.trivial-groups.html#2066" class="Bound">H</a><a id="2067" class="Symbol">)</a> <a id="2069" href="group-theory.trivial-groups.html#2069" class="Bound">K</a> <a id="2071" class="Symbol">=</a>
      <a id="2079" href="group-theory.subgroups.html#13494" class="Function">eq-has-same-elements-Subgroup</a> <a id="2109" href="group-theory.trivial-groups.html#1821" class="Bound">G</a>
        <a id="2119" class="Symbol">(</a> <a id="2121" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a> <a id="2138" href="group-theory.trivial-groups.html#1821" class="Bound">G</a><a id="2139" class="Symbol">)</a>
        <a id="2149" class="Symbol">(</a> <a id="2151" href="group-theory.trivial-groups.html#2069" class="Bound">K</a><a id="2152" class="Symbol">)</a>
        <a id="2162" class="Symbol">(</a> <a id="2164" class="Symbol">λ</a> <a id="2166" href="group-theory.trivial-groups.html#2166" class="Bound">x</a> <a id="2168" class="Symbol">→</a>
          <a id="2180" class="Symbol">(</a> <a id="2182" class="Symbol">λ</a> <a id="2184" class="Keyword">where</a> <a id="2190" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="2195" class="Symbol">→</a> <a id="2197" href="group-theory.subgroups.html#5540" class="Function">contains-unit-Subgroup</a> <a id="2220" href="group-theory.trivial-groups.html#1821" class="Bound">G</a> <a id="2222" href="group-theory.trivial-groups.html#2069" class="Bound">K</a><a id="2223" class="Symbol">)</a> <a id="2225" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
          <a id="2237" class="Symbol">(</a> <a id="2239" class="Symbol">λ</a> <a id="2241" href="group-theory.trivial-groups.html#2241" class="Bound">_</a> <a id="2243" class="Symbol">→</a>
            <a id="2257" href="group-theory.subgroups.html#4765" class="Function">is-closed-under-eq-Subgroup</a> <a id="2285" href="group-theory.trivial-groups.html#1821" class="Bound">G</a>
              <a id="2301" class="Symbol">(</a> <a id="2303" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a> <a id="2320" href="group-theory.trivial-groups.html#1821" class="Bound">G</a><a id="2321" class="Symbol">)</a>
              <a id="2337" class="Symbol">(</a> <a id="2339" href="group-theory.subgroups.html#5540" class="Function">contains-unit-Subgroup</a> <a id="2362" href="group-theory.trivial-groups.html#1821" class="Bound">G</a> <a id="2364" class="Symbol">(</a><a id="2365" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a> <a id="2382" href="group-theory.trivial-groups.html#1821" class="Bound">G</a><a id="2383" class="Symbol">))</a>
              <a id="2400" class="Symbol">(</a> <a id="2402" href="foundation-core.contractible-types.html#1197" class="Function">eq-is-contr</a> <a id="2414" href="group-theory.trivial-groups.html#2066" class="Bound">H</a><a id="2415" class="Symbol">)))</a>
</pre>
### The trivial group is abelian

<pre class="Agda"><a id="is-abelian-trivial-Group"></a><a id="2466" href="group-theory.trivial-groups.html#2466" class="Function">is-abelian-trivial-Group</a> <a id="2491" class="Symbol">:</a> <a id="2493" href="group-theory.abelian-groups.html#2218" class="Function">is-abelian-Group</a> <a id="2510" href="group-theory.trivial-groups.html#1435" class="Function">trivial-Group</a>
<a id="2524" href="group-theory.trivial-groups.html#2466" class="Function">is-abelian-trivial-Group</a> <a id="2549" href="group-theory.trivial-groups.html#2549" class="Bound">x</a> <a id="2551" href="group-theory.trivial-groups.html#2551" class="Bound">y</a> <a id="2553" class="Symbol">=</a> <a id="2555" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="trivial-Ab"></a><a id="2561" href="group-theory.trivial-groups.html#2561" class="Function">trivial-Ab</a> <a id="2572" class="Symbol">:</a> <a id="2574" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="2577" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2583" href="group-theory.trivial-groups.html#2561" class="Function">trivial-Ab</a> <a id="2594" class="Symbol">=</a> <a id="2596" class="Symbol">(</a><a id="2597" href="group-theory.trivial-groups.html#1435" class="Function">trivial-Group</a> <a id="2611" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2613" href="group-theory.trivial-groups.html#2466" class="Function">is-abelian-trivial-Group</a><a id="2637" class="Symbol">)</a>
</pre>