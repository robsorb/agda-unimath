# The W-type of natural numbers

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="trees.w-type-of-natural-numbers.html" class="Module">trees.w-type-of-natural-numbers</a> <a id="81" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="282" class="Keyword">open</a> <a id="287" class="Keyword">import</a> <a id="294" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="404" class="Keyword">open</a> <a id="409" class="Keyword">import</a> <a id="416" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="451" class="Keyword">open</a> <a id="456" class="Keyword">import</a> <a id="463" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="489" class="Keyword">open</a> <a id="494" class="Keyword">import</a> <a id="501" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="594" class="Keyword">open</a> <a id="599" class="Keyword">import</a> <a id="606" href="foundation.universal-property-empty-type.html" class="Module">foundation.universal-property-empty-type</a>
<a id="647" class="Keyword">open</a> <a id="652" class="Keyword">import</a> <a id="659" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="687" class="Keyword">open</a> <a id="692" class="Keyword">import</a> <a id="699" href="trees.w-types.html" class="Module">trees.w-types</a>
</pre>
</details>

## Idea

Since the type of natural numbers is an initial algebra for the polynomial
endofunctor

```text
  X ↦ X + 𝟙,
```

there is an equivalent definition of the natural numbers as a W-type.

## Definition

### The type of natural numbers defined as a W-type

<pre class="Agda"><a id="Nat-𝕎"></a><a id="1000" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a> <a id="1006" class="Symbol">:</a> <a id="1008" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1011" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1017" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a> <a id="1023" class="Symbol">=</a> <a id="1025" href="trees.w-types.html#1681" class="Datatype">𝕎</a> <a id="1027" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="1032" class="Symbol">(</a><a id="1033" href="foundation.booleans.html#2864" class="Function">Eq-bool</a> <a id="1041" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a><a id="1045" class="Symbol">)</a>

<a id="zero-Nat-𝕎"></a><a id="1048" href="trees.w-type-of-natural-numbers.html#1048" class="Function">zero-Nat-𝕎</a> <a id="1059" class="Symbol">:</a> <a id="1061" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a>
<a id="1067" href="trees.w-type-of-natural-numbers.html#1048" class="Function">zero-Nat-𝕎</a> <a id="1078" class="Symbol">=</a> <a id="1080" href="trees.w-types.html#2931" class="Function">constant-𝕎</a> <a id="1091" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="1097" href="foundation-core.function-types.html#307" class="Function">id</a>

<a id="succ-Nat-𝕎"></a><a id="1101" href="trees.w-type-of-natural-numbers.html#1101" class="Function">succ-Nat-𝕎</a> <a id="1112" class="Symbol">:</a> <a id="1114" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a> <a id="1120" class="Symbol">→</a> <a id="1122" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a>
<a id="1128" href="trees.w-type-of-natural-numbers.html#1101" class="Function">succ-Nat-𝕎</a> <a id="1139" href="trees.w-type-of-natural-numbers.html#1139" class="Bound">x</a> <a id="1141" class="Symbol">=</a> <a id="1143" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1150" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a> <a id="1155" class="Symbol">(λ</a> <a id="1158" href="trees.w-type-of-natural-numbers.html#1158" class="Bound">y</a> <a id="1160" class="Symbol">→</a> <a id="1162" href="trees.w-type-of-natural-numbers.html#1139" class="Bound">x</a><a id="1163" class="Symbol">)</a>
</pre>
## Properties

### The type of natural numbers is equivalent to the W-type Nat-𝕎

<pre class="Agda"><a id="Nat-𝕎-ℕ"></a><a id="1260" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a> <a id="1268" class="Symbol">:</a> <a id="1270" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1272" class="Symbol">→</a> <a id="1274" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a>
<a id="1280" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a> <a id="1288" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1295" class="Symbol">=</a> <a id="1297" href="trees.w-type-of-natural-numbers.html#1048" class="Function">zero-Nat-𝕎</a>
<a id="1308" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a> <a id="1316" class="Symbol">(</a><a id="1317" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1324" href="trees.w-type-of-natural-numbers.html#1324" class="Bound">x</a><a id="1325" class="Symbol">)</a> <a id="1327" class="Symbol">=</a> <a id="1329" href="trees.w-type-of-natural-numbers.html#1101" class="Function">succ-Nat-𝕎</a> <a id="1340" class="Symbol">(</a><a id="1341" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a> <a id="1349" href="trees.w-type-of-natural-numbers.html#1324" class="Bound">x</a><a id="1350" class="Symbol">)</a>

<a id="ℕ-Nat-𝕎"></a><a id="1353" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a> <a id="1361" class="Symbol">:</a> <a id="1363" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a> <a id="1369" class="Symbol">→</a> <a id="1371" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1373" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a> <a id="1381" class="Symbol">(</a><a id="1382" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1389" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a> <a id="1394" href="trees.w-type-of-natural-numbers.html#1394" class="Bound">α</a><a id="1395" class="Symbol">)</a> <a id="1397" class="Symbol">=</a> <a id="1399" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1406" class="Symbol">(</a><a id="1407" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a> <a id="1415" class="Symbol">(</a><a id="1416" href="trees.w-type-of-natural-numbers.html#1394" class="Bound">α</a> <a id="1418" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1422" class="Symbol">))</a>
<a id="1425" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a> <a id="1433" class="Symbol">(</a><a id="1434" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1441" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="1447" href="trees.w-type-of-natural-numbers.html#1447" class="Bound">α</a><a id="1448" class="Symbol">)</a> <a id="1450" class="Symbol">=</a> <a id="1452" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a>

<a id="is-section-ℕ-Nat-𝕎"></a><a id="1460" href="trees.w-type-of-natural-numbers.html#1460" class="Function">is-section-ℕ-Nat-𝕎</a> <a id="1479" class="Symbol">:</a> <a id="1481" class="Symbol">(</a><a id="1482" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a> <a id="1490" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1492" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a><a id="1499" class="Symbol">)</a> <a id="1501" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1503" href="foundation-core.function-types.html#307" class="Function">id</a>
<a id="1506" href="trees.w-type-of-natural-numbers.html#1460" class="Function">is-section-ℕ-Nat-𝕎</a> <a id="1525" class="Symbol">(</a><a id="1526" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1533" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a> <a id="1538" href="trees.w-type-of-natural-numbers.html#1538" class="Bound">α</a><a id="1539" class="Symbol">)</a> <a id="1541" class="Symbol">=</a>
  <a id="1545" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
    <a id="1552" class="Symbol">(</a> <a id="1554" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1561" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a><a id="1565" class="Symbol">)</a>
    <a id="1571" class="Symbol">(</a> <a id="1573" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a> <a id="1581" href="trees.w-type-of-natural-numbers.html#1594" class="Function">H</a><a id="1582" class="Symbol">)</a>
  <a id="1586" class="Keyword">where</a>
  <a id="1594" href="trees.w-type-of-natural-numbers.html#1594" class="Function">H</a> <a id="1596" class="Symbol">:</a> <a id="1598" class="Symbol">(</a><a id="1599" href="trees.w-type-of-natural-numbers.html#1599" class="Bound">z</a> <a id="1601" class="Symbol">:</a> <a id="1603" href="foundation.unit-type.html#950" class="Record">unit</a><a id="1607" class="Symbol">)</a> <a id="1609" class="Symbol">→</a> <a id="1611" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a> <a id="1619" class="Symbol">(</a><a id="1620" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a> <a id="1628" class="Symbol">(</a><a id="1629" href="trees.w-type-of-natural-numbers.html#1538" class="Bound">α</a> <a id="1631" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1635" class="Symbol">))</a> <a id="1638" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1640" href="trees.w-type-of-natural-numbers.html#1538" class="Bound">α</a> <a id="1642" href="trees.w-type-of-natural-numbers.html#1599" class="Bound">z</a>
  <a id="1646" href="trees.w-type-of-natural-numbers.html#1594" class="Function">H</a> <a id="1648" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a> <a id="1653" class="Symbol">=</a> <a id="1655" href="trees.w-type-of-natural-numbers.html#1460" class="Function">is-section-ℕ-Nat-𝕎</a> <a id="1674" class="Symbol">(</a><a id="1675" href="trees.w-type-of-natural-numbers.html#1538" class="Bound">α</a> <a id="1677" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1681" class="Symbol">)</a>
<a id="1683" href="trees.w-type-of-natural-numbers.html#1460" class="Function">is-section-ℕ-Nat-𝕎</a> <a id="1702" class="Symbol">(</a><a id="1703" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1710" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="1716" href="trees.w-type-of-natural-numbers.html#1716" class="Bound">α</a><a id="1717" class="Symbol">)</a> <a id="1719" class="Symbol">=</a>
  <a id="1723" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="1726" class="Symbol">(</a><a id="1727" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1734" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a><a id="1739" class="Symbol">)</a> <a id="1741" class="Symbol">(</a><a id="1742" href="foundation-core.contractible-types.html#1197" class="Function">eq-is-contr</a> <a id="1754" class="Symbol">(</a><a id="1755" href="foundation.universal-property-empty-type.html#2447" class="Function">universal-property-empty&#39;</a> <a id="1781" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a><a id="1786" class="Symbol">))</a>

<a id="is-retraction-ℕ-Nat-𝕎"></a><a id="1790" href="trees.w-type-of-natural-numbers.html#1790" class="Function">is-retraction-ℕ-Nat-𝕎</a> <a id="1812" class="Symbol">:</a> <a id="1814" class="Symbol">(</a><a id="1815" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a> <a id="1823" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1825" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a><a id="1832" class="Symbol">)</a> <a id="1834" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1836" href="foundation-core.function-types.html#307" class="Function">id</a>
<a id="1839" href="trees.w-type-of-natural-numbers.html#1790" class="Function">is-retraction-ℕ-Nat-𝕎</a> <a id="1861" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1868" class="Symbol">=</a> <a id="1870" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
<a id="1875" href="trees.w-type-of-natural-numbers.html#1790" class="Function">is-retraction-ℕ-Nat-𝕎</a> <a id="1897" class="Symbol">(</a><a id="1898" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1905" href="trees.w-type-of-natural-numbers.html#1905" class="Bound">x</a><a id="1906" class="Symbol">)</a> <a id="1908" class="Symbol">=</a> <a id="1910" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="1913" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1920" class="Symbol">(</a><a id="1921" href="trees.w-type-of-natural-numbers.html#1790" class="Function">is-retraction-ℕ-Nat-𝕎</a> <a id="1943" href="trees.w-type-of-natural-numbers.html#1905" class="Bound">x</a><a id="1944" class="Symbol">)</a>

<a id="is-equiv-Nat-𝕎-ℕ"></a><a id="1947" href="trees.w-type-of-natural-numbers.html#1947" class="Function">is-equiv-Nat-𝕎-ℕ</a> <a id="1964" class="Symbol">:</a> <a id="1966" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1975" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a>
<a id="1983" href="trees.w-type-of-natural-numbers.html#1947" class="Function">is-equiv-Nat-𝕎-ℕ</a> <a id="2000" class="Symbol">=</a>
  <a id="2004" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
    <a id="2031" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a>
    <a id="2043" href="trees.w-type-of-natural-numbers.html#1460" class="Function">is-section-ℕ-Nat-𝕎</a>
    <a id="2066" href="trees.w-type-of-natural-numbers.html#1790" class="Function">is-retraction-ℕ-Nat-𝕎</a>

<a id="equiv-Nat-𝕎-ℕ"></a><a id="2089" href="trees.w-type-of-natural-numbers.html#2089" class="Function">equiv-Nat-𝕎-ℕ</a> <a id="2103" class="Symbol">:</a> <a id="2105" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2107" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2109" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a>
<a id="2115" href="trees.w-type-of-natural-numbers.html#2089" class="Function">equiv-Nat-𝕎-ℕ</a> <a id="2129" class="Symbol">=</a> <a id="2131" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="2136" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a> <a id="2144" href="trees.w-type-of-natural-numbers.html#1947" class="Function">is-equiv-Nat-𝕎-ℕ</a>

<a id="is-equiv-ℕ-Nat-𝕎"></a><a id="2162" href="trees.w-type-of-natural-numbers.html#2162" class="Function">is-equiv-ℕ-Nat-𝕎</a> <a id="2179" class="Symbol">:</a> <a id="2181" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="2190" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a>
<a id="2198" href="trees.w-type-of-natural-numbers.html#2162" class="Function">is-equiv-ℕ-Nat-𝕎</a> <a id="2215" class="Symbol">=</a>
  <a id="2219" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
    <a id="2246" href="trees.w-type-of-natural-numbers.html#1260" class="Function">Nat-𝕎-ℕ</a>
    <a id="2258" href="trees.w-type-of-natural-numbers.html#1790" class="Function">is-retraction-ℕ-Nat-𝕎</a>
    <a id="2284" href="trees.w-type-of-natural-numbers.html#1460" class="Function">is-section-ℕ-Nat-𝕎</a>

<a id="equiv-ℕ-Nat-𝕎"></a><a id="2304" href="trees.w-type-of-natural-numbers.html#2304" class="Function">equiv-ℕ-Nat-𝕎</a> <a id="2318" class="Symbol">:</a> <a id="2320" href="trees.w-type-of-natural-numbers.html#1000" class="Function">Nat-𝕎</a> <a id="2326" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2328" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="2330" href="trees.w-type-of-natural-numbers.html#2304" class="Function">equiv-ℕ-Nat-𝕎</a> <a id="2344" class="Symbol">=</a> <a id="2346" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="2351" href="trees.w-type-of-natural-numbers.html#1353" class="Function">ℕ-Nat-𝕎</a> <a id="2359" href="trees.w-type-of-natural-numbers.html#2162" class="Function">is-equiv-ℕ-Nat-𝕎</a>
</pre>