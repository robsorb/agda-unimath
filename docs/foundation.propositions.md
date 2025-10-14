# Propositions

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="foundation.propositions.html" class="Module">foundation.propositions</a> <a id="56" class="Keyword">where</a>

<a id="63" class="Keyword">open</a> <a id="68" class="Keyword">import</a> <a id="75" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a> <a id="104" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation.retracts-of-types.html" class="Module">foundation.retracts-of-types</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="403" class="Keyword">open</a> <a id="408" class="Keyword">import</a> <a id="415" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="foundation-core.propositional-maps.html" class="Module">foundation-core.propositional-maps</a>
<a id="570" class="Keyword">open</a> <a id="575" class="Keyword">import</a> <a id="582" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="614" class="Keyword">open</a> <a id="619" class="Keyword">import</a> <a id="626" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

## Properties

### Propositions are `k+1`-truncated for any `k`

<pre class="Agda"><a id="750" class="Keyword">abstract</a>
  <a id="is-trunc-is-prop"></a><a id="761" href="foundation.propositions.html#761" class="Function">is-trunc-is-prop</a> <a id="778" class="Symbol">:</a>
    <a id="784" class="Symbol">{</a><a id="785" href="foundation.propositions.html#785" class="Bound">l</a> <a id="787" class="Symbol">:</a> <a id="789" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="794" class="Symbol">}</a> <a id="796" class="Symbol">(</a><a id="797" href="foundation.propositions.html#797" class="Bound">k</a> <a id="799" class="Symbol">:</a> <a id="801" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="802" class="Symbol">)</a> <a id="804" class="Symbol">{</a><a id="805" href="foundation.propositions.html#805" class="Bound">A</a> <a id="807" class="Symbol">:</a> <a id="809" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="812" href="foundation.propositions.html#785" class="Bound">l</a><a id="813" class="Symbol">}</a> <a id="815" class="Symbol">→</a> <a id="817" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="825" href="foundation.propositions.html#805" class="Bound">A</a> <a id="827" class="Symbol">→</a> <a id="829" href="foundation-core.truncated-types.html#1305" class="Function">is-trunc</a> <a id="838" class="Symbol">(</a><a id="839" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="846" href="foundation.propositions.html#797" class="Bound">k</a><a id="847" class="Symbol">)</a> <a id="849" href="foundation.propositions.html#805" class="Bound">A</a>
  <a id="853" href="foundation.propositions.html#761" class="Function">is-trunc-is-prop</a> <a id="870" href="foundation.propositions.html#870" class="Bound">k</a> <a id="872" href="foundation.propositions.html#872" class="Bound">is-prop-A</a> <a id="882" href="foundation.propositions.html#882" class="Bound">x</a> <a id="884" href="foundation.propositions.html#884" class="Bound">y</a> <a id="886" class="Symbol">=</a> <a id="888" href="foundation.contractible-types.html#4079" class="Function">is-trunc-is-contr</a> <a id="906" href="foundation.propositions.html#870" class="Bound">k</a> <a id="908" class="Symbol">(</a><a id="909" href="foundation.propositions.html#872" class="Bound">is-prop-A</a> <a id="919" href="foundation.propositions.html#882" class="Bound">x</a> <a id="921" href="foundation.propositions.html#884" class="Bound">y</a><a id="922" class="Symbol">)</a>

<a id="truncated-type-Prop"></a><a id="925" href="foundation.propositions.html#925" class="Function">truncated-type-Prop</a> <a id="945" class="Symbol">:</a> <a id="947" class="Symbol">{</a><a id="948" href="foundation.propositions.html#948" class="Bound">l</a> <a id="950" class="Symbol">:</a> <a id="952" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="957" class="Symbol">}</a> <a id="959" class="Symbol">(</a><a id="960" href="foundation.propositions.html#960" class="Bound">k</a> <a id="962" class="Symbol">:</a> <a id="964" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="965" class="Symbol">)</a> <a id="967" class="Symbol">→</a> <a id="969" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="974" href="foundation.propositions.html#948" class="Bound">l</a> <a id="976" class="Symbol">→</a> <a id="978" href="foundation-core.truncated-types.html#1603" class="Function">Truncated-Type</a> <a id="993" href="foundation.propositions.html#948" class="Bound">l</a> <a id="995" class="Symbol">(</a><a id="996" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="1003" href="foundation.propositions.html#960" class="Bound">k</a><a id="1004" class="Symbol">)</a>
<a id="1006" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1010" class="Symbol">(</a><a id="1011" href="foundation.propositions.html#925" class="Function">truncated-type-Prop</a> <a id="1031" href="foundation.propositions.html#1031" class="Bound">k</a> <a id="1033" href="foundation.propositions.html#1033" class="Bound">P</a><a id="1034" class="Symbol">)</a> <a id="1036" class="Symbol">=</a> <a id="1038" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1048" href="foundation.propositions.html#1033" class="Bound">P</a>
<a id="1050" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1054" class="Symbol">(</a><a id="1055" href="foundation.propositions.html#925" class="Function">truncated-type-Prop</a> <a id="1075" href="foundation.propositions.html#1075" class="Bound">k</a> <a id="1077" href="foundation.propositions.html#1077" class="Bound">P</a><a id="1078" class="Symbol">)</a> <a id="1080" class="Symbol">=</a> <a id="1082" href="foundation.propositions.html#761" class="Function">is-trunc-is-prop</a> <a id="1099" href="foundation.propositions.html#1075" class="Bound">k</a> <a id="1101" class="Symbol">(</a><a id="1102" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1120" href="foundation.propositions.html#1077" class="Bound">P</a><a id="1121" class="Symbol">)</a>
</pre>
### Propositions are closed under retracts

<pre class="Agda"><a id="1180" class="Keyword">module</a> <a id="1187" href="foundation.propositions.html#1187" class="Module">_</a>
  <a id="1191" class="Symbol">{</a><a id="1192" href="foundation.propositions.html#1192" class="Bound">l1</a> <a id="1195" href="foundation.propositions.html#1195" class="Bound">l2</a> <a id="1198" class="Symbol">:</a> <a id="1200" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1205" class="Symbol">}</a> <a id="1207" class="Symbol">{</a><a id="1208" href="foundation.propositions.html#1208" class="Bound">A</a> <a id="1210" class="Symbol">:</a> <a id="1212" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1215" href="foundation.propositions.html#1192" class="Bound">l1</a><a id="1217" class="Symbol">}</a> <a id="1219" class="Symbol">{</a><a id="1220" href="foundation.propositions.html#1220" class="Bound">B</a> <a id="1222" class="Symbol">:</a> <a id="1224" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1227" href="foundation.propositions.html#1195" class="Bound">l2</a><a id="1229" class="Symbol">}</a>
  <a id="1233" class="Keyword">where</a>

  <a id="1242" href="foundation.propositions.html#1242" class="Function">is-prop-retract-of</a> <a id="1261" class="Symbol">:</a> <a id="1263" href="foundation.propositions.html#1208" class="Bound">A</a> <a id="1265" href="foundation-core.retracts-of-types.html#1754" class="Function Operator">retract-of</a> <a id="1276" href="foundation.propositions.html#1220" class="Bound">B</a> <a id="1278" class="Symbol">→</a> <a id="1280" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1288" href="foundation.propositions.html#1220" class="Bound">B</a> <a id="1290" class="Symbol">→</a> <a id="1292" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1300" href="foundation.propositions.html#1208" class="Bound">A</a>
  <a id="1304" href="foundation.propositions.html#1242" class="Function">is-prop-retract-of</a> <a id="1323" class="Symbol">=</a> <a id="1325" href="foundation-core.truncated-types.html#3674" class="Function">is-trunc-retract-of</a>
</pre>
### If a type embeds into a proposition, then it is a proposition

<pre class="Agda"><a id="1425" class="Keyword">abstract</a>
  <a id="is-prop-is-emb"></a><a id="1436" href="foundation.propositions.html#1436" class="Function">is-prop-is-emb</a> <a id="1451" class="Symbol">:</a>
    <a id="1457" class="Symbol">{</a><a id="1458" href="foundation.propositions.html#1458" class="Bound">l1</a> <a id="1461" href="foundation.propositions.html#1461" class="Bound">l2</a> <a id="1464" class="Symbol">:</a> <a id="1466" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1471" class="Symbol">}</a> <a id="1473" class="Symbol">{</a><a id="1474" href="foundation.propositions.html#1474" class="Bound">A</a> <a id="1476" class="Symbol">:</a> <a id="1478" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1481" href="foundation.propositions.html#1458" class="Bound">l1</a><a id="1483" class="Symbol">}</a> <a id="1485" class="Symbol">{</a><a id="1486" href="foundation.propositions.html#1486" class="Bound">B</a> <a id="1488" class="Symbol">:</a> <a id="1490" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1493" href="foundation.propositions.html#1461" class="Bound">l2</a><a id="1495" class="Symbol">}</a> <a id="1497" class="Symbol">(</a><a id="1498" href="foundation.propositions.html#1498" class="Bound">f</a> <a id="1500" class="Symbol">:</a> <a id="1502" href="foundation.propositions.html#1474" class="Bound">A</a> <a id="1504" class="Symbol">→</a> <a id="1506" href="foundation.propositions.html#1486" class="Bound">B</a><a id="1507" class="Symbol">)</a> <a id="1509" class="Symbol">→</a>
    <a id="1515" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="1522" href="foundation.propositions.html#1498" class="Bound">f</a> <a id="1524" class="Symbol">→</a> <a id="1526" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1534" href="foundation.propositions.html#1486" class="Bound">B</a> <a id="1536" class="Symbol">→</a> <a id="1538" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1546" href="foundation.propositions.html#1474" class="Bound">A</a>
  <a id="1550" href="foundation.propositions.html#1436" class="Function">is-prop-is-emb</a> <a id="1565" class="Symbol">=</a> <a id="1567" href="foundation-core.truncated-types.html#5097" class="Function">is-trunc-is-emb</a> <a id="1583" href="foundation-core.truncation-levels.html#542" class="InductiveConstructor">neg-two-𝕋</a>

<a id="1594" class="Keyword">abstract</a>
  <a id="is-prop-emb"></a><a id="1605" href="foundation.propositions.html#1605" class="Function">is-prop-emb</a> <a id="1617" class="Symbol">:</a>
    <a id="1623" class="Symbol">{</a><a id="1624" href="foundation.propositions.html#1624" class="Bound">l1</a> <a id="1627" href="foundation.propositions.html#1627" class="Bound">l2</a> <a id="1630" class="Symbol">:</a> <a id="1632" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1637" class="Symbol">}</a> <a id="1639" class="Symbol">{</a><a id="1640" href="foundation.propositions.html#1640" class="Bound">A</a> <a id="1642" class="Symbol">:</a> <a id="1644" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1647" href="foundation.propositions.html#1624" class="Bound">l1</a><a id="1649" class="Symbol">}</a> <a id="1651" class="Symbol">{</a><a id="1652" href="foundation.propositions.html#1652" class="Bound">B</a> <a id="1654" class="Symbol">:</a> <a id="1656" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1659" href="foundation.propositions.html#1627" class="Bound">l2</a><a id="1661" class="Symbol">}</a> <a id="1663" class="Symbol">(</a><a id="1664" href="foundation.propositions.html#1664" class="Bound">f</a> <a id="1666" class="Symbol">:</a> <a id="1668" href="foundation.propositions.html#1640" class="Bound">A</a> <a id="1670" href="foundation-core.embeddings.html#1627" class="Function Operator">↪</a> <a id="1672" href="foundation.propositions.html#1652" class="Bound">B</a><a id="1673" class="Symbol">)</a> <a id="1675" class="Symbol">→</a> <a id="1677" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1685" href="foundation.propositions.html#1652" class="Bound">B</a> <a id="1687" class="Symbol">→</a> <a id="1689" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1697" href="foundation.propositions.html#1640" class="Bound">A</a>
  <a id="1701" href="foundation.propositions.html#1605" class="Function">is-prop-emb</a> <a id="1713" class="Symbol">=</a> <a id="1715" href="foundation-core.truncated-types.html#5363" class="Function">is-trunc-emb</a> <a id="1728" href="foundation-core.truncation-levels.html#542" class="InductiveConstructor">neg-two-𝕋</a>
</pre>
### A type is a proposition if and only if it embeds into the unit type

<pre class="Agda"><a id="1824" class="Keyword">module</a> <a id="1831" href="foundation.propositions.html#1831" class="Module">_</a>
  <a id="1835" class="Symbol">{</a><a id="1836" href="foundation.propositions.html#1836" class="Bound">l</a> <a id="1838" class="Symbol">:</a> <a id="1840" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1845" class="Symbol">}</a> <a id="1847" class="Symbol">{</a><a id="1848" href="foundation.propositions.html#1848" class="Bound">A</a> <a id="1850" class="Symbol">:</a> <a id="1852" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1855" href="foundation.propositions.html#1836" class="Bound">l</a><a id="1856" class="Symbol">}</a>
  <a id="1860" class="Keyword">where</a>

  <a id="1869" class="Keyword">abstract</a>
    <a id="1882" href="foundation.propositions.html#1882" class="Function">is-prop-is-emb-terminal-map</a> <a id="1910" class="Symbol">:</a> <a id="1912" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="1919" class="Symbol">(</a><a id="1920" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="1933" href="foundation.propositions.html#1848" class="Bound">A</a><a id="1934" class="Symbol">)</a> <a id="1936" class="Symbol">→</a> <a id="1938" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1946" href="foundation.propositions.html#1848" class="Bound">A</a>
    <a id="1952" href="foundation.propositions.html#1882" class="Function">is-prop-is-emb-terminal-map</a> <a id="1980" href="foundation.propositions.html#1980" class="Bound">H</a> <a id="1982" class="Symbol">=</a>
      <a id="1990" href="foundation.propositions.html#1436" class="Function">is-prop-is-emb</a> <a id="2005" class="Symbol">(</a><a id="2006" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="2019" href="foundation.propositions.html#1848" class="Bound">A</a><a id="2020" class="Symbol">)</a> <a id="2022" href="foundation.propositions.html#1980" class="Bound">H</a> <a id="2024" href="foundation.unit-type.html#4543" class="Function">is-prop-unit</a>

  <a id="2040" class="Keyword">abstract</a>
    <a id="2053" href="foundation.propositions.html#2053" class="Function">is-emb-terminal-map-is-prop</a> <a id="2081" class="Symbol">:</a> <a id="2083" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2091" href="foundation.propositions.html#1848" class="Bound">A</a> <a id="2093" class="Symbol">→</a> <a id="2095" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="2102" class="Symbol">(</a><a id="2103" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="2116" href="foundation.propositions.html#1848" class="Bound">A</a><a id="2117" class="Symbol">)</a>
    <a id="2123" href="foundation.propositions.html#2053" class="Function">is-emb-terminal-map-is-prop</a> <a id="2151" href="foundation.propositions.html#2151" class="Bound">H</a> <a id="2153" class="Symbol">=</a>
      <a id="2161" href="foundation-core.propositional-maps.html#2081" class="Function">is-emb-is-prop-map</a> <a id="2180" class="Symbol">(λ</a> <a id="2183" href="foundation.propositions.html#2183" class="Bound">y</a> <a id="2185" class="Symbol">→</a> <a id="2187" href="foundation-core.propositions.html#4010" class="Function">is-prop-equiv</a> <a id="2201" class="Symbol">(</a><a id="2202" href="foundation.fibers-of-maps.html#2027" class="Function">equiv-fiber-terminal-map</a> <a id="2227" href="foundation.propositions.html#2183" class="Bound">y</a><a id="2228" class="Symbol">)</a> <a id="2230" href="foundation.propositions.html#2151" class="Bound">H</a><a id="2231" class="Symbol">)</a>
</pre>
### Two equivalent types are equivalently propositions

<pre class="Agda"><a id="equiv-is-prop-equiv"></a><a id="2302" href="foundation.propositions.html#2302" class="Function">equiv-is-prop-equiv</a> <a id="2322" class="Symbol">:</a> <a id="2324" class="Symbol">{</a><a id="2325" href="foundation.propositions.html#2325" class="Bound">l1</a> <a id="2328" href="foundation.propositions.html#2328" class="Bound">l2</a> <a id="2331" class="Symbol">:</a> <a id="2333" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2338" class="Symbol">}</a> <a id="2340" class="Symbol">{</a><a id="2341" href="foundation.propositions.html#2341" class="Bound">A</a> <a id="2343" class="Symbol">:</a> <a id="2345" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2348" href="foundation.propositions.html#2325" class="Bound">l1</a><a id="2350" class="Symbol">}</a> <a id="2352" class="Symbol">{</a><a id="2353" href="foundation.propositions.html#2353" class="Bound">B</a> <a id="2355" class="Symbol">:</a> <a id="2357" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2360" href="foundation.propositions.html#2328" class="Bound">l2</a><a id="2362" class="Symbol">}</a> <a id="2364" class="Symbol">→</a>
  <a id="2368" href="foundation.propositions.html#2341" class="Bound">A</a> <a id="2370" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2372" href="foundation.propositions.html#2353" class="Bound">B</a> <a id="2374" class="Symbol">→</a> <a id="2376" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2384" href="foundation.propositions.html#2341" class="Bound">A</a> <a id="2386" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2388" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2396" href="foundation.propositions.html#2353" class="Bound">B</a>
<a id="2398" href="foundation.propositions.html#2302" class="Function">equiv-is-prop-equiv</a> <a id="2418" class="Symbol">{</a><a id="2419" class="Argument">A</a> <a id="2421" class="Symbol">=</a> <a id="2423" href="foundation.propositions.html#2423" class="Bound">A</a><a id="2424" class="Symbol">}</a> <a id="2426" class="Symbol">{</a><a id="2427" class="Argument">B</a> <a id="2429" class="Symbol">=</a> <a id="2431" href="foundation.propositions.html#2431" class="Bound">B</a><a id="2432" class="Symbol">}</a> <a id="2434" href="foundation.propositions.html#2434" class="Bound">e</a> <a id="2436" class="Symbol">=</a>
  <a id="2440" href="foundation.logical-equivalences.html#4644" class="Function">equiv-iff-is-prop</a>
    <a id="2462" class="Symbol">(</a> <a id="2464" href="foundation-core.propositions.html#10626" class="Function">is-prop-is-prop</a> <a id="2480" href="foundation.propositions.html#2423" class="Bound">A</a><a id="2481" class="Symbol">)</a>
    <a id="2487" class="Symbol">(</a> <a id="2489" href="foundation-core.propositions.html#10626" class="Function">is-prop-is-prop</a> <a id="2505" href="foundation.propositions.html#2431" class="Bound">B</a><a id="2506" class="Symbol">)</a>
    <a id="2512" class="Symbol">(</a> <a id="2514" href="foundation-core.propositions.html#4365" class="Function">is-prop-equiv&#39;</a> <a id="2529" href="foundation.propositions.html#2434" class="Bound">e</a><a id="2530" class="Symbol">)</a>
    <a id="2536" class="Symbol">(</a> <a id="2538" href="foundation-core.propositions.html#4010" class="Function">is-prop-equiv</a> <a id="2552" href="foundation.propositions.html#2434" class="Bound">e</a><a id="2553" class="Symbol">)</a>
</pre>
## See also

### Operations on propositions

There is a wide range of operations on propositions due to the rich structure of
intuitionistic logic. Below we give a structured overview of a notable selection
of such operations and their notation in the library.

The list is split into two sections, the first consists of operations that
generalize to arbitrary types and even sufficiently nice
[subuniverses](foundation.subuniverses.md), such as
$n$-[types](foundation-core.truncated-types.md).

| Name                                                        | Operator on types | Operator on propositions/subtypes |
| ----------------------------------------------------------- | ----------------- | --------------------------------- |
| [Dependent sum](foundation.dependent-pair-types.md)         | `Σ`               | `Σ-Prop`                          |
| [Dependent product](foundation.dependent-function-types.md) | `Π`               | `Π-Prop`                          |
| [Functions](foundation-core.function-types.md)              | `→`               | `⇒`                               |
| [Logical equivalence](foundation.logical-equivalences.md)   | `↔`               | `⇔`                               |
| [Product](foundation-core.cartesian-product-types.md)       | `×`               | `product-Prop`                    |
| [Join](synthetic-homotopy-theory.joins-of-types.md)         | `*`               | `join-Prop`                       |
| [Exclusive sum](foundation.exclusive-sum.md)                | `exclusive-sum`   | `exclusive-sum-Prop`              |
| [Coproduct](foundation-core.coproduct-types.md)             | `+`               | _N/A_                             |

Note that for many operations in the second section, there is an equivalent
operation on propositions in the first.

| Name                                                                         | Operator on types           | Operator on propositions/subtypes        |
| ---------------------------------------------------------------------------- | --------------------------- | ---------------------------------------- |
| [Initial object](foundation-core.empty-types.md)                             | `empty`                     | `empty-Prop`                             |
| [Terminal object](foundation.unit-type.md)                                   | `unit`                      | `unit-Prop`                              |
| [Existential quantification](foundation.existential-quantification.md)       | `exists-structure`          | `∃`                                      |
| [Unique existential quantification](foundation.uniqueness-quantification.md) | `uniquely-exists-structure` | `∃!`                                     |
| [Universal quantification](foundation.universal-quantification.md)           |                             | `∀'` (equivalent to `Π-Prop`)            |
| [Conjunction](foundation.conjunction.md)                                     |                             | `∧` (equivalent to `product-Prop`)       |
| [Disjunction](foundation.disjunction.md)                                     | `disjunction-type`          | `∨` (equivalent to `join-Prop`)          |
| [Exclusive disjunction](foundation.exclusive-disjunction.md)                 | `xor-type`                  | `⊻` (equivalent to `exclusive-sum-Prop`) |
| [Negation](foundation.negation.md)                                           | `¬`                         | `¬'`                                     |
| [Double negation](foundation.double-negation.md)                             | `¬¬`                        | `¬¬'`                                    |

We can also organize these operations by indexed and binary variants, giving us
the following table:

| Name                   | Binary | Indexed |
| ---------------------- | ------ | ------- |
| Product                | `×`    | `Π`     |
| Conjunction            | `∧`    | `∀'`    |
| Constructive existence | `+`    | `Σ`     |
| Existence              | `∨`    | `∃`     |
| Unique existence       | `⊻`    | `∃!`    |

### Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
