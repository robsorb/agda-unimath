# ∞-connected maps

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="foundation.infinity-connected-maps.html" class="Module">foundation.infinity-connected-maps</a> <a id="71" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="foundation.connected-maps.html" class="Module">foundation.connected-maps</a>
<a id="165" class="Keyword">open</a> <a id="170" class="Keyword">import</a> <a id="177" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation.infinity-connected-types.html" class="Module">foundation.infinity-connected-types</a>
<a id="334" class="Keyword">open</a> <a id="339" class="Keyword">import</a> <a id="346" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="494" class="Keyword">open</a> <a id="499" class="Keyword">import</a> <a id="506" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="582" class="Keyword">open</a> <a id="587" class="Keyword">import</a> <a id="594" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="625" class="Keyword">open</a> <a id="630" class="Keyword">import</a> <a id="637" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A map `f : X → Y` is said to be
{{#concept "∞-connected" Disambiguation="map of types" Agda=is-∞-connected-map}}
if it is `k`-[connected](foundation.connected-maps.md) for all
[truncation levels](foundation-core.truncation-levels.md) `k`.

In particular, since [equivalences](foundation-core.equivalences.md) have
[contractible](foundation-core.contractible-types.md)
[fibers](foundation-core.fibers-of-maps.md), equivalences are ∞-connected.

## Definition

### ∞-connected maps

<pre class="Agda"><a id="1181" class="Keyword">module</a> <a id="1188" href="foundation.infinity-connected-maps.html#1188" class="Module">_</a>
  <a id="1192" class="Symbol">{</a><a id="1193" href="foundation.infinity-connected-maps.html#1193" class="Bound">l1</a> <a id="1196" href="foundation.infinity-connected-maps.html#1196" class="Bound">l2</a> <a id="1199" class="Symbol">:</a> <a id="1201" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1206" class="Symbol">}</a> <a id="1208" class="Symbol">{</a><a id="1209" href="foundation.infinity-connected-maps.html#1209" class="Bound">X</a> <a id="1211" class="Symbol">:</a> <a id="1213" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1216" href="foundation.infinity-connected-maps.html#1193" class="Bound">l1</a><a id="1218" class="Symbol">}</a> <a id="1220" class="Symbol">{</a><a id="1221" href="foundation.infinity-connected-maps.html#1221" class="Bound">Y</a> <a id="1223" class="Symbol">:</a> <a id="1225" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1228" href="foundation.infinity-connected-maps.html#1196" class="Bound">l2</a><a id="1230" class="Symbol">}</a> <a id="1232" class="Symbol">(</a><a id="1233" href="foundation.infinity-connected-maps.html#1233" class="Bound">f</a> <a id="1235" class="Symbol">:</a> <a id="1237" href="foundation.infinity-connected-maps.html#1209" class="Bound">X</a> <a id="1239" class="Symbol">→</a> <a id="1241" href="foundation.infinity-connected-maps.html#1221" class="Bound">Y</a><a id="1242" class="Symbol">)</a>
  <a id="1246" class="Keyword">where</a>

  <a id="1255" href="foundation.infinity-connected-maps.html#1255" class="Function">is-∞-connected-map-Prop</a> <a id="1279" class="Symbol">:</a> <a id="1281" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1286" class="Symbol">(</a><a id="1287" href="foundation.infinity-connected-maps.html#1193" class="Bound">l1</a> <a id="1290" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1292" href="foundation.infinity-connected-maps.html#1196" class="Bound">l2</a><a id="1294" class="Symbol">)</a>
  <a id="1298" href="foundation.infinity-connected-maps.html#1255" class="Function">is-∞-connected-map-Prop</a> <a id="1322" class="Symbol">=</a> <a id="1324" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1331" href="foundation.infinity-connected-maps.html#1221" class="Bound">Y</a> <a id="1333" class="Symbol">(λ</a> <a id="1336" href="foundation.infinity-connected-maps.html#1336" class="Bound">y</a> <a id="1338" class="Symbol">→</a> <a id="1340" href="foundation.infinity-connected-types.html#882" class="Function">is-∞-connected-Prop</a> <a id="1360" class="Symbol">(</a><a id="1361" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="1367" href="foundation.infinity-connected-maps.html#1233" class="Bound">f</a> <a id="1369" href="foundation.infinity-connected-maps.html#1336" class="Bound">y</a><a id="1370" class="Symbol">))</a>

  <a id="1376" href="foundation.infinity-connected-maps.html#1376" class="Function">is-∞-connected-map</a> <a id="1395" class="Symbol">:</a> <a id="1397" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1400" class="Symbol">(</a><a id="1401" href="foundation.infinity-connected-maps.html#1193" class="Bound">l1</a> <a id="1404" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1406" href="foundation.infinity-connected-maps.html#1196" class="Bound">l2</a><a id="1408" class="Symbol">)</a>
  <a id="1412" href="foundation.infinity-connected-maps.html#1376" class="Function">is-∞-connected-map</a> <a id="1431" class="Symbol">=</a> <a id="1433" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1443" href="foundation.infinity-connected-maps.html#1255" class="Function">is-∞-connected-map-Prop</a>

  <a id="1470" href="foundation.infinity-connected-maps.html#1470" class="Function">is-prop-is-∞-connected-map</a> <a id="1497" class="Symbol">:</a> <a id="1499" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1507" href="foundation.infinity-connected-maps.html#1376" class="Function">is-∞-connected-map</a>
  <a id="1528" href="foundation.infinity-connected-maps.html#1470" class="Function">is-prop-is-∞-connected-map</a> <a id="1555" class="Symbol">=</a> <a id="1557" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1575" href="foundation.infinity-connected-maps.html#1255" class="Function">is-∞-connected-map-Prop</a>
</pre>
### Equivalences are ∞-connected

<pre class="Agda"><a id="1646" class="Keyword">module</a> <a id="1653" href="foundation.infinity-connected-maps.html#1653" class="Module">_</a>
  <a id="1657" class="Symbol">{</a><a id="1658" href="foundation.infinity-connected-maps.html#1658" class="Bound">l1</a> <a id="1661" href="foundation.infinity-connected-maps.html#1661" class="Bound">l2</a> <a id="1664" class="Symbol">:</a> <a id="1666" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1671" class="Symbol">}</a> <a id="1673" class="Symbol">{</a><a id="1674" href="foundation.infinity-connected-maps.html#1674" class="Bound">X</a> <a id="1676" class="Symbol">:</a> <a id="1678" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1681" href="foundation.infinity-connected-maps.html#1658" class="Bound">l1</a><a id="1683" class="Symbol">}</a> <a id="1685" class="Symbol">{</a><a id="1686" href="foundation.infinity-connected-maps.html#1686" class="Bound">Y</a> <a id="1688" class="Symbol">:</a> <a id="1690" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1693" href="foundation.infinity-connected-maps.html#1661" class="Bound">l2</a><a id="1695" class="Symbol">}</a> <a id="1697" class="Symbol">(</a><a id="1698" href="foundation.infinity-connected-maps.html#1698" class="Bound">f</a> <a id="1700" class="Symbol">:</a> <a id="1702" href="foundation.infinity-connected-maps.html#1674" class="Bound">X</a> <a id="1704" class="Symbol">→</a> <a id="1706" href="foundation.infinity-connected-maps.html#1686" class="Bound">Y</a><a id="1707" class="Symbol">)</a>
  <a id="1711" class="Keyword">where</a>

  <a id="1720" href="foundation.infinity-connected-maps.html#1720" class="Function">is-∞-connected-map-is-equiv</a> <a id="1748" class="Symbol">:</a> <a id="1750" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1759" href="foundation.infinity-connected-maps.html#1698" class="Bound">f</a> <a id="1761" class="Symbol">→</a> <a id="1763" href="foundation.infinity-connected-maps.html#1376" class="Function">is-∞-connected-map</a> <a id="1782" href="foundation.infinity-connected-maps.html#1698" class="Bound">f</a>
  <a id="1786" href="foundation.infinity-connected-maps.html#1720" class="Function">is-∞-connected-map-is-equiv</a> <a id="1814" href="foundation.infinity-connected-maps.html#1814" class="Bound">is-equiv-f</a> <a id="1825" href="foundation.infinity-connected-maps.html#1825" class="Bound">k</a> <a id="1827" href="foundation.infinity-connected-maps.html#1827" class="Bound">x</a> <a id="1829" class="Symbol">=</a>
    <a id="1835" href="foundation.connected-maps.html#7004" class="Function">is-connected-map-is-equiv</a> <a id="1861" href="foundation.infinity-connected-maps.html#1814" class="Bound">is-equiv-f</a> <a id="1872" href="foundation.infinity-connected-maps.html#1825" class="Bound">k</a>
</pre>