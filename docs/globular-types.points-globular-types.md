# Points of globular types

<pre class="Agda"><a id="37" class="Symbol">{-#</a> <a id="41" class="Keyword">OPTIONS</a> <a id="49" class="Pragma">--guardedness</a> <a id="63" class="Symbol">#-}</a>

<a id="68" class="Keyword">module</a> <a id="75" href="globular-types.points-globular-types.html" class="Module">globular-types.points-globular-types</a> <a id="112" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="globular-types.globular-maps.html" class="Module">globular-types.globular-maps</a>
<a id="282" class="Keyword">open</a> <a id="287" class="Keyword">import</a> <a id="294" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="globular-types.unit-globular-type.html" class="Module">globular-types.unit-globular-type</a>
</pre>
</details>

## Idea

A {{#concept "point" Disambiguation="globular type" Agda=point-Globular-Type}}
of a [globular type](globular-types.globular-types.md) `G` consists of a 0-cell
`x₀ : G₀` and a point in the globular type `G' x₀ x₀` of 1-cells from `x₀` to
itself. Equivalently, a point is a
[globular map](globular-types.globular-maps.md) from the
[unit globular type](globular-types.unit-globular-type.md) `𝟏` to `G`.

## Definitions

### Points of globular types

<pre class="Agda"><a id="851" class="Keyword">record</a> <a id="point-Globular-Type"></a><a id="858" href="globular-types.points-globular-types.html#858" class="Record">point-Globular-Type</a>
  <a id="880" class="Symbol">{</a><a id="881" href="globular-types.points-globular-types.html#881" class="Bound">l1</a> <a id="884" href="globular-types.points-globular-types.html#884" class="Bound">l2</a> <a id="887" class="Symbol">:</a> <a id="889" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="894" class="Symbol">}</a> <a id="896" class="Symbol">(</a><a id="897" href="globular-types.points-globular-types.html#897" class="Bound">G</a> <a id="899" class="Symbol">:</a> <a id="901" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="915" href="globular-types.points-globular-types.html#881" class="Bound">l1</a> <a id="918" href="globular-types.points-globular-types.html#884" class="Bound">l2</a><a id="920" class="Symbol">)</a> <a id="922" class="Symbol">:</a> <a id="924" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="927" class="Symbol">(</a><a id="928" href="globular-types.points-globular-types.html#881" class="Bound">l1</a> <a id="931" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="933" href="globular-types.points-globular-types.html#884" class="Bound">l2</a><a id="935" class="Symbol">)</a>
  <a id="939" class="Keyword">where</a>
  <a id="947" class="Keyword">coinductive</a>

  <a id="962" class="Keyword">field</a>
    <a id="point-Globular-Type.0-cell-point-Globular-Type"></a><a id="972" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a> <a id="999" class="Symbol">:</a> <a id="1001" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1022" href="globular-types.points-globular-types.html#897" class="Bound">G</a>

  <a id="1027" class="Keyword">field</a>
    <a id="point-Globular-Type.1-cell-point-point-Globular-Type"></a><a id="1037" href="globular-types.points-globular-types.html#1037" class="Field">1-cell-point-point-Globular-Type</a> <a id="1070" class="Symbol">:</a>
      <a id="1078" href="globular-types.points-globular-types.html#858" class="Record">point-Globular-Type</a>
        <a id="1106" class="Symbol">(</a> <a id="1108" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1143" href="globular-types.points-globular-types.html#897" class="Bound">G</a>
          <a id="1155" class="Symbol">(</a> <a id="1157" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a><a id="1183" class="Symbol">)</a>
          <a id="1195" class="Symbol">(</a> <a id="1197" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a><a id="1223" class="Symbol">))</a>

<a id="1227" class="Keyword">open</a> <a id="1232" href="globular-types.points-globular-types.html#858" class="Module">point-Globular-Type</a> <a id="1252" class="Keyword">public</a>

<a id="1-cell-point-Globular-Type"></a><a id="1260" href="globular-types.points-globular-types.html#1260" class="Function">1-cell-point-Globular-Type</a> <a id="1287" class="Symbol">:</a>
  <a id="1291" class="Symbol">{</a><a id="1292" href="globular-types.points-globular-types.html#1292" class="Bound">l1</a> <a id="1295" href="globular-types.points-globular-types.html#1295" class="Bound">l2</a> <a id="1298" class="Symbol">:</a> <a id="1300" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1305" class="Symbol">}</a> <a id="1307" class="Symbol">(</a><a id="1308" href="globular-types.points-globular-types.html#1308" class="Bound">G</a> <a id="1310" class="Symbol">:</a> <a id="1312" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1326" href="globular-types.points-globular-types.html#1292" class="Bound">l1</a> <a id="1329" href="globular-types.points-globular-types.html#1295" class="Bound">l2</a><a id="1331" class="Symbol">)</a> <a id="1333" class="Symbol">(</a><a id="1334" href="globular-types.points-globular-types.html#1334" class="Bound">x</a> <a id="1336" class="Symbol">:</a> <a id="1338" href="globular-types.points-globular-types.html#858" class="Record">point-Globular-Type</a> <a id="1358" href="globular-types.points-globular-types.html#1308" class="Bound">G</a><a id="1359" class="Symbol">)</a> <a id="1361" class="Symbol">→</a>
  <a id="1365" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="1386" href="globular-types.points-globular-types.html#1308" class="Bound">G</a>
    <a id="1392" class="Symbol">(</a><a id="1393" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a> <a id="1420" href="globular-types.points-globular-types.html#1334" class="Bound">x</a><a id="1421" class="Symbol">)</a>
    <a id="1427" class="Symbol">(</a> <a id="1429" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a> <a id="1456" href="globular-types.points-globular-types.html#1334" class="Bound">x</a><a id="1457" class="Symbol">)</a>
<a id="1459" href="globular-types.points-globular-types.html#1260" class="Function">1-cell-point-Globular-Type</a> <a id="1486" href="globular-types.points-globular-types.html#1486" class="Bound">G</a> <a id="1488" href="globular-types.points-globular-types.html#1488" class="Bound">x</a> <a id="1490" class="Symbol">=</a>
  <a id="1494" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a> <a id="1521" class="Symbol">(</a><a id="1522" href="globular-types.points-globular-types.html#1037" class="Field">1-cell-point-point-Globular-Type</a> <a id="1555" href="globular-types.points-globular-types.html#1488" class="Bound">x</a><a id="1556" class="Symbol">)</a>
</pre>
## Properties

### Evaluating globular maps at points

<pre class="Agda"><a id="ev-point-globular-map"></a><a id="1626" href="globular-types.points-globular-types.html#1626" class="Function">ev-point-globular-map</a> <a id="1648" class="Symbol">:</a>
  <a id="1652" class="Symbol">{</a><a id="1653" href="globular-types.points-globular-types.html#1653" class="Bound">l1</a> <a id="1656" href="globular-types.points-globular-types.html#1656" class="Bound">l2</a> <a id="1659" href="globular-types.points-globular-types.html#1659" class="Bound">l3</a> <a id="1662" href="globular-types.points-globular-types.html#1662" class="Bound">l4</a> <a id="1665" class="Symbol">:</a> <a id="1667" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1672" class="Symbol">}</a> <a id="1674" class="Symbol">{</a><a id="1675" href="globular-types.points-globular-types.html#1675" class="Bound">G</a> <a id="1677" class="Symbol">:</a> <a id="1679" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1693" href="globular-types.points-globular-types.html#1653" class="Bound">l1</a> <a id="1696" href="globular-types.points-globular-types.html#1656" class="Bound">l2</a><a id="1698" class="Symbol">}</a> <a id="1700" class="Symbol">{</a><a id="1701" href="globular-types.points-globular-types.html#1701" class="Bound">H</a> <a id="1703" class="Symbol">:</a> <a id="1705" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1719" href="globular-types.points-globular-types.html#1659" class="Bound">l3</a> <a id="1722" href="globular-types.points-globular-types.html#1662" class="Bound">l4</a><a id="1724" class="Symbol">}</a>
  <a id="1728" class="Symbol">(</a><a id="1729" href="globular-types.points-globular-types.html#1729" class="Bound">f</a> <a id="1731" class="Symbol">:</a> <a id="1733" href="globular-types.globular-maps.html#774" class="Record">globular-map</a> <a id="1746" href="globular-types.points-globular-types.html#1675" class="Bound">G</a> <a id="1748" href="globular-types.points-globular-types.html#1701" class="Bound">H</a><a id="1749" class="Symbol">)</a> <a id="1751" class="Symbol">→</a> <a id="1753" href="globular-types.points-globular-types.html#858" class="Record">point-Globular-Type</a> <a id="1773" href="globular-types.points-globular-types.html#1675" class="Bound">G</a> <a id="1775" class="Symbol">→</a> <a id="1777" href="globular-types.points-globular-types.html#858" class="Record">point-Globular-Type</a> <a id="1797" href="globular-types.points-globular-types.html#1701" class="Bound">H</a>
<a id="1799" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a> <a id="1826" class="Symbol">(</a><a id="1827" href="globular-types.points-globular-types.html#1626" class="Function">ev-point-globular-map</a> <a id="1849" href="globular-types.points-globular-types.html#1849" class="Bound">f</a> <a id="1851" href="globular-types.points-globular-types.html#1851" class="Bound">x</a><a id="1852" class="Symbol">)</a> <a id="1854" class="Symbol">=</a>
  <a id="1858" href="globular-types.globular-maps.html#928" class="Field">0-cell-globular-map</a> <a id="1878" href="globular-types.points-globular-types.html#1849" class="Bound">f</a> <a id="1880" class="Symbol">(</a><a id="1881" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a> <a id="1908" href="globular-types.points-globular-types.html#1851" class="Bound">x</a><a id="1909" class="Symbol">)</a>
<a id="1911" href="globular-types.points-globular-types.html#1037" class="Field">1-cell-point-point-Globular-Type</a> <a id="1944" class="Symbol">(</a><a id="1945" href="globular-types.points-globular-types.html#1626" class="Function">ev-point-globular-map</a> <a id="1967" href="globular-types.points-globular-types.html#1967" class="Bound">f</a> <a id="1969" href="globular-types.points-globular-types.html#1969" class="Bound">x</a><a id="1970" class="Symbol">)</a> <a id="1972" class="Symbol">=</a>
  <a id="1976" href="globular-types.points-globular-types.html#1626" class="Function">ev-point-globular-map</a>
    <a id="2002" class="Symbol">(</a> <a id="2004" href="globular-types.globular-maps.html#1009" class="Field">1-cell-globular-map-globular-map</a> <a id="2037" href="globular-types.points-globular-types.html#1967" class="Bound">f</a><a id="2038" class="Symbol">)</a>
    <a id="2044" class="Symbol">(</a> <a id="2046" href="globular-types.points-globular-types.html#1037" class="Field">1-cell-point-point-Globular-Type</a> <a id="2079" href="globular-types.points-globular-types.html#1969" class="Bound">x</a><a id="2080" class="Symbol">)</a>
</pre>
### Points are globular maps from the terminal globular type

#### The globular map associated to a point of a globular type

<pre class="Agda"><a id="globular-map-point-Globular-Type"></a><a id="2221" href="globular-types.points-globular-types.html#2221" class="Function">globular-map-point-Globular-Type</a> <a id="2254" class="Symbol">:</a>
  <a id="2258" class="Symbol">{</a><a id="2259" href="globular-types.points-globular-types.html#2259" class="Bound">l1</a> <a id="2262" href="globular-types.points-globular-types.html#2262" class="Bound">l2</a> <a id="2265" class="Symbol">:</a> <a id="2267" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2272" class="Symbol">}</a> <a id="2274" class="Symbol">(</a><a id="2275" href="globular-types.points-globular-types.html#2275" class="Bound">G</a> <a id="2277" class="Symbol">:</a> <a id="2279" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="2293" href="globular-types.points-globular-types.html#2259" class="Bound">l1</a> <a id="2296" href="globular-types.points-globular-types.html#2262" class="Bound">l2</a><a id="2298" class="Symbol">)</a> <a id="2300" class="Symbol">→</a>
  <a id="2304" href="globular-types.points-globular-types.html#858" class="Record">point-Globular-Type</a> <a id="2324" href="globular-types.points-globular-types.html#2275" class="Bound">G</a> <a id="2326" class="Symbol">→</a> <a id="2328" href="globular-types.globular-maps.html#774" class="Record">globular-map</a> <a id="2341" href="globular-types.unit-globular-type.html#733" class="Function">unit-Globular-Type</a> <a id="2360" href="globular-types.points-globular-types.html#2275" class="Bound">G</a>
<a id="2362" href="globular-types.globular-maps.html#928" class="Field">0-cell-globular-map</a> <a id="2382" class="Symbol">(</a><a id="2383" href="globular-types.points-globular-types.html#2221" class="Function">globular-map-point-Globular-Type</a> <a id="2416" href="globular-types.points-globular-types.html#2416" class="Bound">G</a> <a id="2418" href="globular-types.points-globular-types.html#2418" class="Bound">x</a><a id="2419" class="Symbol">)</a> <a id="2421" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a> <a id="2426" class="Symbol">=</a>
  <a id="2430" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a> <a id="2457" href="globular-types.points-globular-types.html#2418" class="Bound">x</a>
<a id="2459" href="globular-types.globular-maps.html#1009" class="Field">1-cell-globular-map-globular-map</a> <a id="2492" class="Symbol">(</a><a id="2493" href="globular-types.points-globular-types.html#2221" class="Function">globular-map-point-Globular-Type</a> <a id="2526" href="globular-types.points-globular-types.html#2526" class="Bound">G</a> <a id="2528" href="globular-types.points-globular-types.html#2528" class="Bound">x</a><a id="2529" class="Symbol">)</a> <a id="2531" class="Symbol">=</a>
  <a id="2535" href="globular-types.points-globular-types.html#2221" class="Function">globular-map-point-Globular-Type</a>
    <a id="2572" class="Symbol">(</a> <a id="2574" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="2609" href="globular-types.points-globular-types.html#2526" class="Bound">G</a> <a id="2611" class="Symbol">_</a> <a id="2613" class="Symbol">_)</a>
    <a id="2620" class="Symbol">(</a> <a id="2622" href="globular-types.points-globular-types.html#1037" class="Field">1-cell-point-point-Globular-Type</a> <a id="2655" href="globular-types.points-globular-types.html#2528" class="Bound">x</a><a id="2656" class="Symbol">)</a>
</pre>