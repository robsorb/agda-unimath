# Points of reflexive globular types

<pre class="Agda"><a id="47" class="Symbol">{-#</a> <a id="51" class="Keyword">OPTIONS</a> <a id="59" class="Pragma">--guardedness</a> <a id="73" class="Symbol">#-}</a>

<a id="78" class="Keyword">module</a> <a id="85" href="globular-types.points-reflexive-globular-types.html" class="Module">globular-types.points-reflexive-globular-types</a> <a id="132" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="globular-types.points-globular-types.html" class="Module">globular-types.points-globular-types</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
</pre>
</details>

## Idea

Consider a [reflexive globular type](globular-types.reflexive-globular-types.md)
`G`. A
{{#concept "point" Disambiguation="reflexive globular type" Agda=point-Reflexive-Globular-Type}}
of `G` is a 0-cell of `G`. Equivalently, a point of `G` is a
[reflexive globular map](globular-types.reflexive-globular-maps.md) from the
[unit reflexive globular type](globular-types.unit-reflexive-globular-type.md)
into `G`.

The definition of points of reflexive globular types is much simpler than the
definition of [points](globular-types.points-globular-types.md) of ordinary
[globular types](globular-types.globular-types.md). This is due to the condition
that reflexive globular maps preserve reflexivity, and therefore the type of
higher cells relating the underlying 0-cell to itself is
[contractible](foundation-core.contractible-types.md).

## Definitions

### Points of reflexive globular types

<pre class="Agda"><a id="1257" class="Keyword">module</a> <a id="1264" href="globular-types.points-reflexive-globular-types.html#1264" class="Module">_</a>
  <a id="1268" class="Symbol">{</a><a id="1269" href="globular-types.points-reflexive-globular-types.html#1269" class="Bound">l1</a> <a id="1272" href="globular-types.points-reflexive-globular-types.html#1272" class="Bound">l2</a> <a id="1275" class="Symbol">:</a> <a id="1277" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1282" class="Symbol">}</a> <a id="1284" class="Symbol">(</a><a id="1285" href="globular-types.points-reflexive-globular-types.html#1285" class="Bound">G</a> <a id="1287" class="Symbol">:</a> <a id="1289" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="1313" href="globular-types.points-reflexive-globular-types.html#1269" class="Bound">l1</a> <a id="1316" href="globular-types.points-reflexive-globular-types.html#1272" class="Bound">l2</a><a id="1318" class="Symbol">)</a>
  <a id="1322" class="Keyword">where</a>

  <a id="1331" href="globular-types.points-reflexive-globular-types.html#1331" class="Function">point-Reflexive-Globular-Type</a> <a id="1361" class="Symbol">:</a> <a id="1363" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1366" href="globular-types.points-reflexive-globular-types.html#1269" class="Bound">l1</a>
  <a id="1371" href="globular-types.points-reflexive-globular-types.html#1331" class="Function">point-Reflexive-Globular-Type</a> <a id="1401" class="Symbol">=</a> <a id="1403" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="1434" href="globular-types.points-reflexive-globular-types.html#1285" class="Bound">G</a>
</pre>
### The underlying points of the underlying globular type of a reflexive globular type

<pre class="Agda"><a id="point-globular-type-point-Reflexive-Globular-Type"></a><a id="1537" href="globular-types.points-reflexive-globular-types.html#1537" class="Function">point-globular-type-point-Reflexive-Globular-Type</a> <a id="1587" class="Symbol">:</a>
  <a id="1591" class="Symbol">{</a><a id="1592" href="globular-types.points-reflexive-globular-types.html#1592" class="Bound">l1</a> <a id="1595" href="globular-types.points-reflexive-globular-types.html#1595" class="Bound">l2</a> <a id="1598" class="Symbol">:</a> <a id="1600" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1605" class="Symbol">}</a> <a id="1607" class="Symbol">(</a><a id="1608" href="globular-types.points-reflexive-globular-types.html#1608" class="Bound">G</a> <a id="1610" class="Symbol">:</a> <a id="1612" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="1636" href="globular-types.points-reflexive-globular-types.html#1592" class="Bound">l1</a> <a id="1639" href="globular-types.points-reflexive-globular-types.html#1595" class="Bound">l2</a><a id="1641" class="Symbol">)</a> <a id="1643" class="Symbol">→</a>
  <a id="1647" href="globular-types.points-reflexive-globular-types.html#1331" class="Function">point-Reflexive-Globular-Type</a> <a id="1677" href="globular-types.points-reflexive-globular-types.html#1608" class="Bound">G</a> <a id="1679" class="Symbol">→</a>
  <a id="1683" href="globular-types.points-globular-types.html#858" class="Record">point-Globular-Type</a> <a id="1703" class="Symbol">(</a><a id="1704" href="globular-types.reflexive-globular-types.html#4067" class="Field">globular-type-Reflexive-Globular-Type</a> <a id="1742" href="globular-types.points-reflexive-globular-types.html#1608" class="Bound">G</a><a id="1743" class="Symbol">)</a>
<a id="1745" href="globular-types.points-globular-types.html#972" class="Field">0-cell-point-Globular-Type</a>
  <a id="1774" class="Symbol">(</a> <a id="1776" href="globular-types.points-reflexive-globular-types.html#1537" class="Function">point-globular-type-point-Reflexive-Globular-Type</a> <a id="1826" href="globular-types.points-reflexive-globular-types.html#1826" class="Bound">G</a> <a id="1828" href="globular-types.points-reflexive-globular-types.html#1828" class="Bound">x</a><a id="1829" class="Symbol">)</a> <a id="1831" class="Symbol">=</a>
  <a id="1835" href="globular-types.points-reflexive-globular-types.html#1828" class="Bound">x</a>
<a id="1837" href="globular-types.points-globular-types.html#1037" class="Field">1-cell-point-point-Globular-Type</a>
  <a id="1872" class="Symbol">(</a> <a id="1874" href="globular-types.points-reflexive-globular-types.html#1537" class="Function">point-globular-type-point-Reflexive-Globular-Type</a> <a id="1924" href="globular-types.points-reflexive-globular-types.html#1924" class="Bound">G</a> <a id="1926" href="globular-types.points-reflexive-globular-types.html#1926" class="Bound">x</a><a id="1927" class="Symbol">)</a> <a id="1929" class="Symbol">=</a>
  <a id="1933" href="globular-types.points-reflexive-globular-types.html#1537" class="Function">point-globular-type-point-Reflexive-Globular-Type</a>
    <a id="1987" class="Symbol">(</a> <a id="1989" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="2044" href="globular-types.points-reflexive-globular-types.html#1924" class="Bound">G</a> <a id="2046" href="globular-types.points-reflexive-globular-types.html#1926" class="Bound">x</a> <a id="2048" href="globular-types.points-reflexive-globular-types.html#1926" class="Bound">x</a><a id="2049" class="Symbol">)</a>
    <a id="2055" class="Symbol">(</a> <a id="2057" href="globular-types.reflexive-globular-types.html#5428" class="Function">refl-1-cell-Reflexive-Globular-Type</a> <a id="2093" href="globular-types.points-reflexive-globular-types.html#1924" class="Bound">G</a><a id="2094" class="Symbol">)</a>
</pre>