# Paths in undirected graphs

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="graph-theory.paths-undirected-graphs.html" class="Module">graph-theory.paths-undirected-graphs</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
<a id="358" class="Keyword">open</a> <a id="363" class="Keyword">import</a> <a id="370" href="graph-theory.walks-undirected-graphs.html" class="Module">graph-theory.walks-undirected-graphs</a>
</pre>
</details>

## Idea

A **path** in an [undirected graph](graph-theory.undirected-graphs.md) `G` is a
[walk](graph-theory.walks-undirected-graphs.md) `w` in G such that the inclusion
of the type of vertices on `w` into the vertices of `G` is an
[injective](foundation.injective-maps.md) function.

**Note:** It is too much to ask for for this function to be an
[embedding](foundation-core.embeddings.md), since the type of vertices on `w` is
equivalent to the
[standard finite type](univalent-combinatorics.standard-finite-types.md)
`Fin (n + 1)` where `n` is the length of the walk, whereas the type of vertices
of `G` does not need to be a [set](foundation-core.sets.md).

## Definition

<pre class="Agda"><a id="1109" class="Keyword">module</a> <a id="1116" href="graph-theory.paths-undirected-graphs.html#1116" class="Module">_</a>
  <a id="1120" class="Symbol">{</a><a id="1121" href="graph-theory.paths-undirected-graphs.html#1121" class="Bound">l1</a> <a id="1124" href="graph-theory.paths-undirected-graphs.html#1124" class="Bound">l2</a> <a id="1127" class="Symbol">:</a> <a id="1129" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1134" class="Symbol">}</a> <a id="1136" class="Symbol">(</a><a id="1137" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a> <a id="1139" class="Symbol">:</a> <a id="1141" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="1158" href="graph-theory.paths-undirected-graphs.html#1121" class="Bound">l1</a> <a id="1161" href="graph-theory.paths-undirected-graphs.html#1124" class="Bound">l2</a><a id="1163" class="Symbol">)</a>
  <a id="1167" class="Keyword">where</a>

  <a id="1176" href="graph-theory.paths-undirected-graphs.html#1176" class="Function">is-path-walk-Undirected-Graph</a> <a id="1206" class="Symbol">:</a>
    <a id="1212" class="Symbol">{</a><a id="1213" href="graph-theory.paths-undirected-graphs.html#1213" class="Bound">x</a> <a id="1215" href="graph-theory.paths-undirected-graphs.html#1215" class="Bound">y</a> <a id="1217" class="Symbol">:</a> <a id="1219" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="1243" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a><a id="1244" class="Symbol">}</a> <a id="1246" class="Symbol">→</a> <a id="1248" href="graph-theory.walks-undirected-graphs.html#1491" class="Datatype">walk-Undirected-Graph</a> <a id="1270" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a> <a id="1272" href="graph-theory.paths-undirected-graphs.html#1213" class="Bound">x</a> <a id="1274" href="graph-theory.paths-undirected-graphs.html#1215" class="Bound">y</a> <a id="1276" class="Symbol">→</a> <a id="1278" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1281" href="graph-theory.paths-undirected-graphs.html#1121" class="Bound">l1</a>
  <a id="1286" href="graph-theory.paths-undirected-graphs.html#1176" class="Function">is-path-walk-Undirected-Graph</a> <a id="1316" href="graph-theory.paths-undirected-graphs.html#1316" class="Bound">w</a> <a id="1318" class="Symbol">=</a>
    <a id="1324" href="foundation-core.injective-maps.html#1182" class="Function">is-injective</a> <a id="1337" class="Symbol">(</a><a id="1338" href="graph-theory.walks-undirected-graphs.html#2746" class="Function">vertex-vertex-on-walk-Undirected-Graph</a> <a id="1377" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a> <a id="1379" href="graph-theory.paths-undirected-graphs.html#1316" class="Bound">w</a><a id="1380" class="Symbol">)</a>

  <a id="1385" href="graph-theory.paths-undirected-graphs.html#1385" class="Function">path-Undirected-Graph</a> <a id="1407" class="Symbol">:</a>
    <a id="1413" class="Symbol">(</a><a id="1414" href="graph-theory.paths-undirected-graphs.html#1414" class="Bound">x</a> <a id="1416" href="graph-theory.paths-undirected-graphs.html#1416" class="Bound">y</a> <a id="1418" class="Symbol">:</a> <a id="1420" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="1444" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a><a id="1445" class="Symbol">)</a> <a id="1447" class="Symbol">→</a> <a id="1449" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1452" class="Symbol">(</a><a id="1453" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1458" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1464" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1466" href="graph-theory.paths-undirected-graphs.html#1121" class="Bound">l1</a> <a id="1469" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1471" href="graph-theory.paths-undirected-graphs.html#1124" class="Bound">l2</a><a id="1473" class="Symbol">)</a>
  <a id="1477" href="graph-theory.paths-undirected-graphs.html#1385" class="Function">path-Undirected-Graph</a> <a id="1499" href="graph-theory.paths-undirected-graphs.html#1499" class="Bound">x</a> <a id="1501" href="graph-theory.paths-undirected-graphs.html#1501" class="Bound">y</a> <a id="1503" class="Symbol">=</a>
    <a id="1509" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1511" class="Symbol">(</a><a id="1512" href="graph-theory.walks-undirected-graphs.html#1491" class="Datatype">walk-Undirected-Graph</a> <a id="1534" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a> <a id="1536" href="graph-theory.paths-undirected-graphs.html#1499" class="Bound">x</a> <a id="1538" href="graph-theory.paths-undirected-graphs.html#1501" class="Bound">y</a><a id="1539" class="Symbol">)</a> <a id="1541" href="graph-theory.paths-undirected-graphs.html#1176" class="Function">is-path-walk-Undirected-Graph</a>

  <a id="1574" href="graph-theory.paths-undirected-graphs.html#1574" class="Function">walk-path-Undirected-Graph</a> <a id="1601" class="Symbol">:</a>
    <a id="1607" class="Symbol">{</a><a id="1608" href="graph-theory.paths-undirected-graphs.html#1608" class="Bound">x</a> <a id="1610" href="graph-theory.paths-undirected-graphs.html#1610" class="Bound">y</a> <a id="1612" class="Symbol">:</a> <a id="1614" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="1638" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a><a id="1639" class="Symbol">}</a> <a id="1641" class="Symbol">→</a>
    <a id="1647" href="graph-theory.paths-undirected-graphs.html#1385" class="Function">path-Undirected-Graph</a> <a id="1669" href="graph-theory.paths-undirected-graphs.html#1608" class="Bound">x</a> <a id="1671" href="graph-theory.paths-undirected-graphs.html#1610" class="Bound">y</a> <a id="1673" class="Symbol">→</a> <a id="1675" href="graph-theory.walks-undirected-graphs.html#1491" class="Datatype">walk-Undirected-Graph</a> <a id="1697" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a> <a id="1699" href="graph-theory.paths-undirected-graphs.html#1608" class="Bound">x</a> <a id="1701" href="graph-theory.paths-undirected-graphs.html#1610" class="Bound">y</a>
  <a id="1705" href="graph-theory.paths-undirected-graphs.html#1574" class="Function">walk-path-Undirected-Graph</a> <a id="1732" href="graph-theory.paths-undirected-graphs.html#1732" class="Bound">p</a> <a id="1734" class="Symbol">=</a> <a id="1736" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1740" href="graph-theory.paths-undirected-graphs.html#1732" class="Bound">p</a>

  <a id="1745" href="graph-theory.paths-undirected-graphs.html#1745" class="Function">length-path-Undirected-Graph</a> <a id="1774" class="Symbol">:</a>
    <a id="1780" class="Symbol">{</a><a id="1781" href="graph-theory.paths-undirected-graphs.html#1781" class="Bound">x</a> <a id="1783" href="graph-theory.paths-undirected-graphs.html#1783" class="Bound">y</a> <a id="1785" class="Symbol">:</a> <a id="1787" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="1811" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a><a id="1812" class="Symbol">}</a> <a id="1814" class="Symbol">→</a>
    <a id="1820" href="graph-theory.paths-undirected-graphs.html#1385" class="Function">path-Undirected-Graph</a> <a id="1842" href="graph-theory.paths-undirected-graphs.html#1781" class="Bound">x</a> <a id="1844" href="graph-theory.paths-undirected-graphs.html#1783" class="Bound">y</a> <a id="1846" class="Symbol">→</a> <a id="1848" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
  <a id="1852" href="graph-theory.paths-undirected-graphs.html#1745" class="Function">length-path-Undirected-Graph</a> <a id="1881" href="graph-theory.paths-undirected-graphs.html#1881" class="Bound">p</a> <a id="1883" class="Symbol">=</a>
    <a id="1889" href="graph-theory.walks-undirected-graphs.html#4978" class="Function">length-walk-Undirected-Graph</a> <a id="1918" href="graph-theory.paths-undirected-graphs.html#1137" class="Bound">G</a> <a id="1920" class="Symbol">(</a><a id="1921" href="graph-theory.paths-undirected-graphs.html#1574" class="Function">walk-path-Undirected-Graph</a> <a id="1948" href="graph-theory.paths-undirected-graphs.html#1881" class="Bound">p</a><a id="1949" class="Symbol">)</a>
</pre>
## Properties

### The constant walk is a path

<pre class="Agda"><a id="is-path-refl-walk-Undirected-Graph"></a><a id="2012" href="graph-theory.paths-undirected-graphs.html#2012" class="Function">is-path-refl-walk-Undirected-Graph</a> <a id="2047" class="Symbol">:</a>
  <a id="2051" class="Symbol">{</a><a id="2052" href="graph-theory.paths-undirected-graphs.html#2052" class="Bound">l1</a> <a id="2055" href="graph-theory.paths-undirected-graphs.html#2055" class="Bound">l2</a> <a id="2058" class="Symbol">:</a> <a id="2060" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2065" class="Symbol">}</a> <a id="2067" class="Symbol">(</a><a id="2068" href="graph-theory.paths-undirected-graphs.html#2068" class="Bound">G</a> <a id="2070" class="Symbol">:</a> <a id="2072" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="2089" href="graph-theory.paths-undirected-graphs.html#2052" class="Bound">l1</a> <a id="2092" href="graph-theory.paths-undirected-graphs.html#2055" class="Bound">l2</a><a id="2094" class="Symbol">)</a> <a id="2096" class="Symbol">(</a><a id="2097" href="graph-theory.paths-undirected-graphs.html#2097" class="Bound">x</a> <a id="2099" class="Symbol">:</a> <a id="2101" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="2125" href="graph-theory.paths-undirected-graphs.html#2068" class="Bound">G</a><a id="2126" class="Symbol">)</a> <a id="2128" class="Symbol">→</a>
  <a id="2132" href="graph-theory.paths-undirected-graphs.html#1176" class="Function">is-path-walk-Undirected-Graph</a> <a id="2162" href="graph-theory.paths-undirected-graphs.html#2068" class="Bound">G</a> <a id="2164" class="Symbol">(</a><a id="2165" href="graph-theory.walks-undirected-graphs.html#1625" class="InductiveConstructor">refl-walk-Undirected-Graph</a> <a id="2192" class="Symbol">{</a><a id="2193" class="Argument">x</a> <a id="2195" class="Symbol">=</a> <a id="2197" href="graph-theory.paths-undirected-graphs.html#2097" class="Bound">x</a><a id="2198" class="Symbol">})</a>
<a id="2201" href="graph-theory.paths-undirected-graphs.html#2012" class="Function">is-path-refl-walk-Undirected-Graph</a> <a id="2236" href="graph-theory.paths-undirected-graphs.html#2236" class="Bound">G</a> <a id="2238" href="graph-theory.paths-undirected-graphs.html#2238" class="Bound">x</a> <a id="2240" class="Symbol">=</a>
  <a id="2244" href="foundation-core.injective-maps.html#5180" class="Function">is-injective-is-contr</a>
    <a id="2270" class="Symbol">(</a> <a id="2272" href="graph-theory.walks-undirected-graphs.html#2746" class="Function">vertex-vertex-on-walk-Undirected-Graph</a> <a id="2311" href="graph-theory.paths-undirected-graphs.html#2236" class="Bound">G</a> <a id="2313" href="graph-theory.walks-undirected-graphs.html#1625" class="InductiveConstructor">refl-walk-Undirected-Graph</a><a id="2339" class="Symbol">)</a>
    <a id="2345" class="Symbol">(</a> <a id="2347" href="graph-theory.walks-undirected-graphs.html#5443" class="Function">is-contr-vertex-on-walk-refl-walk-Undirected-Graph</a> <a id="2398" href="graph-theory.paths-undirected-graphs.html#2236" class="Bound">G</a> <a id="2400" href="graph-theory.paths-undirected-graphs.html#2238" class="Bound">x</a><a id="2401" class="Symbol">)</a>
</pre>
## External links

- [Path](https://www.wikidata.org/entity/Q1415372) on Wikidata
- [Path (graph theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>) at
  Wikipedia
- [Graph path](https://mathworld.wolfram.com/GraphPath.html) at Wolfram
  MathWorld
