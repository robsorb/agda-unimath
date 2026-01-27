# Eulerian circuits in undirected graphs

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="graph-theory.eulerian-circuits-undirected-graphs.html" class="Module">graph-theory.eulerian-circuits-undirected-graphs</a> <a id="107" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="261" class="Keyword">open</a> <a id="266" class="Keyword">import</a> <a id="273" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="graph-theory.morphisms-undirected-graphs.html" class="Module">graph-theory.morphisms-undirected-graphs</a>
<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
</details>

## Idea

An **Eulerian circuit** in an
[undirected graph](graph-theory.undirected-graphs.md) `G` consists of a
[circuit](graph-theory.circuits-undirected-graphs.md) `T` in `G` such that every
edge in `G` is in the image of `T`. In other words, an Eulerian circuit `T`
consists of [`k`-gon](graph-theory.polygons.md) `H` equipped with a
[graph homomorphism](graph-theory.morphisms-undirected-graphs.md) `f : H → G`
that induces an [equivalence](foundation-core.equivalences.md)

```text
  Σ (unordered-pair-vertices-Polygon k H) (edge-Polygon k H) ≃
  Σ (unordered-pair-vertices-Undirected-Graph G) (edge-Undirected-Graph G)
```

## Definition

<pre class="Agda"><a id="1194" class="Keyword">module</a> <a id="1201" href="graph-theory.eulerian-circuits-undirected-graphs.html#1201" class="Module">_</a>
  <a id="1205" class="Symbol">{</a><a id="1206" href="graph-theory.eulerian-circuits-undirected-graphs.html#1206" class="Bound">l1</a> <a id="1209" href="graph-theory.eulerian-circuits-undirected-graphs.html#1209" class="Bound">l2</a> <a id="1212" class="Symbol">:</a> <a id="1214" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1219" class="Symbol">}</a> <a id="1221" class="Symbol">(</a><a id="1222" href="graph-theory.eulerian-circuits-undirected-graphs.html#1222" class="Bound">G</a> <a id="1224" class="Symbol">:</a> <a id="1226" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="1243" href="graph-theory.eulerian-circuits-undirected-graphs.html#1206" class="Bound">l1</a> <a id="1246" href="graph-theory.eulerian-circuits-undirected-graphs.html#1209" class="Bound">l2</a><a id="1248" class="Symbol">)</a>
  <a id="1252" class="Keyword">where</a>

  <a id="1261" href="graph-theory.eulerian-circuits-undirected-graphs.html#1261" class="Function">eulerian-circuit-Undirected-Graph</a> <a id="1295" class="Symbol">:</a> <a id="1297" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1300" class="Symbol">(</a><a id="1301" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1306" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1312" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1314" href="graph-theory.eulerian-circuits-undirected-graphs.html#1206" class="Bound">l1</a> <a id="1317" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1319" href="graph-theory.eulerian-circuits-undirected-graphs.html#1209" class="Bound">l2</a><a id="1321" class="Symbol">)</a>
  <a id="1325" href="graph-theory.eulerian-circuits-undirected-graphs.html#1261" class="Function">eulerian-circuit-Undirected-Graph</a> <a id="1359" class="Symbol">=</a>
    <a id="1365" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1367" class="Symbol">(</a> <a id="1369" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1370" class="Symbol">)</a>
      <a id="1378" class="Symbol">(</a> <a id="1380" class="Symbol">λ</a> <a id="1382" href="graph-theory.eulerian-circuits-undirected-graphs.html#1382" class="Bound">k</a> <a id="1384" class="Symbol">→</a>
        <a id="1394" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1396" class="Symbol">(</a> <a id="1398" href="graph-theory.polygons.html#2279" class="Function">Polygon</a> <a id="1406" href="graph-theory.eulerian-circuits-undirected-graphs.html#1382" class="Bound">k</a><a id="1407" class="Symbol">)</a>
          <a id="1419" class="Symbol">(</a> <a id="1421" class="Symbol">λ</a> <a id="1423" href="graph-theory.eulerian-circuits-undirected-graphs.html#1423" class="Bound">H</a> <a id="1425" class="Symbol">→</a>
            <a id="1439" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1441" class="Symbol">(</a> <a id="1443" href="graph-theory.morphisms-undirected-graphs.html#1175" class="Function">hom-Undirected-Graph</a> <a id="1464" class="Symbol">(</a><a id="1465" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a> <a id="1490" href="graph-theory.eulerian-circuits-undirected-graphs.html#1382" class="Bound">k</a> <a id="1492" href="graph-theory.eulerian-circuits-undirected-graphs.html#1423" class="Bound">H</a><a id="1493" class="Symbol">)</a> <a id="1495" href="graph-theory.eulerian-circuits-undirected-graphs.html#1222" class="Bound">G</a><a id="1496" class="Symbol">)</a>
              <a id="1512" class="Symbol">(</a> <a id="1514" class="Symbol">λ</a> <a id="1516" href="graph-theory.eulerian-circuits-undirected-graphs.html#1516" class="Bound">f</a> <a id="1518" class="Symbol">→</a>
                <a id="1536" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a>
                  <a id="1563" class="Symbol">(</a> <a id="1565" href="foundation-core.functoriality-dependent-pair-types.html#1778" class="Function">tot</a>
                    <a id="1589" class="Symbol">(</a> <a id="1591" href="graph-theory.morphisms-undirected-graphs.html#1926" class="Function">edge-hom-Undirected-Graph</a>
                      <a id="1639" class="Symbol">(</a> <a id="1641" href="graph-theory.polygons.html#2477" class="Function">undirected-graph-Polygon</a> <a id="1666" href="graph-theory.eulerian-circuits-undirected-graphs.html#1382" class="Bound">k</a> <a id="1668" href="graph-theory.eulerian-circuits-undirected-graphs.html#1423" class="Bound">H</a><a id="1669" class="Symbol">)</a>
                      <a id="1693" class="Symbol">(</a> <a id="1695" href="graph-theory.eulerian-circuits-undirected-graphs.html#1222" class="Bound">G</a><a id="1696" class="Symbol">)</a>
                      <a id="1720" class="Symbol">(</a> <a id="1722" href="graph-theory.eulerian-circuits-undirected-graphs.html#1516" class="Bound">f</a><a id="1723" class="Symbol">))))))</a>
</pre>
## External links

- [Eulerian circuit](https://d3gt.com/unit.html?eulerian-circuit) on D3 Graph
  theory
- [Eulerian cycle](https://www.wikidata.org/entity/Q11691793) on Wikidata
- [Eulerian path](https://en.wikipedia.org/wiki/Eulerian_path) on Wikipedia
- [Eulerian cycle](https://mathworld.wolfram.com/EulerianCycle.html) on Wolfram
  mathworld
