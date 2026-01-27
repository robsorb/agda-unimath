# Commuting squares of order preserving maps of large posets

<pre class="Agda"><a id="71" class="Keyword">module</a>
  <a id="80" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html" class="Module">order-theory.commuting-squares-of-order-preserving-maps-large-posets</a>
  <a id="151" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation-core.commuting-squares-of-maps.html" class="Module">foundation-core.commuting-squares-of-maps</a>

<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="order-theory.order-preserving-maps-large-posets.html" class="Module">order-theory.order-preserving-maps-large-posets</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="order-theory.similarity-of-order-preserving-maps-large-posets.html" class="Module">order-theory.similarity-of-order-preserving-maps-large-posets</a>
</pre>
</details>

## Idea

A square

```text
        i
    P -----> U
    |        |
  f |        | g
    ∨        ∨
    Q -----> V
        j
```

of [order preserving maps](order-theory.order-preserving-maps-large-posets.md)
between [large posets](order-theory.large-posets.md) is said to **commute** if
for each `x : type-Large-Poset P l` the elements

```text
  j (f x) : type-Large-Poset V (γj (γf l))
  g (i x) : type-Large-Poset V (γg (γi l))
```

are [similar](order-theory.similarity-of-elements-large-posets.md). In other
words, we say that the square above commutes if the composites `j ∘ f` and
`g ∘ i` are
[similar](order-theory.similarity-of-order-preserving-maps-large-posets.md).

## Definitions

<pre class="Agda"><a id="1193" class="Keyword">module</a> <a id="1200" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1200" class="Module">_</a>
  <a id="1204" class="Symbol">{</a><a id="1205" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1205" class="Bound">αP</a> <a id="1208" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1208" class="Bound">αQ</a> <a id="1211" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1211" class="Bound">αU</a> <a id="1214" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1214" class="Bound">αV</a> <a id="1217" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1217" class="Bound">γi</a> <a id="1220" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1220" class="Bound">γf</a> <a id="1223" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1223" class="Bound">γg</a> <a id="1226" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1226" class="Bound">γj</a> <a id="1229" class="Symbol">:</a> <a id="1231" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1237" class="Symbol">→</a> <a id="1239" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1244" class="Symbol">}</a>
  <a id="1248" class="Symbol">{</a><a id="1249" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1249" class="Bound">βP</a> <a id="1252" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1252" class="Bound">βQ</a> <a id="1255" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1255" class="Bound">βU</a> <a id="1258" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1258" class="Bound">βV</a> <a id="1261" class="Symbol">:</a> <a id="1263" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1269" class="Symbol">→</a> <a id="1271" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1277" class="Symbol">→</a> <a id="1279" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1284" class="Symbol">}</a>
  <a id="1288" class="Symbol">(</a><a id="1289" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1289" class="Bound">P</a> <a id="1291" class="Symbol">:</a> <a id="1293" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1305" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1205" class="Bound">αP</a> <a id="1308" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1249" class="Bound">βP</a><a id="1310" class="Symbol">)</a>
  <a id="1314" class="Symbol">(</a><a id="1315" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1315" class="Bound">Q</a> <a id="1317" class="Symbol">:</a> <a id="1319" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1331" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1208" class="Bound">αQ</a> <a id="1334" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1252" class="Bound">βQ</a><a id="1336" class="Symbol">)</a>
  <a id="1340" class="Symbol">(</a><a id="1341" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1341" class="Bound">U</a> <a id="1343" class="Symbol">:</a> <a id="1345" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1357" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1211" class="Bound">αU</a> <a id="1360" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1255" class="Bound">βU</a><a id="1362" class="Symbol">)</a>
  <a id="1366" class="Symbol">(</a><a id="1367" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1367" class="Bound">V</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1383" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1214" class="Bound">αV</a> <a id="1386" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1258" class="Bound">βV</a><a id="1388" class="Symbol">)</a>
  <a id="1392" class="Symbol">(</a><a id="1393" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1393" class="Bound">i</a> <a id="1395" class="Symbol">:</a> <a id="1397" href="order-theory.order-preserving-maps-large-posets.html#1692" class="Function">hom-Large-Poset</a> <a id="1413" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1217" class="Bound">γi</a> <a id="1416" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1289" class="Bound">P</a> <a id="1418" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1341" class="Bound">U</a><a id="1419" class="Symbol">)</a>
  <a id="1423" class="Symbol">(</a><a id="1424" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1424" class="Bound">f</a> <a id="1426" class="Symbol">:</a> <a id="1428" href="order-theory.order-preserving-maps-large-posets.html#1692" class="Function">hom-Large-Poset</a> <a id="1444" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1220" class="Bound">γf</a> <a id="1447" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1289" class="Bound">P</a> <a id="1449" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1315" class="Bound">Q</a><a id="1450" class="Symbol">)</a>
  <a id="1454" class="Symbol">(</a><a id="1455" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1455" class="Bound">g</a> <a id="1457" class="Symbol">:</a> <a id="1459" href="order-theory.order-preserving-maps-large-posets.html#1692" class="Function">hom-Large-Poset</a> <a id="1475" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1223" class="Bound">γg</a> <a id="1478" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1341" class="Bound">U</a> <a id="1480" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1367" class="Bound">V</a><a id="1481" class="Symbol">)</a>
  <a id="1485" class="Symbol">(</a><a id="1486" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1486" class="Bound">j</a> <a id="1488" class="Symbol">:</a> <a id="1490" href="order-theory.order-preserving-maps-large-posets.html#1692" class="Function">hom-Large-Poset</a> <a id="1506" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1226" class="Bound">γj</a> <a id="1509" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1315" class="Bound">Q</a> <a id="1511" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1367" class="Bound">V</a><a id="1512" class="Symbol">)</a>
  <a id="1516" class="Keyword">where</a>

  <a id="1525" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1525" class="Function">coherence-square-hom-Large-Poset</a> <a id="1558" class="Symbol">:</a> <a id="1560" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1566" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1525" class="Function">coherence-square-hom-Large-Poset</a> <a id="1599" class="Symbol">=</a>
    <a id="1605" href="order-theory.similarity-of-order-preserving-maps-large-posets.html#1612" class="Function">sim-hom-Large-Poset</a> <a id="1625" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1289" class="Bound">P</a> <a id="1627" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1367" class="Bound">V</a>
      <a id="1635" class="Symbol">(</a> <a id="1637" href="order-theory.order-preserving-maps-large-posets.html#4069" class="Function">comp-hom-Large-Poset</a> <a id="1658" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1289" class="Bound">P</a> <a id="1660" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1315" class="Bound">Q</a> <a id="1662" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1367" class="Bound">V</a> <a id="1664" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1486" class="Bound">j</a> <a id="1666" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1424" class="Bound">f</a><a id="1667" class="Symbol">)</a>
      <a id="1675" class="Symbol">(</a> <a id="1677" href="order-theory.order-preserving-maps-large-posets.html#4069" class="Function">comp-hom-Large-Poset</a> <a id="1698" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1289" class="Bound">P</a> <a id="1700" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1341" class="Bound">U</a> <a id="1702" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1367" class="Bound">V</a> <a id="1704" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1455" class="Bound">g</a> <a id="1706" href="order-theory.commuting-squares-of-order-preserving-maps-large-posets.html#1393" class="Bound">i</a><a id="1707" class="Symbol">)</a>
</pre>