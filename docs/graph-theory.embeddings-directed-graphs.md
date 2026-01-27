# Embeddings of directed graphs

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="graph-theory.embeddings-directed-graphs.html" class="Module">graph-theory.embeddings-directed-graphs</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="graph-theory.morphisms-directed-graphs.html" class="Module">graph-theory.morphisms-directed-graphs</a>
</pre>
</details>

## Idea

An **embedding of directed graphs** is a
[morphism](graph-theory.morphisms-directed-graphs.md) `f : G → H` of
[directed graphs](graph-theory.directed-graphs.md) which is an
[embedding](foundation.embeddings.md) on vertices such that for each pair
`(x , y)` of vertices in `G` the map

```text
  edge-hom-Graph G H : edge-Graph G p → edge-Graph H x y
```

is also an embedding. Embeddings of directed graphs correspond to directed
subgraphs.

**Note:** Our notion of embeddings of directed graphs differs quite
substantially from the graph theoretic notion of _graph embedding_, which
usually refers to an embedding of a graph into the plane.

## Definition

<pre class="Agda"><a id="1083" class="Keyword">module</a> <a id="1090" href="graph-theory.embeddings-directed-graphs.html#1090" class="Module">_</a>
  <a id="1094" class="Symbol">{</a><a id="1095" href="graph-theory.embeddings-directed-graphs.html#1095" class="Bound">l1</a> <a id="1098" href="graph-theory.embeddings-directed-graphs.html#1098" class="Bound">l2</a> <a id="1101" href="graph-theory.embeddings-directed-graphs.html#1101" class="Bound">l3</a> <a id="1104" href="graph-theory.embeddings-directed-graphs.html#1104" class="Bound">l4</a> <a id="1107" class="Symbol">:</a> <a id="1109" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1114" class="Symbol">}</a> <a id="1116" class="Symbol">(</a><a id="1117" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a> <a id="1119" class="Symbol">:</a> <a id="1121" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="1136" href="graph-theory.embeddings-directed-graphs.html#1095" class="Bound">l1</a> <a id="1139" href="graph-theory.embeddings-directed-graphs.html#1098" class="Bound">l2</a><a id="1141" class="Symbol">)</a> <a id="1143" class="Symbol">(</a><a id="1144" href="graph-theory.embeddings-directed-graphs.html#1144" class="Bound">H</a> <a id="1146" class="Symbol">:</a> <a id="1148" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="1163" href="graph-theory.embeddings-directed-graphs.html#1101" class="Bound">l3</a> <a id="1166" href="graph-theory.embeddings-directed-graphs.html#1104" class="Bound">l4</a><a id="1168" class="Symbol">)</a>
  <a id="1172" class="Keyword">where</a>

  <a id="1181" href="graph-theory.embeddings-directed-graphs.html#1181" class="Function">is-emb-hom-Directed-Graph-Prop</a> <a id="1212" class="Symbol">:</a>
    <a id="1218" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="1237" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a> <a id="1239" href="graph-theory.embeddings-directed-graphs.html#1144" class="Bound">H</a> <a id="1241" class="Symbol">→</a> <a id="1243" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1248" class="Symbol">(</a><a id="1249" href="graph-theory.embeddings-directed-graphs.html#1095" class="Bound">l1</a> <a id="1252" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1254" href="graph-theory.embeddings-directed-graphs.html#1098" class="Bound">l2</a> <a id="1257" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1259" href="graph-theory.embeddings-directed-graphs.html#1101" class="Bound">l3</a> <a id="1262" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1264" href="graph-theory.embeddings-directed-graphs.html#1104" class="Bound">l4</a><a id="1266" class="Symbol">)</a>
  <a id="1270" href="graph-theory.embeddings-directed-graphs.html#1181" class="Function">is-emb-hom-Directed-Graph-Prop</a> <a id="1301" href="graph-theory.embeddings-directed-graphs.html#1301" class="Bound">f</a> <a id="1303" class="Symbol">=</a>
    <a id="1309" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="1328" class="Symbol">(</a> <a id="1330" href="foundation.embeddings.html#1620" class="Function">is-emb-Prop</a> <a id="1342" class="Symbol">(</a><a id="1343" href="graph-theory.morphisms-directed-graphs.html#1534" class="Function">vertex-hom-Directed-Graph</a> <a id="1369" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a> <a id="1371" href="graph-theory.embeddings-directed-graphs.html#1144" class="Bound">H</a> <a id="1373" href="graph-theory.embeddings-directed-graphs.html#1301" class="Bound">f</a><a id="1374" class="Symbol">))</a>
      <a id="1383" class="Symbol">(</a> <a id="1385" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
        <a id="1400" class="Symbol">(</a> <a id="1402" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1424" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a><a id="1425" class="Symbol">)</a>
        <a id="1435" class="Symbol">(</a> <a id="1437" class="Symbol">λ</a> <a id="1439" href="graph-theory.embeddings-directed-graphs.html#1439" class="Bound">x</a> <a id="1441" class="Symbol">→</a>
          <a id="1453" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
            <a id="1472" class="Symbol">(</a> <a id="1474" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1496" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a><a id="1497" class="Symbol">)</a>
            <a id="1511" class="Symbol">(</a> <a id="1513" class="Symbol">λ</a> <a id="1515" href="graph-theory.embeddings-directed-graphs.html#1515" class="Bound">y</a> <a id="1517" class="Symbol">→</a> <a id="1519" href="foundation.embeddings.html#1620" class="Function">is-emb-Prop</a> <a id="1531" class="Symbol">(</a><a id="1532" href="graph-theory.morphisms-directed-graphs.html#1661" class="Function">edge-hom-Directed-Graph</a> <a id="1556" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a> <a id="1558" href="graph-theory.embeddings-directed-graphs.html#1144" class="Bound">H</a> <a id="1560" href="graph-theory.embeddings-directed-graphs.html#1301" class="Bound">f</a> <a id="1562" class="Symbol">{</a><a id="1563" href="graph-theory.embeddings-directed-graphs.html#1439" class="Bound">x</a><a id="1564" class="Symbol">}</a> <a id="1566" class="Symbol">{</a><a id="1567" href="graph-theory.embeddings-directed-graphs.html#1515" class="Bound">y</a><a id="1568" class="Symbol">}))))</a>

  <a id="1577" href="graph-theory.embeddings-directed-graphs.html#1577" class="Function">is-emb-hom-Directed-Graph</a> <a id="1603" class="Symbol">:</a> <a id="1605" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="1624" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a> <a id="1626" href="graph-theory.embeddings-directed-graphs.html#1144" class="Bound">H</a> <a id="1628" class="Symbol">→</a> <a id="1630" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1633" class="Symbol">(</a><a id="1634" href="graph-theory.embeddings-directed-graphs.html#1095" class="Bound">l1</a> <a id="1637" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1639" href="graph-theory.embeddings-directed-graphs.html#1098" class="Bound">l2</a> <a id="1642" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1644" href="graph-theory.embeddings-directed-graphs.html#1101" class="Bound">l3</a> <a id="1647" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1649" href="graph-theory.embeddings-directed-graphs.html#1104" class="Bound">l4</a><a id="1651" class="Symbol">)</a>
  <a id="1655" href="graph-theory.embeddings-directed-graphs.html#1577" class="Function">is-emb-hom-Directed-Graph</a> <a id="1681" href="graph-theory.embeddings-directed-graphs.html#1681" class="Bound">f</a> <a id="1683" class="Symbol">=</a> <a id="1685" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1695" class="Symbol">(</a><a id="1696" href="graph-theory.embeddings-directed-graphs.html#1181" class="Function">is-emb-hom-Directed-Graph-Prop</a> <a id="1727" href="graph-theory.embeddings-directed-graphs.html#1681" class="Bound">f</a><a id="1728" class="Symbol">)</a>

  <a id="1733" href="graph-theory.embeddings-directed-graphs.html#1733" class="Function">emb-Directed-Graph</a> <a id="1752" class="Symbol">:</a> <a id="1754" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1757" class="Symbol">(</a><a id="1758" href="graph-theory.embeddings-directed-graphs.html#1095" class="Bound">l1</a> <a id="1761" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1763" href="graph-theory.embeddings-directed-graphs.html#1098" class="Bound">l2</a> <a id="1766" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1768" href="graph-theory.embeddings-directed-graphs.html#1101" class="Bound">l3</a> <a id="1771" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1773" href="graph-theory.embeddings-directed-graphs.html#1104" class="Bound">l4</a><a id="1775" class="Symbol">)</a>
  <a id="1779" href="graph-theory.embeddings-directed-graphs.html#1733" class="Function">emb-Directed-Graph</a> <a id="1798" class="Symbol">=</a> <a id="1800" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1802" class="Symbol">(</a><a id="1803" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="1822" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a> <a id="1824" href="graph-theory.embeddings-directed-graphs.html#1144" class="Bound">H</a><a id="1825" class="Symbol">)</a> <a id="1827" href="graph-theory.embeddings-directed-graphs.html#1577" class="Function">is-emb-hom-Directed-Graph</a>

  <a id="1856" href="graph-theory.embeddings-directed-graphs.html#1856" class="Function">hom-emb-Directed-Graph</a> <a id="1879" class="Symbol">:</a> <a id="1881" href="graph-theory.embeddings-directed-graphs.html#1733" class="Function">emb-Directed-Graph</a> <a id="1900" class="Symbol">→</a> <a id="1902" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="1921" href="graph-theory.embeddings-directed-graphs.html#1117" class="Bound">G</a> <a id="1923" href="graph-theory.embeddings-directed-graphs.html#1144" class="Bound">H</a>
  <a id="1927" href="graph-theory.embeddings-directed-graphs.html#1856" class="Function">hom-emb-Directed-Graph</a> <a id="1950" class="Symbol">=</a> <a id="1952" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="1959" href="graph-theory.embeddings-directed-graphs.html#1959" class="Function">is-emb-emb-Directed-Graph</a> <a id="1985" class="Symbol">:</a>
    <a id="1991" class="Symbol">(</a><a id="1992" href="graph-theory.embeddings-directed-graphs.html#1992" class="Bound">f</a> <a id="1994" class="Symbol">:</a> <a id="1996" href="graph-theory.embeddings-directed-graphs.html#1733" class="Function">emb-Directed-Graph</a><a id="2014" class="Symbol">)</a> <a id="2016" class="Symbol">→</a>
    <a id="2022" href="graph-theory.embeddings-directed-graphs.html#1577" class="Function">is-emb-hom-Directed-Graph</a> <a id="2048" class="Symbol">(</a><a id="2049" href="graph-theory.embeddings-directed-graphs.html#1856" class="Function">hom-emb-Directed-Graph</a> <a id="2072" href="graph-theory.embeddings-directed-graphs.html#1992" class="Bound">f</a><a id="2073" class="Symbol">)</a>
  <a id="2077" href="graph-theory.embeddings-directed-graphs.html#1959" class="Function">is-emb-emb-Directed-Graph</a> <a id="2103" class="Symbol">=</a> <a id="2105" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>
## External links

- [Graph homomorphism](https://www.wikidata.org/entity/Q3385162) on Wikidata
- [Graph homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphism) on
  Wikipedia
