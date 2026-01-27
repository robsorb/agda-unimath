# Simple undirected graphs

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="graph-theory.simple-undirected-graphs.html" class="Module">graph-theory.simple-undirected-graphs</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>

<a id="407" class="Keyword">open</a> <a id="412" class="Keyword">import</a> <a id="419" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

An [undirected graph](graph-theory.undirected-graphs.md) is said to be
**simple** if it only contains edges between
[distinct points](foundation.pairs-of-distinct-elements.md), and there is at
most one edge between any two vertices.

## Definition

<pre class="Agda"><a id="739" class="Keyword">module</a> <a id="746" href="graph-theory.simple-undirected-graphs.html#746" class="Module">_</a>
  <a id="750" class="Symbol">{</a><a id="751" href="graph-theory.simple-undirected-graphs.html#751" class="Bound">l1</a> <a id="754" href="graph-theory.simple-undirected-graphs.html#754" class="Bound">l2</a> <a id="757" class="Symbol">:</a> <a id="759" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="764" class="Symbol">}</a> <a id="766" class="Symbol">(</a><a id="767" href="graph-theory.simple-undirected-graphs.html#767" class="Bound">G</a> <a id="769" class="Symbol">:</a> <a id="771" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="788" href="graph-theory.simple-undirected-graphs.html#751" class="Bound">l1</a> <a id="791" href="graph-theory.simple-undirected-graphs.html#754" class="Bound">l2</a><a id="793" class="Symbol">)</a>
  <a id="797" class="Keyword">where</a>

  <a id="806" href="graph-theory.simple-undirected-graphs.html#806" class="Function">is-simple-Undirected-Graph-Prop</a> <a id="838" class="Symbol">:</a> <a id="840" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="845" class="Symbol">(</a><a id="846" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="851" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="857" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="859" href="graph-theory.simple-undirected-graphs.html#751" class="Bound">l1</a> <a id="862" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="864" href="graph-theory.simple-undirected-graphs.html#754" class="Bound">l2</a><a id="866" class="Symbol">)</a>
  <a id="870" href="graph-theory.simple-undirected-graphs.html#806" class="Function">is-simple-Undirected-Graph-Prop</a> <a id="902" class="Symbol">=</a>
    <a id="908" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="927" class="Symbol">(</a> <a id="929" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
        <a id="944" class="Symbol">(</a> <a id="946" href="graph-theory.undirected-graphs.html#892" class="Function">unordered-pair-vertices-Undirected-Graph</a> <a id="987" href="graph-theory.simple-undirected-graphs.html#767" class="Bound">G</a><a id="988" class="Symbol">)</a>
        <a id="998" class="Symbol">(</a> <a id="1000" class="Symbol">λ</a> <a id="1002" href="graph-theory.simple-undirected-graphs.html#1002" class="Bound">p</a> <a id="1004" class="Symbol">→</a>
          <a id="1016" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a>
            <a id="1042" class="Symbol">(</a> <a id="1044" href="graph-theory.undirected-graphs.html#1493" class="Function">edge-Undirected-Graph</a> <a id="1066" href="graph-theory.simple-undirected-graphs.html#767" class="Bound">G</a> <a id="1068" href="graph-theory.simple-undirected-graphs.html#1002" class="Bound">p</a><a id="1069" class="Symbol">)</a>
            <a id="1083" class="Symbol">(</a> <a id="1085" href="foundation.embeddings.html#1620" class="Function">is-emb-Prop</a>
              <a id="1111" class="Symbol">(</a> <a id="1113" href="graph-theory.undirected-graphs.html#1228" class="Function">element-unordered-pair-vertices-Undirected-Graph</a> <a id="1162" href="graph-theory.simple-undirected-graphs.html#767" class="Bound">G</a> <a id="1164" href="graph-theory.simple-undirected-graphs.html#1002" class="Bound">p</a><a id="1165" class="Symbol">))))</a>
      <a id="1176" class="Symbol">(</a> <a id="1178" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
        <a id="1193" class="Symbol">(</a> <a id="1195" href="graph-theory.undirected-graphs.html#892" class="Function">unordered-pair-vertices-Undirected-Graph</a> <a id="1236" href="graph-theory.simple-undirected-graphs.html#767" class="Bound">G</a><a id="1237" class="Symbol">)</a>
        <a id="1247" class="Symbol">(</a> <a id="1249" class="Symbol">λ</a> <a id="1251" href="graph-theory.simple-undirected-graphs.html#1251" class="Bound">p</a> <a id="1253" class="Symbol">→</a> <a id="1255" href="foundation-core.propositions.html#10773" class="Function">is-prop-Prop</a> <a id="1268" class="Symbol">(</a><a id="1269" href="graph-theory.undirected-graphs.html#1493" class="Function">edge-Undirected-Graph</a> <a id="1291" href="graph-theory.simple-undirected-graphs.html#767" class="Bound">G</a> <a id="1293" href="graph-theory.simple-undirected-graphs.html#1251" class="Bound">p</a><a id="1294" class="Symbol">)))</a>

  <a id="1301" href="graph-theory.simple-undirected-graphs.html#1301" class="Function">is-simple-Undirected-Graph</a> <a id="1328" class="Symbol">:</a> <a id="1330" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1333" class="Symbol">(</a><a id="1334" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1339" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1345" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1347" href="graph-theory.simple-undirected-graphs.html#751" class="Bound">l1</a> <a id="1350" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1352" href="graph-theory.simple-undirected-graphs.html#754" class="Bound">l2</a><a id="1354" class="Symbol">)</a>
  <a id="1358" href="graph-theory.simple-undirected-graphs.html#1301" class="Function">is-simple-Undirected-Graph</a> <a id="1385" class="Symbol">=</a> <a id="1387" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1397" href="graph-theory.simple-undirected-graphs.html#806" class="Function">is-simple-Undirected-Graph-Prop</a>

  <a id="1432" href="graph-theory.simple-undirected-graphs.html#1432" class="Function">is-prop-is-simple-Undirected-Graph</a> <a id="1467" class="Symbol">:</a> <a id="1469" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1477" href="graph-theory.simple-undirected-graphs.html#1301" class="Function">is-simple-Undirected-Graph</a>
  <a id="1506" href="graph-theory.simple-undirected-graphs.html#1432" class="Function">is-prop-is-simple-Undirected-Graph</a> <a id="1541" class="Symbol">=</a>
    <a id="1547" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1565" href="graph-theory.simple-undirected-graphs.html#806" class="Function">is-simple-Undirected-Graph-Prop</a>

<a id="Simple-Undirected-Graph"></a><a id="1598" href="graph-theory.simple-undirected-graphs.html#1598" class="Function">Simple-Undirected-Graph</a> <a id="1622" class="Symbol">:</a> <a id="1624" class="Symbol">(</a><a id="1625" href="graph-theory.simple-undirected-graphs.html#1625" class="Bound">l1</a> <a id="1628" href="graph-theory.simple-undirected-graphs.html#1628" class="Bound">l2</a> <a id="1631" class="Symbol">:</a> <a id="1633" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1638" class="Symbol">)</a> <a id="1640" class="Symbol">→</a> <a id="1642" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1645" class="Symbol">(</a><a id="1646" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1651" href="graph-theory.simple-undirected-graphs.html#1625" class="Bound">l1</a> <a id="1654" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1656" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1661" href="graph-theory.simple-undirected-graphs.html#1628" class="Bound">l2</a><a id="1663" class="Symbol">)</a>
<a id="1665" href="graph-theory.simple-undirected-graphs.html#1598" class="Function">Simple-Undirected-Graph</a> <a id="1689" href="graph-theory.simple-undirected-graphs.html#1689" class="Bound">l1</a> <a id="1692" href="graph-theory.simple-undirected-graphs.html#1692" class="Bound">l2</a> <a id="1695" class="Symbol">=</a>
  <a id="1699" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1701" class="Symbol">(</a> <a id="1703" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1706" href="graph-theory.simple-undirected-graphs.html#1689" class="Bound">l1</a><a id="1708" class="Symbol">)</a>
    <a id="1714" class="Symbol">(</a> <a id="1716" class="Symbol">λ</a> <a id="1718" href="graph-theory.simple-undirected-graphs.html#1718" class="Bound">V</a> <a id="1720" class="Symbol">→</a>
      <a id="1728" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1730" class="Symbol">(</a> <a id="1732" href="foundation.unordered-pairs.html#2222" class="Function">unordered-pair</a> <a id="1747" href="graph-theory.simple-undirected-graphs.html#1718" class="Bound">V</a> <a id="1749" class="Symbol">→</a> <a id="1751" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1756" href="graph-theory.simple-undirected-graphs.html#1692" class="Bound">l2</a><a id="1758" class="Symbol">)</a>
        <a id="1768" class="Symbol">(</a> <a id="1770" class="Symbol">λ</a> <a id="1772" href="graph-theory.simple-undirected-graphs.html#1772" class="Bound">E</a> <a id="1774" class="Symbol">→</a>
          <a id="1786" class="Symbol">(</a><a id="1787" href="graph-theory.simple-undirected-graphs.html#1787" class="Bound">x</a> <a id="1789" class="Symbol">:</a> <a id="1791" href="graph-theory.simple-undirected-graphs.html#1718" class="Bound">V</a><a id="1792" class="Symbol">)</a> <a id="1794" class="Symbol">→</a>
          <a id="1806" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1808" class="Symbol">(</a> <a id="1810" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a>
              <a id="1834" class="Symbol">(</a> <a id="1836" href="graph-theory.simple-undirected-graphs.html#1772" class="Bound">E</a> <a id="1838" class="Symbol">(</a><a id="1839" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="1844" class="Symbol">(</a><a id="1845" href="univalent-combinatorics.finite-types.html#8212" class="Function">Fin-Type-With-Cardinality-ℕ</a> <a id="1873" class="Number">2</a><a id="1874" class="Symbol">)</a> <a id="1876" class="Symbol">(λ</a> <a id="1879" href="graph-theory.simple-undirected-graphs.html#1879" class="Bound">y</a> <a id="1881" class="Symbol">→</a> <a id="1883" href="graph-theory.simple-undirected-graphs.html#1787" class="Bound">x</a><a id="1884" class="Symbol">))))))</a>
</pre>
## External links

- [Graph](https://ncatlab.org/nlab/show/graph) at $n$Lab
- [Graph (discrete mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>)
  at Wikipedia
- [Simple graph](https://www.wikidata.org/entity/Q15838309) on Wikidata
- [Simple graph](https://mathworld.wolfram.com/SimpleGraph.html) at Wolfram
  MathWorld
