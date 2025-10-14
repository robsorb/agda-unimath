# Terminal directed graphs

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="graph-theory.terminal-directed-graphs.html" class="Module">graph-theory.terminal-directed-graphs</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Idea</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="graph-theory.morphisms-directed-graphs.html" class="Module">graph-theory.morphisms-directed-graphs</a>
</pre>
</details>

## Idea

The {{#concept "terminal directed graph"}} is a
[directed graph](graph-theory.directed-graphs.md) `1` such that the type of
[graph homomorphisms](graph-theory.morphisms-directed-graphs.md) `hom A 1` is
[contractible](foundation-core.contractible-types.md) for any directed graph
`A`.

Concretely, the terminal directed graph `1` is defined by

```text
  1₀ := 1
  1₁ x y := 1.
```

## Definitions

### The predicate of being a terminal directed graph

The (small) predicate of being a terminal directed graph asserts that the type
of vertices and all types of edges are contractible.

<pre class="Agda"><a id="1041" class="Keyword">module</a> <a id="1048" href="graph-theory.terminal-directed-graphs.html#1048" class="Module">_</a>
  <a id="1052" class="Symbol">{</a><a id="1053" href="graph-theory.terminal-directed-graphs.html#1053" class="Bound">l1</a> <a id="1056" href="graph-theory.terminal-directed-graphs.html#1056" class="Bound">l2</a> <a id="1059" class="Symbol">:</a> <a id="1061" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1066" class="Symbol">}</a> <a id="1068" class="Symbol">(</a><a id="1069" href="graph-theory.terminal-directed-graphs.html#1069" class="Bound">A</a> <a id="1071" class="Symbol">:</a> <a id="1073" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="1088" href="graph-theory.terminal-directed-graphs.html#1053" class="Bound">l1</a> <a id="1091" href="graph-theory.terminal-directed-graphs.html#1056" class="Bound">l2</a><a id="1093" class="Symbol">)</a>
  <a id="1097" class="Keyword">where</a>

  <a id="1106" href="graph-theory.terminal-directed-graphs.html#1106" class="Function">is-terminal-prop-Directed-Graph</a> <a id="1138" class="Symbol">:</a> <a id="1140" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1145" class="Symbol">(</a><a id="1146" href="graph-theory.terminal-directed-graphs.html#1053" class="Bound">l1</a> <a id="1149" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1151" href="graph-theory.terminal-directed-graphs.html#1056" class="Bound">l2</a><a id="1153" class="Symbol">)</a>
  <a id="1157" href="graph-theory.terminal-directed-graphs.html#1106" class="Function">is-terminal-prop-Directed-Graph</a> <a id="1189" class="Symbol">=</a>
    <a id="1195" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="1214" class="Symbol">(</a> <a id="1216" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="1230" class="Symbol">(</a><a id="1231" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1253" href="graph-theory.terminal-directed-graphs.html#1069" class="Bound">A</a><a id="1254" class="Symbol">))</a>
      <a id="1263" class="Symbol">(</a> <a id="1265" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
        <a id="1280" class="Symbol">(</a> <a id="1282" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1304" href="graph-theory.terminal-directed-graphs.html#1069" class="Bound">A</a><a id="1305" class="Symbol">)</a>
        <a id="1315" class="Symbol">(</a> <a id="1317" class="Symbol">λ</a> <a id="1319" href="graph-theory.terminal-directed-graphs.html#1319" class="Bound">x</a> <a id="1321" class="Symbol">→</a>
          <a id="1333" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
            <a id="1352" class="Symbol">(</a> <a id="1354" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1376" href="graph-theory.terminal-directed-graphs.html#1069" class="Bound">A</a><a id="1377" class="Symbol">)</a>
            <a id="1391" class="Symbol">(</a> <a id="1393" class="Symbol">λ</a> <a id="1395" href="graph-theory.terminal-directed-graphs.html#1395" class="Bound">y</a> <a id="1397" class="Symbol">→</a> <a id="1399" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="1413" class="Symbol">(</a><a id="1414" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="1434" href="graph-theory.terminal-directed-graphs.html#1069" class="Bound">A</a> <a id="1436" href="graph-theory.terminal-directed-graphs.html#1319" class="Bound">x</a> <a id="1438" href="graph-theory.terminal-directed-graphs.html#1395" class="Bound">y</a><a id="1439" class="Symbol">))))</a>

  <a id="1447" href="graph-theory.terminal-directed-graphs.html#1447" class="Function">is-terminal-Directed-Graph</a> <a id="1474" class="Symbol">:</a> <a id="1476" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1479" class="Symbol">(</a><a id="1480" href="graph-theory.terminal-directed-graphs.html#1053" class="Bound">l1</a> <a id="1483" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1485" href="graph-theory.terminal-directed-graphs.html#1056" class="Bound">l2</a><a id="1487" class="Symbol">)</a>
  <a id="1491" href="graph-theory.terminal-directed-graphs.html#1447" class="Function">is-terminal-Directed-Graph</a> <a id="1518" class="Symbol">=</a> <a id="1520" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1530" href="graph-theory.terminal-directed-graphs.html#1106" class="Function">is-terminal-prop-Directed-Graph</a>

  <a id="1565" href="graph-theory.terminal-directed-graphs.html#1565" class="Function">is-prop-is-terminal-Directed-Graph</a> <a id="1600" class="Symbol">:</a>
    <a id="1606" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1614" href="graph-theory.terminal-directed-graphs.html#1447" class="Function">is-terminal-Directed-Graph</a>
  <a id="1643" href="graph-theory.terminal-directed-graphs.html#1565" class="Function">is-prop-is-terminal-Directed-Graph</a> <a id="1678" class="Symbol">=</a>
    <a id="1684" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1702" href="graph-theory.terminal-directed-graphs.html#1106" class="Function">is-terminal-prop-Directed-Graph</a>
</pre>
### The universal property of being a terminal directed graph

<pre class="Agda"><a id="1810" class="Keyword">module</a> <a id="1817" href="graph-theory.terminal-directed-graphs.html#1817" class="Module">_</a>
  <a id="1821" class="Symbol">{</a><a id="1822" href="graph-theory.terminal-directed-graphs.html#1822" class="Bound">l1</a> <a id="1825" href="graph-theory.terminal-directed-graphs.html#1825" class="Bound">l2</a> <a id="1828" class="Symbol">:</a> <a id="1830" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1835" class="Symbol">}</a> <a id="1837" class="Symbol">(</a><a id="1838" href="graph-theory.terminal-directed-graphs.html#1838" class="Bound">A</a> <a id="1840" class="Symbol">:</a> <a id="1842" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="1857" href="graph-theory.terminal-directed-graphs.html#1822" class="Bound">l1</a> <a id="1860" href="graph-theory.terminal-directed-graphs.html#1825" class="Bound">l2</a><a id="1862" class="Symbol">)</a>
  <a id="1866" class="Keyword">where</a>

  <a id="1875" href="graph-theory.terminal-directed-graphs.html#1875" class="Function">universal-property-terminal-Directed-Graph</a> <a id="1918" class="Symbol">:</a> <a id="1920" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1926" href="graph-theory.terminal-directed-graphs.html#1875" class="Function">universal-property-terminal-Directed-Graph</a> <a id="1969" class="Symbol">=</a>
    <a id="1975" class="Symbol">{</a><a id="1976" href="graph-theory.terminal-directed-graphs.html#1976" class="Bound">l3</a> <a id="1979" href="graph-theory.terminal-directed-graphs.html#1979" class="Bound">l4</a> <a id="1982" class="Symbol">:</a> <a id="1984" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1989" class="Symbol">}</a> <a id="1991" class="Symbol">(</a><a id="1992" href="graph-theory.terminal-directed-graphs.html#1992" class="Bound">X</a> <a id="1994" class="Symbol">:</a> <a id="1996" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="2011" href="graph-theory.terminal-directed-graphs.html#1976" class="Bound">l3</a> <a id="2014" href="graph-theory.terminal-directed-graphs.html#1979" class="Bound">l4</a><a id="2016" class="Symbol">)</a> <a id="2018" class="Symbol">→</a>
    <a id="2024" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2033" class="Symbol">(</a><a id="2034" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="2053" href="graph-theory.terminal-directed-graphs.html#1992" class="Bound">X</a> <a id="2055" href="graph-theory.terminal-directed-graphs.html#1838" class="Bound">A</a><a id="2056" class="Symbol">)</a>
</pre>
### The terminal directed graph

<pre class="Agda"><a id="vertex-terminal-Directed-Graph"></a><a id="2104" href="graph-theory.terminal-directed-graphs.html#2104" class="Function">vertex-terminal-Directed-Graph</a> <a id="2135" class="Symbol">:</a> <a id="2137" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2140" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2146" href="graph-theory.terminal-directed-graphs.html#2104" class="Function">vertex-terminal-Directed-Graph</a> <a id="2177" class="Symbol">=</a> <a id="2179" href="foundation.unit-type.html#950" class="Record">unit</a>

<a id="edge-terminal-Directed-Graph"></a><a id="2185" href="graph-theory.terminal-directed-graphs.html#2185" class="Function">edge-terminal-Directed-Graph</a> <a id="2214" class="Symbol">:</a>
  <a id="2218" class="Symbol">(</a><a id="2219" href="graph-theory.terminal-directed-graphs.html#2219" class="Bound">x</a> <a id="2221" href="graph-theory.terminal-directed-graphs.html#2221" class="Bound">y</a> <a id="2223" class="Symbol">:</a> <a id="2225" href="graph-theory.terminal-directed-graphs.html#2104" class="Function">vertex-terminal-Directed-Graph</a><a id="2255" class="Symbol">)</a> <a id="2257" class="Symbol">→</a> <a id="2259" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2262" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2268" href="graph-theory.terminal-directed-graphs.html#2185" class="Function">edge-terminal-Directed-Graph</a> <a id="2297" href="graph-theory.terminal-directed-graphs.html#2297" class="Bound">x</a> <a id="2299" href="graph-theory.terminal-directed-graphs.html#2299" class="Bound">y</a> <a id="2301" class="Symbol">=</a> <a id="2303" href="foundation.unit-type.html#950" class="Record">unit</a>

<a id="terminal-Directed-Graph"></a><a id="2309" href="graph-theory.terminal-directed-graphs.html#2309" class="Function">terminal-Directed-Graph</a> <a id="2333" class="Symbol">:</a> <a id="2335" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="2350" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2356" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2362" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2366" href="graph-theory.terminal-directed-graphs.html#2309" class="Function">terminal-Directed-Graph</a> <a id="2390" class="Symbol">=</a> <a id="2392" href="graph-theory.terminal-directed-graphs.html#2104" class="Function">vertex-terminal-Directed-Graph</a>
<a id="2423" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2427" href="graph-theory.terminal-directed-graphs.html#2309" class="Function">terminal-Directed-Graph</a> <a id="2451" class="Symbol">=</a> <a id="2453" href="graph-theory.terminal-directed-graphs.html#2185" class="Function">edge-terminal-Directed-Graph</a>
</pre>