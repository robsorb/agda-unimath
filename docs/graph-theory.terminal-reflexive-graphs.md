# Terminal reflexive graphs

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="graph-theory.terminal-reflexive-graphs.html" class="Module">graph-theory.terminal-reflexive-graphs</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Idea</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
<a id="415" class="Keyword">open</a> <a id="420" class="Keyword">import</a> <a id="427" href="graph-theory.morphisms-reflexive-graphs.html" class="Module">graph-theory.morphisms-reflexive-graphs</a>
<a id="467" class="Keyword">open</a> <a id="472" class="Keyword">import</a> <a id="479" href="graph-theory.terminal-directed-graphs.html" class="Module">graph-theory.terminal-directed-graphs</a>
</pre>
</details>

## Idea

The {{#concept "terminal reflexive graph"}} is a
[reflexive graph](graph-theory.reflexive-graphs.md) `1` such that the type of
[graph homomorphisms](graph-theory.morphisms-reflexive-graphs.md) `hom A 1` is
[contractible](foundation-core.contractible-types.md) for any reflexive graph
`A`.

Concretely, the terminal reflexive graph `1` is defined by

```text
  1₀ := 1
  1₁ x y := 1.
```

## Definitions

### The predicate of being a terminal reflexive graph

The (small) predicate of being a terminal reflexive graph asserts that the type
of vertices and all types of edges are contractible.

<pre class="Agda"><a id="1144" class="Keyword">module</a> <a id="1151" href="graph-theory.terminal-reflexive-graphs.html#1151" class="Module">_</a>
  <a id="1155" class="Symbol">{</a><a id="1156" href="graph-theory.terminal-reflexive-graphs.html#1156" class="Bound">l1</a> <a id="1159" href="graph-theory.terminal-reflexive-graphs.html#1159" class="Bound">l2</a> <a id="1162" class="Symbol">:</a> <a id="1164" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1169" class="Symbol">}</a> <a id="1171" class="Symbol">(</a><a id="1172" href="graph-theory.terminal-reflexive-graphs.html#1172" class="Bound">A</a> <a id="1174" class="Symbol">:</a> <a id="1176" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="1192" href="graph-theory.terminal-reflexive-graphs.html#1156" class="Bound">l1</a> <a id="1195" href="graph-theory.terminal-reflexive-graphs.html#1159" class="Bound">l2</a><a id="1197" class="Symbol">)</a>
  <a id="1201" class="Keyword">where</a>

  <a id="1210" href="graph-theory.terminal-reflexive-graphs.html#1210" class="Function">is-terminal-prop-Reflexive-Graph</a> <a id="1243" class="Symbol">:</a> <a id="1245" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1250" class="Symbol">(</a><a id="1251" href="graph-theory.terminal-reflexive-graphs.html#1156" class="Bound">l1</a> <a id="1254" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1256" href="graph-theory.terminal-reflexive-graphs.html#1159" class="Bound">l2</a><a id="1258" class="Symbol">)</a>
  <a id="1262" href="graph-theory.terminal-reflexive-graphs.html#1210" class="Function">is-terminal-prop-Reflexive-Graph</a> <a id="1295" class="Symbol">=</a>
    <a id="1301" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="1320" class="Symbol">(</a> <a id="1322" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="1336" class="Symbol">(</a><a id="1337" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="1360" href="graph-theory.terminal-reflexive-graphs.html#1172" class="Bound">A</a><a id="1361" class="Symbol">))</a>
      <a id="1370" class="Symbol">(</a> <a id="1372" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
        <a id="1387" class="Symbol">(</a> <a id="1389" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="1412" href="graph-theory.terminal-reflexive-graphs.html#1172" class="Bound">A</a><a id="1413" class="Symbol">)</a>
        <a id="1423" class="Symbol">(</a> <a id="1425" class="Symbol">λ</a> <a id="1427" href="graph-theory.terminal-reflexive-graphs.html#1427" class="Bound">x</a> <a id="1429" class="Symbol">→</a>
          <a id="1441" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
            <a id="1460" class="Symbol">(</a> <a id="1462" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="1485" href="graph-theory.terminal-reflexive-graphs.html#1172" class="Bound">A</a><a id="1486" class="Symbol">)</a>
            <a id="1500" class="Symbol">(</a> <a id="1502" class="Symbol">λ</a> <a id="1504" href="graph-theory.terminal-reflexive-graphs.html#1504" class="Bound">y</a> <a id="1506" class="Symbol">→</a> <a id="1508" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="1522" class="Symbol">(</a><a id="1523" href="graph-theory.reflexive-graphs.html#1074" class="Function">edge-Reflexive-Graph</a> <a id="1544" href="graph-theory.terminal-reflexive-graphs.html#1172" class="Bound">A</a> <a id="1546" href="graph-theory.terminal-reflexive-graphs.html#1427" class="Bound">x</a> <a id="1548" href="graph-theory.terminal-reflexive-graphs.html#1504" class="Bound">y</a><a id="1549" class="Symbol">))))</a>

  <a id="1557" href="graph-theory.terminal-reflexive-graphs.html#1557" class="Function">is-terminal-Reflexive-Graph</a> <a id="1585" class="Symbol">:</a> <a id="1587" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1590" class="Symbol">(</a><a id="1591" href="graph-theory.terminal-reflexive-graphs.html#1156" class="Bound">l1</a> <a id="1594" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1596" href="graph-theory.terminal-reflexive-graphs.html#1159" class="Bound">l2</a><a id="1598" class="Symbol">)</a>
  <a id="1602" href="graph-theory.terminal-reflexive-graphs.html#1557" class="Function">is-terminal-Reflexive-Graph</a> <a id="1630" class="Symbol">=</a> <a id="1632" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1642" href="graph-theory.terminal-reflexive-graphs.html#1210" class="Function">is-terminal-prop-Reflexive-Graph</a>

  <a id="1678" href="graph-theory.terminal-reflexive-graphs.html#1678" class="Function">is-prop-is-terminal-Reflexive-Graph</a> <a id="1714" class="Symbol">:</a>
    <a id="1720" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1728" href="graph-theory.terminal-reflexive-graphs.html#1557" class="Function">is-terminal-Reflexive-Graph</a>
  <a id="1758" href="graph-theory.terminal-reflexive-graphs.html#1678" class="Function">is-prop-is-terminal-Reflexive-Graph</a> <a id="1794" class="Symbol">=</a>
    <a id="1800" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1818" href="graph-theory.terminal-reflexive-graphs.html#1210" class="Function">is-terminal-prop-Reflexive-Graph</a>
</pre>
### The universal property of being a terminal reflexive graph

<pre class="Agda"><a id="1928" class="Keyword">module</a> <a id="1935" href="graph-theory.terminal-reflexive-graphs.html#1935" class="Module">_</a>
  <a id="1939" class="Symbol">{</a><a id="1940" href="graph-theory.terminal-reflexive-graphs.html#1940" class="Bound">l1</a> <a id="1943" href="graph-theory.terminal-reflexive-graphs.html#1943" class="Bound">l2</a> <a id="1946" class="Symbol">:</a> <a id="1948" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1953" class="Symbol">}</a> <a id="1955" class="Symbol">(</a><a id="1956" href="graph-theory.terminal-reflexive-graphs.html#1956" class="Bound">A</a> <a id="1958" class="Symbol">:</a> <a id="1960" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="1976" href="graph-theory.terminal-reflexive-graphs.html#1940" class="Bound">l1</a> <a id="1979" href="graph-theory.terminal-reflexive-graphs.html#1943" class="Bound">l2</a><a id="1981" class="Symbol">)</a>
  <a id="1985" class="Keyword">where</a>

  <a id="1994" href="graph-theory.terminal-reflexive-graphs.html#1994" class="Function">universal-property-terminal-Reflexive-Graph</a> <a id="2038" class="Symbol">:</a> <a id="2040" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="2046" href="graph-theory.terminal-reflexive-graphs.html#1994" class="Function">universal-property-terminal-Reflexive-Graph</a> <a id="2090" class="Symbol">=</a>
    <a id="2096" class="Symbol">{</a><a id="2097" href="graph-theory.terminal-reflexive-graphs.html#2097" class="Bound">l3</a> <a id="2100" href="graph-theory.terminal-reflexive-graphs.html#2100" class="Bound">l4</a> <a id="2103" class="Symbol">:</a> <a id="2105" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2110" class="Symbol">}</a> <a id="2112" class="Symbol">(</a><a id="2113" href="graph-theory.terminal-reflexive-graphs.html#2113" class="Bound">X</a> <a id="2115" class="Symbol">:</a> <a id="2117" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="2133" href="graph-theory.terminal-reflexive-graphs.html#2097" class="Bound">l3</a> <a id="2136" href="graph-theory.terminal-reflexive-graphs.html#2100" class="Bound">l4</a><a id="2138" class="Symbol">)</a> <a id="2140" class="Symbol">→</a>
    <a id="2146" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2155" class="Symbol">(</a><a id="2156" href="graph-theory.morphisms-reflexive-graphs.html#1696" class="Function">hom-Reflexive-Graph</a> <a id="2176" href="graph-theory.terminal-reflexive-graphs.html#2113" class="Bound">X</a> <a id="2178" href="graph-theory.terminal-reflexive-graphs.html#1956" class="Bound">A</a><a id="2179" class="Symbol">)</a>
</pre>
### The terminal reflexive graph

<pre class="Agda"><a id="directed-graph-terminal-Reflexive-Graph"></a><a id="2228" href="graph-theory.terminal-reflexive-graphs.html#2228" class="Function">directed-graph-terminal-Reflexive-Graph</a> <a id="2268" class="Symbol">:</a> <a id="2270" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="2285" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2291" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2297" href="graph-theory.terminal-reflexive-graphs.html#2228" class="Function">directed-graph-terminal-Reflexive-Graph</a> <a id="2337" class="Symbol">=</a> <a id="2339" href="graph-theory.terminal-directed-graphs.html#2309" class="Function">terminal-Directed-Graph</a>

<a id="vertex-terminal-Reflexive-Graph"></a><a id="2364" href="graph-theory.terminal-reflexive-graphs.html#2364" class="Function">vertex-terminal-Reflexive-Graph</a> <a id="2396" class="Symbol">:</a> <a id="2398" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2401" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2407" href="graph-theory.terminal-reflexive-graphs.html#2364" class="Function">vertex-terminal-Reflexive-Graph</a> <a id="2439" class="Symbol">=</a>
  <a id="2443" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="2465" href="graph-theory.terminal-reflexive-graphs.html#2228" class="Function">directed-graph-terminal-Reflexive-Graph</a>

<a id="edge-terminal-Reflexive-Graph"></a><a id="2506" href="graph-theory.terminal-reflexive-graphs.html#2506" class="Function">edge-terminal-Reflexive-Graph</a> <a id="2536" class="Symbol">:</a>
  <a id="2540" class="Symbol">(</a><a id="2541" href="graph-theory.terminal-reflexive-graphs.html#2541" class="Bound">x</a> <a id="2543" href="graph-theory.terminal-reflexive-graphs.html#2543" class="Bound">y</a> <a id="2545" class="Symbol">:</a> <a id="2547" href="graph-theory.terminal-reflexive-graphs.html#2364" class="Function">vertex-terminal-Reflexive-Graph</a><a id="2578" class="Symbol">)</a> <a id="2580" class="Symbol">→</a> <a id="2582" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2585" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2591" href="graph-theory.terminal-reflexive-graphs.html#2506" class="Function">edge-terminal-Reflexive-Graph</a> <a id="2621" class="Symbol">=</a>
  <a id="2625" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="2645" href="graph-theory.terminal-reflexive-graphs.html#2228" class="Function">directed-graph-terminal-Reflexive-Graph</a>

<a id="terminal-Reflexive-Graph"></a><a id="2686" href="graph-theory.terminal-reflexive-graphs.html#2686" class="Function">terminal-Reflexive-Graph</a> <a id="2711" class="Symbol">:</a> <a id="2713" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="2729" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2735" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2741" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2745" href="graph-theory.terminal-reflexive-graphs.html#2686" class="Function">terminal-Reflexive-Graph</a> <a id="2770" class="Symbol">=</a> <a id="2772" href="graph-theory.terminal-directed-graphs.html#2309" class="Function">terminal-Directed-Graph</a>
<a id="2796" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2800" href="graph-theory.terminal-reflexive-graphs.html#2686" class="Function">terminal-Reflexive-Graph</a> <a id="2825" class="Symbol">_</a> <a id="2827" class="Symbol">=</a> <a id="2829" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a>
</pre>