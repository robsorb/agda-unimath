# Discrete dependent reflexive graphs

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="graph-theory.discrete-dependent-reflexive-graphs.html" class="Module">graph-theory.discrete-dependent-reflexive-graphs</a> <a id="104" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="graph-theory.dependent-reflexive-graphs.html" class="Module">graph-theory.dependent-reflexive-graphs</a>
<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="graph-theory.discrete-reflexive-graphs.html" class="Module">graph-theory.discrete-reflexive-graphs</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
</pre>
</details>

## Idea

A [dependent reflexive graph](graph-theory.dependent-reflexive-graphs.md) `H`
over a [reflexive graph](graph-theory.reflexive-graphs.md) is said to be
{{#concept "discrete" Disambiguation="dependent reflexive graph" Agda=is-discrete-Dependent-Reflexive-Graph}}
if the dependent edge relation

```text
  H₁ (refl G x) y : H₀ x → Type
```

is [torsorial](foundation-core.torsorial-type-families.md) for every element
`y : H₀ x`. That is, the dependent reflexive graph `H` is discrete precisely
when the reflexive graph

```text
  ev-point H x
```

is [discrete](graph-theory.discrete-reflexive-graphs.md) for every vertex
`x : G₀`. Furthermore, a dependent reflexive graph is discrete precisely when
the dependent edge relation

```text
  H₁ e y : H₀ x' → Type
```

is torsorial for every edge `e : G₁ x x'` and every element `y : H₀ x`.

## Definitions

### The predicate of being a discrete dependent reflexive graph

<pre class="Agda"><a id="1333" class="Keyword">module</a> <a id="1340" href="graph-theory.discrete-dependent-reflexive-graphs.html#1340" class="Module">_</a>
  <a id="1344" class="Symbol">{</a><a id="1345" href="graph-theory.discrete-dependent-reflexive-graphs.html#1345" class="Bound">l1</a> <a id="1348" href="graph-theory.discrete-dependent-reflexive-graphs.html#1348" class="Bound">l2</a> <a id="1351" href="graph-theory.discrete-dependent-reflexive-graphs.html#1351" class="Bound">l3</a> <a id="1354" href="graph-theory.discrete-dependent-reflexive-graphs.html#1354" class="Bound">l4</a> <a id="1357" class="Symbol">:</a> <a id="1359" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1364" class="Symbol">}</a> <a id="1366" class="Symbol">{</a><a id="1367" href="graph-theory.discrete-dependent-reflexive-graphs.html#1367" class="Bound">G</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="1387" href="graph-theory.discrete-dependent-reflexive-graphs.html#1345" class="Bound">l1</a> <a id="1390" href="graph-theory.discrete-dependent-reflexive-graphs.html#1348" class="Bound">l2</a><a id="1392" class="Symbol">}</a>
  <a id="1396" class="Symbol">(</a><a id="1397" href="graph-theory.discrete-dependent-reflexive-graphs.html#1397" class="Bound">H</a> <a id="1399" class="Symbol">:</a> <a id="1401" href="graph-theory.dependent-reflexive-graphs.html#1990" class="Function">Dependent-Reflexive-Graph</a> <a id="1427" href="graph-theory.discrete-dependent-reflexive-graphs.html#1351" class="Bound">l3</a> <a id="1430" href="graph-theory.discrete-dependent-reflexive-graphs.html#1354" class="Bound">l4</a> <a id="1433" href="graph-theory.discrete-dependent-reflexive-graphs.html#1367" class="Bound">G</a><a id="1434" class="Symbol">)</a>
  <a id="1438" class="Keyword">where</a>

  <a id="1447" href="graph-theory.discrete-dependent-reflexive-graphs.html#1447" class="Function">is-discrete-prop-Dependent-Reflexive-Graph</a> <a id="1490" class="Symbol">:</a> <a id="1492" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1497" class="Symbol">(</a><a id="1498" href="graph-theory.discrete-dependent-reflexive-graphs.html#1345" class="Bound">l1</a> <a id="1501" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1503" href="graph-theory.discrete-dependent-reflexive-graphs.html#1351" class="Bound">l3</a> <a id="1506" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1508" href="graph-theory.discrete-dependent-reflexive-graphs.html#1354" class="Bound">l4</a><a id="1510" class="Symbol">)</a>
  <a id="1514" href="graph-theory.discrete-dependent-reflexive-graphs.html#1447" class="Function">is-discrete-prop-Dependent-Reflexive-Graph</a> <a id="1557" class="Symbol">=</a>
    <a id="1563" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1576" class="Symbol">(</a> <a id="1578" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="1601" href="graph-theory.discrete-dependent-reflexive-graphs.html#1367" class="Bound">G</a><a id="1602" class="Symbol">)</a>
      <a id="1610" class="Symbol">(</a> <a id="1612" class="Symbol">λ</a> <a id="1614" href="graph-theory.discrete-dependent-reflexive-graphs.html#1614" class="Bound">x</a> <a id="1616" class="Symbol">→</a>
        <a id="1626" href="graph-theory.discrete-reflexive-graphs.html#2073" class="Function">is-discrete-prop-Reflexive-Graph</a>
          <a id="1669" class="Symbol">(</a> <a id="1671" href="graph-theory.dependent-reflexive-graphs.html#5742" class="Function">ev-point-Dependent-Reflexive-Graph</a> <a id="1706" href="graph-theory.discrete-dependent-reflexive-graphs.html#1397" class="Bound">H</a> <a id="1708" href="graph-theory.discrete-dependent-reflexive-graphs.html#1614" class="Bound">x</a><a id="1709" class="Symbol">))</a>

  <a id="1715" href="graph-theory.discrete-dependent-reflexive-graphs.html#1715" class="Function">is-discrete-Dependent-Reflexive-Graph</a> <a id="1753" class="Symbol">:</a> <a id="1755" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1758" class="Symbol">(</a><a id="1759" href="graph-theory.discrete-dependent-reflexive-graphs.html#1345" class="Bound">l1</a> <a id="1762" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1764" href="graph-theory.discrete-dependent-reflexive-graphs.html#1351" class="Bound">l3</a> <a id="1767" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1769" href="graph-theory.discrete-dependent-reflexive-graphs.html#1354" class="Bound">l4</a><a id="1771" class="Symbol">)</a>
  <a id="1775" href="graph-theory.discrete-dependent-reflexive-graphs.html#1715" class="Function">is-discrete-Dependent-Reflexive-Graph</a> <a id="1813" class="Symbol">=</a>
    <a id="1819" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1829" href="graph-theory.discrete-dependent-reflexive-graphs.html#1447" class="Function">is-discrete-prop-Dependent-Reflexive-Graph</a>

  <a id="1875" href="graph-theory.discrete-dependent-reflexive-graphs.html#1875" class="Function">is-prop-is-discrete-Dependent-Reflexive-Graph</a> <a id="1921" class="Symbol">:</a>
    <a id="1927" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1935" href="graph-theory.discrete-dependent-reflexive-graphs.html#1715" class="Function">is-discrete-Dependent-Reflexive-Graph</a>
  <a id="1975" href="graph-theory.discrete-dependent-reflexive-graphs.html#1875" class="Function">is-prop-is-discrete-Dependent-Reflexive-Graph</a> <a id="2021" class="Symbol">=</a>
    <a id="2027" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2045" href="graph-theory.discrete-dependent-reflexive-graphs.html#1447" class="Function">is-discrete-prop-Dependent-Reflexive-Graph</a>
</pre>