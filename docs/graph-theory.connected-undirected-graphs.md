# Connected graphs

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="graph-theory.connected-undirected-graphs.html" class="Module">graph-theory.connected-undirected-graphs</a> <a id="77" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="133" class="Keyword">open</a> <a id="138" class="Keyword">import</a> <a id="145" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="graph-theory.walks-undirected-graphs.html" class="Module">graph-theory.walks-undirected-graphs</a>
</pre>
</details>

## Idea

An [undirected graph](graph-theory.undirected-graphs.md) is said to be
**connected** if any point can be reached from any point by a
[walk](graph-theory.walks-undirected-graphs.md).

## Definition

<pre class="Agda"><a id="582" class="Keyword">module</a> <a id="589" href="graph-theory.connected-undirected-graphs.html#589" class="Module">_</a>
  <a id="593" class="Symbol">{</a><a id="594" href="graph-theory.connected-undirected-graphs.html#594" class="Bound">l1</a> <a id="597" href="graph-theory.connected-undirected-graphs.html#597" class="Bound">l2</a> <a id="600" class="Symbol">:</a> <a id="602" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="607" class="Symbol">}</a> <a id="609" class="Symbol">(</a><a id="610" href="graph-theory.connected-undirected-graphs.html#610" class="Bound">G</a> <a id="612" class="Symbol">:</a> <a id="614" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="631" href="graph-theory.connected-undirected-graphs.html#594" class="Bound">l1</a> <a id="634" href="graph-theory.connected-undirected-graphs.html#597" class="Bound">l2</a><a id="636" class="Symbol">)</a>
  <a id="640" class="Keyword">where</a>

  <a id="649" href="graph-theory.connected-undirected-graphs.html#649" class="Function">is-connected-Undirected-Graph</a> <a id="679" class="Symbol">:</a> <a id="681" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="684" class="Symbol">(</a><a id="685" href="graph-theory.connected-undirected-graphs.html#594" class="Bound">l1</a> <a id="688" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="690" href="graph-theory.connected-undirected-graphs.html#597" class="Bound">l2</a> <a id="693" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="695" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="700" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="705" class="Symbol">)</a>
  <a id="709" href="graph-theory.connected-undirected-graphs.html#649" class="Function">is-connected-Undirected-Graph</a> <a id="739" class="Symbol">=</a>
    <a id="745" class="Symbol">(</a><a id="746" href="graph-theory.connected-undirected-graphs.html#746" class="Bound">x</a> <a id="748" href="graph-theory.connected-undirected-graphs.html#748" class="Bound">y</a> <a id="750" class="Symbol">:</a> <a id="752" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="776" href="graph-theory.connected-undirected-graphs.html#610" class="Bound">G</a><a id="777" class="Symbol">)</a> <a id="779" class="Symbol">→</a>
    <a id="785" href="foundation.propositional-truncations.html#1578" class="Function">type-trunc-Prop</a> <a id="801" class="Symbol">(</a><a id="802" href="graph-theory.walks-undirected-graphs.html#1491" class="Datatype">walk-Undirected-Graph</a> <a id="824" href="graph-theory.connected-undirected-graphs.html#610" class="Bound">G</a> <a id="826" href="graph-theory.connected-undirected-graphs.html#746" class="Bound">x</a> <a id="828" href="graph-theory.connected-undirected-graphs.html#748" class="Bound">y</a><a id="829" class="Symbol">)</a>
</pre>
## Properties

### The property of being connected for an undirected graph is a proposition

<pre class="Agda">  <a id="939" href="graph-theory.connected-undirected-graphs.html#939" class="Function">is-prop-is-connected-Undirected-Graph</a>
    <a id="981" class="Symbol">:</a> <a id="983" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="991" href="graph-theory.connected-undirected-graphs.html#649" class="Function">is-connected-Undirected-Graph</a>
  <a id="1023" href="graph-theory.connected-undirected-graphs.html#939" class="Function">is-prop-is-connected-Undirected-Graph</a> <a id="1061" class="Symbol">=</a>
    <a id="1067" href="foundation-core.propositions.html#6443" class="Function">is-prop-Π</a> <a id="1077" class="Symbol">(λ</a> <a id="1080" href="graph-theory.connected-undirected-graphs.html#1080" class="Bound">_</a> <a id="1082" class="Symbol">→</a> <a id="1084" href="foundation-core.propositions.html#6443" class="Function">is-prop-Π</a> <a id="1094" class="Symbol">(λ</a> <a id="1097" href="graph-theory.connected-undirected-graphs.html#1097" class="Bound">_</a> <a id="1099" class="Symbol">→</a> <a id="1101" href="foundation.propositional-truncations.html#1806" class="Function">is-prop-type-trunc-Prop</a><a id="1124" class="Symbol">))</a>
</pre>
## External links

- [Connected graph](https://ncatlab.org/nlab/show/connected+graph) at $n$Lab
- [Connected graph](https://www.wikidata.org/entity/Q230655) on Wikidata
- [Connectivity (graph theory)](<https://en.wikipedia.org/wiki/Connectivity_(graph_theory)>)
  on Wikipedia
- [Connected graph](https://mathworld.wolfram.com/ConnectedGraph.html) at
  Wolfram MathWorld
