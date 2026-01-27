# Mere equivalences of undirected graphs

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="graph-theory.mere-equivalences-undirected-graphs.html" class="Module">graph-theory.mere-equivalences-undirected-graphs</a> <a id="107" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="graph-theory.equivalences-undirected-graphs.html" class="Module">graph-theory.equivalences-undirected-graphs</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
</details>

## Idea

Two [undirected graphs](graph-theory.undirected-graphs.md) are said to be
**merely equivalent** if there merely
[exists](foundation.existential-quantification.md) an
[equivalence of undirected graphs](graph-theory.equivalences-undirected-graphs.md)
between them.

## Definition

<pre class="Agda"><a id="700" class="Keyword">module</a> <a id="707" href="graph-theory.mere-equivalences-undirected-graphs.html#707" class="Module">_</a>
  <a id="711" class="Symbol">{</a><a id="712" href="graph-theory.mere-equivalences-undirected-graphs.html#712" class="Bound">l1</a> <a id="715" href="graph-theory.mere-equivalences-undirected-graphs.html#715" class="Bound">l2</a> <a id="718" href="graph-theory.mere-equivalences-undirected-graphs.html#718" class="Bound">l3</a> <a id="721" href="graph-theory.mere-equivalences-undirected-graphs.html#721" class="Bound">l4</a> <a id="724" class="Symbol">:</a> <a id="726" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="731" class="Symbol">}</a>
  <a id="735" class="Symbol">(</a><a id="736" href="graph-theory.mere-equivalences-undirected-graphs.html#736" class="Bound">G</a> <a id="738" class="Symbol">:</a> <a id="740" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="757" href="graph-theory.mere-equivalences-undirected-graphs.html#712" class="Bound">l1</a> <a id="760" href="graph-theory.mere-equivalences-undirected-graphs.html#715" class="Bound">l2</a><a id="762" class="Symbol">)</a> <a id="764" class="Symbol">(</a><a id="765" href="graph-theory.mere-equivalences-undirected-graphs.html#765" class="Bound">H</a> <a id="767" class="Symbol">:</a> <a id="769" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="786" href="graph-theory.mere-equivalences-undirected-graphs.html#718" class="Bound">l3</a> <a id="789" href="graph-theory.mere-equivalences-undirected-graphs.html#721" class="Bound">l4</a><a id="791" class="Symbol">)</a>
  <a id="795" class="Keyword">where</a>

  <a id="804" href="graph-theory.mere-equivalences-undirected-graphs.html#804" class="Function">mere-equiv-Undirected-Graph-Prop</a> <a id="837" class="Symbol">:</a> <a id="839" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="844" class="Symbol">(</a><a id="845" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="850" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="856" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="858" href="graph-theory.mere-equivalences-undirected-graphs.html#712" class="Bound">l1</a> <a id="861" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="863" href="graph-theory.mere-equivalences-undirected-graphs.html#715" class="Bound">l2</a> <a id="866" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="868" href="graph-theory.mere-equivalences-undirected-graphs.html#718" class="Bound">l3</a> <a id="871" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="873" href="graph-theory.mere-equivalences-undirected-graphs.html#721" class="Bound">l4</a><a id="875" class="Symbol">)</a>
  <a id="879" href="graph-theory.mere-equivalences-undirected-graphs.html#804" class="Function">mere-equiv-Undirected-Graph-Prop</a> <a id="912" class="Symbol">=</a> <a id="914" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="925" class="Symbol">(</a><a id="926" href="graph-theory.equivalences-undirected-graphs.html#1550" class="Function">equiv-Undirected-Graph</a> <a id="949" href="graph-theory.mere-equivalences-undirected-graphs.html#736" class="Bound">G</a> <a id="951" href="graph-theory.mere-equivalences-undirected-graphs.html#765" class="Bound">H</a><a id="952" class="Symbol">)</a>

  <a id="957" href="graph-theory.mere-equivalences-undirected-graphs.html#957" class="Function">mere-equiv-Undirected-Graph</a> <a id="985" class="Symbol">:</a> <a id="987" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="990" class="Symbol">(</a><a id="991" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="996" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1002" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1004" href="graph-theory.mere-equivalences-undirected-graphs.html#712" class="Bound">l1</a> <a id="1007" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1009" href="graph-theory.mere-equivalences-undirected-graphs.html#715" class="Bound">l2</a> <a id="1012" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1014" href="graph-theory.mere-equivalences-undirected-graphs.html#718" class="Bound">l3</a> <a id="1017" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1019" href="graph-theory.mere-equivalences-undirected-graphs.html#721" class="Bound">l4</a><a id="1021" class="Symbol">)</a>
  <a id="1025" href="graph-theory.mere-equivalences-undirected-graphs.html#957" class="Function">mere-equiv-Undirected-Graph</a> <a id="1053" class="Symbol">=</a> <a id="1055" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1065" href="graph-theory.mere-equivalences-undirected-graphs.html#804" class="Function">mere-equiv-Undirected-Graph-Prop</a>

  <a id="1101" href="graph-theory.mere-equivalences-undirected-graphs.html#1101" class="Function">is-prop-mere-equiv-Undirected-Graph</a> <a id="1137" class="Symbol">:</a> <a id="1139" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1147" href="graph-theory.mere-equivalences-undirected-graphs.html#957" class="Function">mere-equiv-Undirected-Graph</a>
  <a id="1177" href="graph-theory.mere-equivalences-undirected-graphs.html#1101" class="Function">is-prop-mere-equiv-Undirected-Graph</a> <a id="1213" class="Symbol">=</a>
    <a id="1219" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1237" href="graph-theory.mere-equivalences-undirected-graphs.html#804" class="Function">mere-equiv-Undirected-Graph-Prop</a>
</pre>
## Properties

### The mere equivalence relation on undirected graphs is reflexive

<pre class="Agda"><a id="1367" class="Keyword">module</a> <a id="1374" href="graph-theory.mere-equivalences-undirected-graphs.html#1374" class="Module">_</a>
  <a id="1378" class="Symbol">{</a><a id="1379" href="graph-theory.mere-equivalences-undirected-graphs.html#1379" class="Bound">l1</a> <a id="1382" href="graph-theory.mere-equivalences-undirected-graphs.html#1382" class="Bound">l2</a> <a id="1385" class="Symbol">:</a> <a id="1387" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1392" class="Symbol">}</a> <a id="1394" class="Symbol">(</a><a id="1395" href="graph-theory.mere-equivalences-undirected-graphs.html#1395" class="Bound">G</a> <a id="1397" class="Symbol">:</a> <a id="1399" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="1416" href="graph-theory.mere-equivalences-undirected-graphs.html#1379" class="Bound">l1</a> <a id="1419" href="graph-theory.mere-equivalences-undirected-graphs.html#1382" class="Bound">l2</a><a id="1421" class="Symbol">)</a>
  <a id="1425" class="Keyword">where</a>

  <a id="1434" href="graph-theory.mere-equivalences-undirected-graphs.html#1434" class="Function">refl-mere-equiv-Undirected-Graph</a> <a id="1467" class="Symbol">:</a> <a id="1469" href="graph-theory.mere-equivalences-undirected-graphs.html#957" class="Function">mere-equiv-Undirected-Graph</a> <a id="1497" href="graph-theory.mere-equivalences-undirected-graphs.html#1395" class="Bound">G</a> <a id="1499" href="graph-theory.mere-equivalences-undirected-graphs.html#1395" class="Bound">G</a>
  <a id="1503" href="graph-theory.mere-equivalences-undirected-graphs.html#1434" class="Function">refl-mere-equiv-Undirected-Graph</a> <a id="1536" class="Symbol">=</a>
    <a id="1542" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="1558" class="Symbol">(</a><a id="1559" href="graph-theory.equivalences-undirected-graphs.html#5478" class="Function">id-equiv-Undirected-Graph</a> <a id="1585" href="graph-theory.mere-equivalences-undirected-graphs.html#1395" class="Bound">G</a><a id="1586" class="Symbol">)</a>
</pre>
## External links

- [Graph isomoprhism](https://www.wikidata.org/entity/Q303100) at Wikidata
- [Graph isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphism) at
  Wikipedia
- [Graph isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.html) at
  Wolfram MathWorld
- [Isomorphism](https://ncatlab.org/nlab/show/isomorphism) at $n$Lab
