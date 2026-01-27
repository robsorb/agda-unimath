# Discrete reflexive relations

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation.discrete-reflexive-relations.html" class="Module">foundation.discrete-reflexive-relations</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="184" class="Keyword">open</a> <a id="189" class="Keyword">import</a> <a id="196" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="foundation.reflexive-relations.html" class="Module">foundation.reflexive-relations</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="360" class="Keyword">open</a> <a id="365" class="Keyword">import</a> <a id="372" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A [reflexive relation](foundation.binary-relations.md) `R` on `A` is said to be
{{#concept "discrete" Disambiguation="reflexive relations valued in types" Agda=is-discrete-Reflexive-Relation}}
if, for every element `x : A`, the type family `R x` is
[torsorial](foundation-core.torsorial-type-families.md). In other words, the
[dependent sum](foundation.dependent-pair-types.md) `Σ (y : A), (R x y)` is
[contractible](foundation-core.contractible-types.md) for every `x`.

The {{#concept "standard discrete reflexive relation"}} on a type `X` is the
relation defined by [identifications](foundation-core.identity-types.md),

```text
  R x y := (x ＝ y).
```

## Definitions

### The predicate on reflexive relations of being discrete

<pre class="Agda"><a id="1251" class="Keyword">module</a> <a id="1258" href="foundation.discrete-reflexive-relations.html#1258" class="Module">_</a>
  <a id="1262" class="Symbol">{</a><a id="1263" href="foundation.discrete-reflexive-relations.html#1263" class="Bound">l1</a> <a id="1266" href="foundation.discrete-reflexive-relations.html#1266" class="Bound">l2</a> <a id="1269" class="Symbol">:</a> <a id="1271" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1276" class="Symbol">}</a> <a id="1278" class="Symbol">{</a><a id="1279" href="foundation.discrete-reflexive-relations.html#1279" class="Bound">A</a> <a id="1281" class="Symbol">:</a> <a id="1283" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1286" href="foundation.discrete-reflexive-relations.html#1263" class="Bound">l1</a><a id="1288" class="Symbol">}</a> <a id="1290" class="Symbol">(</a><a id="1291" href="foundation.discrete-reflexive-relations.html#1291" class="Bound">R</a> <a id="1293" class="Symbol">:</a> <a id="1295" href="foundation.reflexive-relations.html#654" class="Function">Reflexive-Relation</a> <a id="1314" href="foundation.discrete-reflexive-relations.html#1266" class="Bound">l2</a> <a id="1317" href="foundation.discrete-reflexive-relations.html#1279" class="Bound">A</a><a id="1318" class="Symbol">)</a>
  <a id="1322" class="Keyword">where</a>

  <a id="1331" href="foundation.discrete-reflexive-relations.html#1331" class="Function">is-discrete-prop-Reflexive-Relation</a> <a id="1367" class="Symbol">:</a> <a id="1369" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1374" class="Symbol">(</a><a id="1375" href="foundation.discrete-reflexive-relations.html#1263" class="Bound">l1</a> <a id="1378" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1380" href="foundation.discrete-reflexive-relations.html#1266" class="Bound">l2</a><a id="1382" class="Symbol">)</a>
  <a id="1386" href="foundation.discrete-reflexive-relations.html#1331" class="Function">is-discrete-prop-Reflexive-Relation</a> <a id="1422" class="Symbol">=</a>
    <a id="1428" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1435" href="foundation.discrete-reflexive-relations.html#1279" class="Bound">A</a> <a id="1437" class="Symbol">(λ</a> <a id="1440" href="foundation.discrete-reflexive-relations.html#1440" class="Bound">a</a> <a id="1442" class="Symbol">→</a> <a id="1444" href="foundation.torsorial-type-families.html#1175" class="Function">is-torsorial-Prop</a> <a id="1462" class="Symbol">(</a><a id="1463" href="foundation.reflexive-relations.html#879" class="Function">rel-Reflexive-Relation</a> <a id="1486" href="foundation.discrete-reflexive-relations.html#1291" class="Bound">R</a> <a id="1488" href="foundation.discrete-reflexive-relations.html#1440" class="Bound">a</a><a id="1489" class="Symbol">))</a>

  <a id="1495" href="foundation.discrete-reflexive-relations.html#1495" class="Function">is-discrete-Reflexive-Relation</a> <a id="1526" class="Symbol">:</a> <a id="1528" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1531" class="Symbol">(</a><a id="1532" href="foundation.discrete-reflexive-relations.html#1263" class="Bound">l1</a> <a id="1535" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1537" href="foundation.discrete-reflexive-relations.html#1266" class="Bound">l2</a><a id="1539" class="Symbol">)</a>
  <a id="1543" href="foundation.discrete-reflexive-relations.html#1495" class="Function">is-discrete-Reflexive-Relation</a> <a id="1574" class="Symbol">=</a>
    <a id="1580" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1590" href="foundation.discrete-reflexive-relations.html#1331" class="Function">is-discrete-prop-Reflexive-Relation</a>

  <a id="1629" href="foundation.discrete-reflexive-relations.html#1629" class="Function">is-prop-is-discrete-Reflexive-Relation</a> <a id="1668" class="Symbol">:</a>
    <a id="1674" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1682" href="foundation.discrete-reflexive-relations.html#1495" class="Function">is-discrete-Reflexive-Relation</a>
  <a id="1715" href="foundation.discrete-reflexive-relations.html#1629" class="Function">is-prop-is-discrete-Reflexive-Relation</a> <a id="1754" class="Symbol">=</a>
    <a id="1760" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1778" href="foundation.discrete-reflexive-relations.html#1331" class="Function">is-discrete-prop-Reflexive-Relation</a>
</pre>
## Properties

### The identity relation is discrete

<pre class="Agda"><a id="1881" class="Keyword">module</a> <a id="1888" href="foundation.discrete-reflexive-relations.html#1888" class="Module">_</a>
  <a id="1892" class="Symbol">{</a><a id="1893" href="foundation.discrete-reflexive-relations.html#1893" class="Bound">l</a> <a id="1895" class="Symbol">:</a> <a id="1897" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1902" class="Symbol">}</a> <a id="1904" class="Symbol">(</a><a id="1905" href="foundation.discrete-reflexive-relations.html#1905" class="Bound">A</a> <a id="1907" class="Symbol">:</a> <a id="1909" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1912" href="foundation.discrete-reflexive-relations.html#1893" class="Bound">l</a><a id="1913" class="Symbol">)</a>
  <a id="1917" class="Keyword">where</a>

  <a id="1926" href="foundation.discrete-reflexive-relations.html#1926" class="Function">is-discrete-Id-Reflexive-Relation</a> <a id="1960" class="Symbol">:</a>
    <a id="1966" href="foundation.discrete-reflexive-relations.html#1495" class="Function">is-discrete-Reflexive-Relation</a> <a id="1997" class="Symbol">(</a><a id="1998" href="foundation.reflexive-relations.html#1110" class="Function">Id-Reflexive-Relation</a> <a id="2020" href="foundation.discrete-reflexive-relations.html#1905" class="Bound">A</a><a id="2021" class="Symbol">)</a>
  <a id="2025" href="foundation.discrete-reflexive-relations.html#1926" class="Function">is-discrete-Id-Reflexive-Relation</a> <a id="2059" class="Symbol">=</a> <a id="2061" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a>
</pre>
## See also

- [Discrete binary relations](foundation.discrete-binary-relations.md)
- [Discrete directed graphs](graph-theory.discrete-directed-graphs.md)
- [Discrete reflexive graphs](graph-theory.discrete-reflexive-graphs.md)
