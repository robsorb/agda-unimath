# Lifting operations

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="orthogonal-factorization-systems.lifting-operations.html" class="Module">orthogonal-factorization-systems.lifting-operations</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="334" class="Keyword">open</a> <a id="339" class="Keyword">import</a> <a id="346" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="orthogonal-factorization-systems.pullback-hom.html" class="Module">orthogonal-factorization-systems.pullback-hom</a>
</pre>
</details>

## Idea

Given two maps, `f : A → X` and `g : B → Y`, a _lifting operation between `f`
and `g`_ is a choice of lifting square for every commuting square

```text
  A ------> B
  |         |
 f|         |g
  ∨         ∨
  X ------> Y.
```

Given a lifting operation we can say that `f` has a _left lifting structure_
with respect to `g` and that `g` has a _right lifting structure_ with respect to
`f`.

**Note**: This is the Curry–Howard interpretation of what is classically called
_lifting properties_. However, these are generally additional structure on the
maps. For the proof-irrelevant notion see
[mere lifting properties](orthogonal-factorization-systems.mere-lifting-properties.md).

## Definition

We define lifting operations to be [sections](foundation-core.sections.md) of
the [pullback-hom](orthogonal-factorization-systems.pullback-hom.md).

<pre class="Agda"><a id="1314" class="Keyword">module</a> <a id="1321" href="orthogonal-factorization-systems.lifting-operations.html#1321" class="Module">_</a>
  <a id="1325" class="Symbol">{</a><a id="1326" href="orthogonal-factorization-systems.lifting-operations.html#1326" class="Bound">l1</a> <a id="1329" href="orthogonal-factorization-systems.lifting-operations.html#1329" class="Bound">l2</a> <a id="1332" href="orthogonal-factorization-systems.lifting-operations.html#1332" class="Bound">l3</a> <a id="1335" href="orthogonal-factorization-systems.lifting-operations.html#1335" class="Bound">l4</a> <a id="1338" class="Symbol">:</a> <a id="1340" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1345" class="Symbol">}</a>
  <a id="1349" class="Symbol">{</a><a id="1350" href="orthogonal-factorization-systems.lifting-operations.html#1350" class="Bound">A</a> <a id="1352" class="Symbol">:</a> <a id="1354" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1357" href="orthogonal-factorization-systems.lifting-operations.html#1326" class="Bound">l1</a><a id="1359" class="Symbol">}</a> <a id="1361" class="Symbol">{</a><a id="1362" href="orthogonal-factorization-systems.lifting-operations.html#1362" class="Bound">B</a> <a id="1364" class="Symbol">:</a> <a id="1366" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1369" href="orthogonal-factorization-systems.lifting-operations.html#1329" class="Bound">l2</a><a id="1371" class="Symbol">}</a> <a id="1373" class="Symbol">{</a><a id="1374" href="orthogonal-factorization-systems.lifting-operations.html#1374" class="Bound">X</a> <a id="1376" class="Symbol">:</a> <a id="1378" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1381" href="orthogonal-factorization-systems.lifting-operations.html#1332" class="Bound">l3</a><a id="1383" class="Symbol">}</a> <a id="1385" class="Symbol">{</a><a id="1386" href="orthogonal-factorization-systems.lifting-operations.html#1386" class="Bound">Y</a> <a id="1388" class="Symbol">:</a> <a id="1390" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1393" href="orthogonal-factorization-systems.lifting-operations.html#1335" class="Bound">l4</a><a id="1395" class="Symbol">}</a>
  <a id="1399" class="Symbol">(</a><a id="1400" href="orthogonal-factorization-systems.lifting-operations.html#1400" class="Bound">f</a> <a id="1402" class="Symbol">:</a> <a id="1404" href="orthogonal-factorization-systems.lifting-operations.html#1350" class="Bound">A</a> <a id="1406" class="Symbol">→</a> <a id="1408" href="orthogonal-factorization-systems.lifting-operations.html#1374" class="Bound">X</a><a id="1409" class="Symbol">)</a> <a id="1411" class="Symbol">(</a><a id="1412" href="orthogonal-factorization-systems.lifting-operations.html#1412" class="Bound">g</a> <a id="1414" class="Symbol">:</a> <a id="1416" href="orthogonal-factorization-systems.lifting-operations.html#1362" class="Bound">B</a> <a id="1418" class="Symbol">→</a> <a id="1420" href="orthogonal-factorization-systems.lifting-operations.html#1386" class="Bound">Y</a><a id="1421" class="Symbol">)</a>
  <a id="1425" class="Keyword">where</a>

  <a id="1434" href="orthogonal-factorization-systems.lifting-operations.html#1434" class="Function">diagonal-lift</a> <a id="1448" class="Symbol">:</a> <a id="1450" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1453" class="Symbol">(</a><a id="1454" href="orthogonal-factorization-systems.lifting-operations.html#1326" class="Bound">l1</a> <a id="1457" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1459" href="orthogonal-factorization-systems.lifting-operations.html#1329" class="Bound">l2</a> <a id="1462" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1464" href="orthogonal-factorization-systems.lifting-operations.html#1332" class="Bound">l3</a> <a id="1467" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1469" href="orthogonal-factorization-systems.lifting-operations.html#1335" class="Bound">l4</a><a id="1471" class="Symbol">)</a>
  <a id="1475" href="orthogonal-factorization-systems.lifting-operations.html#1434" class="Function">diagonal-lift</a> <a id="1489" class="Symbol">=</a> <a id="1491" href="foundation-core.sections.html#1373" class="Function">section</a> <a id="1499" class="Symbol">(</a><a id="1500" href="orthogonal-factorization-systems.pullback-hom.html#5047" class="Function">pullback-hom</a> <a id="1513" href="orthogonal-factorization-systems.lifting-operations.html#1400" class="Bound">f</a> <a id="1515" href="orthogonal-factorization-systems.lifting-operations.html#1412" class="Bound">g</a><a id="1516" class="Symbol">)</a>

  <a id="1521" href="orthogonal-factorization-systems.lifting-operations.html#1521" class="Function Operator">_⧄_</a> <a id="1525" class="Symbol">=</a> <a id="1527" href="orthogonal-factorization-systems.lifting-operations.html#1434" class="Function">diagonal-lift</a>

  <a id="1544" href="orthogonal-factorization-systems.lifting-operations.html#1544" class="Function">map-diagonal-lift</a> <a id="1562" class="Symbol">:</a> <a id="1564" href="orthogonal-factorization-systems.lifting-operations.html#1434" class="Function">diagonal-lift</a> <a id="1578" class="Symbol">→</a> <a id="1580" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="1590" href="orthogonal-factorization-systems.lifting-operations.html#1400" class="Bound">f</a> <a id="1592" href="orthogonal-factorization-systems.lifting-operations.html#1412" class="Bound">g</a> <a id="1594" class="Symbol">→</a> <a id="1596" href="orthogonal-factorization-systems.lifting-operations.html#1374" class="Bound">X</a> <a id="1598" class="Symbol">→</a> <a id="1600" href="orthogonal-factorization-systems.lifting-operations.html#1362" class="Bound">B</a>
  <a id="1604" href="orthogonal-factorization-systems.lifting-operations.html#1544" class="Function">map-diagonal-lift</a> <a id="1622" class="Symbol">=</a> <a id="1624" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="1631" href="orthogonal-factorization-systems.lifting-operations.html#1631" class="Function">is-section-map-diagonal-lift</a> <a id="1660" class="Symbol">:</a>
    <a id="1666" class="Symbol">(</a><a id="1667" href="orthogonal-factorization-systems.lifting-operations.html#1667" class="Bound">d</a> <a id="1669" class="Symbol">:</a> <a id="1671" href="orthogonal-factorization-systems.lifting-operations.html#1434" class="Function">diagonal-lift</a><a id="1684" class="Symbol">)</a> <a id="1686" class="Symbol">→</a> <a id="1688" class="Symbol">(</a><a id="1689" href="orthogonal-factorization-systems.pullback-hom.html#5047" class="Function">pullback-hom</a> <a id="1702" href="orthogonal-factorization-systems.lifting-operations.html#1400" class="Bound">f</a> <a id="1704" href="orthogonal-factorization-systems.lifting-operations.html#1412" class="Bound">g</a> <a id="1706" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1708" href="orthogonal-factorization-systems.lifting-operations.html#1544" class="Function">map-diagonal-lift</a> <a id="1726" href="orthogonal-factorization-systems.lifting-operations.html#1667" class="Bound">d</a><a id="1727" class="Symbol">)</a> <a id="1729" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1731" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="1736" href="orthogonal-factorization-systems.lifting-operations.html#1631" class="Function">is-section-map-diagonal-lift</a> <a id="1765" class="Symbol">=</a> <a id="1767" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>