# Composition structure on globular types

<pre class="Agda"><a id="52" class="Symbol">{-#</a> <a id="56" class="Keyword">OPTIONS</a> <a id="64" class="Pragma">--guardedness</a> <a id="78" class="Symbol">#-}</a>

<a id="83" class="Keyword">module</a> <a id="90" href="globular-types.composition-structure-globular-types.html" class="Module">globular-types.composition-structure-globular-types</a> <a id="142" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="globular-types.binary-globular-maps.html" class="Module">globular-types.binary-globular-maps</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

A
{{#concept "composition structure" Disambiguation="globular type" Agda=composition-Globular-Type}}
on a [globular type](globular-types.globular-types.md) `G` consists of a
[binary globular map](globular-types.binary-globular-maps.md)

```text
  - ∘ - : G' y z → G' x y → G' x z,
```

and for any two `0`-cells `x y : G₀` a composition structure on the globular
type `G' x y` of `1`-cells of `G`. More explicitly, a composition structure
consists of binary operations

```text
  - ∘ - : (𝑛+1)-Cell G y z → (𝑛+1)-Cell G x y → (𝑛+1)-Cell G x z,
```

each of which preserve all higher cells of the globular type `G`. Globular
composition structure is therefore a strengthening of the
[transitivity structure](globular-types.transitive-globular-types.md) on
globular types.

## Definitions

### Globular composition structure

<pre class="Agda"><a id="1186" class="Keyword">record</a>
  <a id="composition-Globular-Type"></a><a id="1195" href="globular-types.composition-structure-globular-types.html#1195" class="Record">composition-Globular-Type</a>
    <a id="1225" class="Symbol">{</a><a id="1226" href="globular-types.composition-structure-globular-types.html#1226" class="Bound">l1</a> <a id="1229" href="globular-types.composition-structure-globular-types.html#1229" class="Bound">l2</a> <a id="1232" class="Symbol">:</a> <a id="1234" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1239" class="Symbol">}</a> <a id="1241" class="Symbol">(</a><a id="1242" href="globular-types.composition-structure-globular-types.html#1242" class="Bound">G</a> <a id="1244" class="Symbol">:</a> <a id="1246" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1260" href="globular-types.composition-structure-globular-types.html#1226" class="Bound">l1</a> <a id="1263" href="globular-types.composition-structure-globular-types.html#1229" class="Bound">l2</a><a id="1265" class="Symbol">)</a> <a id="1267" class="Symbol">:</a> <a id="1269" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1272" class="Symbol">(</a><a id="1273" href="globular-types.composition-structure-globular-types.html#1226" class="Bound">l1</a> <a id="1276" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1278" href="globular-types.composition-structure-globular-types.html#1229" class="Bound">l2</a><a id="1280" class="Symbol">)</a>
  <a id="1284" class="Keyword">where</a>
  <a id="1292" class="Keyword">coinductive</a>

  <a id="1307" class="Keyword">field</a>
    <a id="composition-Globular-Type.comp-binary-globular-map-composition-Globular-Type"></a><a id="1317" href="globular-types.composition-structure-globular-types.html#1317" class="Field">comp-binary-globular-map-composition-Globular-Type</a> <a id="1368" class="Symbol">:</a>
      <a id="1376" class="Symbol">{</a><a id="1377" href="globular-types.composition-structure-globular-types.html#1377" class="Bound">x</a> <a id="1379" href="globular-types.composition-structure-globular-types.html#1379" class="Bound">y</a> <a id="1381" href="globular-types.composition-structure-globular-types.html#1381" class="Bound">z</a> <a id="1383" class="Symbol">:</a> <a id="1385" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1406" href="globular-types.composition-structure-globular-types.html#1242" class="Bound">G</a><a id="1407" class="Symbol">}</a> <a id="1409" class="Symbol">→</a>
      <a id="1417" href="globular-types.binary-globular-maps.html#749" class="Record">binary-globular-map</a>
        <a id="1445" class="Symbol">(</a> <a id="1447" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1482" href="globular-types.composition-structure-globular-types.html#1242" class="Bound">G</a> <a id="1484" href="globular-types.composition-structure-globular-types.html#1379" class="Bound">y</a> <a id="1486" href="globular-types.composition-structure-globular-types.html#1381" class="Bound">z</a><a id="1487" class="Symbol">)</a>
        <a id="1497" class="Symbol">(</a> <a id="1499" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1534" href="globular-types.composition-structure-globular-types.html#1242" class="Bound">G</a> <a id="1536" href="globular-types.composition-structure-globular-types.html#1377" class="Bound">x</a> <a id="1538" href="globular-types.composition-structure-globular-types.html#1379" class="Bound">y</a><a id="1539" class="Symbol">)</a>
        <a id="1549" class="Symbol">(</a> <a id="1551" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1586" href="globular-types.composition-structure-globular-types.html#1242" class="Bound">G</a> <a id="1588" href="globular-types.composition-structure-globular-types.html#1377" class="Bound">x</a> <a id="1590" href="globular-types.composition-structure-globular-types.html#1381" class="Bound">z</a><a id="1591" class="Symbol">)</a>

  <a id="1596" class="Keyword">field</a>
    <a id="composition-Globular-Type.composition-1-cell-globular-type-Globular-Type"></a><a id="1606" href="globular-types.composition-structure-globular-types.html#1606" class="Field">composition-1-cell-globular-type-Globular-Type</a> <a id="1653" class="Symbol">:</a>
      <a id="1661" class="Symbol">{</a><a id="1662" href="globular-types.composition-structure-globular-types.html#1662" class="Bound">x</a> <a id="1664" href="globular-types.composition-structure-globular-types.html#1664" class="Bound">y</a> <a id="1666" class="Symbol">:</a> <a id="1668" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1689" href="globular-types.composition-structure-globular-types.html#1242" class="Bound">G</a><a id="1690" class="Symbol">}</a> <a id="1692" class="Symbol">→</a>
      <a id="1700" href="globular-types.composition-structure-globular-types.html#1195" class="Record">composition-Globular-Type</a>
        <a id="1734" class="Symbol">(</a> <a id="1736" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1771" href="globular-types.composition-structure-globular-types.html#1242" class="Bound">G</a> <a id="1773" href="globular-types.composition-structure-globular-types.html#1662" class="Bound">x</a> <a id="1775" href="globular-types.composition-structure-globular-types.html#1664" class="Bound">y</a><a id="1776" class="Symbol">)</a>

<a id="1779" class="Keyword">open</a> <a id="1784" href="globular-types.composition-structure-globular-types.html#1195" class="Module">composition-Globular-Type</a> <a id="1810" class="Keyword">public</a>
</pre>