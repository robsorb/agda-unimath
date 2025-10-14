# Unlabeled structures of finite species

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="species.unlabeled-structures-species.html" class="Module">species.unlabeled-structures-species</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="species.species-of-types.html" class="Module">species.species-of-types</a>

<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

The type of
{{#concept "unlabeled `F`-structures" Disambiguation="of a species of types" Agda=unlabeled-structure-species-types}}
of order `n` of a [species](species.species-of-types.md) `F` is the type of
[sets](foundation-core.sets.md) `X` of size `n` equipped with an `F`-structure.
Two unlabeled `F`-structures of order `n` are considered to be the same if the
underlying sets are isomorphic and the `F`-structure of the first transports
along this isomorphism to the `F`-structure of the second. It will automatically
follow from the [univalence axiom](foundation.univalence.md) that the
[identity type](foundation-core.identity-types.md) of the type of unlabeled
`F`-structures of order `n` captures this idea.

## Definitions

### Unlabeled structures of a species

<pre class="Agda"><a id="unlabeled-structure-species-types"></a><a id="1183" href="species.unlabeled-structures-species.html#1183" class="Function">unlabeled-structure-species-types</a> <a id="1217" class="Symbol">:</a>
  <a id="1221" class="Symbol">{</a><a id="1222" href="species.unlabeled-structures-species.html#1222" class="Bound">l1</a> <a id="1225" href="species.unlabeled-structures-species.html#1225" class="Bound">l2</a> <a id="1228" class="Symbol">:</a> <a id="1230" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1235" class="Symbol">}</a> <a id="1237" class="Symbol">(</a><a id="1238" href="species.unlabeled-structures-species.html#1238" class="Bound">F</a> <a id="1240" class="Symbol">:</a> <a id="1242" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1256" href="species.unlabeled-structures-species.html#1222" class="Bound">l1</a> <a id="1259" href="species.unlabeled-structures-species.html#1225" class="Bound">l2</a><a id="1261" class="Symbol">)</a> <a id="1263" class="Symbol">→</a> <a id="1265" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1267" class="Symbol">→</a> <a id="1269" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1272" class="Symbol">(</a><a id="1273" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1278" href="species.unlabeled-structures-species.html#1222" class="Bound">l1</a> <a id="1281" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1283" href="species.unlabeled-structures-species.html#1225" class="Bound">l2</a><a id="1285" class="Symbol">)</a>
<a id="1287" href="species.unlabeled-structures-species.html#1183" class="Function">unlabeled-structure-species-types</a> <a id="1321" class="Symbol">{</a><a id="1322" href="species.unlabeled-structures-species.html#1322" class="Bound">l1</a><a id="1324" class="Symbol">}</a> <a id="1326" class="Symbol">{</a><a id="1327" href="species.unlabeled-structures-species.html#1327" class="Bound">l2</a><a id="1329" class="Symbol">}</a> <a id="1331" href="species.unlabeled-structures-species.html#1331" class="Bound">F</a> <a id="1333" href="species.unlabeled-structures-species.html#1333" class="Bound">n</a> <a id="1335" class="Symbol">=</a>
  <a id="1339" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1341" class="Symbol">(</a> <a id="1343" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="1367" href="species.unlabeled-structures-species.html#1322" class="Bound">l1</a> <a id="1370" href="species.unlabeled-structures-species.html#1333" class="Bound">n</a><a id="1371" class="Symbol">)</a>
    <a id="1377" class="Symbol">(</a> <a id="1379" class="Symbol">λ</a> <a id="1381" href="species.unlabeled-structures-species.html#1381" class="Bound">X</a> <a id="1383" class="Symbol">→</a> <a id="1385" href="species.unlabeled-structures-species.html#1331" class="Bound">F</a> <a id="1387" class="Symbol">(</a><a id="1388" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1417" href="species.unlabeled-structures-species.html#1333" class="Bound">n</a> <a id="1419" href="species.unlabeled-structures-species.html#1381" class="Bound">X</a><a id="1420" class="Symbol">))</a>

<a id="1424" class="Keyword">module</a> <a id="1431" href="species.unlabeled-structures-species.html#1431" class="Module">_</a>
  <a id="1435" class="Symbol">{</a><a id="1436" href="species.unlabeled-structures-species.html#1436" class="Bound">l1</a> <a id="1439" href="species.unlabeled-structures-species.html#1439" class="Bound">l2</a> <a id="1442" class="Symbol">:</a> <a id="1444" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1449" class="Symbol">}</a> <a id="1451" class="Symbol">(</a><a id="1452" href="species.unlabeled-structures-species.html#1452" class="Bound">F</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1470" href="species.unlabeled-structures-species.html#1436" class="Bound">l1</a> <a id="1473" href="species.unlabeled-structures-species.html#1439" class="Bound">l2</a><a id="1475" class="Symbol">)</a> <a id="1477" class="Symbol">{</a><a id="1478" href="species.unlabeled-structures-species.html#1478" class="Bound">k</a> <a id="1480" class="Symbol">:</a> <a id="1482" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1483" class="Symbol">}</a>
  <a id="1487" class="Symbol">(</a><a id="1488" href="species.unlabeled-structures-species.html#1488" class="Bound">X</a> <a id="1490" class="Symbol">:</a> <a id="1492" href="species.unlabeled-structures-species.html#1183" class="Function">unlabeled-structure-species-types</a> <a id="1526" href="species.unlabeled-structures-species.html#1452" class="Bound">F</a> <a id="1528" href="species.unlabeled-structures-species.html#1478" class="Bound">k</a><a id="1529" class="Symbol">)</a>
  <a id="1533" class="Keyword">where</a>

  <a id="1542" href="species.unlabeled-structures-species.html#1542" class="Function">type-of-cardinality-unlabeled-structure-species-types</a> <a id="1596" class="Symbol">:</a>
    <a id="1602" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="1626" href="species.unlabeled-structures-species.html#1436" class="Bound">l1</a> <a id="1629" href="species.unlabeled-structures-species.html#1478" class="Bound">k</a>
  <a id="1633" href="species.unlabeled-structures-species.html#1542" class="Function">type-of-cardinality-unlabeled-structure-species-types</a> <a id="1687" class="Symbol">=</a> <a id="1689" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1693" href="species.unlabeled-structures-species.html#1488" class="Bound">X</a>

  <a id="1698" href="species.unlabeled-structures-species.html#1698" class="Function">type-unlabeled-structure-species-types</a> <a id="1737" class="Symbol">:</a> <a id="1739" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1742" href="species.unlabeled-structures-species.html#1436" class="Bound">l1</a>
  <a id="1747" href="species.unlabeled-structures-species.html#1698" class="Function">type-unlabeled-structure-species-types</a> <a id="1786" class="Symbol">=</a>
    <a id="1792" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1821" href="species.unlabeled-structures-species.html#1478" class="Bound">k</a>
      <a id="1829" href="species.unlabeled-structures-species.html#1542" class="Function">type-of-cardinality-unlabeled-structure-species-types</a>

  <a id="1886" href="species.unlabeled-structures-species.html#1886" class="Function">has-cardinality-type-unlabeled-structure-species-types</a> <a id="1941" class="Symbol">:</a>
    <a id="1947" href="univalent-combinatorics.finite-types.html#3146" class="Function">has-cardinality-ℕ</a> <a id="1965" href="species.unlabeled-structures-species.html#1478" class="Bound">k</a> <a id="1967" href="species.unlabeled-structures-species.html#1698" class="Function">type-unlabeled-structure-species-types</a>
  <a id="2008" href="species.unlabeled-structures-species.html#1886" class="Function">has-cardinality-type-unlabeled-structure-species-types</a> <a id="2063" class="Symbol">=</a>
    <a id="2069" href="univalent-combinatorics.finite-types.html#3581" class="Function">has-cardinality-type-Type-With-Cardinality-ℕ</a>
      <a id="2120" href="species.unlabeled-structures-species.html#1478" class="Bound">k</a>
      <a id="2128" href="species.unlabeled-structures-species.html#1542" class="Function">type-of-cardinality-unlabeled-structure-species-types</a>

  <a id="2185" href="species.unlabeled-structures-species.html#2185" class="Function">finite-type-unlabeled-structure-species-types</a> <a id="2231" class="Symbol">:</a> <a id="2233" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="2245" href="species.unlabeled-structures-species.html#1436" class="Bound">l1</a>
  <a id="2250" href="species.unlabeled-structures-species.html#2185" class="Function">finite-type-unlabeled-structure-species-types</a> <a id="2296" class="Symbol">=</a>
    <a id="2302" href="univalent-combinatorics.finite-types.html#8768" class="Function">finite-type-Type-With-Cardinality-ℕ</a> <a id="2338" href="species.unlabeled-structures-species.html#1478" class="Bound">k</a>
      <a id="2346" href="species.unlabeled-structures-species.html#1542" class="Function">type-of-cardinality-unlabeled-structure-species-types</a>

  <a id="2403" href="species.unlabeled-structures-species.html#2403" class="Function">structure-unlabeled-structure-species-types</a> <a id="2447" class="Symbol">:</a>
    <a id="2453" href="species.unlabeled-structures-species.html#1452" class="Bound">F</a> <a id="2455" href="species.unlabeled-structures-species.html#1698" class="Function">type-unlabeled-structure-species-types</a>
  <a id="2496" href="species.unlabeled-structures-species.html#2403" class="Function">structure-unlabeled-structure-species-types</a> <a id="2540" class="Symbol">=</a> <a id="2542" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2546" href="species.unlabeled-structures-species.html#1488" class="Bound">X</a>
</pre>
### Equivalences of unlabeled structures of a species

This remains to be defined.
[#741](https://github.com/UniMath/agda-unimath/issues/741)
