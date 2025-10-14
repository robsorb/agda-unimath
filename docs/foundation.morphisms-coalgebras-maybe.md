# Morphisms of coalgebras of the maybe monad

<pre class="Agda"><a id="55" class="Keyword">module</a> <a id="62" href="foundation.morphisms-coalgebras-maybe.html" class="Module">foundation.morphisms-coalgebras-maybe</a> <a id="100" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="foundation.coalgebras-maybe.html" class="Module">foundation.coalgebras-maybe</a>
<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="318" class="Keyword">open</a> <a id="323" class="Keyword">import</a> <a id="330" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="358" class="Keyword">open</a> <a id="363" class="Keyword">import</a> <a id="370" href="trees.polynomial-endofunctors.html" class="Module">trees.polynomial-endofunctors</a>
</pre>
</details>

## Idea

Given two [coalgebras](foundation.coalgebras-maybe.md) of the
[maybe monad](foundation.maybe.md) `η : X → Maybe X`, `η' : Y → Maybe Y`, then a
map `f : X → Y` is a
{{#concept "morphism of coalgebras" Disambiguation="of the maybe monad" Agda=hom-coalgebra-Maybe}}
if the square

```text
            f
     X ----------> Y
     |             |
     |             |
     ∨             ∨
  Maybe X ----> Maybe Y
         Maybe f
```

[commutes](foundation.commuting-squares-of-maps.md).

## Definitions

<pre class="Agda"><a id="coherence-hom-coalgebra-Maybe"></a><a id="934" href="foundation.morphisms-coalgebras-maybe.html#934" class="Function">coherence-hom-coalgebra-Maybe</a> <a id="964" class="Symbol">:</a>
  <a id="968" class="Symbol">{</a><a id="969" href="foundation.morphisms-coalgebras-maybe.html#969" class="Bound">l1</a> <a id="972" href="foundation.morphisms-coalgebras-maybe.html#972" class="Bound">l2</a> <a id="975" class="Symbol">:</a> <a id="977" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="982" class="Symbol">}</a> <a id="984" class="Symbol">(</a><a id="985" href="foundation.morphisms-coalgebras-maybe.html#985" class="Bound">X</a> <a id="987" class="Symbol">:</a> <a id="989" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1005" href="foundation.morphisms-coalgebras-maybe.html#969" class="Bound">l1</a><a id="1007" class="Symbol">)</a> <a id="1009" class="Symbol">(</a><a id="1010" href="foundation.morphisms-coalgebras-maybe.html#1010" class="Bound">Y</a> <a id="1012" class="Symbol">:</a> <a id="1014" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1030" href="foundation.morphisms-coalgebras-maybe.html#972" class="Bound">l2</a><a id="1032" class="Symbol">)</a> <a id="1034" class="Symbol">→</a>
  <a id="1038" class="Symbol">(</a><a id="1039" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="1060" href="foundation.morphisms-coalgebras-maybe.html#985" class="Bound">X</a> <a id="1062" class="Symbol">→</a> <a id="1064" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="1085" href="foundation.morphisms-coalgebras-maybe.html#1010" class="Bound">Y</a><a id="1086" class="Symbol">)</a> <a id="1088" class="Symbol">→</a> <a id="1090" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1093" class="Symbol">(</a><a id="1094" href="foundation.morphisms-coalgebras-maybe.html#969" class="Bound">l1</a> <a id="1097" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1099" href="foundation.morphisms-coalgebras-maybe.html#972" class="Bound">l2</a><a id="1101" class="Symbol">)</a>
<a id="1103" href="foundation.morphisms-coalgebras-maybe.html#934" class="Function">coherence-hom-coalgebra-Maybe</a> <a id="1133" href="foundation.morphisms-coalgebras-maybe.html#1133" class="Bound">X</a> <a id="1135" href="foundation.morphisms-coalgebras-maybe.html#1135" class="Bound">Y</a> <a id="1137" href="foundation.morphisms-coalgebras-maybe.html#1137" class="Bound">f</a> <a id="1139" class="Symbol">=</a>
  <a id="1143" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
    <a id="1169" class="Symbol">(</a> <a id="1171" href="foundation.morphisms-coalgebras-maybe.html#1137" class="Bound">f</a><a id="1172" class="Symbol">)</a>
    <a id="1178" class="Symbol">(</a> <a id="1180" href="foundation.coalgebras-maybe.html#906" class="Function">map-coalgebra-Maybe</a> <a id="1200" href="foundation.morphisms-coalgebras-maybe.html#1133" class="Bound">X</a><a id="1201" class="Symbol">)</a>
    <a id="1207" class="Symbol">(</a> <a id="1209" href="foundation.coalgebras-maybe.html#906" class="Function">map-coalgebra-Maybe</a> <a id="1229" href="foundation.morphisms-coalgebras-maybe.html#1135" class="Bound">Y</a><a id="1230" class="Symbol">)</a>
    <a id="1236" class="Symbol">(</a> <a id="1238" href="foundation.maybe.html#1946" class="Function">map-Maybe</a> <a id="1248" href="foundation.morphisms-coalgebras-maybe.html#1137" class="Bound">f</a><a id="1249" class="Symbol">)</a>

<a id="hom-coalgebra-Maybe"></a><a id="1252" href="foundation.morphisms-coalgebras-maybe.html#1252" class="Function">hom-coalgebra-Maybe</a> <a id="1272" class="Symbol">:</a>
  <a id="1276" class="Symbol">{</a><a id="1277" href="foundation.morphisms-coalgebras-maybe.html#1277" class="Bound">l1</a> <a id="1280" href="foundation.morphisms-coalgebras-maybe.html#1280" class="Bound">l2</a> <a id="1283" class="Symbol">:</a> <a id="1285" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1290" class="Symbol">}</a> <a id="1292" class="Symbol">(</a><a id="1293" href="foundation.morphisms-coalgebras-maybe.html#1293" class="Bound">X</a> <a id="1295" class="Symbol">:</a> <a id="1297" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1313" href="foundation.morphisms-coalgebras-maybe.html#1277" class="Bound">l1</a><a id="1315" class="Symbol">)</a> <a id="1317" class="Symbol">(</a><a id="1318" href="foundation.morphisms-coalgebras-maybe.html#1318" class="Bound">Y</a> <a id="1320" class="Symbol">:</a> <a id="1322" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1338" href="foundation.morphisms-coalgebras-maybe.html#1280" class="Bound">l2</a><a id="1340" class="Symbol">)</a> <a id="1342" class="Symbol">→</a>
  <a id="1346" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1349" class="Symbol">(</a><a id="1350" href="foundation.morphisms-coalgebras-maybe.html#1277" class="Bound">l1</a> <a id="1353" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1355" href="foundation.morphisms-coalgebras-maybe.html#1280" class="Bound">l2</a><a id="1357" class="Symbol">)</a>
<a id="1359" href="foundation.morphisms-coalgebras-maybe.html#1252" class="Function">hom-coalgebra-Maybe</a> <a id="1379" href="foundation.morphisms-coalgebras-maybe.html#1379" class="Bound">X</a> <a id="1381" href="foundation.morphisms-coalgebras-maybe.html#1381" class="Bound">Y</a> <a id="1383" class="Symbol">=</a>
  <a id="1387" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1389" class="Symbol">(</a> <a id="1391" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="1412" href="foundation.morphisms-coalgebras-maybe.html#1379" class="Bound">X</a> <a id="1414" class="Symbol">→</a> <a id="1416" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="1437" href="foundation.morphisms-coalgebras-maybe.html#1381" class="Bound">Y</a><a id="1438" class="Symbol">)</a>
    <a id="1444" class="Symbol">(</a> <a id="1446" href="foundation.morphisms-coalgebras-maybe.html#934" class="Function">coherence-hom-coalgebra-Maybe</a> <a id="1476" href="foundation.morphisms-coalgebras-maybe.html#1379" class="Bound">X</a> <a id="1478" href="foundation.morphisms-coalgebras-maybe.html#1381" class="Bound">Y</a><a id="1479" class="Symbol">)</a>

<a id="1482" class="Keyword">module</a> <a id="1489" href="foundation.morphisms-coalgebras-maybe.html#1489" class="Module">_</a>
  <a id="1493" class="Symbol">{</a><a id="1494" href="foundation.morphisms-coalgebras-maybe.html#1494" class="Bound">l1</a> <a id="1497" href="foundation.morphisms-coalgebras-maybe.html#1497" class="Bound">l2</a> <a id="1500" class="Symbol">:</a> <a id="1502" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1507" class="Symbol">}</a> <a id="1509" class="Symbol">(</a><a id="1510" href="foundation.morphisms-coalgebras-maybe.html#1510" class="Bound">X</a> <a id="1512" class="Symbol">:</a> <a id="1514" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1530" href="foundation.morphisms-coalgebras-maybe.html#1494" class="Bound">l1</a><a id="1532" class="Symbol">)</a> <a id="1534" class="Symbol">(</a><a id="1535" href="foundation.morphisms-coalgebras-maybe.html#1535" class="Bound">Y</a> <a id="1537" class="Symbol">:</a> <a id="1539" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1555" href="foundation.morphisms-coalgebras-maybe.html#1497" class="Bound">l2</a><a id="1557" class="Symbol">)</a>
  <a id="1561" class="Symbol">(</a><a id="1562" href="foundation.morphisms-coalgebras-maybe.html#1562" class="Bound">f</a> <a id="1564" class="Symbol">:</a> <a id="1566" href="foundation.morphisms-coalgebras-maybe.html#1252" class="Function">hom-coalgebra-Maybe</a> <a id="1586" href="foundation.morphisms-coalgebras-maybe.html#1510" class="Bound">X</a> <a id="1588" href="foundation.morphisms-coalgebras-maybe.html#1535" class="Bound">Y</a><a id="1589" class="Symbol">)</a>
  <a id="1593" class="Keyword">where</a>

  <a id="1602" href="foundation.morphisms-coalgebras-maybe.html#1602" class="Function">map-hom-coalgebra-Maybe</a> <a id="1626" class="Symbol">:</a> <a id="1628" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="1649" href="foundation.morphisms-coalgebras-maybe.html#1510" class="Bound">X</a> <a id="1651" class="Symbol">→</a> <a id="1653" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="1674" href="foundation.morphisms-coalgebras-maybe.html#1535" class="Bound">Y</a>
  <a id="1678" href="foundation.morphisms-coalgebras-maybe.html#1602" class="Function">map-hom-coalgebra-Maybe</a> <a id="1702" class="Symbol">=</a> <a id="1704" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1708" href="foundation.morphisms-coalgebras-maybe.html#1562" class="Bound">f</a>

  <a id="1713" href="foundation.morphisms-coalgebras-maybe.html#1713" class="Function">coh-hom-coalgebra-Maybe</a> <a id="1737" class="Symbol">:</a>
    <a id="1743" href="foundation.morphisms-coalgebras-maybe.html#934" class="Function">coherence-hom-coalgebra-Maybe</a> <a id="1773" href="foundation.morphisms-coalgebras-maybe.html#1510" class="Bound">X</a> <a id="1775" href="foundation.morphisms-coalgebras-maybe.html#1535" class="Bound">Y</a> <a id="1777" href="foundation.morphisms-coalgebras-maybe.html#1602" class="Function">map-hom-coalgebra-Maybe</a>
  <a id="1803" href="foundation.morphisms-coalgebras-maybe.html#1713" class="Function">coh-hom-coalgebra-Maybe</a> <a id="1827" class="Symbol">=</a> <a id="1829" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1833" href="foundation.morphisms-coalgebras-maybe.html#1562" class="Bound">f</a>
</pre>