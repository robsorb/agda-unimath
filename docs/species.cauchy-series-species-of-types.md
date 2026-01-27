# Cauchy series of species of types

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="species.cauchy-series-species-of-types.html" class="Module">species.cauchy-series-species-of-types</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="195" class="Keyword">open</a> <a id="200" class="Keyword">import</a> <a id="207" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="foundation.postcomposition-functions.html" class="Module">foundation.postcomposition-functions</a>
<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="483" class="Keyword">open</a> <a id="488" class="Keyword">import</a> <a id="495" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

In classical mathematics, the _Cauchy series_ of a
[species](species.species-of-finite-types.md) (of
[finite types](univalent-combinatorics.finite-types.md)) `S` is the formal
series in `x`:

```text
  Σ (n : ℕ) (|S({1,...,n})| x^n / n!)
```

The categorified version of this series is:

```text
  Σ (F : Finite-Type), S(F) × (F → X).
```

Hence, we can generalize to
{{#concept "Cauchy series" Disambiguation="of species of types" Agda=cauchy-series-species-types}}
of any [species of types](species.species-of-types.md) `S` with the following
definition:

```text
  Σ (U : UU), S(U) × (U → X).
```

## Definition

<pre class="Agda"><a id="cauchy-series-species-types"></a><a id="1170" href="species.cauchy-series-species-of-types.html#1170" class="Function">cauchy-series-species-types</a> <a id="1198" class="Symbol">:</a>
  <a id="1202" class="Symbol">{</a><a id="1203" href="species.cauchy-series-species-of-types.html#1203" class="Bound">l1</a> <a id="1206" href="species.cauchy-series-species-of-types.html#1206" class="Bound">l2</a> <a id="1209" href="species.cauchy-series-species-of-types.html#1209" class="Bound">l3</a> <a id="1212" class="Symbol">:</a> <a id="1214" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1219" class="Symbol">}</a> <a id="1221" class="Symbol">→</a> <a id="1223" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1237" href="species.cauchy-series-species-of-types.html#1203" class="Bound">l1</a> <a id="1240" href="species.cauchy-series-species-of-types.html#1206" class="Bound">l2</a> <a id="1243" class="Symbol">→</a> <a id="1245" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1248" href="species.cauchy-series-species-of-types.html#1209" class="Bound">l3</a> <a id="1251" class="Symbol">→</a> <a id="1253" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1256" class="Symbol">(</a><a id="1257" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1262" href="species.cauchy-series-species-of-types.html#1203" class="Bound">l1</a> <a id="1265" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1267" href="species.cauchy-series-species-of-types.html#1206" class="Bound">l2</a> <a id="1270" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1272" href="species.cauchy-series-species-of-types.html#1209" class="Bound">l3</a><a id="1274" class="Symbol">)</a>
<a id="1276" href="species.cauchy-series-species-of-types.html#1170" class="Function">cauchy-series-species-types</a> <a id="1304" class="Symbol">{</a><a id="1305" href="species.cauchy-series-species-of-types.html#1305" class="Bound">l1</a><a id="1307" class="Symbol">}</a> <a id="1309" href="species.cauchy-series-species-of-types.html#1309" class="Bound">S</a> <a id="1311" href="species.cauchy-series-species-of-types.html#1311" class="Bound">X</a> <a id="1313" class="Symbol">=</a> <a id="1315" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1317" class="Symbol">(</a><a id="1318" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1321" href="species.cauchy-series-species-of-types.html#1305" class="Bound">l1</a><a id="1323" class="Symbol">)</a> <a id="1325" class="Symbol">(λ</a> <a id="1328" href="species.cauchy-series-species-of-types.html#1328" class="Bound">U</a> <a id="1330" class="Symbol">→</a> <a id="1332" href="species.cauchy-series-species-of-types.html#1309" class="Bound">S</a> <a id="1334" href="species.cauchy-series-species-of-types.html#1328" class="Bound">U</a> <a id="1336" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1338" class="Symbol">(</a><a id="1339" href="species.cauchy-series-species-of-types.html#1328" class="Bound">U</a> <a id="1341" class="Symbol">→</a> <a id="1343" href="species.cauchy-series-species-of-types.html#1311" class="Bound">X</a><a id="1344" class="Symbol">))</a>
</pre>
## Properties

### Equivalent species of types have equivalent Cauchy series

<pre class="Agda"><a id="1438" class="Keyword">module</a> <a id="1445" href="species.cauchy-series-species-of-types.html#1445" class="Module">_</a>
  <a id="1449" class="Symbol">{</a><a id="1450" href="species.cauchy-series-species-of-types.html#1450" class="Bound">l1</a> <a id="1453" href="species.cauchy-series-species-of-types.html#1453" class="Bound">l2</a> <a id="1456" href="species.cauchy-series-species-of-types.html#1456" class="Bound">l3</a> <a id="1459" href="species.cauchy-series-species-of-types.html#1459" class="Bound">l4</a> <a id="1462" class="Symbol">:</a> <a id="1464" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1469" class="Symbol">}</a>
  <a id="1473" class="Symbol">(</a><a id="1474" href="species.cauchy-series-species-of-types.html#1474" class="Bound">S</a> <a id="1476" class="Symbol">:</a> <a id="1478" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1492" href="species.cauchy-series-species-of-types.html#1450" class="Bound">l1</a> <a id="1495" href="species.cauchy-series-species-of-types.html#1453" class="Bound">l2</a><a id="1497" class="Symbol">)</a>
  <a id="1501" class="Symbol">(</a><a id="1502" href="species.cauchy-series-species-of-types.html#1502" class="Bound">T</a> <a id="1504" class="Symbol">:</a> <a id="1506" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1520" href="species.cauchy-series-species-of-types.html#1450" class="Bound">l1</a> <a id="1523" href="species.cauchy-series-species-of-types.html#1456" class="Bound">l3</a><a id="1525" class="Symbol">)</a>
  <a id="1529" class="Symbol">(</a><a id="1530" href="species.cauchy-series-species-of-types.html#1530" class="Bound">f</a> <a id="1532" class="Symbol">:</a> <a id="1534" class="Symbol">(</a><a id="1535" href="species.cauchy-series-species-of-types.html#1535" class="Bound">F</a> <a id="1537" class="Symbol">:</a> <a id="1539" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1542" href="species.cauchy-series-species-of-types.html#1450" class="Bound">l1</a><a id="1544" class="Symbol">)</a> <a id="1546" class="Symbol">→</a> <a id="1548" class="Symbol">(</a><a id="1549" href="species.cauchy-series-species-of-types.html#1474" class="Bound">S</a> <a id="1551" href="species.cauchy-series-species-of-types.html#1535" class="Bound">F</a> <a id="1553" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1555" href="species.cauchy-series-species-of-types.html#1502" class="Bound">T</a> <a id="1557" href="species.cauchy-series-species-of-types.html#1535" class="Bound">F</a><a id="1558" class="Symbol">))</a>
  <a id="1563" class="Symbol">(</a><a id="1564" href="species.cauchy-series-species-of-types.html#1564" class="Bound">X</a> <a id="1566" class="Symbol">:</a> <a id="1568" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1571" href="species.cauchy-series-species-of-types.html#1459" class="Bound">l4</a><a id="1573" class="Symbol">)</a>
  <a id="1577" class="Keyword">where</a>

  <a id="1586" href="species.cauchy-series-species-of-types.html#1586" class="Function">equiv-cauchy-series-equiv-species-types</a> <a id="1626" class="Symbol">:</a>
    <a id="1632" href="species.cauchy-series-species-of-types.html#1170" class="Function">cauchy-series-species-types</a> <a id="1660" href="species.cauchy-series-species-of-types.html#1474" class="Bound">S</a> <a id="1662" href="species.cauchy-series-species-of-types.html#1564" class="Bound">X</a> <a id="1664" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1666" href="species.cauchy-series-species-of-types.html#1170" class="Function">cauchy-series-species-types</a> <a id="1694" href="species.cauchy-series-species-of-types.html#1502" class="Bound">T</a> <a id="1696" href="species.cauchy-series-species-of-types.html#1564" class="Bound">X</a>
  <a id="1700" href="species.cauchy-series-species-of-types.html#1586" class="Function">equiv-cauchy-series-equiv-species-types</a> <a id="1740" class="Symbol">=</a>
    <a id="1746" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a> <a id="1756" class="Symbol">(λ</a> <a id="1759" href="species.cauchy-series-species-of-types.html#1759" class="Bound">X</a> <a id="1761" class="Symbol">→</a> <a id="1763" href="foundation.functoriality-cartesian-product-types.html#5965" class="Function">equiv-product-left</a> <a id="1782" class="Symbol">(</a><a id="1783" href="species.cauchy-series-species-of-types.html#1530" class="Bound">f</a> <a id="1785" href="species.cauchy-series-species-of-types.html#1759" class="Bound">X</a><a id="1786" class="Symbol">))</a>
</pre>
### Cauchy series of types are equivalence invariant

<pre class="Agda"><a id="1856" class="Keyword">module</a> <a id="1863" href="species.cauchy-series-species-of-types.html#1863" class="Module">_</a>
  <a id="1867" class="Symbol">{</a><a id="1868" href="species.cauchy-series-species-of-types.html#1868" class="Bound">l1</a> <a id="1871" href="species.cauchy-series-species-of-types.html#1871" class="Bound">l2</a> <a id="1874" href="species.cauchy-series-species-of-types.html#1874" class="Bound">l3</a> <a id="1877" href="species.cauchy-series-species-of-types.html#1877" class="Bound">l4</a> <a id="1880" class="Symbol">:</a> <a id="1882" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1887" class="Symbol">}</a>
  <a id="1891" class="Symbol">(</a><a id="1892" href="species.cauchy-series-species-of-types.html#1892" class="Bound">S</a> <a id="1894" class="Symbol">:</a> <a id="1896" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1910" href="species.cauchy-series-species-of-types.html#1868" class="Bound">l1</a> <a id="1913" href="species.cauchy-series-species-of-types.html#1871" class="Bound">l2</a><a id="1915" class="Symbol">)</a>
  <a id="1919" class="Symbol">{</a><a id="1920" href="species.cauchy-series-species-of-types.html#1920" class="Bound">X</a> <a id="1922" class="Symbol">:</a> <a id="1924" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1927" href="species.cauchy-series-species-of-types.html#1874" class="Bound">l3</a><a id="1929" class="Symbol">}</a> <a id="1931" class="Symbol">{</a><a id="1932" href="species.cauchy-series-species-of-types.html#1932" class="Bound">Y</a> <a id="1934" class="Symbol">:</a> <a id="1936" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1939" href="species.cauchy-series-species-of-types.html#1877" class="Bound">l4</a><a id="1941" class="Symbol">}</a>
  <a id="1945" class="Symbol">(</a><a id="1946" href="species.cauchy-series-species-of-types.html#1946" class="Bound">e</a> <a id="1948" class="Symbol">:</a> <a id="1950" href="species.cauchy-series-species-of-types.html#1920" class="Bound">X</a> <a id="1952" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1954" href="species.cauchy-series-species-of-types.html#1932" class="Bound">Y</a><a id="1955" class="Symbol">)</a>
  <a id="1959" class="Keyword">where</a>

  <a id="1968" href="species.cauchy-series-species-of-types.html#1968" class="Function">equiv-cauchy-series-species-types</a> <a id="2002" class="Symbol">:</a>
    <a id="2008" href="species.cauchy-series-species-of-types.html#1170" class="Function">cauchy-series-species-types</a> <a id="2036" href="species.cauchy-series-species-of-types.html#1892" class="Bound">S</a> <a id="2038" href="species.cauchy-series-species-of-types.html#1920" class="Bound">X</a> <a id="2040" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2042" href="species.cauchy-series-species-of-types.html#1170" class="Function">cauchy-series-species-types</a> <a id="2070" href="species.cauchy-series-species-of-types.html#1892" class="Bound">S</a> <a id="2072" href="species.cauchy-series-species-of-types.html#1932" class="Bound">Y</a>
  <a id="2076" href="species.cauchy-series-species-of-types.html#1968" class="Function">equiv-cauchy-series-species-types</a> <a id="2110" class="Symbol">=</a>
    <a id="2116" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a> <a id="2126" class="Symbol">(λ</a> <a id="2129" href="species.cauchy-series-species-of-types.html#2129" class="Bound">F</a> <a id="2131" class="Symbol">→</a> <a id="2133" href="foundation.functoriality-cartesian-product-types.html#6061" class="Function">equiv-product-right</a> <a id="2153" class="Symbol">(</a><a id="2154" href="foundation.postcomposition-functions.html#6729" class="Function">equiv-postcomp</a> <a id="2169" href="species.cauchy-series-species-of-types.html#2129" class="Bound">F</a> <a id="2171" href="species.cauchy-series-species-of-types.html#1946" class="Bound">e</a><a id="2172" class="Symbol">))</a>
</pre>