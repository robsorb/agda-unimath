# Binary relations with lifts

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="foundation.binary-relations-with-lifts.html" class="Module">foundation.binary-relations-with-lifts</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.iterated-dependent-product-types.html" class="Module">foundation.iterated-dependent-product-types</a>
<a id="282" class="Keyword">open</a> <a id="287" class="Keyword">import</a> <a id="294" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

We say a [relation](foundation.binary-relations.md) `R`
{{#concept "has lifts" Disambiguation="binary relations of types" Agda=has-lifts-Relation}}
if for every triple `x y z : A`, there is a binary operation

```text
  R x z → R y z → R x y.
```

Relations with lifts are closely related to transitive relations. But, instead
of giving for every diagram

```text
       y
      ∧ \
     /   \
    /     ∨
  x        z
```

a horizontal arrow `x → z`, a binary relation with lifts gives, for every cospan

```text
       y
        \
         \
          ∨
  x -----> z,
```

a _lift_ `x → y`. By symmetry it also gives a lift in the opposite direction
`y → x`.

Dually, a relation `R`
[has extensions](foundation.binary-relations-with-extensions.md) if for every
triple `x y z : A`, there is a binary operation

```text
  R x y → R x z → R y z.
```

## Definition

### The structure on relations of having lifts

<pre class="Agda"><a id="1310" class="Keyword">module</a> <a id="1317" href="foundation.binary-relations-with-lifts.html#1317" class="Module">_</a>
  <a id="1321" class="Symbol">{</a><a id="1322" href="foundation.binary-relations-with-lifts.html#1322" class="Bound">l1</a> <a id="1325" href="foundation.binary-relations-with-lifts.html#1325" class="Bound">l2</a> <a id="1328" class="Symbol">:</a> <a id="1330" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1335" class="Symbol">}</a> <a id="1337" class="Symbol">{</a><a id="1338" href="foundation.binary-relations-with-lifts.html#1338" class="Bound">A</a> <a id="1340" class="Symbol">:</a> <a id="1342" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1345" href="foundation.binary-relations-with-lifts.html#1322" class="Bound">l1</a><a id="1347" class="Symbol">}</a> <a id="1349" class="Symbol">(</a><a id="1350" href="foundation.binary-relations-with-lifts.html#1350" class="Bound">R</a> <a id="1352" class="Symbol">:</a> <a id="1354" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1363" href="foundation.binary-relations-with-lifts.html#1325" class="Bound">l2</a> <a id="1366" href="foundation.binary-relations-with-lifts.html#1338" class="Bound">A</a><a id="1367" class="Symbol">)</a>
  <a id="1371" class="Keyword">where</a>

  <a id="1380" href="foundation.binary-relations-with-lifts.html#1380" class="Function">has-lifts-Relation</a> <a id="1399" class="Symbol">:</a> <a id="1401" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1404" class="Symbol">(</a><a id="1405" href="foundation.binary-relations-with-lifts.html#1322" class="Bound">l1</a> <a id="1408" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1410" href="foundation.binary-relations-with-lifts.html#1325" class="Bound">l2</a><a id="1412" class="Symbol">)</a>
  <a id="1416" href="foundation.binary-relations-with-lifts.html#1380" class="Function">has-lifts-Relation</a> <a id="1435" class="Symbol">=</a> <a id="1437" class="Symbol">{</a><a id="1438" href="foundation.binary-relations-with-lifts.html#1438" class="Bound">x</a> <a id="1440" href="foundation.binary-relations-with-lifts.html#1440" class="Bound">y</a> <a id="1442" href="foundation.binary-relations-with-lifts.html#1442" class="Bound">z</a> <a id="1444" class="Symbol">:</a> <a id="1446" href="foundation.binary-relations-with-lifts.html#1338" class="Bound">A</a><a id="1447" class="Symbol">}</a> <a id="1449" class="Symbol">→</a> <a id="1451" href="foundation.binary-relations-with-lifts.html#1350" class="Bound">R</a> <a id="1453" href="foundation.binary-relations-with-lifts.html#1438" class="Bound">x</a> <a id="1455" href="foundation.binary-relations-with-lifts.html#1442" class="Bound">z</a> <a id="1457" class="Symbol">→</a> <a id="1459" href="foundation.binary-relations-with-lifts.html#1350" class="Bound">R</a> <a id="1461" href="foundation.binary-relations-with-lifts.html#1440" class="Bound">y</a> <a id="1463" href="foundation.binary-relations-with-lifts.html#1442" class="Bound">z</a> <a id="1465" class="Symbol">→</a> <a id="1467" href="foundation.binary-relations-with-lifts.html#1350" class="Bound">R</a> <a id="1469" href="foundation.binary-relations-with-lifts.html#1438" class="Bound">x</a> <a id="1471" href="foundation.binary-relations-with-lifts.html#1440" class="Bound">y</a>
</pre>
## Properties

### If `x` relates to an element and the relation has lifts, then `x` relates to `x`

<pre class="Agda"><a id="1587" class="Keyword">module</a> <a id="1594" href="foundation.binary-relations-with-lifts.html#1594" class="Module">_</a>
  <a id="1598" class="Symbol">{</a><a id="1599" href="foundation.binary-relations-with-lifts.html#1599" class="Bound">l1</a> <a id="1602" href="foundation.binary-relations-with-lifts.html#1602" class="Bound">l2</a> <a id="1605" class="Symbol">:</a> <a id="1607" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1612" class="Symbol">}</a> <a id="1614" class="Symbol">{</a><a id="1615" href="foundation.binary-relations-with-lifts.html#1615" class="Bound">A</a> <a id="1617" class="Symbol">:</a> <a id="1619" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1622" href="foundation.binary-relations-with-lifts.html#1599" class="Bound">l1</a><a id="1624" class="Symbol">}</a> <a id="1626" class="Symbol">(</a><a id="1627" href="foundation.binary-relations-with-lifts.html#1627" class="Bound">R</a> <a id="1629" class="Symbol">:</a> <a id="1631" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1640" href="foundation.binary-relations-with-lifts.html#1602" class="Bound">l2</a> <a id="1643" href="foundation.binary-relations-with-lifts.html#1615" class="Bound">A</a><a id="1644" class="Symbol">)</a>
  <a id="1648" class="Keyword">where</a>

  <a id="1657" href="foundation.binary-relations-with-lifts.html#1657" class="Function">rel-self-rel-any-has-lifts-Relation</a> <a id="1693" class="Symbol">:</a>
    <a id="1699" href="foundation.binary-relations-with-lifts.html#1380" class="Function">has-lifts-Relation</a> <a id="1718" href="foundation.binary-relations-with-lifts.html#1627" class="Bound">R</a> <a id="1720" class="Symbol">→</a> <a id="1722" class="Symbol">{</a><a id="1723" href="foundation.binary-relations-with-lifts.html#1723" class="Bound">x</a> <a id="1725" href="foundation.binary-relations-with-lifts.html#1725" class="Bound">y</a> <a id="1727" class="Symbol">:</a> <a id="1729" href="foundation.binary-relations-with-lifts.html#1615" class="Bound">A</a><a id="1730" class="Symbol">}</a> <a id="1732" class="Symbol">→</a> <a id="1734" href="foundation.binary-relations-with-lifts.html#1627" class="Bound">R</a> <a id="1736" href="foundation.binary-relations-with-lifts.html#1723" class="Bound">x</a> <a id="1738" href="foundation.binary-relations-with-lifts.html#1725" class="Bound">y</a> <a id="1740" class="Symbol">→</a> <a id="1742" href="foundation.binary-relations-with-lifts.html#1627" class="Bound">R</a> <a id="1744" href="foundation.binary-relations-with-lifts.html#1723" class="Bound">x</a> <a id="1746" href="foundation.binary-relations-with-lifts.html#1723" class="Bound">x</a>
  <a id="1750" href="foundation.binary-relations-with-lifts.html#1657" class="Function">rel-self-rel-any-has-lifts-Relation</a> <a id="1786" href="foundation.binary-relations-with-lifts.html#1786" class="Bound">H</a> <a id="1788" href="foundation.binary-relations-with-lifts.html#1788" class="Bound">p</a> <a id="1790" class="Symbol">=</a> <a id="1792" href="foundation.binary-relations-with-lifts.html#1786" class="Bound">H</a> <a id="1794" href="foundation.binary-relations-with-lifts.html#1788" class="Bound">p</a> <a id="1796" href="foundation.binary-relations-with-lifts.html#1788" class="Bound">p</a>
</pre>
### The reverse of a lift

<pre class="Agda"><a id="1838" class="Keyword">module</a> <a id="1845" href="foundation.binary-relations-with-lifts.html#1845" class="Module">_</a>
  <a id="1849" class="Symbol">{</a><a id="1850" href="foundation.binary-relations-with-lifts.html#1850" class="Bound">l1</a> <a id="1853" href="foundation.binary-relations-with-lifts.html#1853" class="Bound">l2</a> <a id="1856" class="Symbol">:</a> <a id="1858" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1863" class="Symbol">}</a> <a id="1865" class="Symbol">{</a><a id="1866" href="foundation.binary-relations-with-lifts.html#1866" class="Bound">A</a> <a id="1868" class="Symbol">:</a> <a id="1870" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1873" href="foundation.binary-relations-with-lifts.html#1850" class="Bound">l1</a><a id="1875" class="Symbol">}</a> <a id="1877" class="Symbol">(</a><a id="1878" href="foundation.binary-relations-with-lifts.html#1878" class="Bound">R</a> <a id="1880" class="Symbol">:</a> <a id="1882" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1891" href="foundation.binary-relations-with-lifts.html#1853" class="Bound">l2</a> <a id="1894" href="foundation.binary-relations-with-lifts.html#1866" class="Bound">A</a><a id="1895" class="Symbol">)</a>
  <a id="1899" class="Keyword">where</a>

  <a id="1908" href="foundation.binary-relations-with-lifts.html#1908" class="Function">reverse-has-lifts-Relation</a> <a id="1935" class="Symbol">:</a>
    <a id="1941" href="foundation.binary-relations-with-lifts.html#1380" class="Function">has-lifts-Relation</a> <a id="1960" href="foundation.binary-relations-with-lifts.html#1878" class="Bound">R</a> <a id="1962" class="Symbol">→</a> <a id="1964" class="Symbol">{</a><a id="1965" href="foundation.binary-relations-with-lifts.html#1965" class="Bound">x</a> <a id="1967" href="foundation.binary-relations-with-lifts.html#1967" class="Bound">y</a> <a id="1969" href="foundation.binary-relations-with-lifts.html#1969" class="Bound">z</a> <a id="1971" class="Symbol">:</a> <a id="1973" href="foundation.binary-relations-with-lifts.html#1866" class="Bound">A</a><a id="1974" class="Symbol">}</a> <a id="1976" class="Symbol">→</a> <a id="1978" href="foundation.binary-relations-with-lifts.html#1878" class="Bound">R</a> <a id="1980" href="foundation.binary-relations-with-lifts.html#1965" class="Bound">x</a> <a id="1982" href="foundation.binary-relations-with-lifts.html#1969" class="Bound">z</a> <a id="1984" class="Symbol">→</a> <a id="1986" href="foundation.binary-relations-with-lifts.html#1878" class="Bound">R</a> <a id="1988" href="foundation.binary-relations-with-lifts.html#1967" class="Bound">y</a> <a id="1990" href="foundation.binary-relations-with-lifts.html#1969" class="Bound">z</a> <a id="1992" class="Symbol">→</a> <a id="1994" href="foundation.binary-relations-with-lifts.html#1878" class="Bound">R</a> <a id="1996" href="foundation.binary-relations-with-lifts.html#1967" class="Bound">y</a> <a id="1998" href="foundation.binary-relations-with-lifts.html#1965" class="Bound">x</a>
  <a id="2002" href="foundation.binary-relations-with-lifts.html#1908" class="Function">reverse-has-lifts-Relation</a> <a id="2029" href="foundation.binary-relations-with-lifts.html#2029" class="Bound">H</a> <a id="2031" href="foundation.binary-relations-with-lifts.html#2031" class="Bound">p</a> <a id="2033" href="foundation.binary-relations-with-lifts.html#2033" class="Bound">q</a> <a id="2035" class="Symbol">=</a> <a id="2037" href="foundation.binary-relations-with-lifts.html#2029" class="Bound">H</a> <a id="2039" href="foundation.binary-relations-with-lifts.html#2033" class="Bound">q</a> <a id="2041" href="foundation.binary-relations-with-lifts.html#2031" class="Bound">p</a>
</pre>
### Reflexive relations with lifts are symmetric

<pre class="Agda"><a id="2106" class="Keyword">module</a> <a id="2113" href="foundation.binary-relations-with-lifts.html#2113" class="Module">_</a>
  <a id="2117" class="Symbol">{</a><a id="2118" href="foundation.binary-relations-with-lifts.html#2118" class="Bound">l1</a> <a id="2121" href="foundation.binary-relations-with-lifts.html#2121" class="Bound">l2</a> <a id="2124" class="Symbol">:</a> <a id="2126" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2131" class="Symbol">}</a> <a id="2133" class="Symbol">{</a><a id="2134" href="foundation.binary-relations-with-lifts.html#2134" class="Bound">A</a> <a id="2136" class="Symbol">:</a> <a id="2138" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2141" href="foundation.binary-relations-with-lifts.html#2118" class="Bound">l1</a><a id="2143" class="Symbol">}</a> <a id="2145" class="Symbol">(</a><a id="2146" href="foundation.binary-relations-with-lifts.html#2146" class="Bound">R</a> <a id="2148" class="Symbol">:</a> <a id="2150" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="2159" href="foundation.binary-relations-with-lifts.html#2121" class="Bound">l2</a> <a id="2162" href="foundation.binary-relations-with-lifts.html#2134" class="Bound">A</a><a id="2163" class="Symbol">)</a>
  <a id="2167" class="Symbol">(</a><a id="2168" href="foundation.binary-relations-with-lifts.html#2168" class="Bound">H</a> <a id="2170" class="Symbol">:</a> <a id="2172" href="foundation.binary-relations-with-lifts.html#1380" class="Function">has-lifts-Relation</a> <a id="2191" href="foundation.binary-relations-with-lifts.html#2146" class="Bound">R</a><a id="2192" class="Symbol">)</a>
  <a id="2196" class="Keyword">where</a>

  <a id="2205" href="foundation.binary-relations-with-lifts.html#2205" class="Function">is-symmetric-is-reflexive-has-lifts-Relation</a> <a id="2250" class="Symbol">:</a>
    <a id="2256" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="2269" href="foundation.binary-relations-with-lifts.html#2146" class="Bound">R</a> <a id="2271" class="Symbol">→</a> <a id="2273" href="foundation.binary-relations.html#3402" class="Function">is-symmetric</a> <a id="2286" href="foundation.binary-relations-with-lifts.html#2146" class="Bound">R</a>
  <a id="2290" href="foundation.binary-relations-with-lifts.html#2205" class="Function">is-symmetric-is-reflexive-has-lifts-Relation</a> <a id="2335" href="foundation.binary-relations-with-lifts.html#2335" class="Bound">r</a> <a id="2337" href="foundation.binary-relations-with-lifts.html#2337" class="Bound">x</a> <a id="2339" href="foundation.binary-relations-with-lifts.html#2339" class="Bound">y</a> <a id="2341" href="foundation.binary-relations-with-lifts.html#2341" class="Bound">p</a> <a id="2343" class="Symbol">=</a> <a id="2345" href="foundation.binary-relations-with-lifts.html#2168" class="Bound">H</a> <a id="2347" class="Symbol">(</a><a id="2348" href="foundation.binary-relations-with-lifts.html#2335" class="Bound">r</a> <a id="2350" href="foundation.binary-relations-with-lifts.html#2339" class="Bound">y</a><a id="2351" class="Symbol">)</a> <a id="2353" href="foundation.binary-relations-with-lifts.html#2341" class="Bound">p</a>
</pre>
### Reflexive relations with lifts are transitive

<pre class="Agda"><a id="2419" class="Keyword">module</a> <a id="2426" href="foundation.binary-relations-with-lifts.html#2426" class="Module">_</a>
  <a id="2430" class="Symbol">{</a><a id="2431" href="foundation.binary-relations-with-lifts.html#2431" class="Bound">l1</a> <a id="2434" href="foundation.binary-relations-with-lifts.html#2434" class="Bound">l2</a> <a id="2437" class="Symbol">:</a> <a id="2439" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2444" class="Symbol">}</a> <a id="2446" class="Symbol">{</a><a id="2447" href="foundation.binary-relations-with-lifts.html#2447" class="Bound">A</a> <a id="2449" class="Symbol">:</a> <a id="2451" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2454" href="foundation.binary-relations-with-lifts.html#2431" class="Bound">l1</a><a id="2456" class="Symbol">}</a> <a id="2458" class="Symbol">(</a><a id="2459" href="foundation.binary-relations-with-lifts.html#2459" class="Bound">R</a> <a id="2461" class="Symbol">:</a> <a id="2463" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="2472" href="foundation.binary-relations-with-lifts.html#2434" class="Bound">l2</a> <a id="2475" href="foundation.binary-relations-with-lifts.html#2447" class="Bound">A</a><a id="2476" class="Symbol">)</a>
  <a id="2480" class="Symbol">(</a><a id="2481" href="foundation.binary-relations-with-lifts.html#2481" class="Bound">H</a> <a id="2483" class="Symbol">:</a> <a id="2485" href="foundation.binary-relations-with-lifts.html#1380" class="Function">has-lifts-Relation</a> <a id="2504" href="foundation.binary-relations-with-lifts.html#2459" class="Bound">R</a><a id="2505" class="Symbol">)</a>
  <a id="2509" class="Keyword">where</a>

  <a id="2518" href="foundation.binary-relations-with-lifts.html#2518" class="Function">is-transitive-is-symmetric-has-lifts-Relation</a> <a id="2564" class="Symbol">:</a>
    <a id="2570" href="foundation.binary-relations.html#3402" class="Function">is-symmetric</a> <a id="2583" href="foundation.binary-relations-with-lifts.html#2459" class="Bound">R</a> <a id="2585" class="Symbol">→</a> <a id="2587" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2601" href="foundation.binary-relations-with-lifts.html#2459" class="Bound">R</a>
  <a id="2605" href="foundation.binary-relations-with-lifts.html#2518" class="Function">is-transitive-is-symmetric-has-lifts-Relation</a> <a id="2651" href="foundation.binary-relations-with-lifts.html#2651" class="Bound">s</a> <a id="2653" href="foundation.binary-relations-with-lifts.html#2653" class="Bound">x</a> <a id="2655" href="foundation.binary-relations-with-lifts.html#2655" class="Bound">y</a> <a id="2657" href="foundation.binary-relations-with-lifts.html#2657" class="Bound">z</a> <a id="2659" href="foundation.binary-relations-with-lifts.html#2659" class="Bound">p</a> <a id="2661" href="foundation.binary-relations-with-lifts.html#2661" class="Bound">q</a> <a id="2663" class="Symbol">=</a> <a id="2665" href="foundation.binary-relations-with-lifts.html#2481" class="Bound">H</a> <a id="2667" href="foundation.binary-relations-with-lifts.html#2661" class="Bound">q</a> <a id="2669" class="Symbol">(</a><a id="2670" href="foundation.binary-relations-with-lifts.html#2651" class="Bound">s</a> <a id="2672" href="foundation.binary-relations-with-lifts.html#2655" class="Bound">y</a> <a id="2674" href="foundation.binary-relations-with-lifts.html#2657" class="Bound">z</a> <a id="2676" href="foundation.binary-relations-with-lifts.html#2659" class="Bound">p</a><a id="2677" class="Symbol">)</a>

  <a id="2682" href="foundation.binary-relations-with-lifts.html#2682" class="Function">is-transitive-is-reflexive-has-lifts-Relation</a> <a id="2728" class="Symbol">:</a>
    <a id="2734" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="2747" href="foundation.binary-relations-with-lifts.html#2459" class="Bound">R</a> <a id="2749" class="Symbol">→</a> <a id="2751" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2765" href="foundation.binary-relations-with-lifts.html#2459" class="Bound">R</a>
  <a id="2769" href="foundation.binary-relations-with-lifts.html#2682" class="Function">is-transitive-is-reflexive-has-lifts-Relation</a> <a id="2815" href="foundation.binary-relations-with-lifts.html#2815" class="Bound">r</a> <a id="2817" class="Symbol">=</a>
    <a id="2823" href="foundation.binary-relations-with-lifts.html#2518" class="Function">is-transitive-is-symmetric-has-lifts-Relation</a>
      <a id="2875" class="Symbol">(</a> <a id="2877" href="foundation.binary-relations-with-lifts.html#2205" class="Function">is-symmetric-is-reflexive-has-lifts-Relation</a> <a id="2922" href="foundation.binary-relations-with-lifts.html#2459" class="Bound">R</a> <a id="2924" href="foundation.binary-relations-with-lifts.html#2481" class="Bound">H</a> <a id="2926" href="foundation.binary-relations-with-lifts.html#2815" class="Bound">r</a><a id="2927" class="Symbol">)</a>
</pre>