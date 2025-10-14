# Binary relations with extensions

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="foundation.binary-relations-with-extensions.html" class="Module">foundation.binary-relations-with-extensions</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="foundation.iterated-dependent-product-types.html" class="Module">foundation.iterated-dependent-product-types</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

We say a [relation](foundation.binary-relations.md) `R`
{{#concept "has extensions" Disambiguation="binary relations of types" Agda=has-extensions-Relation}}
if for every triple `x y z : A`, there is a binary operation

```text
  R x y → R x z → R y z.
```

Relations with extensions are closely related to transitive relations. But,
instead of giving for every diagram

```text
       y
      ∧ \
     /   \
    /     ∨
  x        z
```

a horizontal arrow `x → z`, a binary relation with extensions gives, for every
span

```text
       y
      ∧
     /
    /
  x -----> z,
```

an _extension_ `y → z`. By symmetry it also gives an extension in the opposite
direction `z → y`.

Dually, a relation `R`
[has lifts](foundation.binary-relations-with-extensions.md) if for every triple
`x y z : A`, there is a binary operation

```text
  R x z → R y z → R x y.
```

## Definition

### The structure on relations of having extensions

<pre class="Agda"><a id="1338" class="Keyword">module</a> <a id="1345" href="foundation.binary-relations-with-extensions.html#1345" class="Module">_</a>
  <a id="1349" class="Symbol">{</a><a id="1350" href="foundation.binary-relations-with-extensions.html#1350" class="Bound">l1</a> <a id="1353" href="foundation.binary-relations-with-extensions.html#1353" class="Bound">l2</a> <a id="1356" class="Symbol">:</a> <a id="1358" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1363" class="Symbol">}</a> <a id="1365" class="Symbol">{</a><a id="1366" href="foundation.binary-relations-with-extensions.html#1366" class="Bound">A</a> <a id="1368" class="Symbol">:</a> <a id="1370" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1373" href="foundation.binary-relations-with-extensions.html#1350" class="Bound">l1</a><a id="1375" class="Symbol">}</a> <a id="1377" class="Symbol">(</a><a id="1378" href="foundation.binary-relations-with-extensions.html#1378" class="Bound">R</a> <a id="1380" class="Symbol">:</a> <a id="1382" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1391" href="foundation.binary-relations-with-extensions.html#1353" class="Bound">l2</a> <a id="1394" href="foundation.binary-relations-with-extensions.html#1366" class="Bound">A</a><a id="1395" class="Symbol">)</a>
  <a id="1399" class="Keyword">where</a>

  <a id="1408" href="foundation.binary-relations-with-extensions.html#1408" class="Function">has-extensions-Relation</a> <a id="1432" class="Symbol">:</a> <a id="1434" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1437" class="Symbol">(</a><a id="1438" href="foundation.binary-relations-with-extensions.html#1350" class="Bound">l1</a> <a id="1441" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1443" href="foundation.binary-relations-with-extensions.html#1353" class="Bound">l2</a><a id="1445" class="Symbol">)</a>
  <a id="1449" href="foundation.binary-relations-with-extensions.html#1408" class="Function">has-extensions-Relation</a> <a id="1473" class="Symbol">=</a> <a id="1475" class="Symbol">{</a><a id="1476" href="foundation.binary-relations-with-extensions.html#1476" class="Bound">x</a> <a id="1478" href="foundation.binary-relations-with-extensions.html#1478" class="Bound">y</a> <a id="1480" href="foundation.binary-relations-with-extensions.html#1480" class="Bound">z</a> <a id="1482" class="Symbol">:</a> <a id="1484" href="foundation.binary-relations-with-extensions.html#1366" class="Bound">A</a><a id="1485" class="Symbol">}</a> <a id="1487" class="Symbol">→</a> <a id="1489" href="foundation.binary-relations-with-extensions.html#1378" class="Bound">R</a> <a id="1491" href="foundation.binary-relations-with-extensions.html#1476" class="Bound">x</a> <a id="1493" href="foundation.binary-relations-with-extensions.html#1478" class="Bound">y</a> <a id="1495" class="Symbol">→</a> <a id="1497" href="foundation.binary-relations-with-extensions.html#1378" class="Bound">R</a> <a id="1499" href="foundation.binary-relations-with-extensions.html#1476" class="Bound">x</a> <a id="1501" href="foundation.binary-relations-with-extensions.html#1480" class="Bound">z</a> <a id="1503" class="Symbol">→</a> <a id="1505" href="foundation.binary-relations-with-extensions.html#1378" class="Bound">R</a> <a id="1507" href="foundation.binary-relations-with-extensions.html#1478" class="Bound">y</a> <a id="1509" href="foundation.binary-relations-with-extensions.html#1480" class="Bound">z</a>
</pre>
## Properties

### If there is an element that relates to `y` and the relation has extensions, then `y` relates to `y`

<pre class="Agda"><a id="1644" class="Keyword">module</a> <a id="1651" href="foundation.binary-relations-with-extensions.html#1651" class="Module">_</a>
  <a id="1655" class="Symbol">{</a><a id="1656" href="foundation.binary-relations-with-extensions.html#1656" class="Bound">l1</a> <a id="1659" href="foundation.binary-relations-with-extensions.html#1659" class="Bound">l2</a> <a id="1662" class="Symbol">:</a> <a id="1664" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1669" class="Symbol">}</a> <a id="1671" class="Symbol">{</a><a id="1672" href="foundation.binary-relations-with-extensions.html#1672" class="Bound">A</a> <a id="1674" class="Symbol">:</a> <a id="1676" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1679" href="foundation.binary-relations-with-extensions.html#1656" class="Bound">l1</a><a id="1681" class="Symbol">}</a> <a id="1683" class="Symbol">(</a><a id="1684" href="foundation.binary-relations-with-extensions.html#1684" class="Bound">R</a> <a id="1686" class="Symbol">:</a> <a id="1688" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1697" href="foundation.binary-relations-with-extensions.html#1659" class="Bound">l2</a> <a id="1700" href="foundation.binary-relations-with-extensions.html#1672" class="Bound">A</a><a id="1701" class="Symbol">)</a>
  <a id="1705" class="Keyword">where</a>

  <a id="1714" href="foundation.binary-relations-with-extensions.html#1714" class="Function">rel-self-any-rel-has-extensions-Relation</a> <a id="1755" class="Symbol">:</a>
    <a id="1761" href="foundation.binary-relations-with-extensions.html#1408" class="Function">has-extensions-Relation</a> <a id="1785" href="foundation.binary-relations-with-extensions.html#1684" class="Bound">R</a> <a id="1787" class="Symbol">→</a> <a id="1789" class="Symbol">{</a><a id="1790" href="foundation.binary-relations-with-extensions.html#1790" class="Bound">x</a> <a id="1792" href="foundation.binary-relations-with-extensions.html#1792" class="Bound">y</a> <a id="1794" class="Symbol">:</a> <a id="1796" href="foundation.binary-relations-with-extensions.html#1672" class="Bound">A</a><a id="1797" class="Symbol">}</a> <a id="1799" class="Symbol">→</a> <a id="1801" href="foundation.binary-relations-with-extensions.html#1684" class="Bound">R</a> <a id="1803" href="foundation.binary-relations-with-extensions.html#1790" class="Bound">x</a> <a id="1805" href="foundation.binary-relations-with-extensions.html#1792" class="Bound">y</a> <a id="1807" class="Symbol">→</a> <a id="1809" href="foundation.binary-relations-with-extensions.html#1684" class="Bound">R</a> <a id="1811" href="foundation.binary-relations-with-extensions.html#1792" class="Bound">y</a> <a id="1813" href="foundation.binary-relations-with-extensions.html#1792" class="Bound">y</a>
  <a id="1817" href="foundation.binary-relations-with-extensions.html#1714" class="Function">rel-self-any-rel-has-extensions-Relation</a> <a id="1858" href="foundation.binary-relations-with-extensions.html#1858" class="Bound">H</a> <a id="1860" href="foundation.binary-relations-with-extensions.html#1860" class="Bound">p</a> <a id="1862" class="Symbol">=</a> <a id="1864" href="foundation.binary-relations-with-extensions.html#1858" class="Bound">H</a> <a id="1866" href="foundation.binary-relations-with-extensions.html#1860" class="Bound">p</a> <a id="1868" href="foundation.binary-relations-with-extensions.html#1860" class="Bound">p</a>
</pre>
### The reverse of an extension

<pre class="Agda"><a id="1916" class="Keyword">module</a> <a id="1923" href="foundation.binary-relations-with-extensions.html#1923" class="Module">_</a>
  <a id="1927" class="Symbol">{</a><a id="1928" href="foundation.binary-relations-with-extensions.html#1928" class="Bound">l1</a> <a id="1931" href="foundation.binary-relations-with-extensions.html#1931" class="Bound">l2</a> <a id="1934" class="Symbol">:</a> <a id="1936" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1941" class="Symbol">}</a> <a id="1943" class="Symbol">{</a><a id="1944" href="foundation.binary-relations-with-extensions.html#1944" class="Bound">A</a> <a id="1946" class="Symbol">:</a> <a id="1948" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1951" href="foundation.binary-relations-with-extensions.html#1928" class="Bound">l1</a><a id="1953" class="Symbol">}</a> <a id="1955" class="Symbol">(</a><a id="1956" href="foundation.binary-relations-with-extensions.html#1956" class="Bound">R</a> <a id="1958" class="Symbol">:</a> <a id="1960" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1969" href="foundation.binary-relations-with-extensions.html#1931" class="Bound">l2</a> <a id="1972" href="foundation.binary-relations-with-extensions.html#1944" class="Bound">A</a><a id="1973" class="Symbol">)</a>
  <a id="1977" class="Keyword">where</a>

  <a id="1986" href="foundation.binary-relations-with-extensions.html#1986" class="Function">reverse-has-extensions-Relation</a> <a id="2018" class="Symbol">:</a>
    <a id="2024" href="foundation.binary-relations-with-extensions.html#1408" class="Function">has-extensions-Relation</a> <a id="2048" href="foundation.binary-relations-with-extensions.html#1956" class="Bound">R</a> <a id="2050" class="Symbol">→</a> <a id="2052" class="Symbol">{</a><a id="2053" href="foundation.binary-relations-with-extensions.html#2053" class="Bound">x</a> <a id="2055" href="foundation.binary-relations-with-extensions.html#2055" class="Bound">y</a> <a id="2057" href="foundation.binary-relations-with-extensions.html#2057" class="Bound">z</a> <a id="2059" class="Symbol">:</a> <a id="2061" href="foundation.binary-relations-with-extensions.html#1944" class="Bound">A</a><a id="2062" class="Symbol">}</a> <a id="2064" class="Symbol">→</a> <a id="2066" href="foundation.binary-relations-with-extensions.html#1956" class="Bound">R</a> <a id="2068" href="foundation.binary-relations-with-extensions.html#2057" class="Bound">z</a> <a id="2070" href="foundation.binary-relations-with-extensions.html#2053" class="Bound">x</a> <a id="2072" class="Symbol">→</a> <a id="2074" href="foundation.binary-relations-with-extensions.html#1956" class="Bound">R</a> <a id="2076" href="foundation.binary-relations-with-extensions.html#2057" class="Bound">z</a> <a id="2078" href="foundation.binary-relations-with-extensions.html#2055" class="Bound">y</a> <a id="2080" class="Symbol">→</a> <a id="2082" href="foundation.binary-relations-with-extensions.html#1956" class="Bound">R</a> <a id="2084" href="foundation.binary-relations-with-extensions.html#2055" class="Bound">y</a> <a id="2086" href="foundation.binary-relations-with-extensions.html#2053" class="Bound">x</a>
  <a id="2090" href="foundation.binary-relations-with-extensions.html#1986" class="Function">reverse-has-extensions-Relation</a> <a id="2122" href="foundation.binary-relations-with-extensions.html#2122" class="Bound">H</a> <a id="2124" href="foundation.binary-relations-with-extensions.html#2124" class="Bound">p</a> <a id="2126" href="foundation.binary-relations-with-extensions.html#2126" class="Bound">q</a> <a id="2128" class="Symbol">=</a> <a id="2130" href="foundation.binary-relations-with-extensions.html#2122" class="Bound">H</a> <a id="2132" href="foundation.binary-relations-with-extensions.html#2126" class="Bound">q</a> <a id="2134" href="foundation.binary-relations-with-extensions.html#2124" class="Bound">p</a>
</pre>
### Reflexive relations with extensions are symmetric

<pre class="Agda"><a id="2204" class="Keyword">module</a> <a id="2211" href="foundation.binary-relations-with-extensions.html#2211" class="Module">_</a>
  <a id="2215" class="Symbol">{</a><a id="2216" href="foundation.binary-relations-with-extensions.html#2216" class="Bound">l1</a> <a id="2219" href="foundation.binary-relations-with-extensions.html#2219" class="Bound">l2</a> <a id="2222" class="Symbol">:</a> <a id="2224" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2229" class="Symbol">}</a> <a id="2231" class="Symbol">{</a><a id="2232" href="foundation.binary-relations-with-extensions.html#2232" class="Bound">A</a> <a id="2234" class="Symbol">:</a> <a id="2236" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2239" href="foundation.binary-relations-with-extensions.html#2216" class="Bound">l1</a><a id="2241" class="Symbol">}</a> <a id="2243" class="Symbol">(</a><a id="2244" href="foundation.binary-relations-with-extensions.html#2244" class="Bound">R</a> <a id="2246" class="Symbol">:</a> <a id="2248" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="2257" href="foundation.binary-relations-with-extensions.html#2219" class="Bound">l2</a> <a id="2260" href="foundation.binary-relations-with-extensions.html#2232" class="Bound">A</a><a id="2261" class="Symbol">)</a>
  <a id="2265" class="Symbol">(</a><a id="2266" href="foundation.binary-relations-with-extensions.html#2266" class="Bound">H</a> <a id="2268" class="Symbol">:</a> <a id="2270" href="foundation.binary-relations-with-extensions.html#1408" class="Function">has-extensions-Relation</a> <a id="2294" href="foundation.binary-relations-with-extensions.html#2244" class="Bound">R</a><a id="2295" class="Symbol">)</a>
  <a id="2299" class="Keyword">where</a>

  <a id="2308" href="foundation.binary-relations-with-extensions.html#2308" class="Function">is-symmetric-is-reflexive-has-extensions-Relation</a> <a id="2358" class="Symbol">:</a>
    <a id="2364" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="2377" href="foundation.binary-relations-with-extensions.html#2244" class="Bound">R</a> <a id="2379" class="Symbol">→</a> <a id="2381" href="foundation.binary-relations.html#3402" class="Function">is-symmetric</a> <a id="2394" href="foundation.binary-relations-with-extensions.html#2244" class="Bound">R</a>
  <a id="2398" href="foundation.binary-relations-with-extensions.html#2308" class="Function">is-symmetric-is-reflexive-has-extensions-Relation</a> <a id="2448" href="foundation.binary-relations-with-extensions.html#2448" class="Bound">r</a> <a id="2450" href="foundation.binary-relations-with-extensions.html#2450" class="Bound">x</a> <a id="2452" href="foundation.binary-relations-with-extensions.html#2452" class="Bound">y</a> <a id="2454" href="foundation.binary-relations-with-extensions.html#2454" class="Bound">p</a> <a id="2456" class="Symbol">=</a> <a id="2458" href="foundation.binary-relations-with-extensions.html#2266" class="Bound">H</a> <a id="2460" href="foundation.binary-relations-with-extensions.html#2454" class="Bound">p</a> <a id="2462" class="Symbol">(</a><a id="2463" href="foundation.binary-relations-with-extensions.html#2448" class="Bound">r</a> <a id="2465" href="foundation.binary-relations-with-extensions.html#2450" class="Bound">x</a><a id="2466" class="Symbol">)</a>
</pre>
### Reflexive relations with extensions are transitive

<pre class="Agda"><a id="2537" class="Keyword">module</a> <a id="2544" href="foundation.binary-relations-with-extensions.html#2544" class="Module">_</a>
  <a id="2548" class="Symbol">{</a><a id="2549" href="foundation.binary-relations-with-extensions.html#2549" class="Bound">l1</a> <a id="2552" href="foundation.binary-relations-with-extensions.html#2552" class="Bound">l2</a> <a id="2555" class="Symbol">:</a> <a id="2557" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2562" class="Symbol">}</a> <a id="2564" class="Symbol">{</a><a id="2565" href="foundation.binary-relations-with-extensions.html#2565" class="Bound">A</a> <a id="2567" class="Symbol">:</a> <a id="2569" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2572" href="foundation.binary-relations-with-extensions.html#2549" class="Bound">l1</a><a id="2574" class="Symbol">}</a> <a id="2576" class="Symbol">(</a><a id="2577" href="foundation.binary-relations-with-extensions.html#2577" class="Bound">R</a> <a id="2579" class="Symbol">:</a> <a id="2581" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="2590" href="foundation.binary-relations-with-extensions.html#2552" class="Bound">l2</a> <a id="2593" href="foundation.binary-relations-with-extensions.html#2565" class="Bound">A</a><a id="2594" class="Symbol">)</a>
  <a id="2598" class="Symbol">(</a><a id="2599" href="foundation.binary-relations-with-extensions.html#2599" class="Bound">H</a> <a id="2601" class="Symbol">:</a> <a id="2603" href="foundation.binary-relations-with-extensions.html#1408" class="Function">has-extensions-Relation</a> <a id="2627" href="foundation.binary-relations-with-extensions.html#2577" class="Bound">R</a><a id="2628" class="Symbol">)</a>
  <a id="2632" class="Keyword">where</a>

  <a id="2641" href="foundation.binary-relations-with-extensions.html#2641" class="Function">is-transitive-is-symmetric-has-extensions-Relation</a> <a id="2692" class="Symbol">:</a>
    <a id="2698" href="foundation.binary-relations.html#3402" class="Function">is-symmetric</a> <a id="2711" href="foundation.binary-relations-with-extensions.html#2577" class="Bound">R</a> <a id="2713" class="Symbol">→</a> <a id="2715" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2729" href="foundation.binary-relations-with-extensions.html#2577" class="Bound">R</a>
  <a id="2733" href="foundation.binary-relations-with-extensions.html#2641" class="Function">is-transitive-is-symmetric-has-extensions-Relation</a> <a id="2784" href="foundation.binary-relations-with-extensions.html#2784" class="Bound">s</a> <a id="2786" href="foundation.binary-relations-with-extensions.html#2786" class="Bound">x</a> <a id="2788" href="foundation.binary-relations-with-extensions.html#2788" class="Bound">y</a> <a id="2790" href="foundation.binary-relations-with-extensions.html#2790" class="Bound">z</a> <a id="2792" href="foundation.binary-relations-with-extensions.html#2792" class="Bound">p</a> <a id="2794" href="foundation.binary-relations-with-extensions.html#2794" class="Bound">q</a> <a id="2796" class="Symbol">=</a> <a id="2798" href="foundation.binary-relations-with-extensions.html#2599" class="Bound">H</a> <a id="2800" class="Symbol">(</a><a id="2801" href="foundation.binary-relations-with-extensions.html#2784" class="Bound">s</a> <a id="2803" href="foundation.binary-relations-with-extensions.html#2786" class="Bound">x</a> <a id="2805" href="foundation.binary-relations-with-extensions.html#2788" class="Bound">y</a> <a id="2807" href="foundation.binary-relations-with-extensions.html#2794" class="Bound">q</a><a id="2808" class="Symbol">)</a> <a id="2810" href="foundation.binary-relations-with-extensions.html#2792" class="Bound">p</a>

  <a id="2815" href="foundation.binary-relations-with-extensions.html#2815" class="Function">is-transitive-is-reflexive-has-extensions-Relation</a> <a id="2866" class="Symbol">:</a>
    <a id="2872" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="2885" href="foundation.binary-relations-with-extensions.html#2577" class="Bound">R</a> <a id="2887" class="Symbol">→</a> <a id="2889" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2903" href="foundation.binary-relations-with-extensions.html#2577" class="Bound">R</a>
  <a id="2907" href="foundation.binary-relations-with-extensions.html#2815" class="Function">is-transitive-is-reflexive-has-extensions-Relation</a> <a id="2958" href="foundation.binary-relations-with-extensions.html#2958" class="Bound">r</a> <a id="2960" class="Symbol">=</a>
    <a id="2966" href="foundation.binary-relations-with-extensions.html#2641" class="Function">is-transitive-is-symmetric-has-extensions-Relation</a>
      <a id="3023" class="Symbol">(</a> <a id="3025" href="foundation.binary-relations-with-extensions.html#2308" class="Function">is-symmetric-is-reflexive-has-extensions-Relation</a> <a id="3075" href="foundation.binary-relations-with-extensions.html#2577" class="Bound">R</a> <a id="3077" href="foundation.binary-relations-with-extensions.html#2599" class="Bound">H</a> <a id="3079" href="foundation.binary-relations-with-extensions.html#2958" class="Bound">r</a><a id="3080" class="Symbol">)</a>
</pre>
## See also

- [Strict symmetrization of binary relations](foundation.strict-symmetrization-binary-relations.md)
