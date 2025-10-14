# Dependent epimorphisms with respect to truncated types

<pre class="Agda"><a id="67" class="Keyword">module</a> <a id="74" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html" class="Module">foundation.dependent-epimorphisms-with-respect-to-truncated-types</a> <a id="140" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.epimorphisms-with-respect-to-truncated-types.html" class="Module">foundation.epimorphisms-with-respect-to-truncated-types</a>
<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation-core.precomposition-dependent-functions.html" class="Module">foundation-core.precomposition-dependent-functions</a>
<a id="406" class="Keyword">open</a> <a id="411" class="Keyword">import</a> <a id="418" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="450" class="Keyword">open</a> <a id="455" class="Keyword">import</a> <a id="462" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

## Idea

A **dependent `k`-epimorphism** is a map `f : A → B` such that the
[precomposition function](foundation.precomposition-dependent-functions.md)

```text
  - ∘ f : ((b : B) → C b) → ((a : A) → C (f a))
```

is an [embedding](foundation-core.embeddings.md) for every family `C` of
[`k`-types](foundation.truncated-types.md) over `B`.

Clearly, every dependent `k`-epimorphism is a
[`k`-epimorphism](foundation.epimorphisms-with-respect-to-truncated-types.md).
The converse is also true, i.e., every `k`-epimorphism is a dependent
`k`-epimorphism. Therefore it follows that a map `f : A → B` is
[`k`-acyclic](synthetic-homotopy-theory.truncated-acyclic-maps.md) if and only
if it is a `k`-epimorphism, if and only if it is a dependent `k`-epimorphism.

## Definitions

### The predicate of being a dependent `k`-epimorphism

<pre class="Agda"><a id="1351" class="Keyword">module</a> <a id="1358" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1358" class="Module">_</a>
  <a id="1362" class="Symbol">{</a><a id="1363" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1363" class="Bound">l1</a> <a id="1366" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1366" class="Bound">l2</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1376" class="Symbol">}</a> <a id="1378" class="Symbol">(</a><a id="1379" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1379" class="Bound">k</a> <a id="1381" class="Symbol">:</a> <a id="1383" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="1384" class="Symbol">)</a> <a id="1386" class="Symbol">{</a><a id="1387" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1387" class="Bound">A</a> <a id="1389" class="Symbol">:</a> <a id="1391" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1394" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1363" class="Bound">l1</a><a id="1396" class="Symbol">}</a> <a id="1398" class="Symbol">{</a><a id="1399" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1399" class="Bound">B</a> <a id="1401" class="Symbol">:</a> <a id="1403" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1406" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1366" class="Bound">l2</a><a id="1408" class="Symbol">}</a>
  <a id="1412" class="Keyword">where</a>

  <a id="1421" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1421" class="Function">is-dependent-epimorphism-Truncated-Type</a> <a id="1461" class="Symbol">:</a> <a id="1463" class="Symbol">(</a><a id="1464" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1387" class="Bound">A</a> <a id="1466" class="Symbol">→</a> <a id="1468" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1399" class="Bound">B</a><a id="1469" class="Symbol">)</a> <a id="1471" class="Symbol">→</a> <a id="1473" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1479" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1421" class="Function">is-dependent-epimorphism-Truncated-Type</a> <a id="1519" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1519" class="Bound">f</a> <a id="1521" class="Symbol">=</a>
    <a id="1527" class="Symbol">{</a><a id="1528" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1528" class="Bound">l</a> <a id="1530" class="Symbol">:</a> <a id="1532" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1537" class="Symbol">}</a> <a id="1539" class="Symbol">(</a><a id="1540" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1540" class="Bound">C</a> <a id="1542" class="Symbol">:</a> <a id="1544" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1399" class="Bound">B</a> <a id="1546" class="Symbol">→</a> <a id="1548" href="foundation-core.truncated-types.html#1603" class="Function">Truncated-Type</a> <a id="1563" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1528" class="Bound">l</a> <a id="1565" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1379" class="Bound">k</a><a id="1566" class="Symbol">)</a> <a id="1568" class="Symbol">→</a>
    <a id="1574" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="1581" class="Symbol">(</a><a id="1582" href="foundation-core.precomposition-dependent-functions.html#744" class="Function">precomp-Π</a> <a id="1592" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1519" class="Bound">f</a> <a id="1594" class="Symbol">(λ</a> <a id="1597" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1597" class="Bound">b</a> <a id="1599" class="Symbol">→</a> <a id="1601" href="foundation-core.truncated-types.html#1736" class="Function">type-Truncated-Type</a> <a id="1621" class="Symbol">(</a><a id="1622" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1540" class="Bound">C</a> <a id="1624" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1597" class="Bound">b</a><a id="1625" class="Symbol">)))</a>
</pre>
## Properties

### Every dependent `k`-epimorphism is a `k`-epimorphism

<pre class="Agda"><a id="1715" class="Keyword">module</a> <a id="1722" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1722" class="Module">_</a>
  <a id="1726" class="Symbol">{</a><a id="1727" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1727" class="Bound">l1</a> <a id="1730" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1730" class="Bound">l2</a> <a id="1733" class="Symbol">:</a> <a id="1735" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1740" class="Symbol">}</a> <a id="1742" class="Symbol">{</a><a id="1743" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1743" class="Bound">k</a> <a id="1745" class="Symbol">:</a> <a id="1747" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="1748" class="Symbol">}</a> <a id="1750" class="Symbol">{</a><a id="1751" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1751" class="Bound">A</a> <a id="1753" class="Symbol">:</a> <a id="1755" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1758" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1727" class="Bound">l1</a><a id="1760" class="Symbol">}</a> <a id="1762" class="Symbol">{</a><a id="1763" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1763" class="Bound">B</a> <a id="1765" class="Symbol">:</a> <a id="1767" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1770" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1730" class="Bound">l2</a><a id="1772" class="Symbol">}</a> <a id="1774" class="Symbol">(</a><a id="1775" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1775" class="Bound">f</a> <a id="1777" class="Symbol">:</a> <a id="1779" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1751" class="Bound">A</a> <a id="1781" class="Symbol">→</a> <a id="1783" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1763" class="Bound">B</a><a id="1784" class="Symbol">)</a>
  <a id="1788" class="Keyword">where</a>

  <a id="1797" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1797" class="Function">is-epimorphism-is-dependent-epimorphism-Truncated-Type</a> <a id="1852" class="Symbol">:</a>
    <a id="1858" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1421" class="Function">is-dependent-epimorphism-Truncated-Type</a> <a id="1898" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1743" class="Bound">k</a> <a id="1900" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1775" class="Bound">f</a> <a id="1902" class="Symbol">→</a>
    <a id="1908" href="foundation.epimorphisms-with-respect-to-truncated-types.html#1562" class="Function">is-epimorphism-Truncated-Type</a> <a id="1938" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1743" class="Bound">k</a> <a id="1940" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1775" class="Bound">f</a>
  <a id="1944" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1797" class="Function">is-epimorphism-is-dependent-epimorphism-Truncated-Type</a> <a id="1999" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1999" class="Bound">e</a> <a id="2001" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#2001" class="Bound">X</a> <a id="2003" class="Symbol">=</a> <a id="2005" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#1999" class="Bound">e</a> <a id="2007" class="Symbol">(λ</a> <a id="2010" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#2010" class="Bound">_</a> <a id="2012" class="Symbol">→</a> <a id="2014" href="foundation.dependent-epimorphisms-with-respect-to-truncated-types.html#2001" class="Bound">X</a><a id="2015" class="Symbol">)</a>
</pre>
The converse of the above, that every `k`-epimorphism is a dependent
`k`-epimorphism, can be found in the file on
[`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md).

## See also

- [`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
