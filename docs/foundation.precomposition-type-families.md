# Precomposition of type families

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="foundation.precomposition-type-families.html" class="Module">foundation.precomposition-type-families</a> <a id="91" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="147" class="Keyword">open</a> <a id="152" class="Keyword">import</a> <a id="159" href="foundation.homotopy-induction.html" class="Module">foundation.homotopy-induction</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.transport-along-homotopies.html" class="Module">foundation.transport-along-homotopies</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

Any map `f : A → B` induces a
{{#concept "precomposition operation" Disambiguation="type families" Agda=precomp-family}}

```text
  (B → 𝒰) → (A → 𝒰)
```

given by [precomposing](foundation-core.precomposition-functions.md) any
`Q : B → 𝒰` to `Q ∘ f : A → 𝒰`.

## Definitions

### The precomposition operation on type families

<pre class="Agda"><a id="823" class="Keyword">module</a> <a id="830" href="foundation.precomposition-type-families.html#830" class="Module">_</a>
  <a id="834" class="Symbol">{</a><a id="835" href="foundation.precomposition-type-families.html#835" class="Bound">l1</a> <a id="838" href="foundation.precomposition-type-families.html#838" class="Bound">l2</a> <a id="841" class="Symbol">:</a> <a id="843" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="848" class="Symbol">}</a> <a id="850" class="Symbol">{</a><a id="851" href="foundation.precomposition-type-families.html#851" class="Bound">A</a> <a id="853" class="Symbol">:</a> <a id="855" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="858" href="foundation.precomposition-type-families.html#835" class="Bound">l1</a><a id="860" class="Symbol">}</a> <a id="862" class="Symbol">{</a><a id="863" href="foundation.precomposition-type-families.html#863" class="Bound">B</a> <a id="865" class="Symbol">:</a> <a id="867" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="870" href="foundation.precomposition-type-families.html#838" class="Bound">l2</a><a id="872" class="Symbol">}</a> <a id="874" class="Symbol">(</a><a id="875" href="foundation.precomposition-type-families.html#875" class="Bound">f</a> <a id="877" class="Symbol">:</a> <a id="879" href="foundation.precomposition-type-families.html#851" class="Bound">A</a> <a id="881" class="Symbol">→</a> <a id="883" href="foundation.precomposition-type-families.html#863" class="Bound">B</a><a id="884" class="Symbol">)</a>
  <a id="888" class="Keyword">where</a>

  <a id="897" href="foundation.precomposition-type-families.html#897" class="Function">precomp-family</a> <a id="912" class="Symbol">:</a> <a id="914" class="Symbol">{</a><a id="915" href="foundation.precomposition-type-families.html#915" class="Bound">l</a> <a id="917" class="Symbol">:</a> <a id="919" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="924" class="Symbol">}</a> <a id="926" class="Symbol">→</a> <a id="928" class="Symbol">(</a><a id="929" href="foundation.precomposition-type-families.html#863" class="Bound">B</a> <a id="931" class="Symbol">→</a> <a id="933" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="936" href="foundation.precomposition-type-families.html#915" class="Bound">l</a><a id="937" class="Symbol">)</a> <a id="939" class="Symbol">→</a> <a id="941" class="Symbol">(</a><a id="942" href="foundation.precomposition-type-families.html#851" class="Bound">A</a> <a id="944" class="Symbol">→</a> <a id="946" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="949" href="foundation.precomposition-type-families.html#915" class="Bound">l</a><a id="950" class="Symbol">)</a>
  <a id="954" href="foundation.precomposition-type-families.html#897" class="Function">precomp-family</a> <a id="969" href="foundation.precomposition-type-families.html#969" class="Bound">Q</a> <a id="971" class="Symbol">=</a> <a id="973" href="foundation.precomposition-type-families.html#969" class="Bound">Q</a> <a id="975" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="977" href="foundation.precomposition-type-families.html#875" class="Bound">f</a>
</pre>
## Properties

### Transport along homotopies in precomposed type families

[Transporting](foundation.transport-along-homotopies.md) along a
[homotopy](foundation.homotopies.md) `H : g ~ h` in the family `Q ∘ f` gives us
a map of families of elements

```text
  ((a : A) → Q (f (g a))) → ((a : A) → Q (f (h a))) .
```

We show that this map is homotopic to transporting along
`f ·l H : f ∘ g ~ f ∘ h` in the family `Q`.

<pre class="Agda"><a id="1413" class="Keyword">module</a> <a id="1420" href="foundation.precomposition-type-families.html#1420" class="Module">_</a>
  <a id="1424" class="Symbol">{</a><a id="1425" href="foundation.precomposition-type-families.html#1425" class="Bound">l1</a> <a id="1428" href="foundation.precomposition-type-families.html#1428" class="Bound">l2</a> <a id="1431" href="foundation.precomposition-type-families.html#1431" class="Bound">l3</a> <a id="1434" href="foundation.precomposition-type-families.html#1434" class="Bound">l4</a> <a id="1437" class="Symbol">:</a> <a id="1439" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1444" class="Symbol">}</a> <a id="1446" class="Symbol">{</a><a id="1447" href="foundation.precomposition-type-families.html#1447" class="Bound">A</a> <a id="1449" class="Symbol">:</a> <a id="1451" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1454" href="foundation.precomposition-type-families.html#1425" class="Bound">l1</a><a id="1456" class="Symbol">}</a> <a id="1458" class="Symbol">{</a><a id="1459" href="foundation.precomposition-type-families.html#1459" class="Bound">B</a> <a id="1461" class="Symbol">:</a> <a id="1463" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1466" href="foundation.precomposition-type-families.html#1428" class="Bound">l2</a><a id="1468" class="Symbol">}</a> <a id="1470" class="Symbol">(</a><a id="1471" href="foundation.precomposition-type-families.html#1471" class="Bound">f</a> <a id="1473" class="Symbol">:</a> <a id="1475" href="foundation.precomposition-type-families.html#1447" class="Bound">A</a> <a id="1477" class="Symbol">→</a> <a id="1479" href="foundation.precomposition-type-families.html#1459" class="Bound">B</a><a id="1480" class="Symbol">)</a> <a id="1482" class="Symbol">(</a><a id="1483" href="foundation.precomposition-type-families.html#1483" class="Bound">Q</a> <a id="1485" class="Symbol">:</a> <a id="1487" href="foundation.precomposition-type-families.html#1459" class="Bound">B</a> <a id="1489" class="Symbol">→</a> <a id="1491" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1494" href="foundation.precomposition-type-families.html#1431" class="Bound">l3</a><a id="1496" class="Symbol">)</a>
  <a id="1500" class="Symbol">{</a><a id="1501" href="foundation.precomposition-type-families.html#1501" class="Bound">X</a> <a id="1503" class="Symbol">:</a> <a id="1505" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1508" href="foundation.precomposition-type-families.html#1434" class="Bound">l4</a><a id="1510" class="Symbol">}</a> <a id="1512" class="Symbol">{</a><a id="1513" href="foundation.precomposition-type-families.html#1513" class="Bound">g</a> <a id="1515" class="Symbol">:</a> <a id="1517" href="foundation.precomposition-type-families.html#1501" class="Bound">X</a> <a id="1519" class="Symbol">→</a> <a id="1521" href="foundation.precomposition-type-families.html#1447" class="Bound">A</a><a id="1522" class="Symbol">}</a>
  <a id="1526" class="Keyword">where</a>

  <a id="1535" href="foundation.precomposition-type-families.html#1535" class="Function">statement-tr-htpy-precomp-family</a> <a id="1568" class="Symbol">:</a>
    <a id="1574" class="Symbol">{</a><a id="1575" href="foundation.precomposition-type-families.html#1575" class="Bound">h</a> <a id="1577" class="Symbol">:</a> <a id="1579" href="foundation.precomposition-type-families.html#1501" class="Bound">X</a> <a id="1581" class="Symbol">→</a> <a id="1583" href="foundation.precomposition-type-families.html#1447" class="Bound">A</a><a id="1584" class="Symbol">}</a> <a id="1586" class="Symbol">(</a><a id="1587" href="foundation.precomposition-type-families.html#1587" class="Bound">H</a> <a id="1589" class="Symbol">:</a> <a id="1591" href="foundation.precomposition-type-families.html#1513" class="Bound">g</a> <a id="1593" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1595" href="foundation.precomposition-type-families.html#1575" class="Bound">h</a><a id="1596" class="Symbol">)</a> <a id="1598" class="Symbol">→</a> <a id="1600" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1603" class="Symbol">(</a><a id="1604" href="foundation.precomposition-type-families.html#1431" class="Bound">l3</a> <a id="1607" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1609" href="foundation.precomposition-type-families.html#1434" class="Bound">l4</a><a id="1611" class="Symbol">)</a>
  <a id="1615" href="foundation.precomposition-type-families.html#1535" class="Function">statement-tr-htpy-precomp-family</a> <a id="1648" href="foundation.precomposition-type-families.html#1648" class="Bound">H</a> <a id="1650" class="Symbol">=</a>
    <a id="1656" href="foundation.transport-along-homotopies.html#1000" class="Function">tr-htpy</a> <a id="1664" class="Symbol">(λ</a> <a id="1667" href="foundation.precomposition-type-families.html#1667" class="Bound">_</a> <a id="1669" class="Symbol">→</a> <a id="1671" href="foundation.precomposition-type-families.html#897" class="Function">precomp-family</a> <a id="1686" href="foundation.precomposition-type-families.html#1471" class="Bound">f</a> <a id="1688" href="foundation.precomposition-type-families.html#1483" class="Bound">Q</a><a id="1689" class="Symbol">)</a> <a id="1691" href="foundation.precomposition-type-families.html#1648" class="Bound">H</a> <a id="1693" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1695" href="foundation.transport-along-homotopies.html#1000" class="Function">tr-htpy</a> <a id="1703" class="Symbol">(λ</a> <a id="1706" href="foundation.precomposition-type-families.html#1706" class="Bound">_</a> <a id="1708" class="Symbol">→</a> <a id="1710" href="foundation.precomposition-type-families.html#1483" class="Bound">Q</a><a id="1711" class="Symbol">)</a> <a id="1713" class="Symbol">(</a><a id="1714" href="foundation.precomposition-type-families.html#1471" class="Bound">f</a> <a id="1716" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a> <a id="1719" href="foundation.precomposition-type-families.html#1648" class="Bound">H</a><a id="1720" class="Symbol">)</a>

  <a id="1725" class="Keyword">abstract</a>
    <a id="1738" href="foundation.precomposition-type-families.html#1738" class="Function">tr-htpy-precomp-family</a> <a id="1761" class="Symbol">:</a>
      <a id="1769" class="Symbol">{</a><a id="1770" href="foundation.precomposition-type-families.html#1770" class="Bound">h</a> <a id="1772" class="Symbol">:</a> <a id="1774" href="foundation.precomposition-type-families.html#1501" class="Bound">X</a> <a id="1776" class="Symbol">→</a> <a id="1778" href="foundation.precomposition-type-families.html#1447" class="Bound">A</a><a id="1779" class="Symbol">}</a> <a id="1781" class="Symbol">(</a><a id="1782" href="foundation.precomposition-type-families.html#1782" class="Bound">H</a> <a id="1784" class="Symbol">:</a> <a id="1786" href="foundation.precomposition-type-families.html#1513" class="Bound">g</a> <a id="1788" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1790" href="foundation.precomposition-type-families.html#1770" class="Bound">h</a><a id="1791" class="Symbol">)</a> <a id="1793" class="Symbol">→</a>
      <a id="1801" href="foundation.precomposition-type-families.html#1535" class="Function">statement-tr-htpy-precomp-family</a> <a id="1834" href="foundation.precomposition-type-families.html#1782" class="Bound">H</a>
    <a id="1840" href="foundation.precomposition-type-families.html#1738" class="Function">tr-htpy-precomp-family</a> <a id="1863" class="Symbol">=</a>
      <a id="1871" href="foundation.homotopy-induction.html#4265" class="Function">ind-htpy</a> <a id="1880" href="foundation.precomposition-type-families.html#1513" class="Bound">g</a>
        <a id="1890" class="Symbol">(</a> <a id="1892" class="Symbol">λ</a> <a id="1894" href="foundation.precomposition-type-families.html#1894" class="Bound">h</a> <a id="1896" class="Symbol">→</a> <a id="1898" href="foundation.precomposition-type-families.html#1535" class="Function">statement-tr-htpy-precomp-family</a><a id="1930" class="Symbol">)</a>
        <a id="1940" class="Symbol">(</a> <a id="1942" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="1951" class="Symbol">)</a>

    <a id="1958" href="foundation.precomposition-type-families.html#1958" class="Function">compute-tr-htpy-precomp-family</a> <a id="1989" class="Symbol">:</a>
      <a id="1997" href="foundation.precomposition-type-families.html#1738" class="Function">tr-htpy-precomp-family</a> <a id="2020" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a> <a id="2030" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="2038" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
    <a id="2052" href="foundation.precomposition-type-families.html#1958" class="Function">compute-tr-htpy-precomp-family</a> <a id="2083" class="Symbol">=</a>
      <a id="2091" href="foundation.homotopy-induction.html#4496" class="Function">compute-ind-htpy</a> <a id="2108" href="foundation.precomposition-type-families.html#1513" class="Bound">g</a>
        <a id="2118" class="Symbol">(</a> <a id="2120" class="Symbol">λ</a> <a id="2122" href="foundation.precomposition-type-families.html#2122" class="Bound">h</a> <a id="2124" class="Symbol">→</a> <a id="2126" href="foundation.precomposition-type-families.html#1535" class="Function">statement-tr-htpy-precomp-family</a><a id="2158" class="Symbol">)</a>
        <a id="2168" class="Symbol">(</a> <a id="2170" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="2179" class="Symbol">)</a>
</pre>