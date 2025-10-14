# Standard ternary pullbacks

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="foundation.standard-ternary-pullbacks.html" class="Module">foundation.standard-ternary-pullbacks</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.cones-over-cospan-diagrams.html" class="Module">foundation.cones-over-cospan-diagrams</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation.equality-cartesian-product-types.html" class="Module">foundation.equality-cartesian-product-types</a>
<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="410" class="Keyword">open</a> <a id="415" class="Keyword">import</a> <a id="422" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="foundation.structure-identity-principle.html" class="Module">foundation.structure-identity-principle</a>
<a id="500" class="Keyword">open</a> <a id="505" class="Keyword">import</a> <a id="512" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="540" class="Keyword">open</a> <a id="545" class="Keyword">import</a> <a id="552" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="592" class="Keyword">open</a> <a id="597" class="Keyword">import</a> <a id="604" href="foundation-core.commuting-squares-of-maps.html" class="Module">foundation-core.commuting-squares-of-maps</a>
<a id="646" class="Keyword">open</a> <a id="651" class="Keyword">import</a> <a id="658" href="foundation-core.diagonal-maps-cartesian-products-of-types.html" class="Module">foundation-core.diagonal-maps-cartesian-products-of-types</a>
<a id="716" class="Keyword">open</a> <a id="721" class="Keyword">import</a> <a id="728" href="foundation-core.equality-dependent-pair-types.html" class="Module">foundation-core.equality-dependent-pair-types</a>
<a id="774" class="Keyword">open</a> <a id="779" class="Keyword">import</a> <a id="786" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="815" class="Keyword">open</a> <a id="820" class="Keyword">import</a> <a id="827" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="858" class="Keyword">open</a> <a id="863" class="Keyword">import</a> <a id="870" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="921" class="Keyword">open</a> <a id="926" class="Keyword">import</a> <a id="933" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="960" class="Keyword">open</a> <a id="965" class="Keyword">import</a> <a id="972" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>
<a id="1000" class="Keyword">open</a> <a id="1005" class="Keyword">import</a> <a id="1012" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="1037" class="Keyword">open</a> <a id="1042" class="Keyword">import</a> <a id="1049" href="foundation-core.type-theoretic-principle-of-choice.html" class="Module">foundation-core.type-theoretic-principle-of-choice</a>
<a id="1100" class="Keyword">open</a> <a id="1105" class="Keyword">import</a> <a id="1112" href="foundation-core.universal-property-pullbacks.html" class="Module">foundation-core.universal-property-pullbacks</a>
<a id="1157" class="Keyword">open</a> <a id="1162" class="Keyword">import</a> <a id="1169" href="foundation-core.whiskering-identifications-concatenation.html" class="Module">foundation-core.whiskering-identifications-concatenation</a>
</pre>
</details>

## Idea

Given two [cospan of types](foundation.cospans.md) with a shared vertex `B`:

```text
      f       g       h       i
  A ----> X <---- B ----> Y <---- C,
```

we call the standard limit of the diagram the
{{#concept "standard ternary pullback" Disambiguation="of types" Agda=standard-ternary-pullback}}.
It is defined as the [sum](foundation.dependent-pair-types.md)

```text
  standard-ternary-pullback f g h i :=
    Σ (a : A) (b : B) (c : C), ((f a ＝ g b) × (h b ＝ i c)).
```

## Definitions

<pre class="Agda"><a id="1757" class="Keyword">module</a> <a id="1764" href="foundation.standard-ternary-pullbacks.html#1764" class="Module">_</a>
  <a id="1768" class="Symbol">{</a><a id="1769" href="foundation.standard-ternary-pullbacks.html#1769" class="Bound">l1</a> <a id="1772" href="foundation.standard-ternary-pullbacks.html#1772" class="Bound">l2</a> <a id="1775" href="foundation.standard-ternary-pullbacks.html#1775" class="Bound">l3</a> <a id="1778" href="foundation.standard-ternary-pullbacks.html#1778" class="Bound">l4</a> <a id="1781" href="foundation.standard-ternary-pullbacks.html#1781" class="Bound">l5</a> <a id="1784" class="Symbol">:</a> <a id="1786" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1791" class="Symbol">}</a>
  <a id="1795" class="Symbol">{</a><a id="1796" href="foundation.standard-ternary-pullbacks.html#1796" class="Bound">X</a> <a id="1798" class="Symbol">:</a> <a id="1800" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1803" href="foundation.standard-ternary-pullbacks.html#1769" class="Bound">l1</a><a id="1805" class="Symbol">}</a> <a id="1807" class="Symbol">{</a><a id="1808" href="foundation.standard-ternary-pullbacks.html#1808" class="Bound">Y</a> <a id="1810" class="Symbol">:</a> <a id="1812" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1815" href="foundation.standard-ternary-pullbacks.html#1772" class="Bound">l2</a><a id="1817" class="Symbol">}</a> <a id="1819" class="Symbol">{</a><a id="1820" href="foundation.standard-ternary-pullbacks.html#1820" class="Bound">A</a> <a id="1822" class="Symbol">:</a> <a id="1824" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1827" href="foundation.standard-ternary-pullbacks.html#1775" class="Bound">l3</a><a id="1829" class="Symbol">}</a> <a id="1831" class="Symbol">{</a><a id="1832" href="foundation.standard-ternary-pullbacks.html#1832" class="Bound">B</a> <a id="1834" class="Symbol">:</a> <a id="1836" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1839" href="foundation.standard-ternary-pullbacks.html#1778" class="Bound">l4</a><a id="1841" class="Symbol">}</a> <a id="1843" class="Symbol">{</a><a id="1844" href="foundation.standard-ternary-pullbacks.html#1844" class="Bound">C</a> <a id="1846" class="Symbol">:</a> <a id="1848" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1851" href="foundation.standard-ternary-pullbacks.html#1781" class="Bound">l5</a><a id="1853" class="Symbol">}</a>
  <a id="1857" class="Symbol">(</a><a id="1858" href="foundation.standard-ternary-pullbacks.html#1858" class="Bound">f</a> <a id="1860" class="Symbol">:</a> <a id="1862" href="foundation.standard-ternary-pullbacks.html#1820" class="Bound">A</a> <a id="1864" class="Symbol">→</a> <a id="1866" href="foundation.standard-ternary-pullbacks.html#1796" class="Bound">X</a><a id="1867" class="Symbol">)</a> <a id="1869" class="Symbol">(</a><a id="1870" href="foundation.standard-ternary-pullbacks.html#1870" class="Bound">g</a> <a id="1872" class="Symbol">:</a> <a id="1874" href="foundation.standard-ternary-pullbacks.html#1832" class="Bound">B</a> <a id="1876" class="Symbol">→</a> <a id="1878" href="foundation.standard-ternary-pullbacks.html#1796" class="Bound">X</a><a id="1879" class="Symbol">)</a> <a id="1881" class="Symbol">(</a><a id="1882" href="foundation.standard-ternary-pullbacks.html#1882" class="Bound">h</a> <a id="1884" class="Symbol">:</a> <a id="1886" href="foundation.standard-ternary-pullbacks.html#1832" class="Bound">B</a> <a id="1888" class="Symbol">→</a> <a id="1890" href="foundation.standard-ternary-pullbacks.html#1808" class="Bound">Y</a><a id="1891" class="Symbol">)</a> <a id="1893" class="Symbol">(</a><a id="1894" href="foundation.standard-ternary-pullbacks.html#1894" class="Bound">i</a> <a id="1896" class="Symbol">:</a> <a id="1898" href="foundation.standard-ternary-pullbacks.html#1844" class="Bound">C</a> <a id="1900" class="Symbol">→</a> <a id="1902" href="foundation.standard-ternary-pullbacks.html#1808" class="Bound">Y</a><a id="1903" class="Symbol">)</a>
  <a id="1907" class="Keyword">where</a>

  <a id="1916" href="foundation.standard-ternary-pullbacks.html#1916" class="Function">standard-ternary-pullback</a> <a id="1942" class="Symbol">:</a> <a id="1944" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1947" class="Symbol">(</a><a id="1948" href="foundation.standard-ternary-pullbacks.html#1769" class="Bound">l1</a> <a id="1951" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1953" href="foundation.standard-ternary-pullbacks.html#1772" class="Bound">l2</a> <a id="1956" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1958" href="foundation.standard-ternary-pullbacks.html#1775" class="Bound">l3</a> <a id="1961" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1963" href="foundation.standard-ternary-pullbacks.html#1778" class="Bound">l4</a> <a id="1966" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1968" href="foundation.standard-ternary-pullbacks.html#1781" class="Bound">l5</a><a id="1970" class="Symbol">)</a>
  <a id="1974" href="foundation.standard-ternary-pullbacks.html#1916" class="Function">standard-ternary-pullback</a> <a id="2000" class="Symbol">=</a>
    <a id="2006" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2008" href="foundation.standard-ternary-pullbacks.html#1820" class="Bound">A</a> <a id="2010" class="Symbol">(λ</a> <a id="2013" href="foundation.standard-ternary-pullbacks.html#2013" class="Bound">a</a> <a id="2015" class="Symbol">→</a> <a id="2017" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2019" href="foundation.standard-ternary-pullbacks.html#1832" class="Bound">B</a> <a id="2021" class="Symbol">(λ</a> <a id="2024" href="foundation.standard-ternary-pullbacks.html#2024" class="Bound">b</a> <a id="2026" class="Symbol">→</a> <a id="2028" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2030" href="foundation.standard-ternary-pullbacks.html#1844" class="Bound">C</a> <a id="2032" class="Symbol">(λ</a> <a id="2035" href="foundation.standard-ternary-pullbacks.html#2035" class="Bound">c</a> <a id="2037" class="Symbol">→</a> <a id="2039" class="Symbol">(</a><a id="2040" href="foundation.standard-ternary-pullbacks.html#1858" class="Bound">f</a> <a id="2042" href="foundation.standard-ternary-pullbacks.html#2013" class="Bound">a</a> <a id="2044" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2046" href="foundation.standard-ternary-pullbacks.html#1870" class="Bound">g</a> <a id="2048" href="foundation.standard-ternary-pullbacks.html#2024" class="Bound">b</a><a id="2049" class="Symbol">)</a> <a id="2051" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="2053" class="Symbol">(</a><a id="2054" href="foundation.standard-ternary-pullbacks.html#1882" class="Bound">h</a> <a id="2056" href="foundation.standard-ternary-pullbacks.html#2024" class="Bound">b</a> <a id="2058" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2060" href="foundation.standard-ternary-pullbacks.html#1894" class="Bound">i</a> <a id="2062" href="foundation.standard-ternary-pullbacks.html#2035" class="Bound">c</a><a id="2063" class="Symbol">))))</a>
</pre>
## See also

- [Type arithmetic with standard pullbacks](foundation.type-arithmetic-standard-pullbacks.md)

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
