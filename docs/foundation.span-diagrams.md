# Span diagrams

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a> <a id="58" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="114" class="Keyword">open</a> <a id="119" class="Keyword">import</a> <a id="126" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A {{#concept "(binary) span diagram" Agda=span-diagram}} is a diagram of the
form

```text
       f       g
  A <----- S -----> B.
```

In other words, a span diagram consists of two types `A` and `B` and a
[span](foundation.spans.md) from `A` to `B`.

We disambiguate between [spans](foundation.spans.md) and span diagrams. We
consider spans from `A` to `B` to be _morphisms_ from `A` to `B` in the category
of types and spans between them, whereas we consider span diagrams to be
_objects_ in the category of diagrams of types of the form `* <---- * ----> *`.
Conceptually there is a subtle, but important distinction between spans and span
diagrams. In [binary type duality](foundation.binary-type-duality.md) we show a
span from `A` to `B` is [equivalently](foundation-core.equivalences.md)
described as a [binary relation](foundation.binary-relations.md) from `A` to
`B`. On the other hand, span diagrams are more suitable for functorial
operations that take "spans" as input, but for which the functorial action takes
a natural transformation, i.e., a morphism of span diagrams, as input. Examples
of this kind include [pushouts](synthetic-homotopy-theory.pushouts.md).

### (Binary) span diagrams

<pre class="Agda"><a id="span-diagram"></a><a id="1505" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1518" class="Symbol">:</a> <a id="1520" class="Symbol">(</a><a id="1521" href="foundation.span-diagrams.html#1521" class="Bound">l1</a> <a id="1524" href="foundation.span-diagrams.html#1524" class="Bound">l2</a> <a id="1527" href="foundation.span-diagrams.html#1527" class="Bound">l3</a> <a id="1530" class="Symbol">:</a> <a id="1532" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1537" class="Symbol">)</a> <a id="1539" class="Symbol">→</a> <a id="1541" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1544" class="Symbol">(</a><a id="1545" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1550" href="foundation.span-diagrams.html#1521" class="Bound">l1</a> <a id="1553" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1555" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1560" href="foundation.span-diagrams.html#1524" class="Bound">l2</a> <a id="1563" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1565" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1570" href="foundation.span-diagrams.html#1527" class="Bound">l3</a><a id="1572" class="Symbol">)</a>
<a id="1574" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1587" href="foundation.span-diagrams.html#1587" class="Bound">l1</a> <a id="1590" href="foundation.span-diagrams.html#1590" class="Bound">l2</a> <a id="1593" href="foundation.span-diagrams.html#1593" class="Bound">l3</a> <a id="1596" class="Symbol">=</a>
  <a id="1600" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1602" class="Symbol">(</a><a id="1603" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1606" href="foundation.span-diagrams.html#1587" class="Bound">l1</a><a id="1608" class="Symbol">)</a> <a id="1610" class="Symbol">(λ</a> <a id="1613" href="foundation.span-diagrams.html#1613" class="Bound">A</a> <a id="1615" class="Symbol">→</a> <a id="1617" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1619" class="Symbol">(</a><a id="1620" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1623" href="foundation.span-diagrams.html#1590" class="Bound">l2</a><a id="1625" class="Symbol">)</a> <a id="1627" class="Symbol">(λ</a> <a id="1630" href="foundation.span-diagrams.html#1630" class="Bound">B</a> <a id="1632" class="Symbol">→</a> <a id="1634" href="foundation.spans.html#1830" class="Function">span</a> <a id="1639" href="foundation.span-diagrams.html#1593" class="Bound">l3</a> <a id="1642" href="foundation.span-diagrams.html#1613" class="Bound">A</a> <a id="1644" href="foundation.span-diagrams.html#1630" class="Bound">B</a><a id="1645" class="Symbol">))</a>

<a id="1649" class="Keyword">module</a> <a id="1656" href="foundation.span-diagrams.html#1656" class="Module">_</a>
  <a id="1660" class="Symbol">{</a><a id="1661" href="foundation.span-diagrams.html#1661" class="Bound">l1</a> <a id="1664" href="foundation.span-diagrams.html#1664" class="Bound">l2</a> <a id="1667" href="foundation.span-diagrams.html#1667" class="Bound">l3</a> <a id="1670" class="Symbol">:</a> <a id="1672" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1677" class="Symbol">}</a> <a id="1679" class="Symbol">{</a><a id="1680" href="foundation.span-diagrams.html#1680" class="Bound">S</a> <a id="1682" class="Symbol">:</a> <a id="1684" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1687" href="foundation.span-diagrams.html#1661" class="Bound">l1</a><a id="1689" class="Symbol">}</a> <a id="1691" class="Symbol">{</a><a id="1692" href="foundation.span-diagrams.html#1692" class="Bound">A</a> <a id="1694" class="Symbol">:</a> <a id="1696" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1699" href="foundation.span-diagrams.html#1664" class="Bound">l2</a><a id="1701" class="Symbol">}</a> <a id="1703" class="Symbol">{</a><a id="1704" href="foundation.span-diagrams.html#1704" class="Bound">B</a> <a id="1706" class="Symbol">:</a> <a id="1708" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1711" href="foundation.span-diagrams.html#1667" class="Bound">l3</a><a id="1713" class="Symbol">}</a>
  <a id="1717" class="Keyword">where</a>

  <a id="1726" href="foundation.span-diagrams.html#1726" class="Function">make-span-diagram</a> <a id="1744" class="Symbol">:</a>
    <a id="1750" class="Symbol">(</a><a id="1751" href="foundation.span-diagrams.html#1680" class="Bound">S</a> <a id="1753" class="Symbol">→</a> <a id="1755" href="foundation.span-diagrams.html#1692" class="Bound">A</a><a id="1756" class="Symbol">)</a> <a id="1758" class="Symbol">→</a> <a id="1760" class="Symbol">(</a><a id="1761" href="foundation.span-diagrams.html#1680" class="Bound">S</a> <a id="1763" class="Symbol">→</a> <a id="1765" href="foundation.span-diagrams.html#1704" class="Bound">B</a><a id="1766" class="Symbol">)</a> <a id="1768" class="Symbol">→</a> <a id="1770" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1783" href="foundation.span-diagrams.html#1664" class="Bound">l2</a> <a id="1786" href="foundation.span-diagrams.html#1667" class="Bound">l3</a> <a id="1789" href="foundation.span-diagrams.html#1661" class="Bound">l1</a>
  <a id="1794" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1798" class="Symbol">(</a><a id="1799" href="foundation.span-diagrams.html#1726" class="Function">make-span-diagram</a> <a id="1817" href="foundation.span-diagrams.html#1817" class="Bound">f</a> <a id="1819" href="foundation.span-diagrams.html#1819" class="Bound">g</a><a id="1820" class="Symbol">)</a> <a id="1822" class="Symbol">=</a> <a id="1824" href="foundation.span-diagrams.html#1692" class="Bound">A</a>
  <a id="1828" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1832" class="Symbol">(</a><a id="1833" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1837" class="Symbol">(</a><a id="1838" href="foundation.span-diagrams.html#1726" class="Function">make-span-diagram</a> <a id="1856" href="foundation.span-diagrams.html#1856" class="Bound">f</a> <a id="1858" href="foundation.span-diagrams.html#1858" class="Bound">g</a><a id="1859" class="Symbol">))</a> <a id="1862" class="Symbol">=</a> <a id="1864" href="foundation.span-diagrams.html#1704" class="Bound">B</a>
  <a id="1868" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1872" class="Symbol">(</a><a id="1873" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1877" class="Symbol">(</a><a id="1878" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1882" class="Symbol">(</a><a id="1883" href="foundation.span-diagrams.html#1726" class="Function">make-span-diagram</a> <a id="1901" href="foundation.span-diagrams.html#1901" class="Bound">f</a> <a id="1903" href="foundation.span-diagrams.html#1903" class="Bound">g</a><a id="1904" class="Symbol">)))</a> <a id="1908" class="Symbol">=</a> <a id="1910" href="foundation.span-diagrams.html#1680" class="Bound">S</a>
  <a id="1914" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1918" class="Symbol">(</a><a id="1919" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1923" class="Symbol">(</a><a id="1924" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1928" class="Symbol">(</a><a id="1929" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1933" class="Symbol">(</a><a id="1934" href="foundation.span-diagrams.html#1726" class="Function">make-span-diagram</a> <a id="1952" href="foundation.span-diagrams.html#1952" class="Bound">f</a> <a id="1954" href="foundation.span-diagrams.html#1954" class="Bound">g</a><a id="1955" class="Symbol">))))</a> <a id="1960" class="Symbol">=</a> <a id="1962" href="foundation.span-diagrams.html#1952" class="Bound">f</a>
  <a id="1966" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1970" class="Symbol">(</a><a id="1971" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1975" class="Symbol">(</a><a id="1976" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1980" class="Symbol">(</a><a id="1981" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1985" class="Symbol">(</a><a id="1986" href="foundation.span-diagrams.html#1726" class="Function">make-span-diagram</a> <a id="2004" href="foundation.span-diagrams.html#2004" class="Bound">f</a> <a id="2006" href="foundation.span-diagrams.html#2006" class="Bound">g</a><a id="2007" class="Symbol">))))</a> <a id="2012" class="Symbol">=</a> <a id="2014" href="foundation.span-diagrams.html#2006" class="Bound">g</a>

<a id="2017" class="Keyword">module</a> <a id="2024" href="foundation.span-diagrams.html#2024" class="Module">_</a>
  <a id="2028" class="Symbol">{</a><a id="2029" href="foundation.span-diagrams.html#2029" class="Bound">l1</a> <a id="2032" href="foundation.span-diagrams.html#2032" class="Bound">l2</a> <a id="2035" href="foundation.span-diagrams.html#2035" class="Bound">l3</a> <a id="2038" class="Symbol">:</a> <a id="2040" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2045" class="Symbol">}</a> <a id="2047" class="Symbol">(</a><a id="2048" href="foundation.span-diagrams.html#2048" class="Bound">𝒮</a> <a id="2050" class="Symbol">:</a> <a id="2052" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2065" href="foundation.span-diagrams.html#2029" class="Bound">l1</a> <a id="2068" href="foundation.span-diagrams.html#2032" class="Bound">l2</a> <a id="2071" href="foundation.span-diagrams.html#2035" class="Bound">l3</a><a id="2073" class="Symbol">)</a>
  <a id="2077" class="Keyword">where</a>

  <a id="2086" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="2106" class="Symbol">:</a> <a id="2108" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2111" href="foundation.span-diagrams.html#2029" class="Bound">l1</a>
  <a id="2116" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="2136" class="Symbol">=</a> <a id="2138" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2142" href="foundation.span-diagrams.html#2048" class="Bound">𝒮</a>

  <a id="2147" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="2169" class="Symbol">:</a> <a id="2171" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2174" href="foundation.span-diagrams.html#2032" class="Bound">l2</a>
  <a id="2179" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="2201" class="Symbol">=</a> <a id="2203" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2207" class="Symbol">(</a><a id="2208" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2212" href="foundation.span-diagrams.html#2048" class="Bound">𝒮</a><a id="2213" class="Symbol">)</a>

  <a id="2218" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="2236" class="Symbol">:</a>
    <a id="2242" href="foundation.spans.html#1830" class="Function">span</a> <a id="2247" href="foundation.span-diagrams.html#2035" class="Bound">l3</a> <a id="2250" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="2270" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a>
  <a id="2294" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="2312" class="Symbol">=</a> <a id="2314" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2318" class="Symbol">(</a><a id="2319" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2323" href="foundation.span-diagrams.html#2048" class="Bound">𝒮</a><a id="2324" class="Symbol">)</a>

  <a id="2329" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="2356" class="Symbol">:</a> <a id="2358" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2361" href="foundation.span-diagrams.html#2035" class="Bound">l3</a>
  <a id="2366" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="2393" class="Symbol">=</a>
    <a id="2399" href="foundation.spans.html#2049" class="Function">spanning-type-span</a> <a id="2418" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a>

  <a id="2439" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="2461" class="Symbol">:</a> <a id="2463" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="2490" class="Symbol">→</a> <a id="2492" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a>
  <a id="2514" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="2536" class="Symbol">=</a>
    <a id="2542" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="2556" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a>

  <a id="2577" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="2600" class="Symbol">:</a> <a id="2602" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="2629" class="Symbol">→</a> <a id="2631" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a>
  <a id="2655" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="2678" class="Symbol">=</a>
    <a id="2684" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="2699" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a>
</pre>
### The span diagram obtained from a morphism of arrows

Given maps `f : A → B` and `g : X → Y` and a morphism of arrows `α : f → g`, the
span diagram associated to `α` is the span diagram

```text
       f       α₀
  B <----- A -----> X.
```

<pre class="Agda"><a id="2974" class="Keyword">module</a> <a id="2981" href="foundation.span-diagrams.html#2981" class="Module">_</a>
  <a id="2985" class="Symbol">{</a><a id="2986" href="foundation.span-diagrams.html#2986" class="Bound">l1</a> <a id="2989" href="foundation.span-diagrams.html#2989" class="Bound">l2</a> <a id="2992" href="foundation.span-diagrams.html#2992" class="Bound">l3</a> <a id="2995" href="foundation.span-diagrams.html#2995" class="Bound">l4</a> <a id="2998" class="Symbol">:</a> <a id="3000" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3005" class="Symbol">}</a> <a id="3007" class="Symbol">{</a><a id="3008" href="foundation.span-diagrams.html#3008" class="Bound">A</a> <a id="3010" class="Symbol">:</a> <a id="3012" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3015" href="foundation.span-diagrams.html#2986" class="Bound">l1</a><a id="3017" class="Symbol">}</a> <a id="3019" class="Symbol">{</a><a id="3020" href="foundation.span-diagrams.html#3020" class="Bound">B</a> <a id="3022" class="Symbol">:</a> <a id="3024" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3027" href="foundation.span-diagrams.html#2989" class="Bound">l2</a><a id="3029" class="Symbol">}</a> <a id="3031" class="Symbol">{</a><a id="3032" href="foundation.span-diagrams.html#3032" class="Bound">X</a> <a id="3034" class="Symbol">:</a> <a id="3036" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3039" href="foundation.span-diagrams.html#2992" class="Bound">l3</a><a id="3041" class="Symbol">}</a> <a id="3043" class="Symbol">{</a><a id="3044" href="foundation.span-diagrams.html#3044" class="Bound">Y</a> <a id="3046" class="Symbol">:</a> <a id="3048" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3051" href="foundation.span-diagrams.html#2995" class="Bound">l4</a><a id="3053" class="Symbol">}</a>
  <a id="3057" class="Symbol">(</a><a id="3058" href="foundation.span-diagrams.html#3058" class="Bound">f</a> <a id="3060" class="Symbol">:</a> <a id="3062" href="foundation.span-diagrams.html#3008" class="Bound">A</a> <a id="3064" class="Symbol">→</a> <a id="3066" href="foundation.span-diagrams.html#3020" class="Bound">B</a><a id="3067" class="Symbol">)</a> <a id="3069" class="Symbol">(</a><a id="3070" href="foundation.span-diagrams.html#3070" class="Bound">g</a> <a id="3072" class="Symbol">:</a> <a id="3074" href="foundation.span-diagrams.html#3032" class="Bound">X</a> <a id="3076" class="Symbol">→</a> <a id="3078" href="foundation.span-diagrams.html#3044" class="Bound">Y</a><a id="3079" class="Symbol">)</a> <a id="3081" class="Symbol">(</a><a id="3082" href="foundation.span-diagrams.html#3082" class="Bound">α</a> <a id="3084" class="Symbol">:</a> <a id="3086" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="3096" href="foundation.span-diagrams.html#3058" class="Bound">f</a> <a id="3098" href="foundation.span-diagrams.html#3070" class="Bound">g</a><a id="3099" class="Symbol">)</a>
  <a id="3103" class="Keyword">where</a>

  <a id="3112" href="foundation.span-diagrams.html#3112" class="Function">domain-span-diagram-hom-arrow</a> <a id="3142" class="Symbol">:</a> <a id="3144" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3147" href="foundation.span-diagrams.html#2989" class="Bound">l2</a>
  <a id="3152" href="foundation.span-diagrams.html#3112" class="Function">domain-span-diagram-hom-arrow</a> <a id="3182" class="Symbol">=</a> <a id="3184" href="foundation.span-diagrams.html#3020" class="Bound">B</a>

  <a id="3189" href="foundation.span-diagrams.html#3189" class="Function">codomain-span-diagram-hom-arrow</a> <a id="3221" class="Symbol">:</a> <a id="3223" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3226" href="foundation.span-diagrams.html#2992" class="Bound">l3</a>
  <a id="3231" href="foundation.span-diagrams.html#3189" class="Function">codomain-span-diagram-hom-arrow</a> <a id="3263" class="Symbol">=</a> <a id="3265" href="foundation.span-diagrams.html#3032" class="Bound">X</a>

  <a id="3270" href="foundation.span-diagrams.html#3270" class="Function">spanning-type-hom-arrow</a> <a id="3294" class="Symbol">:</a> <a id="3296" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3299" href="foundation.span-diagrams.html#2986" class="Bound">l1</a>
  <a id="3304" href="foundation.span-diagrams.html#3270" class="Function">spanning-type-hom-arrow</a> <a id="3328" class="Symbol">=</a> <a id="3330" href="foundation.span-diagrams.html#3008" class="Bound">A</a>

  <a id="3335" href="foundation.span-diagrams.html#3335" class="Function">left-map-span-diagram-hom-arrow</a> <a id="3367" class="Symbol">:</a>
    <a id="3373" href="foundation.span-diagrams.html#3270" class="Function">spanning-type-hom-arrow</a> <a id="3397" class="Symbol">→</a> <a id="3399" href="foundation.span-diagrams.html#3112" class="Function">domain-span-diagram-hom-arrow</a>
  <a id="3431" href="foundation.span-diagrams.html#3335" class="Function">left-map-span-diagram-hom-arrow</a> <a id="3463" class="Symbol">=</a> <a id="3465" href="foundation.span-diagrams.html#3058" class="Bound">f</a>

  <a id="3470" href="foundation.span-diagrams.html#3470" class="Function">right-map-span-diagram-hom-arrow</a> <a id="3503" class="Symbol">:</a>
    <a id="3509" href="foundation.span-diagrams.html#3270" class="Function">spanning-type-hom-arrow</a> <a id="3533" class="Symbol">→</a> <a id="3535" href="foundation.span-diagrams.html#3189" class="Function">codomain-span-diagram-hom-arrow</a>
  <a id="3569" href="foundation.span-diagrams.html#3470" class="Function">right-map-span-diagram-hom-arrow</a> <a id="3602" class="Symbol">=</a> <a id="3604" href="foundation.morphisms-arrows.html#1743" class="Function">map-domain-hom-arrow</a> <a id="3625" href="foundation.span-diagrams.html#3058" class="Bound">f</a> <a id="3627" href="foundation.span-diagrams.html#3070" class="Bound">g</a> <a id="3629" href="foundation.span-diagrams.html#3082" class="Bound">α</a>

  <a id="3634" href="foundation.span-diagrams.html#3634" class="Function">span-hom-arrow</a> <a id="3649" class="Symbol">:</a>
    <a id="3655" href="foundation.spans.html#1830" class="Function">span</a> <a id="3660" href="foundation.span-diagrams.html#2986" class="Bound">l1</a> <a id="3663" href="foundation.span-diagrams.html#3020" class="Bound">B</a> <a id="3665" href="foundation.span-diagrams.html#3032" class="Bound">X</a>
  <a id="3669" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3673" href="foundation.span-diagrams.html#3634" class="Function">span-hom-arrow</a> <a id="3688" class="Symbol">=</a> <a id="3690" href="foundation.span-diagrams.html#3008" class="Bound">A</a>
  <a id="3694" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3698" class="Symbol">(</a><a id="3699" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3703" href="foundation.span-diagrams.html#3634" class="Function">span-hom-arrow</a><a id="3717" class="Symbol">)</a> <a id="3719" class="Symbol">=</a> <a id="3721" href="foundation.span-diagrams.html#3335" class="Function">left-map-span-diagram-hom-arrow</a>
  <a id="3755" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3759" class="Symbol">(</a><a id="3760" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3764" href="foundation.span-diagrams.html#3634" class="Function">span-hom-arrow</a><a id="3778" class="Symbol">)</a> <a id="3780" class="Symbol">=</a> <a id="3782" href="foundation.span-diagrams.html#3470" class="Function">right-map-span-diagram-hom-arrow</a>

  <a id="3818" href="foundation.span-diagrams.html#3818" class="Function">span-diagram-hom-arrow</a> <a id="3841" class="Symbol">:</a> <a id="3843" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="3856" href="foundation.span-diagrams.html#2989" class="Bound">l2</a> <a id="3859" href="foundation.span-diagrams.html#2992" class="Bound">l3</a> <a id="3862" href="foundation.span-diagrams.html#2986" class="Bound">l1</a>
  <a id="3867" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3871" href="foundation.span-diagrams.html#3818" class="Function">span-diagram-hom-arrow</a> <a id="3894" class="Symbol">=</a> <a id="3896" href="foundation.span-diagrams.html#3112" class="Function">domain-span-diagram-hom-arrow</a>
  <a id="3928" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3932" class="Symbol">(</a><a id="3933" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3937" href="foundation.span-diagrams.html#3818" class="Function">span-diagram-hom-arrow</a><a id="3959" class="Symbol">)</a> <a id="3961" class="Symbol">=</a> <a id="3963" href="foundation.span-diagrams.html#3189" class="Function">codomain-span-diagram-hom-arrow</a>
  <a id="3997" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4001" class="Symbol">(</a><a id="4002" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4006" href="foundation.span-diagrams.html#3818" class="Function">span-diagram-hom-arrow</a><a id="4028" class="Symbol">)</a> <a id="4030" class="Symbol">=</a> <a id="4032" href="foundation.span-diagrams.html#3634" class="Function">span-hom-arrow</a>
</pre>
## See also

- [Cospan diagrams](foundation.cospan-diagrams.md)
- [Diagonal span diagrams](foundation.diagonal-span-diagrams.md)
- [Extensions of span diagrams](foundation.operations-span-diagrams.md)
- [Kernel span diagrams of maps](foundation.kernel-span-diagrams-of-maps.md)
- [Spans of families of types](foundation.spans-families-of-types.md)
- [Transposition of span diagrams](foundation.transposition-span-diagrams.md)
