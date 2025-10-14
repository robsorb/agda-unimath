# Spans of types

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="foundation.spans.html" class="Module">foundation.spans</a> <a id="51" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="107" class="Keyword">open</a> <a id="112" class="Keyword">import</a> <a id="119" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

A {{#concept "binary span" Agda=span}} from `A` to `B` consists of a
{{#concept "spanning type" Disambiguation="binary span" Agda=spanning-type-span}}
`S` and a [pair](foundation.dependent-pair-types.md) of functions `f : S → A`
and `g : S → B`. The types `A` and `B` in the specification of a binary span are
also referred to as the {{#concept "domain" Disambiguation="binary span"}} and
{{#concept "codomain" Disambiguation="binary span"}} of the span, respectively.

In [`foundation.binary-type-duality`](foundation.binary-type-duality.md) we show
that [binary relations](foundation.binary-relations.md) are equivalently
described as spans of types.

We disambiguate between spans and [span diagrams](foundation.span-diagrams.md).
We consider spans from `A` to `B` to be _morphisms_ from `A` to `B` in the
category of types and spans between them, whereas we consider span diagrams to
be _objects_ in the category of diagrams of types of the form
`* <---- * ----> *`. Conceptually there is a subtle, but important distinction
between spans and span diagrams. As mentioned previously, a span from `A` to `B`
is equivalently described as a binary relation from `A` to `B`. On the other
hand, span diagrams are more suitable for functorial operations that take
"spans" as input, but for which the functorial action takes a natural
transformation, i.e., a morphism of span diagrams, as input. Examples of this
kind include [pushouts](synthetic-homotopy-theory.pushouts.md).

## Definitions

### (Binary) spans

<pre class="Agda"><a id="span"></a><a id="1830" href="foundation.spans.html#1830" class="Function">span</a> <a id="1835" class="Symbol">:</a>
  <a id="1839" class="Symbol">{</a><a id="1840" href="foundation.spans.html#1840" class="Bound">l1</a> <a id="1843" href="foundation.spans.html#1843" class="Bound">l2</a> <a id="1846" class="Symbol">:</a> <a id="1848" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1853" class="Symbol">}</a> <a id="1855" class="Symbol">(</a><a id="1856" href="foundation.spans.html#1856" class="Bound">l</a> <a id="1858" class="Symbol">:</a> <a id="1860" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1865" class="Symbol">)</a> <a id="1867" class="Symbol">(</a><a id="1868" href="foundation.spans.html#1868" class="Bound">A</a> <a id="1870" class="Symbol">:</a> <a id="1872" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1875" href="foundation.spans.html#1840" class="Bound">l1</a><a id="1877" class="Symbol">)</a> <a id="1879" class="Symbol">(</a><a id="1880" href="foundation.spans.html#1880" class="Bound">B</a> <a id="1882" class="Symbol">:</a> <a id="1884" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1887" href="foundation.spans.html#1843" class="Bound">l2</a><a id="1889" class="Symbol">)</a> <a id="1891" class="Symbol">→</a> <a id="1893" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1896" class="Symbol">(</a><a id="1897" href="foundation.spans.html#1840" class="Bound">l1</a> <a id="1900" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1902" href="foundation.spans.html#1843" class="Bound">l2</a> <a id="1905" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1907" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1912" href="foundation.spans.html#1856" class="Bound">l</a><a id="1913" class="Symbol">)</a>
<a id="1915" href="foundation.spans.html#1830" class="Function">span</a> <a id="1920" href="foundation.spans.html#1920" class="Bound">l</a> <a id="1922" href="foundation.spans.html#1922" class="Bound">A</a> <a id="1924" href="foundation.spans.html#1924" class="Bound">B</a> <a id="1926" class="Symbol">=</a> <a id="1928" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1930" class="Symbol">(</a><a id="1931" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1934" href="foundation.spans.html#1920" class="Bound">l</a><a id="1935" class="Symbol">)</a> <a id="1937" class="Symbol">(λ</a> <a id="1940" href="foundation.spans.html#1940" class="Bound">X</a> <a id="1942" class="Symbol">→</a> <a id="1944" class="Symbol">(</a><a id="1945" href="foundation.spans.html#1940" class="Bound">X</a> <a id="1947" class="Symbol">→</a> <a id="1949" href="foundation.spans.html#1922" class="Bound">A</a><a id="1950" class="Symbol">)</a> <a id="1952" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1954" class="Symbol">(</a><a id="1955" href="foundation.spans.html#1940" class="Bound">X</a> <a id="1957" class="Symbol">→</a> <a id="1959" href="foundation.spans.html#1924" class="Bound">B</a><a id="1960" class="Symbol">))</a>

<a id="1964" class="Keyword">module</a> <a id="1971" href="foundation.spans.html#1971" class="Module">_</a>
  <a id="1975" class="Symbol">{</a><a id="1976" href="foundation.spans.html#1976" class="Bound">l1</a> <a id="1979" href="foundation.spans.html#1979" class="Bound">l2</a> <a id="1982" href="foundation.spans.html#1982" class="Bound">l3</a> <a id="1985" class="Symbol">:</a> <a id="1987" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1992" class="Symbol">}</a> <a id="1994" class="Symbol">{</a><a id="1995" href="foundation.spans.html#1995" class="Bound">A</a> <a id="1997" class="Symbol">:</a> <a id="1999" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2002" href="foundation.spans.html#1976" class="Bound">l1</a><a id="2004" class="Symbol">}</a> <a id="2006" class="Symbol">{</a><a id="2007" href="foundation.spans.html#2007" class="Bound">B</a> <a id="2009" class="Symbol">:</a> <a id="2011" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2014" href="foundation.spans.html#1979" class="Bound">l2</a><a id="2016" class="Symbol">}</a>
  <a id="2020" class="Symbol">(</a><a id="2021" href="foundation.spans.html#2021" class="Bound">c</a> <a id="2023" class="Symbol">:</a> <a id="2025" href="foundation.spans.html#1830" class="Function">span</a> <a id="2030" href="foundation.spans.html#1982" class="Bound">l3</a> <a id="2033" href="foundation.spans.html#1995" class="Bound">A</a> <a id="2035" href="foundation.spans.html#2007" class="Bound">B</a><a id="2036" class="Symbol">)</a>
  <a id="2040" class="Keyword">where</a>

  <a id="2049" href="foundation.spans.html#2049" class="Function">spanning-type-span</a> <a id="2068" class="Symbol">:</a> <a id="2070" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2073" href="foundation.spans.html#1982" class="Bound">l3</a>
  <a id="2078" href="foundation.spans.html#2049" class="Function">spanning-type-span</a> <a id="2097" class="Symbol">=</a> <a id="2099" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2103" href="foundation.spans.html#2021" class="Bound">c</a>

  <a id="2108" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="2122" class="Symbol">:</a> <a id="2124" href="foundation.spans.html#2049" class="Function">spanning-type-span</a> <a id="2143" class="Symbol">→</a> <a id="2145" href="foundation.spans.html#1995" class="Bound">A</a>
  <a id="2149" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="2163" class="Symbol">=</a> <a id="2165" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2169" class="Symbol">(</a><a id="2170" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2174" href="foundation.spans.html#2021" class="Bound">c</a><a id="2175" class="Symbol">)</a>

  <a id="2180" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="2195" class="Symbol">:</a> <a id="2197" href="foundation.spans.html#2049" class="Function">spanning-type-span</a> <a id="2216" class="Symbol">→</a> <a id="2218" href="foundation.spans.html#2007" class="Bound">B</a>
  <a id="2222" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="2237" class="Symbol">=</a> <a id="2239" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2243" class="Symbol">(</a><a id="2244" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2248" href="foundation.spans.html#2021" class="Bound">c</a><a id="2249" class="Symbol">)</a>
</pre>
### Identity spans

<pre class="Agda"><a id="2284" class="Keyword">module</a> <a id="2291" href="foundation.spans.html#2291" class="Module">_</a>
  <a id="2295" class="Symbol">{</a><a id="2296" href="foundation.spans.html#2296" class="Bound">l1</a> <a id="2299" class="Symbol">:</a> <a id="2301" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2306" class="Symbol">}</a> <a id="2308" class="Symbol">{</a><a id="2309" href="foundation.spans.html#2309" class="Bound">X</a> <a id="2311" class="Symbol">:</a> <a id="2313" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2316" href="foundation.spans.html#2296" class="Bound">l1</a><a id="2318" class="Symbol">}</a>
  <a id="2322" class="Keyword">where</a>

  <a id="2331" href="foundation.spans.html#2331" class="Function">id-span</a> <a id="2339" class="Symbol">:</a> <a id="2341" href="foundation.spans.html#1830" class="Function">span</a> <a id="2346" href="foundation.spans.html#2296" class="Bound">l1</a> <a id="2349" href="foundation.spans.html#2309" class="Bound">X</a> <a id="2351" href="foundation.spans.html#2309" class="Bound">X</a>
  <a id="2355" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2359" href="foundation.spans.html#2331" class="Function">id-span</a> <a id="2367" class="Symbol">=</a> <a id="2369" href="foundation.spans.html#2309" class="Bound">X</a>
  <a id="2373" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2377" class="Symbol">(</a><a id="2378" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2382" href="foundation.spans.html#2331" class="Function">id-span</a><a id="2389" class="Symbol">)</a> <a id="2391" class="Symbol">=</a> <a id="2393" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="2398" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2402" class="Symbol">(</a><a id="2403" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2407" href="foundation.spans.html#2331" class="Function">id-span</a><a id="2414" class="Symbol">)</a> <a id="2416" class="Symbol">=</a> <a id="2418" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>
## See also

- [Binary type duality](foundation.binary-type-duality.md)
- [Cospans](foundation.cospans.md)
- [Span diagrams](foundation.span-diagrams.md)
- [Spans of families of types](foundation.spans-families-of-types.md)
- [Spans of pointed types](structured-types.pointed-spans.md)
