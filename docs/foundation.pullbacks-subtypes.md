# Pullbacks of subtypes

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="foundation.pullbacks-subtypes.html" class="Module">foundation.pullbacks-subtypes</a> <a id="71" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.powersets.html" class="Module">foundation.powersets</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation-core.subtypes.html" class="Module">foundation-core.subtypes</a>

<a id="366" class="Keyword">open</a> <a id="371" class="Keyword">import</a> <a id="378" href="order-theory.order-preserving-maps-large-posets.html" class="Module">order-theory.order-preserving-maps-large-posets</a>
<a id="426" class="Keyword">open</a> <a id="431" class="Keyword">import</a> <a id="438" href="order-theory.order-preserving-maps-large-preorders.html" class="Module">order-theory.order-preserving-maps-large-preorders</a>
</pre>
</details>

## Idea

Consider a [subtype](foundation-core.subtypes.md) `T` of a type `B` and a map
`f : A → B`. Then the {{#concept "pullback subtype" Agda=pullback-subtype}}
`pullback f T` of `A` is defined to be `T ∘ f`. This fits in a
[pullback diagram](foundation-core.pullbacks.md)

```text
                 π₂
  pullback f T -----> T
       | ⌟            |
    π₁ |              | i
       |              |
       ∨              ∨
       A -----------> B
               f
```

The
[universal property of pullbacks](foundation.universal-property-pullbacks.md)
quite literally returns the definition of the subtype `pullback f T`, because it
essentially asserts that

```text
  (S ⊆ pullback f T) ↔ ((x : A) → is-in-subtype S x → is-in-subtype T (f x)).
```

The operation `pullback f : subtype B → subtype A` is an
[order preserving map](order-theory.order-preserving-maps-large-posets.md)
between the [powersets](foundation.powersets.md) of `B` and `A`.

In the file [Images of subtypes](foundation.images-subtypes.md) we show that the
pullback operation on subtypes is the upper adjoint of a
[Galois connection](order-theory.galois-connections-large-posets.md).

## Definitions

### The predicate of being a pullback of subtypes

<pre class="Agda"><a id="1740" class="Keyword">module</a> <a id="1747" href="foundation.pullbacks-subtypes.html#1747" class="Module">_</a>
  <a id="1751" class="Symbol">{</a><a id="1752" href="foundation.pullbacks-subtypes.html#1752" class="Bound">l1</a> <a id="1755" href="foundation.pullbacks-subtypes.html#1755" class="Bound">l2</a> <a id="1758" href="foundation.pullbacks-subtypes.html#1758" class="Bound">l3</a> <a id="1761" href="foundation.pullbacks-subtypes.html#1761" class="Bound">l4</a> <a id="1764" class="Symbol">:</a> <a id="1766" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1771" class="Symbol">}</a> <a id="1773" class="Symbol">{</a><a id="1774" href="foundation.pullbacks-subtypes.html#1774" class="Bound">A</a> <a id="1776" class="Symbol">:</a> <a id="1778" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1781" href="foundation.pullbacks-subtypes.html#1752" class="Bound">l1</a><a id="1783" class="Symbol">}</a> <a id="1785" class="Symbol">{</a><a id="1786" href="foundation.pullbacks-subtypes.html#1786" class="Bound">B</a> <a id="1788" class="Symbol">:</a> <a id="1790" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1793" href="foundation.pullbacks-subtypes.html#1755" class="Bound">l2</a><a id="1795" class="Symbol">}</a> <a id="1797" class="Symbol">(</a><a id="1798" href="foundation.pullbacks-subtypes.html#1798" class="Bound">f</a> <a id="1800" class="Symbol">:</a> <a id="1802" href="foundation.pullbacks-subtypes.html#1774" class="Bound">A</a> <a id="1804" class="Symbol">→</a> <a id="1806" href="foundation.pullbacks-subtypes.html#1786" class="Bound">B</a><a id="1807" class="Symbol">)</a>
  <a id="1811" class="Symbol">(</a><a id="1812" href="foundation.pullbacks-subtypes.html#1812" class="Bound">T</a> <a id="1814" class="Symbol">:</a> <a id="1816" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1824" href="foundation.pullbacks-subtypes.html#1758" class="Bound">l3</a> <a id="1827" href="foundation.pullbacks-subtypes.html#1786" class="Bound">B</a><a id="1828" class="Symbol">)</a> <a id="1830" class="Symbol">(</a><a id="1831" href="foundation.pullbacks-subtypes.html#1831" class="Bound">S</a> <a id="1833" class="Symbol">:</a> <a id="1835" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1843" href="foundation.pullbacks-subtypes.html#1761" class="Bound">l4</a> <a id="1846" href="foundation.pullbacks-subtypes.html#1774" class="Bound">A</a><a id="1847" class="Symbol">)</a>
  <a id="1851" class="Keyword">where</a>

  <a id="1860" href="foundation.pullbacks-subtypes.html#1860" class="Function">is-pullback-subtype</a> <a id="1880" class="Symbol">:</a> <a id="1882" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1888" href="foundation.pullbacks-subtypes.html#1860" class="Function">is-pullback-subtype</a> <a id="1908" class="Symbol">=</a>
    <a id="1914" class="Symbol">{</a><a id="1915" href="foundation.pullbacks-subtypes.html#1915" class="Bound">l</a> <a id="1917" class="Symbol">:</a> <a id="1919" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1924" class="Symbol">}</a> <a id="1926" class="Symbol">(</a><a id="1927" href="foundation.pullbacks-subtypes.html#1927" class="Bound">U</a> <a id="1929" class="Symbol">:</a> <a id="1931" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1939" href="foundation.pullbacks-subtypes.html#1915" class="Bound">l</a> <a id="1941" href="foundation.pullbacks-subtypes.html#1774" class="Bound">A</a><a id="1942" class="Symbol">)</a> <a id="1944" class="Symbol">→</a>
    <a id="1950" class="Symbol">(</a><a id="1951" href="foundation.pullbacks-subtypes.html#1927" class="Bound">U</a> <a id="1953" href="foundation-core.subtypes.html#2877" class="Function Operator">⊆</a> <a id="1955" href="foundation.pullbacks-subtypes.html#1831" class="Bound">S</a><a id="1956" class="Symbol">)</a> <a id="1958" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="1960" class="Symbol">((</a><a id="1962" href="foundation.pullbacks-subtypes.html#1962" class="Bound">x</a> <a id="1964" class="Symbol">:</a> <a id="1966" href="foundation.pullbacks-subtypes.html#1774" class="Bound">A</a><a id="1967" class="Symbol">)</a> <a id="1969" class="Symbol">→</a> <a id="1971" href="foundation-core.subtypes.html#1596" class="Function">is-in-subtype</a> <a id="1985" href="foundation.pullbacks-subtypes.html#1927" class="Bound">U</a> <a id="1987" href="foundation.pullbacks-subtypes.html#1962" class="Bound">x</a> <a id="1989" class="Symbol">→</a> <a id="1991" href="foundation-core.subtypes.html#1596" class="Function">is-in-subtype</a> <a id="2005" href="foundation.pullbacks-subtypes.html#1812" class="Bound">T</a> <a id="2007" class="Symbol">(</a><a id="2008" href="foundation.pullbacks-subtypes.html#1798" class="Bound">f</a> <a id="2010" href="foundation.pullbacks-subtypes.html#1962" class="Bound">x</a><a id="2011" class="Symbol">))</a>
</pre>
### Pullbacks of subtypes

<pre class="Agda"><a id="2054" class="Keyword">module</a> <a id="2061" href="foundation.pullbacks-subtypes.html#2061" class="Module">_</a>
  <a id="2065" class="Symbol">{</a><a id="2066" href="foundation.pullbacks-subtypes.html#2066" class="Bound">l1</a> <a id="2069" href="foundation.pullbacks-subtypes.html#2069" class="Bound">l2</a> <a id="2072" href="foundation.pullbacks-subtypes.html#2072" class="Bound">l3</a> <a id="2075" class="Symbol">:</a> <a id="2077" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2082" class="Symbol">}</a> <a id="2084" class="Symbol">{</a><a id="2085" href="foundation.pullbacks-subtypes.html#2085" class="Bound">A</a> <a id="2087" class="Symbol">:</a> <a id="2089" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2092" href="foundation.pullbacks-subtypes.html#2066" class="Bound">l1</a><a id="2094" class="Symbol">}</a> <a id="2096" class="Symbol">{</a><a id="2097" href="foundation.pullbacks-subtypes.html#2097" class="Bound">B</a> <a id="2099" class="Symbol">:</a> <a id="2101" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2104" href="foundation.pullbacks-subtypes.html#2069" class="Bound">l2</a><a id="2106" class="Symbol">}</a> <a id="2108" class="Symbol">(</a><a id="2109" href="foundation.pullbacks-subtypes.html#2109" class="Bound">f</a> <a id="2111" class="Symbol">:</a> <a id="2113" href="foundation.pullbacks-subtypes.html#2085" class="Bound">A</a> <a id="2115" class="Symbol">→</a> <a id="2117" href="foundation.pullbacks-subtypes.html#2097" class="Bound">B</a><a id="2118" class="Symbol">)</a> <a id="2120" class="Symbol">(</a><a id="2121" href="foundation.pullbacks-subtypes.html#2121" class="Bound">T</a> <a id="2123" class="Symbol">:</a> <a id="2125" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="2133" href="foundation.pullbacks-subtypes.html#2072" class="Bound">l3</a> <a id="2136" href="foundation.pullbacks-subtypes.html#2097" class="Bound">B</a><a id="2137" class="Symbol">)</a>
  <a id="2141" class="Keyword">where</a>

  <a id="2150" href="foundation.pullbacks-subtypes.html#2150" class="Function">pullback-subtype</a> <a id="2167" class="Symbol">:</a> <a id="2169" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="2177" href="foundation.pullbacks-subtypes.html#2072" class="Bound">l3</a> <a id="2180" href="foundation.pullbacks-subtypes.html#2085" class="Bound">A</a>
  <a id="2184" href="foundation.pullbacks-subtypes.html#2150" class="Function">pullback-subtype</a> <a id="2201" class="Symbol">=</a> <a id="2203" href="foundation.pullbacks-subtypes.html#2121" class="Bound">T</a> <a id="2205" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2207" href="foundation.pullbacks-subtypes.html#2109" class="Bound">f</a>

  <a id="2212" href="foundation.pullbacks-subtypes.html#2212" class="Function">is-in-pullback-subtype</a> <a id="2235" class="Symbol">:</a> <a id="2237" href="foundation.pullbacks-subtypes.html#2085" class="Bound">A</a> <a id="2239" class="Symbol">→</a> <a id="2241" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2244" href="foundation.pullbacks-subtypes.html#2072" class="Bound">l3</a>
  <a id="2249" href="foundation.pullbacks-subtypes.html#2212" class="Function">is-in-pullback-subtype</a> <a id="2272" class="Symbol">=</a> <a id="2274" href="foundation-core.subtypes.html#1596" class="Function">is-in-subtype</a> <a id="2288" href="foundation.pullbacks-subtypes.html#2150" class="Function">pullback-subtype</a>

  <a id="2308" href="foundation.pullbacks-subtypes.html#2308" class="Function">is-prop-is-in-pullback-subtype</a> <a id="2339" class="Symbol">:</a>
    <a id="2345" class="Symbol">(</a><a id="2346" href="foundation.pullbacks-subtypes.html#2346" class="Bound">x</a> <a id="2348" class="Symbol">:</a> <a id="2350" href="foundation.pullbacks-subtypes.html#2085" class="Bound">A</a><a id="2351" class="Symbol">)</a> <a id="2353" class="Symbol">→</a> <a id="2355" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2363" class="Symbol">(</a><a id="2364" href="foundation.pullbacks-subtypes.html#2212" class="Function">is-in-pullback-subtype</a> <a id="2387" href="foundation.pullbacks-subtypes.html#2346" class="Bound">x</a><a id="2388" class="Symbol">)</a>
  <a id="2392" href="foundation.pullbacks-subtypes.html#2308" class="Function">is-prop-is-in-pullback-subtype</a> <a id="2423" class="Symbol">=</a> <a id="2425" href="foundation-core.subtypes.html#1661" class="Function">is-prop-is-in-subtype</a> <a id="2447" href="foundation.pullbacks-subtypes.html#2150" class="Function">pullback-subtype</a>

  <a id="2467" href="foundation.pullbacks-subtypes.html#2467" class="Function">type-pullback-subtype</a> <a id="2489" class="Symbol">:</a> <a id="2491" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2494" class="Symbol">(</a><a id="2495" href="foundation.pullbacks-subtypes.html#2066" class="Bound">l1</a> <a id="2498" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2500" href="foundation.pullbacks-subtypes.html#2072" class="Bound">l3</a><a id="2502" class="Symbol">)</a>
  <a id="2506" href="foundation.pullbacks-subtypes.html#2467" class="Function">type-pullback-subtype</a> <a id="2528" class="Symbol">=</a> <a id="2530" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="2543" href="foundation.pullbacks-subtypes.html#2150" class="Function">pullback-subtype</a>

  <a id="2563" href="foundation.pullbacks-subtypes.html#2563" class="Function">inclusion-pullback-subtype</a> <a id="2590" class="Symbol">:</a> <a id="2592" href="foundation.pullbacks-subtypes.html#2467" class="Function">type-pullback-subtype</a> <a id="2614" class="Symbol">→</a> <a id="2616" href="foundation.pullbacks-subtypes.html#2085" class="Bound">A</a>
  <a id="2620" href="foundation.pullbacks-subtypes.html#2563" class="Function">inclusion-pullback-subtype</a> <a id="2647" class="Symbol">=</a> <a id="2649" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a> <a id="2667" href="foundation.pullbacks-subtypes.html#2150" class="Function">pullback-subtype</a>
</pre>
### The order preserving pullback operation on subtypes

<pre class="Agda"><a id="2754" class="Keyword">module</a> <a id="2761" href="foundation.pullbacks-subtypes.html#2761" class="Module">_</a>
  <a id="2765" class="Symbol">{</a><a id="2766" href="foundation.pullbacks-subtypes.html#2766" class="Bound">l1</a> <a id="2769" href="foundation.pullbacks-subtypes.html#2769" class="Bound">l2</a> <a id="2772" class="Symbol">:</a> <a id="2774" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2779" class="Symbol">}</a> <a id="2781" class="Symbol">{</a><a id="2782" href="foundation.pullbacks-subtypes.html#2782" class="Bound">A</a> <a id="2784" class="Symbol">:</a> <a id="2786" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2789" href="foundation.pullbacks-subtypes.html#2766" class="Bound">l1</a><a id="2791" class="Symbol">}</a> <a id="2793" class="Symbol">{</a><a id="2794" href="foundation.pullbacks-subtypes.html#2794" class="Bound">B</a> <a id="2796" class="Symbol">:</a> <a id="2798" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2801" href="foundation.pullbacks-subtypes.html#2769" class="Bound">l2</a><a id="2803" class="Symbol">}</a> <a id="2805" class="Symbol">(</a><a id="2806" href="foundation.pullbacks-subtypes.html#2806" class="Bound">f</a> <a id="2808" class="Symbol">:</a> <a id="2810" href="foundation.pullbacks-subtypes.html#2782" class="Bound">A</a> <a id="2812" class="Symbol">→</a> <a id="2814" href="foundation.pullbacks-subtypes.html#2794" class="Bound">B</a><a id="2815" class="Symbol">)</a>
  <a id="2819" class="Keyword">where</a>

  <a id="2828" href="foundation.pullbacks-subtypes.html#2828" class="Function">preserves-order-pullback-subtype</a> <a id="2861" class="Symbol">:</a>
    <a id="2867" href="order-theory.order-preserving-maps-large-posets.html#1206" class="Function">preserves-order-map-Large-Poset</a>
      <a id="2905" class="Symbol">(</a> <a id="2907" href="foundation.powersets.html#2632" class="Function">powerset-Large-Poset</a> <a id="2928" href="foundation.pullbacks-subtypes.html#2794" class="Bound">B</a><a id="2929" class="Symbol">)</a>
      <a id="2937" class="Symbol">(</a> <a id="2939" href="foundation.powersets.html#2632" class="Function">powerset-Large-Poset</a> <a id="2960" href="foundation.pullbacks-subtypes.html#2782" class="Bound">A</a><a id="2961" class="Symbol">)</a>
      <a id="2969" class="Symbol">(</a> <a id="2971" href="foundation.pullbacks-subtypes.html#2150" class="Function">pullback-subtype</a> <a id="2988" href="foundation.pullbacks-subtypes.html#2806" class="Bound">f</a><a id="2989" class="Symbol">)</a>
  <a id="2993" href="foundation.pullbacks-subtypes.html#2828" class="Function">preserves-order-pullback-subtype</a> <a id="3026" href="foundation.pullbacks-subtypes.html#3026" class="Bound">S</a> <a id="3028" href="foundation.pullbacks-subtypes.html#3028" class="Bound">T</a> <a id="3030" href="foundation.pullbacks-subtypes.html#3030" class="Bound">H</a> <a id="3032" href="foundation.pullbacks-subtypes.html#3032" class="Bound">x</a> <a id="3034" class="Symbol">=</a> <a id="3036" href="foundation.pullbacks-subtypes.html#3030" class="Bound">H</a> <a id="3038" class="Symbol">(</a><a id="3039" href="foundation.pullbacks-subtypes.html#2806" class="Bound">f</a> <a id="3041" href="foundation.pullbacks-subtypes.html#3032" class="Bound">x</a><a id="3042" class="Symbol">)</a>

  <a id="3047" href="foundation.pullbacks-subtypes.html#3047" class="Function">pullback-subtype-hom-Large-Poset</a> <a id="3080" class="Symbol">:</a>
    <a id="3086" href="order-theory.order-preserving-maps-large-posets.html#1692" class="Function">hom-Large-Poset</a> <a id="3102" class="Symbol">(λ</a> <a id="3105" href="foundation.pullbacks-subtypes.html#3105" class="Bound">l</a> <a id="3107" class="Symbol">→</a> <a id="3109" href="foundation.pullbacks-subtypes.html#3105" class="Bound">l</a><a id="3110" class="Symbol">)</a> <a id="3112" class="Symbol">(</a><a id="3113" href="foundation.powersets.html#2632" class="Function">powerset-Large-Poset</a> <a id="3134" href="foundation.pullbacks-subtypes.html#2794" class="Bound">B</a><a id="3135" class="Symbol">)</a> <a id="3137" class="Symbol">(</a><a id="3138" href="foundation.powersets.html#2632" class="Function">powerset-Large-Poset</a> <a id="3159" href="foundation.pullbacks-subtypes.html#2782" class="Bound">A</a><a id="3160" class="Symbol">)</a>
  <a id="3164" href="order-theory.order-preserving-maps-large-preorders.html#1956" class="Field">map-hom-Large-Preorder</a> <a id="3187" href="foundation.pullbacks-subtypes.html#3047" class="Function">pullback-subtype-hom-Large-Poset</a> <a id="3220" class="Symbol">=</a>
    <a id="3226" href="foundation.pullbacks-subtypes.html#2150" class="Function">pullback-subtype</a> <a id="3243" href="foundation.pullbacks-subtypes.html#2806" class="Bound">f</a>
  <a id="3247" href="order-theory.order-preserving-maps-large-preorders.html#2066" class="Field">preserves-order-hom-Large-Preorder</a> <a id="3282" href="foundation.pullbacks-subtypes.html#3047" class="Function">pullback-subtype-hom-Large-Poset</a> <a id="3315" class="Symbol">=</a>
    <a id="3321" href="foundation.pullbacks-subtypes.html#2828" class="Function">preserves-order-pullback-subtype</a>
</pre>
## See also

- The [image of a subtype](foundation.images-subtypes.md)
