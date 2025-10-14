# The universal property of flat discrete crisp types

<pre class="Agda"><a id="64" class="Symbol">{-#</a> <a id="68" class="Keyword">OPTIONS</a> <a id="76" class="Pragma">--cohesion</a> <a id="87" class="Pragma">--flat-split</a> <a id="100" class="Symbol">#-}</a>

<a id="105" class="Keyword">module</a> <a id="112" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html" class="Module">modal-type-theory.universal-property-flat-discrete-crisp-types</a> <a id="175" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="334" class="Keyword">open</a> <a id="339" class="Keyword">import</a> <a id="346" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="455" class="Keyword">open</a> <a id="460" class="Keyword">import</a> <a id="467" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="foundation.postcomposition-functions.html" class="Module">foundation.postcomposition-functions</a>
<a id="542" class="Keyword">open</a> <a id="547" class="Keyword">import</a> <a id="554" href="foundation.universal-property-equivalences.html" class="Module">foundation.universal-property-equivalences</a>
<a id="597" class="Keyword">open</a> <a id="602" class="Keyword">import</a> <a id="609" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="modal-type-theory.action-on-identifications-crisp-functions.html" class="Module">modal-type-theory.action-on-identifications-crisp-functions</a>
<a id="709" class="Keyword">open</a> <a id="714" class="Keyword">import</a> <a id="721" href="modal-type-theory.crisp-function-types.html" class="Module">modal-type-theory.crisp-function-types</a>
<a id="760" class="Keyword">open</a> <a id="765" class="Keyword">import</a> <a id="772" href="modal-type-theory.flat-discrete-crisp-types.html" class="Module">modal-type-theory.flat-discrete-crisp-types</a>
<a id="816" class="Keyword">open</a> <a id="821" class="Keyword">import</a> <a id="828" href="modal-type-theory.flat-modality.html" class="Module">modal-type-theory.flat-modality</a>
<a id="860" class="Keyword">open</a> <a id="865" class="Keyword">import</a> <a id="872" href="modal-type-theory.functoriality-flat-modality.html" class="Module">modal-type-theory.functoriality-flat-modality</a>
</pre>
</details>

## Idea

The
{{#concept "universal property" Disambiguation="of flat discrete crisp types" Agda=universal-property-flat-discrete-crisp-type}}
of a [flat discrete crisp type](modal-type-theory.flat-discrete-crisp-types.md)
`A` states that under the [flat modality](modal-type-theory.flat-modality.md)
`♭`, `A` is [colocal](orthogonal-factorization-systems.types-colocal-at-maps.md)
at the counit of `♭`.

By this we mean that for every [crisp type](modal-type-theory.crisp-types.md)
`B` the map

```text
  coev-flat : ♭ (A → ♭ B) → ♭ (A → B)
```

is an [equivalence](foundation-core.equivalences.md).

## Definitions

### The universal property of flat discrete crisp types

<pre class="Agda"><a id="coev-flat"></a><a id="1617" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1617" class="Function">coev-flat</a> <a id="1627" class="Symbol">:</a>
  <a id="1631" class="Symbol">{@</a>♭ <a id="1635" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1635" class="Bound">l1</a> <a id="1638" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1638" class="Bound">l2</a> <a id="1641" class="Symbol">:</a> <a id="1643" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1648" class="Symbol">}</a> <a id="1650" class="Symbol">{@</a>♭ <a id="1654" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1654" class="Bound">A</a> <a id="1656" class="Symbol">:</a> <a id="1658" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1661" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1635" class="Bound">l1</a><a id="1663" class="Symbol">}</a> <a id="1665" class="Symbol">{@</a>♭ <a id="1669" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1669" class="Bound">B</a> <a id="1671" class="Symbol">:</a> <a id="1673" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1676" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1638" class="Bound">l2</a><a id="1678" class="Symbol">}</a> <a id="1680" class="Symbol">→</a> <a id="1682" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="1684" class="Symbol">(</a><a id="1685" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1654" class="Bound">A</a> <a id="1687" class="Symbol">→</a> <a id="1689" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="1691" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1669" class="Bound">B</a><a id="1692" class="Symbol">)</a> <a id="1694" class="Symbol">→</a> <a id="1696" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="1698" class="Symbol">(</a><a id="1699" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1654" class="Bound">A</a> <a id="1701" class="Symbol">→</a> <a id="1703" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1669" class="Bound">B</a><a id="1704" class="Symbol">)</a>
<a id="1706" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1617" class="Function">coev-flat</a> <a id="1716" class="Symbol">{</a><a id="1717" class="Argument">A</a> <a id="1719" class="Symbol">=</a> <a id="1721" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1721" class="Bound">A</a><a id="1722" class="Symbol">}</a> <a id="1724" class="Symbol">(</a><a id="1725" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="1736" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1736" class="Bound">f</a><a id="1737" class="Symbol">)</a> <a id="1739" class="Symbol">=</a> <a id="1741" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="1752" class="Symbol">(</a><a id="1753" href="foundation-core.postcomposition-functions.html#551" class="Function">postcomp</a> <a id="1762" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1721" class="Bound">A</a> <a id="1764" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a> <a id="1776" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1736" class="Bound">f</a><a id="1777" class="Symbol">)</a>

<a id="universal-property-flat-discrete-crisp-type"></a><a id="1780" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1780" class="Function">universal-property-flat-discrete-crisp-type</a> <a id="1824" class="Symbol">:</a>
  <a id="1828" class="Symbol">{@</a>♭ <a id="1832" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1832" class="Bound">l1</a> <a id="1835" class="Symbol">:</a> <a id="1837" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1842" class="Symbol">}</a> <a id="1844" class="Symbol">(@</a>♭ <a id="1848" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1848" class="Bound">A</a> <a id="1850" class="Symbol">:</a> <a id="1852" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1855" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1832" class="Bound">l1</a><a id="1857" class="Symbol">)</a> <a id="1859" class="Symbol">→</a> <a id="1861" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
<a id="1865" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1780" class="Function">universal-property-flat-discrete-crisp-type</a> <a id="1909" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1909" class="Bound">A</a> <a id="1911" class="Symbol">=</a>
  <a id="1915" class="Symbol">{@</a>♭ <a id="1919" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1919" class="Bound">l</a> <a id="1921" class="Symbol">:</a> <a id="1923" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1928" class="Symbol">}</a> <a id="1930" class="Symbol">{@</a>♭ <a id="1934" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1934" class="Bound">B</a> <a id="1936" class="Symbol">:</a> <a id="1938" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1941" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1919" class="Bound">l</a><a id="1942" class="Symbol">}</a> <a id="1944" class="Symbol">→</a> <a id="1946" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1955" class="Symbol">(</a><a id="1956" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1617" class="Function">coev-flat</a> <a id="1966" class="Symbol">{</a><a id="1967" class="Argument">A</a> <a id="1969" class="Symbol">=</a> <a id="1971" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1909" class="Bound">A</a><a id="1972" class="Symbol">}</a> <a id="1974" class="Symbol">{</a><a id="1975" class="Argument">B</a> <a id="1977" class="Symbol">=</a> <a id="1979" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1934" class="Bound">B</a><a id="1980" class="Symbol">})</a>
</pre>
## Properties

### Flat discrete crisp types satisfy the universal property of flat discrete crisp types

This is Corollary 6.15 of {{#cite Shu18}}.

<pre class="Agda"><a id="2146" class="Keyword">module</a> <a id="2153" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2153" class="Module">_</a>
  <a id="2157" class="Symbol">{@</a>♭ <a id="2161" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2161" class="Bound">l</a> <a id="2163" class="Symbol">:</a> <a id="2165" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2170" class="Symbol">}</a> <a id="2172" class="Symbol">{@</a>♭ <a id="2176" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2176" class="Bound">A</a> <a id="2178" class="Symbol">:</a> <a id="2180" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2183" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2161" class="Bound">l</a><a id="2184" class="Symbol">}</a>
  <a id="2188" class="Keyword">where</a>

  <a id="2197" class="Keyword">abstract</a>
    <a id="2210" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2210" class="Function">universal-property-is-flat-discrete-crisp</a> <a id="2252" class="Symbol">:</a>
      <a id="2260" class="Symbol">@</a>♭ <a id="2263" href="modal-type-theory.flat-discrete-crisp-types.html#1882" class="Function">is-flat-discrete-crisp</a> <a id="2286" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2176" class="Bound">A</a> <a id="2288" class="Symbol">→</a>
      <a id="2296" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#1780" class="Function">universal-property-flat-discrete-crisp-type</a> <a id="2340" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2176" class="Bound">A</a>
    <a id="2346" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2210" class="Function">universal-property-is-flat-discrete-crisp</a>
      <a id="2394" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2394" class="Bound">is-disc-A</a> <a id="2404" class="Symbol">{</a><a id="2405" class="Argument">B</a> <a id="2407" class="Symbol">=</a> <a id="2409" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2409" class="Bound">B</a><a id="2410" class="Symbol">}</a> <a id="2412" class="Symbol">=</a>
      <a id="2420" href="foundation-core.equivalences.html#14856" class="Function">is-equiv-htpy-equiv</a>
        <a id="2448" class="Symbol">(</a> <a id="2450" class="Symbol">(</a> <a id="2452" href="modal-type-theory.functoriality-flat-modality.html#4863" class="Function">action-flat-equiv</a>
            <a id="2482" class="Symbol">(</a> <a id="2484" href="foundation.universal-property-equivalences.html#2020" class="Function">equiv-precomp</a> <a id="2498" class="Symbol">(</a><a id="2499" href="foundation-core.equivalences.html#8859" class="Function">inv-equiv</a> <a id="2509" class="Symbol">(</a><a id="2510" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a> <a id="2522" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2524" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2394" class="Bound">is-disc-A</a><a id="2533" class="Symbol">))</a> <a id="2536" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2409" class="Bound">B</a><a id="2537" class="Symbol">))</a> <a id="2540" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
          <a id="2553" class="Symbol">(</a> <a id="2555" href="modal-type-theory.crisp-function-types.html#4362" class="Function">equiv-action-flat-map-postcomp-counit-flat</a><a id="2597" class="Symbol">)</a> <a id="2599" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
          <a id="2612" class="Symbol">(</a> <a id="2614" href="modal-type-theory.functoriality-flat-modality.html#4863" class="Function">action-flat-equiv</a> <a id="2632" class="Symbol">(</a><a id="2633" href="foundation.universal-property-equivalences.html#2020" class="Function">equiv-precomp</a> <a id="2647" class="Symbol">(</a><a id="2648" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a> <a id="2660" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2662" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2394" class="Bound">is-disc-A</a><a id="2671" class="Symbol">)</a> <a id="2673" class="Symbol">(</a><a id="2674" href="modal-type-theory.flat-modality.html#614" class="Datatype">♭</a> <a id="2676" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2409" class="Bound">B</a><a id="2677" class="Symbol">))))</a>
        <a id="2690" class="Symbol">(</a> <a id="2692" class="Symbol">λ</a> <a id="2694" class="Keyword">where</a>
          <a id="2710" class="Symbol">(</a><a id="2711" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a> <a id="2722" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2722" class="Bound">f</a><a id="2723" class="Symbol">)</a> <a id="2725" class="Symbol">→</a>
            <a id="2739" href="modal-type-theory.action-on-identifications-crisp-functions.html#1102" class="Function">crisp-ap</a>
              <a id="2762" class="Symbol">(</a> <a id="2764" href="modal-type-theory.flat-modality.html#660" class="InductiveConstructor">intro-flat</a><a id="2774" class="Symbol">)</a>
              <a id="2790" class="Symbol">(</a> <a id="2792" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a>
                <a id="2816" class="Symbol">(</a> <a id="2818" class="Symbol">λ</a> <a id="2820" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2820" class="Bound">x</a> <a id="2822" class="Symbol">→</a>
                  <a id="2842" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
                    <a id="2865" class="Symbol">(</a> <a id="2867" href="modal-type-theory.flat-modality.html#771" class="Function">counit-flat</a> <a id="2879" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2881" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2722" class="Bound">f</a><a id="2882" class="Symbol">)</a>
                    <a id="2904" class="Symbol">(</a> <a id="2906" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="2910" class="Symbol">(</a><a id="2911" href="foundation-core.equivalences.html#7065" class="Function">is-section-map-inv-is-equiv</a> <a id="2939" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2394" class="Bound">is-disc-A</a> <a id="2949" href="modal-type-theory.universal-property-flat-discrete-crisp-types.html#2820" class="Bound">x</a><a id="2950" class="Symbol">)))))</a>
</pre>
## See also

- [The dependent universal property of flat discrete crisp types](modal-type-theory.dependent-universal-property-flat-discrete-crisp-types.md)

## References

{{#bibliography}} {{#reference Shu18}}
