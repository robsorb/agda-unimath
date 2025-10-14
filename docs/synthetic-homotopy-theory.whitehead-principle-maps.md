# The Whitehead principle for maps

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="synthetic-homotopy-theory.whitehead-principle-maps.html" class="Module">synthetic-homotopy-theory.whitehead-principle-maps</a> <a id="103" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="159" class="Keyword">open</a> <a id="164" class="Keyword">import</a> <a id="171" href="foundation.connected-maps.html" class="Module">foundation.connected-maps</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="318" class="Keyword">open</a> <a id="323" class="Keyword">import</a> <a id="330" href="foundation.infinity-connected-maps.html" class="Module">foundation.infinity-connected-maps</a>
<a id="365" class="Keyword">open</a> <a id="370" class="Keyword">import</a> <a id="377" href="foundation.infinity-connected-types.html" class="Module">foundation.infinity-connected-types</a>
<a id="413" class="Keyword">open</a> <a id="418" class="Keyword">import</a> <a id="425" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="454" class="Keyword">open</a> <a id="459" class="Keyword">import</a> <a id="466" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="489" class="Keyword">open</a> <a id="494" class="Keyword">import</a> <a id="501" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="522" class="Keyword">open</a> <a id="527" class="Keyword">import</a> <a id="534" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="562" class="Keyword">open</a> <a id="567" class="Keyword">import</a> <a id="574" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="608" class="Keyword">open</a> <a id="613" class="Keyword">import</a> <a id="620" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="655" class="Keyword">open</a> <a id="660" class="Keyword">import</a> <a id="667" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="696" class="Keyword">open</a> <a id="701" class="Keyword">import</a> <a id="708" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="739" class="Keyword">open</a> <a id="744" class="Keyword">import</a> <a id="751" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>

<a id="781" class="Keyword">open</a> <a id="786" class="Keyword">import</a> <a id="793" href="synthetic-homotopy-theory.whitehead-principle-types.html" class="Module">synthetic-homotopy-theory.whitehead-principle-types</a>
</pre>
</details>

## Idea

The {{#concept "Whitehead principle for maps" Agda=Whitehead-Principle-Map}}
asserts that [∞-connected maps](foundation.infinity-connected-maps.md) are
[equivalences](foundation-core.equivalences.md). I.e., if the
[fibers](foundation-core.fibers-of-maps.md) of a map `f : X → Y` are
[∞-connected](foundation.infinity-connected-types.md), then it is an
equivalence. This principle is also referred to as _hypercompleteness_ and is
not validated in every ∞-topos.

## Definition

<pre class="Agda"><a id="Whitehead-Principle-Map-Level"></a><a id="1357" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1357" class="Function">Whitehead-Principle-Map-Level</a> <a id="1387" class="Symbol">:</a> <a id="1389" class="Symbol">(</a><a id="1390" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1390" class="Bound">l1</a> <a id="1393" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1393" class="Bound">l2</a> <a id="1396" class="Symbol">:</a> <a id="1398" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1403" class="Symbol">)</a> <a id="1405" class="Symbol">→</a> <a id="1407" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1410" class="Symbol">(</a><a id="1411" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1416" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1390" class="Bound">l1</a> <a id="1419" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1421" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1426" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1393" class="Bound">l2</a><a id="1428" class="Symbol">)</a>
<a id="1430" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1357" class="Function">Whitehead-Principle-Map-Level</a> <a id="1460" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1460" class="Bound">l1</a> <a id="1463" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1463" class="Bound">l2</a> <a id="1466" class="Symbol">=</a>
  <a id="1470" class="Symbol">(</a> <a id="1472" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1472" class="Bound">X</a> <a id="1474" class="Symbol">:</a> <a id="1476" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1479" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1460" class="Bound">l1</a><a id="1481" class="Symbol">)</a> <a id="1483" class="Symbol">→</a> <a id="1485" class="Symbol">(</a><a id="1486" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1486" class="Bound">Y</a> <a id="1488" class="Symbol">:</a> <a id="1490" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1493" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1463" class="Bound">l2</a><a id="1495" class="Symbol">)</a> <a id="1497" class="Symbol">→</a> <a id="1499" class="Symbol">(</a><a id="1500" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1500" class="Bound">f</a> <a id="1502" class="Symbol">:</a> <a id="1504" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1472" class="Bound">X</a> <a id="1506" class="Symbol">→</a> <a id="1508" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1486" class="Bound">Y</a><a id="1509" class="Symbol">)</a> <a id="1511" class="Symbol">→</a> <a id="1513" href="foundation.infinity-connected-maps.html#1376" class="Function">is-∞-connected-map</a> <a id="1532" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1500" class="Bound">f</a> <a id="1534" class="Symbol">→</a> <a id="1536" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1545" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1500" class="Bound">f</a>

<a id="Whitehead-Principle-Map"></a><a id="1548" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1548" class="Function">Whitehead-Principle-Map</a> <a id="1572" class="Symbol">:</a> <a id="1574" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
<a id="1578" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1548" class="Function">Whitehead-Principle-Map</a> <a id="1602" class="Symbol">=</a> <a id="1604" class="Symbol">{</a><a id="1605" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1605" class="Bound">l1</a> <a id="1608" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1608" class="Bound">l2</a> <a id="1611" class="Symbol">:</a> <a id="1613" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1618" class="Symbol">}</a> <a id="1620" class="Symbol">→</a> <a id="1622" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1357" class="Function">Whitehead-Principle-Map-Level</a> <a id="1652" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1605" class="Bound">l1</a> <a id="1655" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1608" class="Bound">l2</a>
</pre>
## Properties

### The Whitehead principle for maps implies the Whitehead principle for types

<pre class="Agda"><a id="Whitehead-Principle-Maps-implies-Types"></a><a id="1766" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1766" class="Function">Whitehead-Principle-Maps-implies-Types</a> <a id="1805" class="Symbol">:</a>
  <a id="1809" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1548" class="Function">Whitehead-Principle-Map</a> <a id="1833" class="Symbol">→</a> <a id="1835" href="synthetic-homotopy-theory.whitehead-principle-types.html#1629" class="Function">Whitehead-Principle</a>
<a id="1855" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1766" class="Function">Whitehead-Principle-Maps-implies-Types</a> <a id="1894" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1894" class="Bound">WP</a> <a id="1897" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1897" class="Bound">X</a> <a id="1899" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1899" class="Bound">is-∞-conn-X</a> <a id="1911" class="Symbol">=</a>
  <a id="1915" href="foundation.unit-type.html#3066" class="Function">is-contr-equiv-unit</a> <a id="1935" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1950" class="Function">eq</a>
  <a id="1940" class="Keyword">where</a>
    <a id="1950" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1950" class="Function">eq</a> <a id="1953" class="Symbol">:</a> <a id="1955" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1897" class="Bound">X</a> <a id="1957" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1959" href="foundation.unit-type.html#950" class="Record">unit</a>
    <a id="1968" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1972" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1950" class="Function">eq</a> <a id="1975" class="Symbol">=</a> <a id="1977" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="1990" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1897" class="Bound">X</a>
    <a id="1996" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2000" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1950" class="Function">eq</a> <a id="2003" class="Symbol">=</a>
      <a id="2011" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1894" class="Bound">WP</a> <a id="2014" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1897" class="Bound">X</a> <a id="2016" href="foundation.unit-type.html#950" class="Record">unit</a> <a id="2021" class="Symbol">(</a><a id="2022" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="2035" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1897" class="Bound">X</a><a id="2036" class="Symbol">)</a>
        <a id="2046" class="Symbol">(</a> <a id="2048" class="Symbol">λ</a> <a id="2050" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2050" class="Bound">x</a> <a id="2052" class="Symbol">→</a> <a id="2054" href="foundation.infinity-connected-types.html#1879" class="Function">is-∞-connected-equiv</a>
          <a id="2085" class="Symbol">(</a> <a id="2087" href="foundation.fibers-of-maps.html#2027" class="Function">equiv-fiber-terminal-map</a> <a id="2112" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="2116" class="Symbol">)</a> <a id="2118" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1899" class="Bound">is-∞-conn-X</a><a id="2129" class="Symbol">)</a>
</pre>
### The Whitehead principle for types implies the Whitehead principle for maps

<pre class="Agda"><a id="Whitehead-Principle-Types-implies-Maps"></a><a id="2224" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2224" class="Function">Whitehead-Principle-Types-implies-Maps</a> <a id="2263" class="Symbol">:</a>
  <a id="2267" href="synthetic-homotopy-theory.whitehead-principle-types.html#1629" class="Function">Whitehead-Principle</a> <a id="2287" class="Symbol">→</a> <a id="2289" href="synthetic-homotopy-theory.whitehead-principle-maps.html#1548" class="Function">Whitehead-Principle-Map</a>
<a id="2313" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2224" class="Function">Whitehead-Principle-Types-implies-Maps</a> <a id="2352" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2352" class="Bound">WP</a> <a id="2355" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2355" class="Bound">X</a> <a id="2357" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2357" class="Bound">Y</a> <a id="2359" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2359" class="Bound">f</a> <a id="2361" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2361" class="Bound">is-∞-conn-f</a> <a id="2373" class="Symbol">=</a>
  <a id="2377" href="foundation-core.contractible-maps.html#2276" class="Function">is-equiv-is-contr-map</a> <a id="2399" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2426" class="Function">is-contr-map-f</a>
  <a id="2416" class="Keyword">where</a>
    <a id="2426" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2426" class="Function">is-contr-map-f</a> <a id="2441" class="Symbol">:</a> <a id="2443" href="foundation-core.contractible-maps.html#1162" class="Function">is-contr-map</a> <a id="2456" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2359" class="Bound">f</a>
    <a id="2462" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2426" class="Function">is-contr-map-f</a> <a id="2477" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2477" class="Bound">y</a> <a id="2479" class="Symbol">=</a> <a id="2481" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2352" class="Bound">WP</a> <a id="2484" class="Symbol">(</a><a id="2485" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="2491" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2359" class="Bound">f</a> <a id="2493" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2477" class="Bound">y</a><a id="2494" class="Symbol">)</a> <a id="2496" class="Symbol">(λ</a> <a id="2499" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2499" class="Bound">x</a> <a id="2501" class="Symbol">→</a> <a id="2503" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2361" class="Bound">is-∞-conn-f</a> <a id="2515" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2477" class="Bound">y</a> <a id="2517" href="synthetic-homotopy-theory.whitehead-principle-maps.html#2499" class="Bound">x</a><a id="2518" class="Symbol">)</a>
</pre>
## External links

- [hypercomplete object](https://ncatlab.org/nlab/show/hypercomplete+object) on
  $n$Lab
- [Whitehead theorem](https://en.m.wikipedia.org/w/index.php?title=Whitehead_theorem)
  on Wikipedia

## References

For the equivalent concept in the ∞-categorical semantics of homotopy type
theory, cf. §6.5.2 of Lurie's _Higher Topos Theory_ {{#cite Lurie09}}.

{{#bibliography}}
