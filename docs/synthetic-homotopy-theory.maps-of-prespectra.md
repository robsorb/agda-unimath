# Maps of prespectra

<pre class="Agda"><a id="31" class="Symbol">{-#</a> <a id="35" class="Keyword">OPTIONS</a> <a id="43" class="Pragma">--guardedness</a> <a id="57" class="Symbol">#-}</a>

<a id="62" class="Keyword">module</a> <a id="69" href="synthetic-homotopy-theory.maps-of-prespectra.html" class="Module">synthetic-homotopy-theory.maps-of-prespectra</a> <a id="114" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="structured-types.commuting-squares-of-pointed-maps.html" class="Module">structured-types.commuting-squares-of-pointed-maps</a>
<a id="464" class="Keyword">open</a> <a id="469" class="Keyword">import</a> <a id="476" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="512" class="Keyword">open</a> <a id="517" class="Keyword">import</a> <a id="524" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="554" class="Keyword">open</a> <a id="559" class="Keyword">import</a> <a id="566" href="structured-types.whiskering-pointed-homotopies-composition.html" class="Module">structured-types.whiskering-pointed-homotopies-composition</a>
<a id="625" class="Keyword">open</a> <a id="630" class="Keyword">import</a> <a id="637" href="structured-types.wild-category-of-pointed-types.html" class="Module">structured-types.wild-category-of-pointed-types</a>

<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="synthetic-homotopy-theory.functoriality-loop-spaces.html" class="Module">synthetic-homotopy-theory.functoriality-loop-spaces</a>
<a id="750" class="Keyword">open</a> <a id="755" class="Keyword">import</a> <a id="762" href="synthetic-homotopy-theory.prespectra.html" class="Module">synthetic-homotopy-theory.prespectra</a>
</pre>
</details>

## Idea

A {{#concept "map" Disambiguation="of prespectra" Agda=map-Prespectrum}} of
[prespectra](synthetic-homotopy-theory.prespectra.md) `f : A → B` is a
[sequence](lists.dependent-sequences.md) of
[pointed maps](structured-types.pointed-maps.md)

```text
  fₙ : Aₙ →∗ Bₙ
```

such that the squares

```text
        fₙ
  Aₙ --------> Bₙ
  |            |
  |            |
  |            |
  ∨            ∨
  ΩAₙ₊₁ -----> ΩBₙ₊₁
        Ωfₙ₊₁
```

commute in the
[category of pointed types](structured-types.wild-category-of-pointed-types.md).

## Definitions

### Maps of prespectra

<pre class="Agda"><a id="coherence-map-Prespectrum"></a><a id="1408" href="synthetic-homotopy-theory.maps-of-prespectra.html#1408" class="Function">coherence-map-Prespectrum</a> <a id="1434" class="Symbol">:</a>
  <a id="1438" class="Symbol">{</a><a id="1439" href="synthetic-homotopy-theory.maps-of-prespectra.html#1439" class="Bound">l1</a> <a id="1442" href="synthetic-homotopy-theory.maps-of-prespectra.html#1442" class="Bound">l2</a> <a id="1445" class="Symbol">:</a> <a id="1447" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1452" class="Symbol">}</a> <a id="1454" class="Symbol">(</a><a id="1455" href="synthetic-homotopy-theory.maps-of-prespectra.html#1455" class="Bound">A</a> <a id="1457" class="Symbol">:</a> <a id="1459" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1471" href="synthetic-homotopy-theory.maps-of-prespectra.html#1439" class="Bound">l1</a><a id="1473" class="Symbol">)</a> <a id="1475" class="Symbol">(</a><a id="1476" href="synthetic-homotopy-theory.maps-of-prespectra.html#1476" class="Bound">B</a> <a id="1478" class="Symbol">:</a> <a id="1480" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1492" href="synthetic-homotopy-theory.maps-of-prespectra.html#1442" class="Bound">l2</a><a id="1494" class="Symbol">)</a> <a id="1496" class="Symbol">→</a>
  <a id="1500" class="Symbol">(</a> <a id="1502" class="Symbol">(</a><a id="1503" href="synthetic-homotopy-theory.maps-of-prespectra.html#1503" class="Bound">n</a> <a id="1505" class="Symbol">:</a> <a id="1507" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1508" class="Symbol">)</a> <a id="1510" class="Symbol">→</a>
    <a id="1516" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="1541" href="synthetic-homotopy-theory.maps-of-prespectra.html#1455" class="Bound">A</a> <a id="1543" href="synthetic-homotopy-theory.maps-of-prespectra.html#1503" class="Bound">n</a> <a id="1545" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1548" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="1573" href="synthetic-homotopy-theory.maps-of-prespectra.html#1476" class="Bound">B</a> <a id="1575" href="synthetic-homotopy-theory.maps-of-prespectra.html#1503" class="Bound">n</a><a id="1576" class="Symbol">)</a> <a id="1578" class="Symbol">→</a>
  <a id="1582" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1585" class="Symbol">(</a><a id="1586" href="synthetic-homotopy-theory.maps-of-prespectra.html#1439" class="Bound">l1</a> <a id="1589" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1591" href="synthetic-homotopy-theory.maps-of-prespectra.html#1442" class="Bound">l2</a><a id="1593" class="Symbol">)</a>
<a id="1595" href="synthetic-homotopy-theory.maps-of-prespectra.html#1408" class="Function">coherence-map-Prespectrum</a> <a id="1621" href="synthetic-homotopy-theory.maps-of-prespectra.html#1621" class="Bound">A</a> <a id="1623" href="synthetic-homotopy-theory.maps-of-prespectra.html#1623" class="Bound">B</a> <a id="1625" href="synthetic-homotopy-theory.maps-of-prespectra.html#1625" class="Bound">f</a> <a id="1627" class="Symbol">=</a>
  <a id="1631" class="Symbol">(</a><a id="1632" href="synthetic-homotopy-theory.maps-of-prespectra.html#1632" class="Bound">n</a> <a id="1634" class="Symbol">:</a> <a id="1636" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1637" class="Symbol">)</a> <a id="1639" class="Symbol">→</a>
  <a id="1643" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a>
    <a id="1677" class="Symbol">(</a> <a id="1679" href="synthetic-homotopy-theory.maps-of-prespectra.html#1625" class="Bound">f</a> <a id="1681" href="synthetic-homotopy-theory.maps-of-prespectra.html#1632" class="Bound">n</a><a id="1682" class="Symbol">)</a>
    <a id="1688" class="Symbol">(</a> <a id="1690" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="1732" href="synthetic-homotopy-theory.maps-of-prespectra.html#1621" class="Bound">A</a> <a id="1734" href="synthetic-homotopy-theory.maps-of-prespectra.html#1632" class="Bound">n</a><a id="1735" class="Symbol">)</a>
    <a id="1741" class="Symbol">(</a> <a id="1743" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="1785" href="synthetic-homotopy-theory.maps-of-prespectra.html#1623" class="Bound">B</a> <a id="1787" href="synthetic-homotopy-theory.maps-of-prespectra.html#1632" class="Bound">n</a><a id="1788" class="Symbol">)</a>
    <a id="1794" class="Symbol">(</a> <a id="1796" href="synthetic-homotopy-theory.functoriality-loop-spaces.html#1443" class="Function">pointed-map-Ω</a> <a id="1810" class="Symbol">(</a><a id="1811" href="synthetic-homotopy-theory.maps-of-prespectra.html#1625" class="Bound">f</a> <a id="1813" class="Symbol">(</a><a id="1814" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1821" href="synthetic-homotopy-theory.maps-of-prespectra.html#1632" class="Bound">n</a><a id="1822" class="Symbol">)))</a>

<a id="map-Prespectrum"></a><a id="1827" href="synthetic-homotopy-theory.maps-of-prespectra.html#1827" class="Function">map-Prespectrum</a> <a id="1843" class="Symbol">:</a>
  <a id="1847" class="Symbol">{</a><a id="1848" href="synthetic-homotopy-theory.maps-of-prespectra.html#1848" class="Bound">l1</a> <a id="1851" href="synthetic-homotopy-theory.maps-of-prespectra.html#1851" class="Bound">l2</a> <a id="1854" class="Symbol">:</a> <a id="1856" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1861" class="Symbol">}</a> <a id="1863" class="Symbol">(</a><a id="1864" href="synthetic-homotopy-theory.maps-of-prespectra.html#1864" class="Bound">A</a> <a id="1866" class="Symbol">:</a> <a id="1868" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1880" href="synthetic-homotopy-theory.maps-of-prespectra.html#1848" class="Bound">l1</a><a id="1882" class="Symbol">)</a> <a id="1884" class="Symbol">(</a><a id="1885" href="synthetic-homotopy-theory.maps-of-prespectra.html#1885" class="Bound">B</a> <a id="1887" class="Symbol">:</a> <a id="1889" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1901" href="synthetic-homotopy-theory.maps-of-prespectra.html#1851" class="Bound">l2</a><a id="1903" class="Symbol">)</a> <a id="1905" class="Symbol">→</a>
  <a id="1909" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1912" class="Symbol">(</a><a id="1913" href="synthetic-homotopy-theory.maps-of-prespectra.html#1848" class="Bound">l1</a> <a id="1916" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1918" href="synthetic-homotopy-theory.maps-of-prespectra.html#1851" class="Bound">l2</a><a id="1920" class="Symbol">)</a>
<a id="1922" href="synthetic-homotopy-theory.maps-of-prespectra.html#1827" class="Function">map-Prespectrum</a> <a id="1938" href="synthetic-homotopy-theory.maps-of-prespectra.html#1938" class="Bound">A</a> <a id="1940" href="synthetic-homotopy-theory.maps-of-prespectra.html#1940" class="Bound">B</a> <a id="1942" class="Symbol">=</a>
  <a id="1946" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1948" class="Symbol">(</a> <a id="1950" class="Symbol">(</a><a id="1951" href="synthetic-homotopy-theory.maps-of-prespectra.html#1951" class="Bound">n</a> <a id="1953" class="Symbol">:</a> <a id="1955" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1956" class="Symbol">)</a> <a id="1958" class="Symbol">→</a>
      <a id="1966" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="1991" href="synthetic-homotopy-theory.maps-of-prespectra.html#1938" class="Bound">A</a> <a id="1993" href="synthetic-homotopy-theory.maps-of-prespectra.html#1951" class="Bound">n</a> <a id="1995" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1998" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2023" href="synthetic-homotopy-theory.maps-of-prespectra.html#1940" class="Bound">B</a> <a id="2025" href="synthetic-homotopy-theory.maps-of-prespectra.html#1951" class="Bound">n</a><a id="2026" class="Symbol">)</a>
    <a id="2032" class="Symbol">(</a> <a id="2034" class="Symbol">λ</a> <a id="2036" href="synthetic-homotopy-theory.maps-of-prespectra.html#2036" class="Bound">f</a> <a id="2038" class="Symbol">→</a> <a id="2040" href="synthetic-homotopy-theory.maps-of-prespectra.html#1408" class="Function">coherence-map-Prespectrum</a> <a id="2066" href="synthetic-homotopy-theory.maps-of-prespectra.html#1938" class="Bound">A</a> <a id="2068" href="synthetic-homotopy-theory.maps-of-prespectra.html#1940" class="Bound">B</a> <a id="2070" href="synthetic-homotopy-theory.maps-of-prespectra.html#2036" class="Bound">f</a><a id="2071" class="Symbol">)</a>
</pre>
## Properties

### The identity map on a prespectrum

<pre class="Agda"><a id="2140" class="Keyword">module</a> <a id="2147" href="synthetic-homotopy-theory.maps-of-prespectra.html#2147" class="Module">_</a>
  <a id="2151" class="Symbol">{</a><a id="2152" href="synthetic-homotopy-theory.maps-of-prespectra.html#2152" class="Bound">l</a> <a id="2154" class="Symbol">:</a> <a id="2156" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2161" class="Symbol">}</a> <a id="2163" class="Symbol">(</a><a id="2164" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2166" class="Symbol">:</a> <a id="2168" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="2180" href="synthetic-homotopy-theory.maps-of-prespectra.html#2152" class="Bound">l</a><a id="2181" class="Symbol">)</a>
  <a id="2185" class="Keyword">where</a>

  <a id="2194" href="synthetic-homotopy-theory.maps-of-prespectra.html#2194" class="Function">map-id-map-Prespectrum</a> <a id="2217" class="Symbol">:</a>
    <a id="2223" class="Symbol">(</a><a id="2224" href="synthetic-homotopy-theory.maps-of-prespectra.html#2224" class="Bound">n</a> <a id="2226" class="Symbol">:</a> <a id="2228" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2229" class="Symbol">)</a> <a id="2231" class="Symbol">→</a> <a id="2233" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2258" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2260" href="synthetic-homotopy-theory.maps-of-prespectra.html#2224" class="Bound">n</a> <a id="2262" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2265" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2290" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2292" href="synthetic-homotopy-theory.maps-of-prespectra.html#2224" class="Bound">n</a>
  <a id="2296" href="synthetic-homotopy-theory.maps-of-prespectra.html#2194" class="Function">map-id-map-Prespectrum</a> <a id="2319" class="Symbol">_</a> <a id="2321" class="Symbol">=</a> <a id="2323" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a>

  <a id="2341" href="synthetic-homotopy-theory.maps-of-prespectra.html#2341" class="Function">coherence-id-map-id-map-Prespectrum</a> <a id="2377" class="Symbol">:</a>
    <a id="2383" href="synthetic-homotopy-theory.maps-of-prespectra.html#1408" class="Function">coherence-map-Prespectrum</a> <a id="2409" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2411" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2413" href="synthetic-homotopy-theory.maps-of-prespectra.html#2194" class="Function">map-id-map-Prespectrum</a>
  <a id="2438" href="synthetic-homotopy-theory.maps-of-prespectra.html#2341" class="Function">coherence-id-map-id-map-Prespectrum</a> <a id="2474" href="synthetic-homotopy-theory.maps-of-prespectra.html#2474" class="Bound">n</a> <a id="2476" class="Symbol">=</a>
    <a id="2482" href="structured-types.pointed-homotopies.html#18184" class="Function Operator">pointed-homotopy-reasoning</a>
    <a id="2513" class="Symbol">(</a> <a id="2515" href="synthetic-homotopy-theory.functoriality-loop-spaces.html#1443" class="Function">pointed-map-Ω</a> <a id="2529" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a> <a id="2544" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a>
      <a id="2553" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="2595" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2597" href="synthetic-homotopy-theory.maps-of-prespectra.html#2474" class="Bound">n</a><a id="2598" class="Symbol">)</a>
    <a id="2604" href="structured-types.pointed-homotopies.html#18360" class="Function">~∗</a> <a id="2607" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a> <a id="2622" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="2625" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="2667" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2669" href="synthetic-homotopy-theory.maps-of-prespectra.html#2474" class="Bound">n</a>
      <a id="2677" href="structured-types.pointed-homotopies.html#18360" class="Function">by</a>
        <a id="2688" href="structured-types.whiskering-pointed-homotopies-composition.html#7011" class="Function">right-whisker-comp-pointed-htpy</a>
          <a id="2730" class="Symbol">(</a> <a id="2732" href="synthetic-homotopy-theory.functoriality-loop-spaces.html#1443" class="Function">pointed-map-Ω</a> <a id="2746" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a><a id="2760" class="Symbol">)</a>
          <a id="2772" class="Symbol">(</a> <a id="2774" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a><a id="2788" class="Symbol">)</a>
          <a id="2800" class="Symbol">(</a> <a id="2802" href="synthetic-homotopy-theory.functoriality-loop-spaces.html#3993" class="Function">preserves-id-pointed-map-Ω</a><a id="2828" class="Symbol">)</a>
          <a id="2840" class="Symbol">(</a> <a id="2842" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="2884" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2886" href="synthetic-homotopy-theory.maps-of-prespectra.html#2474" class="Bound">n</a><a id="2887" class="Symbol">)</a>
    <a id="2893" href="structured-types.pointed-homotopies.html#18360" class="Function">~∗</a> <a id="2896" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="2938" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="2940" href="synthetic-homotopy-theory.maps-of-prespectra.html#2474" class="Bound">n</a>
      <a id="2948" href="structured-types.pointed-homotopies.html#18360" class="Function">by</a>
        <a id="2959" href="structured-types.pointed-homotopies.html#14081" class="Function">left-unit-law-comp-pointed-map</a>
          <a id="3000" class="Symbol">(</a> <a id="3002" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="3044" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="3046" href="synthetic-homotopy-theory.maps-of-prespectra.html#2474" class="Bound">n</a><a id="3047" class="Symbol">)</a>
    <a id="3053" href="structured-types.pointed-homotopies.html#18360" class="Function">~∗</a> <a id="3056" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="3098" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="3100" href="synthetic-homotopy-theory.maps-of-prespectra.html#2474" class="Bound">n</a> <a id="3102" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="3105" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a>
      <a id="3126" href="structured-types.pointed-homotopies.html#18360" class="Function">by</a>
        <a id="3137" href="structured-types.pointed-homotopies.html#9643" class="Function">inv-pointed-htpy</a>
          <a id="3164" class="Symbol">(</a> <a id="3166" href="structured-types.pointed-homotopies.html#15517" class="Function">right-unit-law-comp-pointed-map</a>
            <a id="3210" class="Symbol">(</a> <a id="3212" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="3254" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="3256" href="synthetic-homotopy-theory.maps-of-prespectra.html#2474" class="Bound">n</a><a id="3257" class="Symbol">))</a>

  <a id="3263" href="synthetic-homotopy-theory.maps-of-prespectra.html#3263" class="Function">id-map-Prespectrum</a> <a id="3282" class="Symbol">:</a> <a id="3284" href="synthetic-homotopy-theory.maps-of-prespectra.html#1827" class="Function">map-Prespectrum</a> <a id="3300" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a> <a id="3302" href="synthetic-homotopy-theory.maps-of-prespectra.html#2164" class="Bound">A</a>
  <a id="3306" href="synthetic-homotopy-theory.maps-of-prespectra.html#3263" class="Function">id-map-Prespectrum</a> <a id="3325" class="Symbol">=</a>
    <a id="3331" href="synthetic-homotopy-theory.maps-of-prespectra.html#2194" class="Function">map-id-map-Prespectrum</a> <a id="3354" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3356" href="synthetic-homotopy-theory.maps-of-prespectra.html#2341" class="Function">coherence-id-map-id-map-Prespectrum</a>
</pre>
## References

{{#bibliography}} {{#reference May99}}
