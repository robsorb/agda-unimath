# Equivalences of span diagrams on families of types

<pre class="Agda"><a id="63" class="Keyword">module</a> <a id="70" href="foundation.equivalences-span-diagrams-families-of-types.html" class="Module">foundation.equivalences-span-diagrams-families-of-types</a> <a id="126" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="foundation.equivalences-spans-families-of-types.html" class="Module">foundation.equivalences-spans-families-of-types</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="405" class="Keyword">open</a> <a id="410" class="Keyword">import</a> <a id="417" href="foundation.operations-spans-families-of-types.html" class="Module">foundation.operations-spans-families-of-types</a>
<a id="463" class="Keyword">open</a> <a id="468" class="Keyword">import</a> <a id="475" href="foundation.span-diagrams-families-of-types.html" class="Module">foundation.span-diagrams-families-of-types</a>
<a id="518" class="Keyword">open</a> <a id="523" class="Keyword">import</a> <a id="530" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An
{{#concept "equivalence of span diagrams on families of types" Agda=equiv-span-diagram-type-family}}
from a [span](foundation.spans-families-of-types.md) `(A , s)` of families of
types indexed by a type `I` to a span `(B , t)` indexed by `I` consists of a
[family of equivalences](foundation-core.families-of-equivalences.md)
`h : Aᵢ ≃ Bᵢ`, and an equivalence `e : S ≃ T`
[equipped](foundation.structure.md) with a family of
[homotopies](foundation-core.homotopies.md) witnessing that the square

```text
         e
     S -----> T
     |        |
  fᵢ |        | gᵢ
     ∨        ∨
     Aᵢ ----> Bᵢ
         h
```

[commutes](foundation-core.commuting-squares-of-maps.md) for each `i : I`.

## Definitions

### Equivalences of span diagrams on families of types

<pre class="Agda"><a id="1358" class="Keyword">module</a> <a id="1365" href="foundation.equivalences-span-diagrams-families-of-types.html#1365" class="Module">_</a>
  <a id="1369" class="Symbol">{</a><a id="1370" href="foundation.equivalences-span-diagrams-families-of-types.html#1370" class="Bound">l1</a> <a id="1373" href="foundation.equivalences-span-diagrams-families-of-types.html#1373" class="Bound">l2</a> <a id="1376" href="foundation.equivalences-span-diagrams-families-of-types.html#1376" class="Bound">l3</a> <a id="1379" href="foundation.equivalences-span-diagrams-families-of-types.html#1379" class="Bound">l4</a> <a id="1382" href="foundation.equivalences-span-diagrams-families-of-types.html#1382" class="Bound">l5</a> <a id="1385" class="Symbol">:</a> <a id="1387" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1392" class="Symbol">}</a> <a id="1394" class="Symbol">{</a><a id="1395" href="foundation.equivalences-span-diagrams-families-of-types.html#1395" class="Bound">I</a> <a id="1397" class="Symbol">:</a> <a id="1399" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1402" href="foundation.equivalences-span-diagrams-families-of-types.html#1370" class="Bound">l1</a><a id="1404" class="Symbol">}</a>
  <a id="1408" class="Symbol">(</a><a id="1409" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a> <a id="1411" class="Symbol">:</a> <a id="1413" href="foundation.span-diagrams-families-of-types.html#835" class="Function">span-diagram-type-family</a> <a id="1438" href="foundation.equivalences-span-diagrams-families-of-types.html#1373" class="Bound">l2</a> <a id="1441" href="foundation.equivalences-span-diagrams-families-of-types.html#1376" class="Bound">l3</a> <a id="1444" href="foundation.equivalences-span-diagrams-families-of-types.html#1395" class="Bound">I</a><a id="1445" class="Symbol">)</a>
  <a id="1449" class="Symbol">(</a><a id="1450" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a> <a id="1452" class="Symbol">:</a> <a id="1454" href="foundation.span-diagrams-families-of-types.html#835" class="Function">span-diagram-type-family</a> <a id="1479" href="foundation.equivalences-span-diagrams-families-of-types.html#1379" class="Bound">l4</a> <a id="1482" href="foundation.equivalences-span-diagrams-families-of-types.html#1382" class="Bound">l5</a> <a id="1485" href="foundation.equivalences-span-diagrams-families-of-types.html#1395" class="Bound">I</a><a id="1486" class="Symbol">)</a>
  <a id="1490" class="Keyword">where</a>

  <a id="1499" href="foundation.equivalences-span-diagrams-families-of-types.html#1499" class="Function">equiv-span-diagram-type-family</a> <a id="1530" class="Symbol">:</a> <a id="1532" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1535" class="Symbol">(</a><a id="1536" href="foundation.equivalences-span-diagrams-families-of-types.html#1370" class="Bound">l1</a> <a id="1539" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1541" href="foundation.equivalences-span-diagrams-families-of-types.html#1373" class="Bound">l2</a> <a id="1544" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1546" href="foundation.equivalences-span-diagrams-families-of-types.html#1376" class="Bound">l3</a> <a id="1549" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1551" href="foundation.equivalences-span-diagrams-families-of-types.html#1379" class="Bound">l4</a> <a id="1554" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1556" href="foundation.equivalences-span-diagrams-families-of-types.html#1382" class="Bound">l5</a><a id="1558" class="Symbol">)</a>
  <a id="1562" href="foundation.equivalences-span-diagrams-families-of-types.html#1499" class="Function">equiv-span-diagram-type-family</a> <a id="1593" class="Symbol">=</a>
    <a id="1599" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1601" class="Symbol">(</a> <a id="1603" class="Symbol">(</a><a id="1604" href="foundation.equivalences-span-diagrams-families-of-types.html#1604" class="Bound">i</a> <a id="1606" class="Symbol">:</a> <a id="1608" href="foundation.equivalences-span-diagrams-families-of-types.html#1395" class="Bound">I</a><a id="1609" class="Symbol">)</a> <a id="1611" class="Symbol">→</a>
        <a id="1621" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="1653" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a> <a id="1655" href="foundation.equivalences-span-diagrams-families-of-types.html#1604" class="Bound">i</a> <a id="1657" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
        <a id="1667" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="1699" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a> <a id="1701" href="foundation.equivalences-span-diagrams-families-of-types.html#1604" class="Bound">i</a><a id="1702" class="Symbol">)</a>
      <a id="1710" class="Symbol">(</a> <a id="1712" class="Symbol">λ</a> <a id="1714" href="foundation.equivalences-span-diagrams-families-of-types.html#1714" class="Bound">e</a> <a id="1716" class="Symbol">→</a>
        <a id="1726" href="foundation.equivalences-spans-families-of-types.html#1576" class="Function">equiv-span-type-family</a>
          <a id="1759" class="Symbol">(</a> <a id="1761" href="foundation.operations-spans-families-of-types.html#1318" class="Function">concat-span-hom-family-of-types</a>
            <a id="1805" class="Symbol">(</a> <a id="1807" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="1837" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a><a id="1838" class="Symbol">)</a>
            <a id="1852" class="Symbol">(</a> <a id="1854" class="Symbol">λ</a> <a id="1856" href="foundation.equivalences-span-diagrams-families-of-types.html#1856" class="Bound">i</a> <a id="1858" class="Symbol">→</a> <a id="1860" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="1870" class="Symbol">(</a><a id="1871" href="foundation.equivalences-span-diagrams-families-of-types.html#1714" class="Bound">e</a> <a id="1873" href="foundation.equivalences-span-diagrams-families-of-types.html#1856" class="Bound">i</a><a id="1874" class="Symbol">)))</a>
          <a id="1888" class="Symbol">(</a> <a id="1890" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="1920" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a><a id="1921" class="Symbol">))</a>

  <a id="1927" class="Keyword">module</a> <a id="1934" href="foundation.equivalences-span-diagrams-families-of-types.html#1934" class="Module">_</a>
    <a id="1940" class="Symbol">(</a><a id="1941" href="foundation.equivalences-span-diagrams-families-of-types.html#1941" class="Bound">e</a> <a id="1943" class="Symbol">:</a> <a id="1945" href="foundation.equivalences-span-diagrams-families-of-types.html#1499" class="Function">equiv-span-diagram-type-family</a><a id="1975" class="Symbol">)</a>
    <a id="1981" class="Keyword">where</a>

    <a id="1992" href="foundation.equivalences-span-diagrams-families-of-types.html#1992" class="Function">equiv-family-equiv-span-diagram-type-family</a> <a id="2036" class="Symbol">:</a>
      <a id="2044" class="Symbol">(</a><a id="2045" href="foundation.equivalences-span-diagrams-families-of-types.html#2045" class="Bound">i</a> <a id="2047" class="Symbol">:</a> <a id="2049" href="foundation.equivalences-span-diagrams-families-of-types.html#1395" class="Bound">I</a><a id="2050" class="Symbol">)</a> <a id="2052" class="Symbol">→</a>
      <a id="2060" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="2092" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a> <a id="2094" href="foundation.equivalences-span-diagrams-families-of-types.html#2045" class="Bound">i</a> <a id="2096" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
      <a id="2104" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="2136" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a> <a id="2138" href="foundation.equivalences-span-diagrams-families-of-types.html#2045" class="Bound">i</a>
    <a id="2144" href="foundation.equivalences-span-diagrams-families-of-types.html#1992" class="Function">equiv-family-equiv-span-diagram-type-family</a> <a id="2188" class="Symbol">=</a> <a id="2190" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2194" href="foundation.equivalences-span-diagrams-families-of-types.html#1941" class="Bound">e</a>

    <a id="2201" href="foundation.equivalences-span-diagrams-families-of-types.html#2201" class="Function">map-family-equiv-span-diagram-type-family</a> <a id="2243" class="Symbol">:</a>
      <a id="2251" class="Symbol">(</a><a id="2252" href="foundation.equivalences-span-diagrams-families-of-types.html#2252" class="Bound">i</a> <a id="2254" class="Symbol">:</a> <a id="2256" href="foundation.equivalences-span-diagrams-families-of-types.html#1395" class="Bound">I</a><a id="2257" class="Symbol">)</a> <a id="2259" class="Symbol">→</a>
      <a id="2267" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="2299" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a> <a id="2301" href="foundation.equivalences-span-diagrams-families-of-types.html#2252" class="Bound">i</a> <a id="2303" class="Symbol">→</a>
      <a id="2311" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="2343" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a> <a id="2345" href="foundation.equivalences-span-diagrams-families-of-types.html#2252" class="Bound">i</a>
    <a id="2351" href="foundation.equivalences-span-diagrams-families-of-types.html#2201" class="Function">map-family-equiv-span-diagram-type-family</a> <a id="2393" href="foundation.equivalences-span-diagrams-families-of-types.html#2393" class="Bound">i</a> <a id="2395" class="Symbol">=</a>
      <a id="2403" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="2413" class="Symbol">(</a><a id="2414" href="foundation.equivalences-span-diagrams-families-of-types.html#1992" class="Function">equiv-family-equiv-span-diagram-type-family</a> <a id="2458" href="foundation.equivalences-span-diagrams-families-of-types.html#2393" class="Bound">i</a><a id="2459" class="Symbol">)</a>

    <a id="2466" href="foundation.equivalences-span-diagrams-families-of-types.html#2466" class="Function">equiv-span-equiv-span-diagram-type-family</a> <a id="2508" class="Symbol">:</a>
      <a id="2516" href="foundation.equivalences-spans-families-of-types.html#1576" class="Function">equiv-span-type-family</a>
        <a id="2547" class="Symbol">(</a> <a id="2549" href="foundation.operations-spans-families-of-types.html#1318" class="Function">concat-span-hom-family-of-types</a>
          <a id="2591" class="Symbol">(</a> <a id="2593" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="2623" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a><a id="2624" class="Symbol">)</a>
          <a id="2636" class="Symbol">(</a> <a id="2638" href="foundation.equivalences-span-diagrams-families-of-types.html#2201" class="Function">map-family-equiv-span-diagram-type-family</a><a id="2679" class="Symbol">))</a>
        <a id="2690" class="Symbol">(</a> <a id="2692" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="2722" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a><a id="2723" class="Symbol">)</a>
    <a id="2729" href="foundation.equivalences-span-diagrams-families-of-types.html#2466" class="Function">equiv-span-equiv-span-diagram-type-family</a> <a id="2771" class="Symbol">=</a> <a id="2773" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2777" href="foundation.equivalences-span-diagrams-families-of-types.html#1941" class="Bound">e</a>

    <a id="2784" href="foundation.equivalences-span-diagrams-families-of-types.html#2784" class="Function">spanning-equiv-equiv-span-diagram-type-family</a> <a id="2830" class="Symbol">:</a>
      <a id="2838" href="foundation.span-diagrams-families-of-types.html#1325" class="Function">spanning-type-span-diagram-type-family</a> <a id="2877" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a> <a id="2879" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
      <a id="2887" href="foundation.span-diagrams-families-of-types.html#1325" class="Function">spanning-type-span-diagram-type-family</a> <a id="2926" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a>
    <a id="2932" href="foundation.equivalences-span-diagrams-families-of-types.html#2784" class="Function">spanning-equiv-equiv-span-diagram-type-family</a> <a id="2978" class="Symbol">=</a>
      <a id="2986" href="foundation.equivalences-spans-families-of-types.html#1962" class="Function">equiv-equiv-span-type-family</a>
        <a id="3023" class="Symbol">(</a> <a id="3025" href="foundation.operations-spans-families-of-types.html#1318" class="Function">concat-span-hom-family-of-types</a>
          <a id="3067" class="Symbol">(</a> <a id="3069" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="3099" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a><a id="3100" class="Symbol">)</a>
          <a id="3112" class="Symbol">(</a> <a id="3114" href="foundation.equivalences-span-diagrams-families-of-types.html#2201" class="Function">map-family-equiv-span-diagram-type-family</a><a id="3155" class="Symbol">))</a>
        <a id="3166" class="Symbol">(</a> <a id="3168" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="3198" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a><a id="3199" class="Symbol">)</a>
        <a id="3209" class="Symbol">(</a> <a id="3211" href="foundation.equivalences-span-diagrams-families-of-types.html#2466" class="Function">equiv-span-equiv-span-diagram-type-family</a><a id="3252" class="Symbol">)</a>

    <a id="3259" href="foundation.equivalences-span-diagrams-families-of-types.html#3259" class="Function">spanning-map-equiv-span-diagram-type-family</a> <a id="3303" class="Symbol">:</a>
      <a id="3311" href="foundation.span-diagrams-families-of-types.html#1325" class="Function">spanning-type-span-diagram-type-family</a> <a id="3350" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a> <a id="3352" class="Symbol">→</a>
      <a id="3360" href="foundation.span-diagrams-families-of-types.html#1325" class="Function">spanning-type-span-diagram-type-family</a> <a id="3399" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a>
    <a id="3405" href="foundation.equivalences-span-diagrams-families-of-types.html#3259" class="Function">spanning-map-equiv-span-diagram-type-family</a> <a id="3449" class="Symbol">=</a>
      <a id="3457" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="3467" href="foundation.equivalences-span-diagrams-families-of-types.html#2784" class="Function">spanning-equiv-equiv-span-diagram-type-family</a>

    <a id="3518" href="foundation.equivalences-span-diagrams-families-of-types.html#3518" class="Function">coherence-square-equiv-span-diagram-type-family</a> <a id="3566" class="Symbol">:</a>
      <a id="3574" class="Symbol">(</a><a id="3575" href="foundation.equivalences-span-diagrams-families-of-types.html#3575" class="Bound">i</a> <a id="3577" class="Symbol">:</a> <a id="3579" href="foundation.equivalences-span-diagrams-families-of-types.html#1395" class="Bound">I</a><a id="3580" class="Symbol">)</a> <a id="3582" class="Symbol">→</a>
      <a id="3590" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
        <a id="3620" class="Symbol">(</a> <a id="3622" href="foundation.equivalences-span-diagrams-families-of-types.html#3259" class="Function">spanning-map-equiv-span-diagram-type-family</a><a id="3665" class="Symbol">)</a>
        <a id="3675" class="Symbol">(</a> <a id="3677" href="foundation.span-diagrams-families-of-types.html#1492" class="Function">map-span-diagram-type-family</a> <a id="3706" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a> <a id="3708" href="foundation.equivalences-span-diagrams-families-of-types.html#3575" class="Bound">i</a><a id="3709" class="Symbol">)</a>
        <a id="3719" class="Symbol">(</a> <a id="3721" href="foundation.span-diagrams-families-of-types.html#1492" class="Function">map-span-diagram-type-family</a> <a id="3750" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a> <a id="3752" href="foundation.equivalences-span-diagrams-families-of-types.html#3575" class="Bound">i</a><a id="3753" class="Symbol">)</a>
        <a id="3763" class="Symbol">(</a> <a id="3765" href="foundation.equivalences-span-diagrams-families-of-types.html#2201" class="Function">map-family-equiv-span-diagram-type-family</a> <a id="3807" href="foundation.equivalences-span-diagrams-families-of-types.html#3575" class="Bound">i</a><a id="3808" class="Symbol">)</a>
    <a id="3814" href="foundation.equivalences-span-diagrams-families-of-types.html#3518" class="Function">coherence-square-equiv-span-diagram-type-family</a> <a id="3862" class="Symbol">=</a>
      <a id="3870" href="foundation.equivalences-spans-families-of-types.html#2478" class="Function">triangle-equiv-span-type-family</a>
        <a id="3910" class="Symbol">(</a> <a id="3912" href="foundation.operations-spans-families-of-types.html#1318" class="Function">concat-span-hom-family-of-types</a>
          <a id="3954" class="Symbol">(</a> <a id="3956" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="3986" href="foundation.equivalences-span-diagrams-families-of-types.html#1409" class="Bound">S</a><a id="3987" class="Symbol">)</a>
          <a id="3999" class="Symbol">(</a> <a id="4001" href="foundation.equivalences-span-diagrams-families-of-types.html#2201" class="Function">map-family-equiv-span-diagram-type-family</a><a id="4042" class="Symbol">))</a>
        <a id="4053" class="Symbol">(</a> <a id="4055" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="4085" href="foundation.equivalences-span-diagrams-families-of-types.html#1450" class="Bound">T</a><a id="4086" class="Symbol">)</a>
        <a id="4096" class="Symbol">(</a> <a id="4098" href="foundation.equivalences-span-diagrams-families-of-types.html#2466" class="Function">equiv-span-equiv-span-diagram-type-family</a><a id="4139" class="Symbol">)</a>
</pre>
### Identity equivalences of spans diagrams on families of types

<pre class="Agda"><a id="4220" class="Keyword">module</a> <a id="4227" href="foundation.equivalences-span-diagrams-families-of-types.html#4227" class="Module">_</a>
  <a id="4231" class="Symbol">{</a><a id="4232" href="foundation.equivalences-span-diagrams-families-of-types.html#4232" class="Bound">l1</a> <a id="4235" href="foundation.equivalences-span-diagrams-families-of-types.html#4235" class="Bound">l2</a> <a id="4238" href="foundation.equivalences-span-diagrams-families-of-types.html#4238" class="Bound">l3</a> <a id="4241" class="Symbol">:</a> <a id="4243" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4248" class="Symbol">}</a> <a id="4250" class="Symbol">{</a><a id="4251" href="foundation.equivalences-span-diagrams-families-of-types.html#4251" class="Bound">I</a> <a id="4253" class="Symbol">:</a> <a id="4255" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4258" href="foundation.equivalences-span-diagrams-families-of-types.html#4232" class="Bound">l1</a><a id="4260" class="Symbol">}</a> <a id="4262" class="Symbol">{</a><a id="4263" href="foundation.equivalences-span-diagrams-families-of-types.html#4263" class="Bound">𝒮</a> <a id="4265" class="Symbol">:</a> <a id="4267" href="foundation.span-diagrams-families-of-types.html#835" class="Function">span-diagram-type-family</a> <a id="4292" href="foundation.equivalences-span-diagrams-families-of-types.html#4235" class="Bound">l2</a> <a id="4295" href="foundation.equivalences-span-diagrams-families-of-types.html#4238" class="Bound">l3</a> <a id="4298" href="foundation.equivalences-span-diagrams-families-of-types.html#4251" class="Bound">I</a><a id="4299" class="Symbol">}</a>
  <a id="4303" class="Keyword">where</a>

  <a id="4312" href="foundation.equivalences-span-diagrams-families-of-types.html#4312" class="Function">id-equiv-span-diagram-type-family</a> <a id="4346" class="Symbol">:</a>
    <a id="4352" href="foundation.equivalences-span-diagrams-families-of-types.html#1499" class="Function">equiv-span-diagram-type-family</a> <a id="4383" href="foundation.equivalences-span-diagrams-families-of-types.html#4263" class="Bound">𝒮</a> <a id="4385" href="foundation.equivalences-span-diagrams-families-of-types.html#4263" class="Bound">𝒮</a>
  <a id="4389" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4393" href="foundation.equivalences-span-diagrams-families-of-types.html#4312" class="Function">id-equiv-span-diagram-type-family</a> <a id="4427" href="foundation.equivalences-span-diagrams-families-of-types.html#4427" class="Bound">i</a> <a id="4429" class="Symbol">=</a> <a id="4431" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
  <a id="4442" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4446" class="Symbol">(</a><a id="4447" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4451" href="foundation.equivalences-span-diagrams-families-of-types.html#4312" class="Function">id-equiv-span-diagram-type-family</a><a id="4484" class="Symbol">)</a> <a id="4486" class="Symbol">=</a> <a id="4488" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
  <a id="4499" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4503" class="Symbol">(</a><a id="4504" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4508" href="foundation.equivalences-span-diagrams-families-of-types.html#4312" class="Function">id-equiv-span-diagram-type-family</a><a id="4541" class="Symbol">)</a> <a id="4543" href="foundation.equivalences-span-diagrams-families-of-types.html#4543" class="Bound">i</a> <a id="4545" class="Symbol">=</a> <a id="4547" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
</pre>
## See also

- [Equivalences of spans on families of types](foundation.equivalences-spans-families-of-types.md)
