# Prespectra

<pre class="Agda"><a id="23" class="Keyword">module</a> <a id="30" href="synthetic-homotopy-theory.prespectra.html" class="Module">synthetic-homotopy-theory.prespectra</a> <a id="67" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="123" class="Keyword">open</a> <a id="128" class="Keyword">import</a> <a id="135" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="341" class="Keyword">open</a> <a id="346" class="Keyword">import</a> <a id="353" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="385" class="Keyword">open</a> <a id="390" class="Keyword">import</a> <a id="397" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
<a id="435" class="Keyword">open</a> <a id="440" class="Keyword">import</a> <a id="447" href="synthetic-homotopy-theory.suspensions-of-pointed-types.html" class="Module">synthetic-homotopy-theory.suspensions-of-pointed-types</a>
<a id="502" class="Keyword">open</a> <a id="507" class="Keyword">import</a> <a id="514" href="synthetic-homotopy-theory.suspensions-of-types.html" class="Module">synthetic-homotopy-theory.suspensions-of-types</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.html" class="Module">synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types</a>
</pre>
</details>

## Idea

A **prespectrum** is a [sequence](lists.sequences.md) of
[pointed types](structured-types.pointed-types.md) `Aₙ`
[equipped](foundation.structure.md) with
[pointed maps](structured-types.pointed-maps.md)

```text
  ε : Aₙ →∗ ΩAₙ₊₁
```

for each `n : ℕ`, called the **adjoint structure maps** of the prespectrum.

By the
[loop-suspension adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md),
specifying structure maps `Aₙ →∗ Ω Aₙ₊₁` is
[equivalent](foundation-core.equivalences.md) to specifying their adjoint maps

```text
  ΣAₙ → Aₙ₊₁.
```

## Definition

<pre class="Agda"><a id="Prespectrum"></a><a id="1274" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1286" class="Symbol">:</a> <a id="1288" class="Symbol">(</a><a id="1289" href="synthetic-homotopy-theory.prespectra.html#1289" class="Bound">l</a> <a id="1291" class="Symbol">:</a> <a id="1293" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1298" class="Symbol">)</a> <a id="1300" class="Symbol">→</a> <a id="1302" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1305" class="Symbol">(</a><a id="1306" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1311" href="synthetic-homotopy-theory.prespectra.html#1289" class="Bound">l</a><a id="1312" class="Symbol">)</a>
<a id="1314" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1326" href="synthetic-homotopy-theory.prespectra.html#1326" class="Bound">l</a> <a id="1328" class="Symbol">=</a>
  <a id="1332" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1334" class="Symbol">(</a><a id="1335" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1337" class="Symbol">→</a> <a id="1339" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1352" href="synthetic-homotopy-theory.prespectra.html#1326" class="Bound">l</a><a id="1353" class="Symbol">)</a> <a id="1355" class="Symbol">(λ</a> <a id="1358" href="synthetic-homotopy-theory.prespectra.html#1358" class="Bound">A</a> <a id="1360" class="Symbol">→</a> <a id="1362" class="Symbol">(</a><a id="1363" href="synthetic-homotopy-theory.prespectra.html#1363" class="Bound">n</a> <a id="1365" class="Symbol">:</a> <a id="1367" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1368" class="Symbol">)</a> <a id="1370" class="Symbol">→</a> <a id="1372" href="synthetic-homotopy-theory.prespectra.html#1358" class="Bound">A</a> <a id="1374" href="synthetic-homotopy-theory.prespectra.html#1363" class="Bound">n</a> <a id="1376" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1379" href="synthetic-homotopy-theory.loop-spaces.html#1152" class="Function">Ω</a> <a id="1381" class="Symbol">(</a><a id="1382" href="synthetic-homotopy-theory.prespectra.html#1358" class="Bound">A</a> <a id="1384" class="Symbol">(</a><a id="1385" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1392" href="synthetic-homotopy-theory.prespectra.html#1363" class="Bound">n</a><a id="1393" class="Symbol">)))</a>

<a id="1398" class="Keyword">module</a> <a id="1405" href="synthetic-homotopy-theory.prespectra.html#1405" class="Module">_</a>
  <a id="1409" class="Symbol">{</a><a id="1410" href="synthetic-homotopy-theory.prespectra.html#1410" class="Bound">l</a> <a id="1412" class="Symbol">:</a> <a id="1414" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1419" class="Symbol">}</a> <a id="1421" class="Symbol">(</a><a id="1422" href="synthetic-homotopy-theory.prespectra.html#1422" class="Bound">A</a> <a id="1424" class="Symbol">:</a> <a id="1426" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1438" href="synthetic-homotopy-theory.prespectra.html#1410" class="Bound">l</a><a id="1439" class="Symbol">)</a> <a id="1441" class="Symbol">(</a><a id="1442" href="synthetic-homotopy-theory.prespectra.html#1442" class="Bound">n</a> <a id="1444" class="Symbol">:</a> <a id="1446" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1447" class="Symbol">)</a>
  <a id="1451" class="Keyword">where</a>

  <a id="1460" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="1485" class="Symbol">:</a> <a id="1487" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1500" href="synthetic-homotopy-theory.prespectra.html#1410" class="Bound">l</a>
  <a id="1504" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="1529" class="Symbol">=</a> <a id="1531" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1535" href="synthetic-homotopy-theory.prespectra.html#1422" class="Bound">A</a> <a id="1537" href="synthetic-homotopy-theory.prespectra.html#1442" class="Bound">n</a>

  <a id="1542" href="synthetic-homotopy-theory.prespectra.html#1542" class="Function">type-Prespectrum</a> <a id="1559" class="Symbol">:</a> <a id="1561" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1564" href="synthetic-homotopy-theory.prespectra.html#1410" class="Bound">l</a>
  <a id="1568" href="synthetic-homotopy-theory.prespectra.html#1542" class="Function">type-Prespectrum</a> <a id="1585" class="Symbol">=</a> <a id="1587" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1605" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a>

  <a id="1633" href="synthetic-homotopy-theory.prespectra.html#1633" class="Function">point-Prespectrum</a> <a id="1651" class="Symbol">:</a> <a id="1653" href="synthetic-homotopy-theory.prespectra.html#1542" class="Function">type-Prespectrum</a>
  <a id="1672" href="synthetic-homotopy-theory.prespectra.html#1633" class="Function">point-Prespectrum</a> <a id="1690" class="Symbol">=</a> <a id="1692" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1711" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a>

<a id="1737" class="Keyword">module</a> <a id="1744" href="synthetic-homotopy-theory.prespectra.html#1744" class="Module">_</a>
  <a id="1748" class="Symbol">{</a><a id="1749" href="synthetic-homotopy-theory.prespectra.html#1749" class="Bound">l</a> <a id="1751" class="Symbol">:</a> <a id="1753" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1758" class="Symbol">}</a> <a id="1760" class="Symbol">(</a><a id="1761" href="synthetic-homotopy-theory.prespectra.html#1761" class="Bound">A</a> <a id="1763" class="Symbol">:</a> <a id="1765" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="1777" href="synthetic-homotopy-theory.prespectra.html#1749" class="Bound">l</a><a id="1778" class="Symbol">)</a> <a id="1780" class="Symbol">(</a><a id="1781" href="synthetic-homotopy-theory.prespectra.html#1781" class="Bound">n</a> <a id="1783" class="Symbol">:</a> <a id="1785" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1786" class="Symbol">)</a>
  <a id="1790" class="Keyword">where</a>

  <a id="1799" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="1841" class="Symbol">:</a>
    <a id="1847" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="1872" href="synthetic-homotopy-theory.prespectra.html#1761" class="Bound">A</a> <a id="1874" href="synthetic-homotopy-theory.prespectra.html#1781" class="Bound">n</a> <a id="1876" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1879" href="synthetic-homotopy-theory.loop-spaces.html#1152" class="Function">Ω</a> <a id="1881" class="Symbol">(</a><a id="1882" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="1907" href="synthetic-homotopy-theory.prespectra.html#1761" class="Bound">A</a> <a id="1909" class="Symbol">(</a><a id="1910" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1917" href="synthetic-homotopy-theory.prespectra.html#1781" class="Bound">n</a><a id="1918" class="Symbol">))</a>
  <a id="1923" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="1965" class="Symbol">=</a> <a id="1967" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1971" href="synthetic-homotopy-theory.prespectra.html#1761" class="Bound">A</a> <a id="1973" href="synthetic-homotopy-theory.prespectra.html#1781" class="Bound">n</a>

  <a id="1978" href="synthetic-homotopy-theory.prespectra.html#1978" class="Function">adjoint-structure-map-Prespectrum</a> <a id="2012" class="Symbol">:</a>
    <a id="2018" href="synthetic-homotopy-theory.prespectra.html#1542" class="Function">type-Prespectrum</a> <a id="2035" href="synthetic-homotopy-theory.prespectra.html#1761" class="Bound">A</a> <a id="2037" href="synthetic-homotopy-theory.prespectra.html#1781" class="Bound">n</a> <a id="2039" class="Symbol">→</a> <a id="2041" href="synthetic-homotopy-theory.loop-spaces.html#1040" class="Function">type-Ω</a> <a id="2048" class="Symbol">(</a><a id="2049" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2074" href="synthetic-homotopy-theory.prespectra.html#1761" class="Bound">A</a> <a id="2076" class="Symbol">(</a><a id="2077" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2084" href="synthetic-homotopy-theory.prespectra.html#1781" class="Bound">n</a><a id="2085" class="Symbol">))</a>
  <a id="2090" href="synthetic-homotopy-theory.prespectra.html#1978" class="Function">adjoint-structure-map-Prespectrum</a> <a id="2124" class="Symbol">=</a>
    <a id="2130" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2146" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a>

  <a id="2191" href="synthetic-homotopy-theory.prespectra.html#2191" class="Function">preserves-point-adjoint-structure-map-Prespectrum</a> <a id="2241" class="Symbol">:</a>
    <a id="2247" href="synthetic-homotopy-theory.prespectra.html#1978" class="Function">adjoint-structure-map-Prespectrum</a> <a id="2281" class="Symbol">(</a><a id="2282" href="synthetic-homotopy-theory.prespectra.html#1633" class="Function">point-Prespectrum</a> <a id="2300" href="synthetic-homotopy-theory.prespectra.html#1761" class="Bound">A</a> <a id="2302" href="synthetic-homotopy-theory.prespectra.html#1781" class="Bound">n</a><a id="2303" class="Symbol">)</a> <a id="2305" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2311" href="synthetic-homotopy-theory.loop-spaces.html#1117" class="Function">refl-Ω</a> <a id="2318" class="Symbol">(</a><a id="2319" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2344" href="synthetic-homotopy-theory.prespectra.html#1761" class="Bound">A</a> <a id="2346" class="Symbol">(</a><a id="2347" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2354" href="synthetic-homotopy-theory.prespectra.html#1781" class="Bound">n</a><a id="2355" class="Symbol">))</a>
  <a id="2360" href="synthetic-homotopy-theory.prespectra.html#2191" class="Function">preserves-point-adjoint-structure-map-Prespectrum</a> <a id="2410" class="Symbol">=</a>
    <a id="2416" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="2444" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a>
</pre>
### The structure maps of a prespectrum

<pre class="Agda"><a id="2540" class="Keyword">module</a> <a id="2547" href="synthetic-homotopy-theory.prespectra.html#2547" class="Module">_</a>
  <a id="2551" class="Symbol">{</a><a id="2552" href="synthetic-homotopy-theory.prespectra.html#2552" class="Bound">l</a> <a id="2554" class="Symbol">:</a> <a id="2556" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2561" class="Symbol">}</a> <a id="2563" class="Symbol">(</a><a id="2564" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="2566" class="Symbol">:</a> <a id="2568" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="2580" href="synthetic-homotopy-theory.prespectra.html#2552" class="Bound">l</a><a id="2581" class="Symbol">)</a> <a id="2583" class="Symbol">(</a><a id="2584" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a> <a id="2586" class="Symbol">:</a> <a id="2588" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2589" class="Symbol">)</a>
  <a id="2593" class="Keyword">where</a>

  <a id="2602" href="synthetic-homotopy-theory.prespectra.html#2602" class="Function">pointed-structure-map-Prespectrum</a> <a id="2636" class="Symbol">:</a>
    <a id="2642" href="synthetic-homotopy-theory.suspensions-of-pointed-types.html#674" class="Function">suspension-Pointed-Type</a> <a id="2666" class="Symbol">(</a><a id="2667" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2692" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="2694" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a><a id="2695" class="Symbol">)</a> <a id="2697" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a>
    <a id="2704" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2729" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="2731" class="Symbol">(</a><a id="2732" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2739" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a><a id="2740" class="Symbol">)</a>
  <a id="2744" href="synthetic-homotopy-theory.prespectra.html#2602" class="Function">pointed-structure-map-Prespectrum</a> <a id="2778" class="Symbol">=</a>
    <a id="2784" href="synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.html#4018" class="Function">inv-transpose-suspension-loop-adjunction</a>
      <a id="2831" class="Symbol">(</a> <a id="2833" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2858" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="2860" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a><a id="2861" class="Symbol">)</a>
      <a id="2869" class="Symbol">(</a> <a id="2871" href="synthetic-homotopy-theory.prespectra.html#1460" class="Function">pointed-type-Prespectrum</a> <a id="2896" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="2898" class="Symbol">(</a><a id="2899" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2906" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a><a id="2907" class="Symbol">))</a>
      <a id="2916" class="Symbol">(</a> <a id="2918" href="synthetic-homotopy-theory.prespectra.html#1799" class="Function">pointed-adjoint-structure-map-Prespectrum</a> <a id="2960" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="2962" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a><a id="2963" class="Symbol">)</a>

  <a id="2968" href="synthetic-homotopy-theory.prespectra.html#2968" class="Function">structure-map-Prespectrum</a> <a id="2994" class="Symbol">:</a>
    <a id="3000" href="synthetic-homotopy-theory.suspensions-of-types.html#2638" class="Function">suspension</a> <a id="3011" class="Symbol">(</a><a id="3012" href="synthetic-homotopy-theory.prespectra.html#1542" class="Function">type-Prespectrum</a> <a id="3029" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="3031" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a><a id="3032" class="Symbol">)</a> <a id="3034" class="Symbol">→</a> <a id="3036" href="synthetic-homotopy-theory.prespectra.html#1542" class="Function">type-Prespectrum</a> <a id="3053" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="3055" class="Symbol">(</a><a id="3056" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="3063" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a><a id="3064" class="Symbol">)</a>
  <a id="3068" href="synthetic-homotopy-theory.prespectra.html#2968" class="Function">structure-map-Prespectrum</a> <a id="3094" class="Symbol">=</a> <a id="3096" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="3112" href="synthetic-homotopy-theory.prespectra.html#2602" class="Function">pointed-structure-map-Prespectrum</a>

  <a id="3149" href="synthetic-homotopy-theory.prespectra.html#3149" class="Function">preserves-point-structure-map-Prespectrum</a> <a id="3191" class="Symbol">:</a>
    <a id="3197" href="synthetic-homotopy-theory.prespectra.html#2968" class="Function">structure-map-Prespectrum</a> <a id="3223" href="synthetic-homotopy-theory.suspensions-of-types.html#2737" class="Function">north-suspension</a> <a id="3240" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3242" href="synthetic-homotopy-theory.prespectra.html#1633" class="Function">point-Prespectrum</a> <a id="3260" href="synthetic-homotopy-theory.prespectra.html#2564" class="Bound">A</a> <a id="3262" class="Symbol">(</a><a id="3263" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="3270" href="synthetic-homotopy-theory.prespectra.html#2584" class="Bound">n</a><a id="3271" class="Symbol">)</a>
  <a id="3275" href="synthetic-homotopy-theory.prespectra.html#3149" class="Function">preserves-point-structure-map-Prespectrum</a> <a id="3317" class="Symbol">=</a>
    <a id="3323" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="3351" href="synthetic-homotopy-theory.prespectra.html#2602" class="Function">pointed-structure-map-Prespectrum</a>
</pre>
## References

{{#bibliography}} {{#reference May99}}
