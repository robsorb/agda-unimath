# Large Lawvere–Tierney topologies

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html" class="Module">orthogonal-factorization-systems.large-lawvere-tierney-topologies</a> <a id="118" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="382" class="Keyword">open</a> <a id="387" class="Keyword">import</a> <a id="394" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="451" class="Keyword">open</a> <a id="456" class="Keyword">import</a> <a id="463" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="491" class="Keyword">open</a> <a id="496" class="Keyword">import</a> <a id="503" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html" class="Module">orthogonal-factorization-systems.lawvere-tierney-topologies</a>
</pre>
</details>

## Idea

A {#concept "Lawvere–Tierney topology" Disambiguation="on types"} on types is a
hierarchy of maps

```text
  j : {l : Level} → Prop l → Prop (δ l)
```

that is [idempotent](foundation.idempotent-maps.md) and preserves the
[unit type](foundation.unit-type.md) and
[binary products](foundation.conjunction.md)

```text
  j (j P) ≃ j P      j unit ≃ unit      j (P ∧ Q) ≃ j P ∧ j Q
```

such operations give rise to a notion of `j`-sheaves of types.

## Definitions

### The predicate on an operator on propositions of defining a Lawvere-Tierney topology

<pre class="Agda"><a id="1150" class="Keyword">record</a>
  <a id="is-large-lawvere-tierney-topology"></a><a id="1159" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1159" class="Record">is-large-lawvere-tierney-topology</a>
    <a id="1197" class="Symbol">{</a><a id="1198" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1198" class="Bound">δ</a> <a id="1200" class="Symbol">:</a> <a id="1202" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1208" class="Symbol">→</a> <a id="1210" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1215" class="Symbol">}</a> <a id="1217" class="Symbol">(</a><a id="1218" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1218" class="Bound">j</a> <a id="1220" class="Symbol">:</a> <a id="1222" class="Symbol">{</a><a id="1223" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1223" class="Bound">l</a> <a id="1225" class="Symbol">:</a> <a id="1227" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1232" class="Symbol">}</a> <a id="1234" class="Symbol">→</a> <a id="1236" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1241" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1223" class="Bound">l</a> <a id="1243" class="Symbol">→</a> <a id="1245" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1250" class="Symbol">(</a><a id="1251" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1198" class="Bound">δ</a> <a id="1253" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1223" class="Bound">l</a><a id="1254" class="Symbol">))</a> <a id="1257" class="Symbol">:</a> <a id="1259" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1265" class="Keyword">where</a>
  <a id="1273" class="Keyword">field</a>
    <a id="is-large-lawvere-tierney-topology.is-idempotent-is-large-lawvere-tierney-topology"></a><a id="1283" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1283" class="Field">is-idempotent-is-large-lawvere-tierney-topology</a> <a id="1331" class="Symbol">:</a>
      <a id="1339" class="Symbol">{</a><a id="1340" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1340" class="Bound">l</a> <a id="1342" class="Symbol">:</a> <a id="1344" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1349" class="Symbol">}</a> <a id="1351" class="Symbol">(</a><a id="1352" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1352" class="Bound">P</a> <a id="1354" class="Symbol">:</a> <a id="1356" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1361" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1340" class="Bound">l</a><a id="1362" class="Symbol">)</a> <a id="1364" class="Symbol">→</a> <a id="1366" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1376" class="Symbol">(</a><a id="1377" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1218" class="Bound">j</a> <a id="1379" class="Symbol">(</a><a id="1380" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1218" class="Bound">j</a> <a id="1382" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1352" class="Bound">P</a><a id="1383" class="Symbol">)</a> <a id="1385" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="1387" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1218" class="Bound">j</a> <a id="1389" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1352" class="Bound">P</a><a id="1390" class="Symbol">)</a>

    <a id="is-large-lawvere-tierney-topology.preserves-unit-is-large-lawvere-tierney-topology"></a><a id="1397" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1397" class="Field">preserves-unit-is-large-lawvere-tierney-topology</a> <a id="1446" class="Symbol">:</a>
      <a id="1454" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1464" class="Symbol">(</a><a id="1465" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1218" class="Bound">j</a> <a id="1467" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a> <a id="1477" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="1479" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a><a id="1488" class="Symbol">)</a>

    <a id="is-large-lawvere-tierney-topology.preserves-conjunction-is-large-lawvere-tierney-topology"></a><a id="1495" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1495" class="Field">preserves-conjunction-is-large-lawvere-tierney-topology</a> <a id="1551" class="Symbol">:</a>
      <a id="1559" class="Symbol">{</a><a id="1560" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1560" class="Bound">l1</a> <a id="1563" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1563" class="Bound">l2</a> <a id="1566" class="Symbol">:</a> <a id="1568" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1573" class="Symbol">}</a> <a id="1575" class="Symbol">(</a><a id="1576" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1576" class="Bound">P</a> <a id="1578" class="Symbol">:</a> <a id="1580" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1585" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1560" class="Bound">l1</a><a id="1587" class="Symbol">)</a> <a id="1589" class="Symbol">(</a><a id="1590" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1590" class="Bound">Q</a> <a id="1592" class="Symbol">:</a> <a id="1594" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1599" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1563" class="Bound">l2</a><a id="1601" class="Symbol">)</a> <a id="1603" class="Symbol">→</a>
      <a id="1611" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1621" class="Symbol">(</a><a id="1622" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1218" class="Bound">j</a> <a id="1624" class="Symbol">(</a><a id="1625" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1576" class="Bound">P</a> <a id="1627" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="1629" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1590" class="Bound">Q</a><a id="1630" class="Symbol">)</a> <a id="1632" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="1634" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1218" class="Bound">j</a> <a id="1636" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1576" class="Bound">P</a> <a id="1638" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="1640" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1218" class="Bound">j</a> <a id="1642" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1590" class="Bound">Q</a><a id="1643" class="Symbol">)</a>

<a id="1646" class="Keyword">open</a> <a id="1651" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1159" class="Module">is-large-lawvere-tierney-topology</a> <a id="1685" class="Keyword">public</a>
</pre>
### The large type of Lawvere-Tierney topologies

<pre class="Agda"><a id="1755" class="Keyword">record</a>
  <a id="large-lawvere-tierney-topology"></a><a id="1764" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1764" class="Record">large-lawvere-tierney-topology</a> <a id="1795" class="Symbol">(</a><a id="1796" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1796" class="Bound">δ</a> <a id="1798" class="Symbol">:</a> <a id="1800" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1806" class="Symbol">→</a> <a id="1808" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1813" class="Symbol">)</a> <a id="1815" class="Symbol">:</a> <a id="1817" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1823" class="Keyword">where</a>
  <a id="1831" class="Keyword">field</a>
    <a id="large-lawvere-tierney-topology.operator-large-lawvere-tierney-topology"></a><a id="1841" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="1881" class="Symbol">:</a> <a id="1883" class="Symbol">{</a><a id="1884" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1884" class="Bound">l</a> <a id="1886" class="Symbol">:</a> <a id="1888" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1893" class="Symbol">}</a> <a id="1895" class="Symbol">→</a> <a id="1897" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1902" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1884" class="Bound">l</a> <a id="1904" class="Symbol">→</a> <a id="1906" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1911" class="Symbol">(</a><a id="1912" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1796" class="Bound">δ</a> <a id="1914" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1884" class="Bound">l</a><a id="1915" class="Symbol">)</a>

    <a id="large-lawvere-tierney-topology.is-large-lawvere-tierney-topology-large-lawvere-tierney-topology"></a><a id="1922" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1922" class="Field">is-large-lawvere-tierney-topology-large-lawvere-tierney-topology</a> <a id="1987" class="Symbol">:</a>
      <a id="1995" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1159" class="Record">is-large-lawvere-tierney-topology</a> <a id="2029" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a>

  <a id="large-lawvere-tierney-topology.is-idempotent-large-lawvere-tierney-topology"></a><a id="2072" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2072" class="Function">is-idempotent-large-lawvere-tierney-topology</a> <a id="2117" class="Symbol">:</a>
    <a id="2123" class="Symbol">{</a><a id="2124" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2124" class="Bound">l</a> <a id="2126" class="Symbol">:</a> <a id="2128" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2133" class="Symbol">}</a> <a id="2135" class="Symbol">(</a><a id="2136" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2136" class="Bound">P</a> <a id="2138" class="Symbol">:</a> <a id="2140" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2145" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2124" class="Bound">l</a><a id="2146" class="Symbol">)</a> <a id="2148" class="Symbol">→</a>
    <a id="2154" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a>
      <a id="2170" class="Symbol">(</a> <a id="2172" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a>
        <a id="2220" class="Symbol">(</a> <a id="2222" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="2262" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2136" class="Bound">P</a><a id="2263" class="Symbol">)</a> <a id="2265" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a>
        <a id="2275" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="2315" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2136" class="Bound">P</a><a id="2316" class="Symbol">)</a>
  <a id="2320" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2072" class="Function">is-idempotent-large-lawvere-tierney-topology</a> <a id="2365" class="Symbol">=</a>
    <a id="2371" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1283" class="Field">is-idempotent-is-large-lawvere-tierney-topology</a>
      <a id="2425" class="Symbol">(</a> <a id="2427" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1922" class="Field">is-large-lawvere-tierney-topology-large-lawvere-tierney-topology</a><a id="2491" class="Symbol">)</a>

  <a id="large-lawvere-tierney-topology.preserves-unit-large-lawvere-tierney-topology"></a><a id="2496" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2496" class="Function">preserves-unit-large-lawvere-tierney-topology</a> <a id="2542" class="Symbol">:</a>
    <a id="2548" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2558" class="Symbol">(</a><a id="2559" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="2599" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a> <a id="2609" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="2611" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a><a id="2620" class="Symbol">)</a>
  <a id="2624" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2496" class="Function">preserves-unit-large-lawvere-tierney-topology</a> <a id="2670" class="Symbol">=</a>
    <a id="2676" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1397" class="Field">preserves-unit-is-large-lawvere-tierney-topology</a>
      <a id="2731" class="Symbol">(</a> <a id="2733" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1922" class="Field">is-large-lawvere-tierney-topology-large-lawvere-tierney-topology</a><a id="2797" class="Symbol">)</a>

  <a id="large-lawvere-tierney-topology.preserves-conjunction-large-lawvere-tierney-topology"></a><a id="2802" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2802" class="Function">preserves-conjunction-large-lawvere-tierney-topology</a> <a id="2855" class="Symbol">:</a>
    <a id="2861" class="Symbol">{</a><a id="2862" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2862" class="Bound">l1</a> <a id="2865" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2865" class="Bound">l2</a> <a id="2868" class="Symbol">:</a> <a id="2870" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2875" class="Symbol">}</a> <a id="2877" class="Symbol">(</a><a id="2878" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2878" class="Bound">P</a> <a id="2880" class="Symbol">:</a> <a id="2882" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2887" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2862" class="Bound">l1</a><a id="2889" class="Symbol">)</a> <a id="2891" class="Symbol">(</a><a id="2892" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2892" class="Bound">Q</a> <a id="2894" class="Symbol">:</a> <a id="2896" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2901" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2865" class="Bound">l2</a><a id="2903" class="Symbol">)</a> <a id="2905" class="Symbol">→</a>
    <a id="2911" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a>
      <a id="2927" class="Symbol">(</a> <a id="2929" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="2969" class="Symbol">(</a><a id="2970" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2878" class="Bound">P</a> <a id="2972" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="2974" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2892" class="Bound">Q</a><a id="2975" class="Symbol">)</a> <a id="2977" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a>
        <a id="2987" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="3027" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2878" class="Bound">P</a> <a id="3029" href="foundation.conjunction.html#2377" class="Function Operator">∧</a>
        <a id="3039" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="3079" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2892" class="Bound">Q</a><a id="3080" class="Symbol">)</a>
  <a id="3084" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#2802" class="Function">preserves-conjunction-large-lawvere-tierney-topology</a> <a id="3137" class="Symbol">=</a>
    <a id="3143" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1495" class="Field">preserves-conjunction-is-large-lawvere-tierney-topology</a>
      <a id="3205" class="Symbol">(</a> <a id="3207" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1922" class="Field">is-large-lawvere-tierney-topology-large-lawvere-tierney-topology</a><a id="3271" class="Symbol">)</a>

  <a id="large-lawvere-tierney-topology.type-operator-large-lawvere-tierney-topology"></a><a id="3276" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3276" class="Function">type-operator-large-lawvere-tierney-topology</a> <a id="3321" class="Symbol">:</a> <a id="3323" class="Symbol">{</a><a id="3324" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3324" class="Bound">l</a> <a id="3326" class="Symbol">:</a> <a id="3328" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3333" class="Symbol">}</a> <a id="3335" class="Symbol">→</a> <a id="3337" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3342" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3324" class="Bound">l</a> <a id="3344" class="Symbol">→</a> <a id="3346" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3349" class="Symbol">(</a><a id="3350" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1796" class="Bound">δ</a> <a id="3352" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3324" class="Bound">l</a><a id="3353" class="Symbol">)</a>
  <a id="3357" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3276" class="Function">type-operator-large-lawvere-tierney-topology</a> <a id="3402" class="Symbol">=</a>
    <a id="3408" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="3418" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3420" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a>

<a id="3461" class="Keyword">open</a> <a id="3466" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1764" class="Module">large-lawvere-tierney-topology</a> <a id="3497" class="Keyword">public</a>
</pre>
## Examples

### The identity large Lawvere-Tierney topology

<pre class="Agda"><a id="is-large-lawvere-tierney-topology-id"></a><a id="3579" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3579" class="Function">is-large-lawvere-tierney-topology-id</a> <a id="3616" class="Symbol">:</a> <a id="3618" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1159" class="Record">is-large-lawvere-tierney-topology</a> <a id="3652" href="foundation-core.function-types.html#307" class="Function">id</a>
<a id="3655" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3579" class="Function">is-large-lawvere-tierney-topology-id</a> <a id="3692" class="Symbol">=</a>
  <a id="3696" class="Symbol">λ</a> <a id="3698" class="Keyword">where</a>
  <a id="3706" class="Symbol">.</a><a id="3707" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1283" class="Field">is-idempotent-is-large-lawvere-tierney-topology</a> <a id="3755" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3755" class="Bound">P</a> <a id="3757" class="Symbol">→</a> <a id="3759" href="foundation.logical-equivalences.html#2946" class="Function">id-iff</a>
  <a id="3768" class="Symbol">.</a><a id="3769" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1397" class="Field">preserves-unit-is-large-lawvere-tierney-topology</a> <a id="3818" class="Symbol">→</a> <a id="3820" href="foundation.logical-equivalences.html#2946" class="Function">id-iff</a>
  <a id="3829" class="Symbol">.</a><a id="3830" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1495" class="Field">preserves-conjunction-is-large-lawvere-tierney-topology</a> <a id="3886" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3886" class="Bound">P</a> <a id="3888" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3888" class="Bound">Q</a> <a id="3890" class="Symbol">→</a> <a id="3892" href="foundation.logical-equivalences.html#2946" class="Function">id-iff</a>

<a id="id-large-lawvere-tierney-topology"></a><a id="3900" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3900" class="Function">id-large-lawvere-tierney-topology</a> <a id="3934" class="Symbol">:</a> <a id="3936" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1764" class="Record">large-lawvere-tierney-topology</a> <a id="3967" class="Symbol">(λ</a> <a id="3970" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3970" class="Bound">l</a> <a id="3972" class="Symbol">→</a> <a id="3974" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3970" class="Bound">l</a><a id="3975" class="Symbol">)</a>
<a id="3977" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3900" class="Function">id-large-lawvere-tierney-topology</a> <a id="4011" class="Symbol">=</a>
  <a id="4015" class="Symbol">λ</a> <a id="4017" class="Keyword">where</a>
  <a id="4025" class="Symbol">.</a><a id="4026" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="4066" class="Symbol">→</a>
    <a id="4072" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="4077" class="Symbol">.</a><a id="4078" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1922" class="Field">is-large-lawvere-tierney-topology-large-lawvere-tierney-topology</a> <a id="4143" class="Symbol">→</a>
    <a id="4149" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#3579" class="Function">is-large-lawvere-tierney-topology-id</a>
</pre>
## See also

- [(Small) Lawvere-Tierney topologies](orthogonal-factorization-systems.lawvere-tierney-topologies.md)
- The
  [continuation modalities](orthogonal-factorization-systems.continuation-modalities.md)
  define Lawvere–Tierney topologies, and as a special case so does the
  [double negation modality](foundation.double-negation-modality.md).

## References

Lawvere–Tierney topologies in the context of Homotopy Type Theory are introduced
and studied in Chapter 6 of {{#cite Qui16}}.

{{#bibliography}} {{#reference Qui16}}

## External links

- [Lawvere–Tierney topology](https://ncatlab.org/nlab/show/Lawvere-Tierney+topology)
  at $n$Lab
- [Lawvere–Tierney topology](https://en.wikipedia.org/wiki/Lawvere%E2%80%93Tierney_topology)
  at Wikipedia
