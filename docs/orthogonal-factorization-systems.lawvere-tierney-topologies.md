# Lawvere–Tierney topologies

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html" class="Module">orthogonal-factorization-systems.lawvere-tierney-topologies</a> <a id="106" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="foundation.propositional-extensionality.html" class="Module">foundation.propositional-extensionality</a>
<a id="422" class="Keyword">open</a> <a id="427" class="Keyword">import</a> <a id="434" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="458" class="Keyword">open</a> <a id="463" class="Keyword">import</a> <a id="470" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="518" class="Keyword">open</a> <a id="523" class="Keyword">import</a> <a id="530" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="551" class="Keyword">open</a> <a id="556" class="Keyword">import</a> <a id="563" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A (small) {#concept "Lawvere–Tierney topology" Disambiguation="on types"} on
types is a map

```text
  j : Prop → Prop
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

<pre class="Agda"><a id="1149" class="Keyword">module</a> <a id="1156" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1156" class="Module">_</a>
  <a id="1160" class="Symbol">{</a><a id="1161" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a> <a id="1163" class="Symbol">:</a> <a id="1165" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1170" class="Symbol">}</a> <a id="1172" class="Symbol">(</a><a id="1173" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1173" class="Bound">j</a> <a id="1175" class="Symbol">:</a> <a id="1177" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1182" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a> <a id="1184" class="Symbol">→</a> <a id="1186" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1191" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a><a id="1192" class="Symbol">)</a>
  <a id="1196" class="Keyword">where</a>

  <a id="1205" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1205" class="Function">is-lawvere-tierney-topology-Prop</a> <a id="1238" class="Symbol">:</a> <a id="1240" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1245" class="Symbol">(</a><a id="1246" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1251" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a><a id="1252" class="Symbol">)</a>
  <a id="1256" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1205" class="Function">is-lawvere-tierney-topology-Prop</a> <a id="1289" class="Symbol">=</a>
    <a id="1295" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="1314" class="Symbol">(</a> <a id="1316" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1323" class="Symbol">(</a><a id="1324" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1329" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a><a id="1330" class="Symbol">)</a> <a id="1332" class="Symbol">(λ</a> <a id="1335" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1335" class="Bound">P</a> <a id="1337" class="Symbol">→</a> <a id="1339" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1173" class="Bound">j</a> <a id="1341" class="Symbol">(</a><a id="1342" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1173" class="Bound">j</a> <a id="1344" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1335" class="Bound">P</a><a id="1345" class="Symbol">)</a> <a id="1347" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="1349" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1173" class="Bound">j</a> <a id="1351" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1335" class="Bound">P</a><a id="1352" class="Symbol">))</a>
      <a id="1361" class="Symbol">(</a> <a id="1363" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
        <a id="1384" class="Symbol">(</a> <a id="1386" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1173" class="Bound">j</a> <a id="1388" class="Symbol">(</a><a id="1389" href="foundation.unit-type.html#4828" class="Function">raise-unit-Prop</a> <a id="1405" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a><a id="1406" class="Symbol">)</a> <a id="1408" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="1410" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a><a id="1419" class="Symbol">)</a>
        <a id="1429" class="Symbol">(</a> <a id="1431" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
          <a id="1448" class="Symbol">(</a> <a id="1450" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1455" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a><a id="1456" class="Symbol">)</a>
          <a id="1468" class="Symbol">(</a> <a id="1470" class="Symbol">λ</a> <a id="1472" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1472" class="Bound">P</a> <a id="1474" class="Symbol">→</a>
            <a id="1488" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1495" class="Symbol">(</a><a id="1496" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1501" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a><a id="1502" class="Symbol">)</a> <a id="1504" class="Symbol">(λ</a> <a id="1507" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1507" class="Bound">Q</a> <a id="1509" class="Symbol">→</a> <a id="1511" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1173" class="Bound">j</a> <a id="1513" class="Symbol">(</a><a id="1514" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1472" class="Bound">P</a> <a id="1516" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="1518" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1507" class="Bound">Q</a><a id="1519" class="Symbol">)</a> <a id="1521" href="foundation.logical-equivalences.html#2857" class="Function Operator">⇔</a> <a id="1523" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1173" class="Bound">j</a> <a id="1525" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1472" class="Bound">P</a> <a id="1527" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="1529" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1173" class="Bound">j</a> <a id="1531" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1507" class="Bound">Q</a><a id="1532" class="Symbol">))))</a>

  <a id="1540" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1540" class="Function">is-lawvere-tierney-topology</a> <a id="1568" class="Symbol">:</a> <a id="1570" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1573" class="Symbol">(</a><a id="1574" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1579" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1161" class="Bound">l</a><a id="1580" class="Symbol">)</a>
  <a id="1584" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1540" class="Function">is-lawvere-tierney-topology</a> <a id="1612" class="Symbol">=</a> <a id="1614" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1624" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1205" class="Function">is-lawvere-tierney-topology-Prop</a>

  <a id="1660" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1660" class="Function">is-prop-is-lawvere-tierney-topology</a> <a id="1696" class="Symbol">:</a> <a id="1698" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1706" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1540" class="Function">is-lawvere-tierney-topology</a>
  <a id="1736" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1660" class="Function">is-prop-is-lawvere-tierney-topology</a> <a id="1772" class="Symbol">=</a>
    <a id="1778" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1796" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1205" class="Function">is-lawvere-tierney-topology-Prop</a>
</pre>
### The set of Lawvere-Tierney topologies

<pre class="Agda"><a id="lawvere-tierney-topology"></a><a id="1885" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1885" class="Function">lawvere-tierney-topology</a> <a id="1910" class="Symbol">:</a> <a id="1912" class="Symbol">(</a><a id="1913" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1913" class="Bound">l</a> <a id="1915" class="Symbol">:</a> <a id="1917" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1922" class="Symbol">)</a> <a id="1924" class="Symbol">→</a> <a id="1926" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1929" class="Symbol">(</a><a id="1930" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1935" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1913" class="Bound">l</a><a id="1936" class="Symbol">)</a>
<a id="1938" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1885" class="Function">lawvere-tierney-topology</a> <a id="1963" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1963" class="Bound">l</a> <a id="1965" class="Symbol">=</a> <a id="1967" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1969" class="Symbol">(</a><a id="1970" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1975" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1963" class="Bound">l</a> <a id="1977" class="Symbol">→</a> <a id="1979" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1984" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1963" class="Bound">l</a><a id="1985" class="Symbol">)</a> <a id="1987" class="Symbol">(</a><a id="1988" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1540" class="Function">is-lawvere-tierney-topology</a><a id="2015" class="Symbol">)</a>

<a id="is-set-lawvere-tierney-topology"></a><a id="2018" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2018" class="Function">is-set-lawvere-tierney-topology</a> <a id="2050" class="Symbol">:</a>
  <a id="2054" class="Symbol">{</a><a id="2055" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2055" class="Bound">l</a> <a id="2057" class="Symbol">:</a> <a id="2059" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2064" class="Symbol">}</a> <a id="2066" class="Symbol">→</a> <a id="2068" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="2075" class="Symbol">(</a><a id="2076" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1885" class="Function">lawvere-tierney-topology</a> <a id="2101" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2055" class="Bound">l</a><a id="2102" class="Symbol">)</a>
<a id="2104" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2018" class="Function">is-set-lawvere-tierney-topology</a> <a id="2136" class="Symbol">=</a>
  <a id="2140" href="foundation-core.subtypes.html#8055" class="Function">is-set-type-subtype</a> <a id="2160" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1205" class="Function">is-lawvere-tierney-topology-Prop</a> <a id="2193" class="Symbol">(</a><a id="2194" href="foundation.subtypes.html#5155" class="Function">is-set-subtype</a><a id="2208" class="Symbol">)</a>

<a id="set-lawvere-tierney-topology"></a><a id="2211" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2211" class="Function">set-lawvere-tierney-topology</a> <a id="2240" class="Symbol">:</a> <a id="2242" class="Symbol">(</a><a id="2243" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2243" class="Bound">l</a> <a id="2245" class="Symbol">:</a> <a id="2247" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2252" class="Symbol">)</a> <a id="2254" class="Symbol">→</a> <a id="2256" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="2260" class="Symbol">(</a><a id="2261" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2266" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2243" class="Bound">l</a><a id="2267" class="Symbol">)</a>
<a id="2269" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2211" class="Function">set-lawvere-tierney-topology</a> <a id="2298" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2298" class="Bound">l</a> <a id="2300" class="Symbol">=</a>
  <a id="2304" class="Symbol">(</a><a id="2305" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1885" class="Function">lawvere-tierney-topology</a> <a id="2330" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2298" class="Bound">l</a> <a id="2332" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2334" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2018" class="Function">is-set-lawvere-tierney-topology</a><a id="2365" class="Symbol">)</a>
</pre>
## Examples

### The identity function on propositions defines a Lawvere–Tierney topology

<pre class="Agda"><a id="is-lawvere-tierney-topology-id"></a><a id="2471" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2471" class="Function">is-lawvere-tierney-topology-id</a> <a id="2502" class="Symbol">:</a>
  <a id="2506" class="Symbol">(</a><a id="2507" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2507" class="Bound">l</a> <a id="2509" class="Symbol">:</a> <a id="2511" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2516" class="Symbol">)</a> <a id="2518" class="Symbol">→</a> <a id="2520" class="Symbol">(</a><a id="2521" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1540" class="Function">is-lawvere-tierney-topology</a> <a id="2549" class="Symbol">(</a><a id="2550" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2553" class="Symbol">{</a><a id="2554" class="Argument">A</a> <a id="2556" class="Symbol">=</a> <a id="2558" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2563" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2507" class="Bound">l</a><a id="2564" class="Symbol">}))</a>
<a id="2568" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2572" class="Symbol">(</a><a id="2573" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2471" class="Function">is-lawvere-tierney-topology-id</a> <a id="2604" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2604" class="Bound">l</a><a id="2605" class="Symbol">)</a> <a id="2607" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2607" class="Bound">P</a> <a id="2609" class="Symbol">=</a>
  <a id="2613" href="foundation.logical-equivalences.html#2946" class="Function">id-iff</a>
<a id="2620" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2624" class="Symbol">(</a><a id="2625" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2629" class="Symbol">(</a><a id="2630" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2471" class="Function">is-lawvere-tierney-topology-id</a> <a id="2661" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2661" class="Bound">l</a><a id="2662" class="Symbol">))</a> <a id="2665" class="Symbol">=</a>
  <a id="2669" href="foundation.logical-equivalences.html#5651" class="Function">iff-equiv</a> <a id="2679" class="Symbol">(</a><a id="2680" href="foundation.unit-type.html#1897" class="Function">inv-compute-raise-unit</a> <a id="2703" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2661" class="Bound">l</a><a id="2704" class="Symbol">)</a>
<a id="2706" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2710" class="Symbol">(</a><a id="2711" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2715" class="Symbol">(</a><a id="2716" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2471" class="Function">is-lawvere-tierney-topology-id</a> <a id="2747" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2747" class="Bound">l</a><a id="2748" class="Symbol">))</a> <a id="2751" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2751" class="Bound">Q</a> <a id="2753" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2753" class="Bound">P</a> <a id="2755" class="Symbol">=</a>
  <a id="2759" href="foundation.logical-equivalences.html#2946" class="Function">id-iff</a>

<a id="id-lawvere-tierney-topology"></a><a id="2767" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2767" class="Function">id-lawvere-tierney-topology</a> <a id="2795" class="Symbol">:</a> <a id="2797" class="Symbol">(</a><a id="2798" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2798" class="Bound">l</a> <a id="2800" class="Symbol">:</a> <a id="2802" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2807" class="Symbol">)</a> <a id="2809" class="Symbol">→</a> <a id="2811" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#1885" class="Function">lawvere-tierney-topology</a> <a id="2836" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2798" class="Bound">l</a>
<a id="2838" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2767" class="Function">id-lawvere-tierney-topology</a> <a id="2866" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2866" class="Bound">l</a> <a id="2868" class="Symbol">=</a> <a id="2870" class="Symbol">(</a><a id="2871" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2874" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2876" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2471" class="Function">is-lawvere-tierney-topology-id</a> <a id="2907" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html#2866" class="Bound">l</a><a id="2908" class="Symbol">)</a>
</pre>
## See also

- [Large Lawvere-Tierney topologies](orthogonal-factorization-systems.large-lawvere-tierney-topologies.md)
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
