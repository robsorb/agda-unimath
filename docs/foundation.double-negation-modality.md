# The double negation modality

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation.double-negation-modality.html" class="Module">foundation.double-negation-modality</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="184" class="Keyword">open</a> <a id="189" class="Keyword">import</a> <a id="196" href="foundation.double-negation.html" class="Module">foundation.double-negation</a>
<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="334" class="Keyword">open</a> <a id="339" class="Keyword">import</a> <a id="346" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="403" class="Keyword">open</a> <a id="408" class="Keyword">import</a> <a id="415" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="foundation-core.transport-along-identifications.html" class="Module">foundation-core.transport-along-identifications</a>

<a id="547" class="Keyword">open</a> <a id="552" class="Keyword">import</a> <a id="559" href="logic.double-negation-elimination.html" class="Module">logic.double-negation-elimination</a>

<a id="594" class="Keyword">open</a> <a id="599" class="Keyword">import</a> <a id="606" href="orthogonal-factorization-systems.continuation-modalities.html" class="Module">orthogonal-factorization-systems.continuation-modalities</a>
<a id="663" class="Keyword">open</a> <a id="668" class="Keyword">import</a> <a id="675" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html" class="Module">orthogonal-factorization-systems.large-lawvere-tierney-topologies</a>
<a id="741" class="Keyword">open</a> <a id="746" class="Keyword">import</a> <a id="753" href="orthogonal-factorization-systems.lawvere-tierney-topologies.html" class="Module">orthogonal-factorization-systems.lawvere-tierney-topologies</a>
<a id="813" class="Keyword">open</a> <a id="818" class="Keyword">import</a> <a id="825" href="orthogonal-factorization-systems.modal-operators.html" class="Module">orthogonal-factorization-systems.modal-operators</a>
<a id="874" class="Keyword">open</a> <a id="879" class="Keyword">import</a> <a id="886" href="orthogonal-factorization-systems.types-local-at-maps.html" class="Module">orthogonal-factorization-systems.types-local-at-maps</a>
<a id="939" class="Keyword">open</a> <a id="944" class="Keyword">import</a> <a id="951" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html" class="Module">orthogonal-factorization-systems.uniquely-eliminating-modalities</a>
</pre>
</details>

## Idea

The [double negation](foundation.double-negation.md) operation `¬¬` is a
[modality](orthogonal-factorization-systems.higher-modalities.md).

## Definition

### The double negation modality

<pre class="Agda"><a id="operator-double-negation-modality"></a><a id="1240" href="foundation.double-negation-modality.html#1240" class="Function">operator-double-negation-modality</a> <a id="1274" class="Symbol">:</a>
  <a id="1278" class="Symbol">(</a><a id="1279" href="foundation.double-negation-modality.html#1279" class="Bound">l</a> <a id="1281" class="Symbol">:</a> <a id="1283" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1288" class="Symbol">)</a> <a id="1290" class="Symbol">→</a> <a id="1292" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="1310" href="foundation.double-negation-modality.html#1279" class="Bound">l</a> <a id="1312" href="foundation.double-negation-modality.html#1279" class="Bound">l</a>
<a id="1314" href="foundation.double-negation-modality.html#1240" class="Function">operator-double-negation-modality</a> <a id="1348" class="Symbol">_</a> <a id="1350" class="Symbol">=</a> <a id="1352" href="foundation.double-negation.html#572" class="Function Operator">¬¬_</a>

<a id="unit-double-negation-modality"></a><a id="1357" href="foundation.double-negation-modality.html#1357" class="Function">unit-double-negation-modality</a> <a id="1387" class="Symbol">:</a>
  <a id="1391" class="Symbol">{</a><a id="1392" href="foundation.double-negation-modality.html#1392" class="Bound">l</a> <a id="1394" class="Symbol">:</a> <a id="1396" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1401" class="Symbol">}</a> <a id="1403" class="Symbol">→</a> <a id="1405" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="1419" class="Symbol">(</a><a id="1420" href="foundation.double-negation-modality.html#1240" class="Function">operator-double-negation-modality</a> <a id="1454" href="foundation.double-negation-modality.html#1392" class="Bound">l</a><a id="1455" class="Symbol">)</a>
<a id="1457" href="foundation.double-negation-modality.html#1357" class="Function">unit-double-negation-modality</a> <a id="1487" class="Symbol">=</a> <a id="1489" href="foundation.double-negation.html#782" class="Function">intro-double-negation</a>
</pre>
## Properties

### The double negation modality is a uniquely eliminating modality

The double negation modality is an instance of a
[continuation modality](orthogonal-factorization-systems.continuation-modalities.md).

<pre class="Agda"><a id="is-uniquely-eliminating-modality-double-negation-modality"></a><a id="1744" href="foundation.double-negation-modality.html#1744" class="Function">is-uniquely-eliminating-modality-double-negation-modality</a> <a id="1802" class="Symbol">:</a>
  <a id="1806" class="Symbol">{</a><a id="1807" href="foundation.double-negation-modality.html#1807" class="Bound">l</a> <a id="1809" class="Symbol">:</a> <a id="1811" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1816" class="Symbol">}</a> <a id="1818" class="Symbol">→</a>
  <a id="1822" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html#1327" class="Function">is-uniquely-eliminating-modality</a> <a id="1855" class="Symbol">(</a><a id="1856" href="foundation.double-negation-modality.html#1357" class="Function">unit-double-negation-modality</a> <a id="1886" class="Symbol">{</a><a id="1887" href="foundation.double-negation-modality.html#1807" class="Bound">l</a><a id="1888" class="Symbol">})</a>
<a id="1891" href="foundation.double-negation-modality.html#1744" class="Function">is-uniquely-eliminating-modality-double-negation-modality</a> <a id="1949" class="Symbol">{</a><a id="1950" href="foundation.double-negation-modality.html#1950" class="Bound">l</a><a id="1951" class="Symbol">}</a> <a id="1953" class="Symbol">=</a>
  <a id="1957" href="orthogonal-factorization-systems.continuation-modalities.html#2119" class="Function">is-uniquely-eliminating-modality-continuation-modality</a> <a id="2012" href="foundation.double-negation-modality.html#1950" class="Bound">l</a> <a id="2014" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a>
</pre>
### The double negation modality defines a Lawvere–Tierney topology

<pre class="Agda"><a id="is-large-lawvere-tierney-topology-double-negation"></a><a id="2107" href="foundation.double-negation-modality.html#2107" class="Function">is-large-lawvere-tierney-topology-double-negation</a> <a id="2157" class="Symbol">:</a>
  <a id="2161" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1159" class="Record">is-large-lawvere-tierney-topology</a> <a id="2195" href="foundation.double-negation.html#1513" class="Function">double-negation-Prop</a>
<a id="2216" href="foundation.double-negation-modality.html#2107" class="Function">is-large-lawvere-tierney-topology-double-negation</a> <a id="2266" class="Symbol">=</a>
  <a id="2270" class="Symbol">λ</a> <a id="2272" class="Keyword">where</a>
  <a id="2280" class="Symbol">.</a><a id="2281" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1283" class="Field">is-idempotent-is-large-lawvere-tierney-topology</a> <a id="2329" href="foundation.double-negation-modality.html#2329" class="Bound">P</a> <a id="2331" class="Symbol">→</a>
    <a id="2337" class="Symbol">(</a> <a id="2339" href="logic.double-negation-elimination.html#4755" class="Function">double-negation-elim-neg</a> <a id="2364" class="Symbol">(</a><a id="2365" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2367" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2377" href="foundation.double-negation-modality.html#2329" class="Bound">P</a><a id="2378" class="Symbol">)</a> <a id="2380" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2382" href="foundation.double-negation.html#782" class="Function">intro-double-negation</a><a id="2403" class="Symbol">)</a>
  <a id="2407" class="Symbol">.</a><a id="2408" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1397" class="Field">preserves-unit-is-large-lawvere-tierney-topology</a> <a id="2457" class="Symbol">→</a>
    <a id="2463" href="orthogonal-factorization-systems.continuation-modalities.html#3085" class="Function">preserves-unit-continuation-modality&#39;</a>
  <a id="2503" class="Symbol">.</a><a id="2504" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1495" class="Field">preserves-conjunction-is-large-lawvere-tierney-topology</a> <a id="2560" href="foundation.double-negation-modality.html#2560" class="Bound">P</a> <a id="2562" href="foundation.double-negation-modality.html#2562" class="Bound">Q</a> <a id="2564" class="Symbol">→</a>
    <a id="2570" href="orthogonal-factorization-systems.continuation-modalities.html#4812" class="Function">distributive-product-continuation-modality&#39;</a>

<a id="large-lawvere-tierney-topology-double-negation"></a><a id="2615" href="foundation.double-negation-modality.html#2615" class="Function">large-lawvere-tierney-topology-double-negation</a> <a id="2662" class="Symbol">:</a>
  <a id="2666" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1764" class="Record">large-lawvere-tierney-topology</a> <a id="2697" class="Symbol">(λ</a> <a id="2700" href="foundation.double-negation-modality.html#2700" class="Bound">l</a> <a id="2702" class="Symbol">→</a> <a id="2704" href="foundation.double-negation-modality.html#2700" class="Bound">l</a><a id="2705" class="Symbol">)</a>
<a id="2707" href="foundation.double-negation-modality.html#2615" class="Function">large-lawvere-tierney-topology-double-negation</a> <a id="2754" class="Symbol">=</a>
  <a id="2758" class="Symbol">λ</a> <a id="2760" class="Keyword">where</a>
  <a id="2768" class="Symbol">.</a><a id="2769" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1841" class="Field">operator-large-lawvere-tierney-topology</a> <a id="2809" class="Symbol">→</a>
    <a id="2815" href="foundation.double-negation.html#1513" class="Function">double-negation-Prop</a>
  <a id="2838" class="Symbol">.</a><a id="2839" href="orthogonal-factorization-systems.large-lawvere-tierney-topologies.html#1922" class="Field">is-large-lawvere-tierney-topology-large-lawvere-tierney-topology</a> <a id="2904" class="Symbol">→</a>
    <a id="2910" href="foundation.double-negation-modality.html#2107" class="Function">is-large-lawvere-tierney-topology-double-negation</a>
</pre>