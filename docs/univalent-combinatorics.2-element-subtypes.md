# `2`-element subtypes

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="univalent-combinatorics.2-element-subtypes.html" class="Module">univalent-combinatorics.2-element-subtypes</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="409" class="Keyword">open</a> <a id="414" class="Keyword">import</a> <a id="421" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="462" class="Keyword">open</a> <a id="467" class="Keyword">import</a> <a id="474" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="500" class="Keyword">open</a> <a id="505" class="Keyword">import</a> <a id="512" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="538" class="Keyword">open</a> <a id="543" class="Keyword">import</a> <a id="550" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="582" class="Keyword">open</a> <a id="587" class="Keyword">import</a> <a id="594" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="623" class="Keyword">open</a> <a id="628" class="Keyword">import</a> <a id="635" href="foundation.negated-equality.html" class="Module">foundation.negated-equality</a>
<a id="663" class="Keyword">open</a> <a id="668" class="Keyword">import</a> <a id="675" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="712" class="Keyword">open</a> <a id="717" class="Keyword">import</a> <a id="724" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="748" class="Keyword">open</a> <a id="753" class="Keyword">import</a> <a id="760" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="776" class="Keyword">open</a> <a id="781" class="Keyword">import</a> <a id="788" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="808" class="Keyword">open</a> <a id="813" class="Keyword">import</a> <a id="820" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="855" class="Keyword">open</a> <a id="860" class="Keyword">import</a> <a id="867" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="910" class="Keyword">open</a> <a id="915" class="Keyword">import</a> <a id="922" href="foundation.type-arithmetic-coproduct-types.html" class="Module">foundation.type-arithmetic-coproduct-types</a>
<a id="965" class="Keyword">open</a> <a id="970" class="Keyword">import</a> <a id="977" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="998" class="Keyword">open</a> <a id="1003" class="Keyword">import</a> <a id="1010" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="1038" class="Keyword">open</a> <a id="1043" class="Keyword">import</a> <a id="1050" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="1090" class="Keyword">open</a> <a id="1095" class="Keyword">import</a> <a id="1102" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

A 2-element subtype of a type `A` is a subtype `P` of `A` of which its
underlying type `Σ A P` has cardinality 2. Such a subtype is said to be
decidable if the proposition `P x` is decidable for every `x : A`.

## Definitions

### The type of 2-element subtypes of a type

<pre class="Agda"><a id="2-Element-Subtype"></a><a id="1455" href="univalent-combinatorics.2-element-subtypes.html#1455" class="Function">2-Element-Subtype</a> <a id="1473" class="Symbol">:</a> <a id="1475" class="Symbol">{</a><a id="1476" href="univalent-combinatorics.2-element-subtypes.html#1476" class="Bound">l1</a> <a id="1479" class="Symbol">:</a> <a id="1481" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1486" class="Symbol">}</a> <a id="1488" class="Symbol">(</a><a id="1489" href="univalent-combinatorics.2-element-subtypes.html#1489" class="Bound">l2</a> <a id="1492" class="Symbol">:</a> <a id="1494" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1499" class="Symbol">)</a> <a id="1501" class="Symbol">→</a> <a id="1503" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1506" href="univalent-combinatorics.2-element-subtypes.html#1476" class="Bound">l1</a> <a id="1509" class="Symbol">→</a> <a id="1511" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1514" class="Symbol">(</a><a id="1515" href="univalent-combinatorics.2-element-subtypes.html#1476" class="Bound">l1</a> <a id="1518" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1520" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1525" href="univalent-combinatorics.2-element-subtypes.html#1489" class="Bound">l2</a><a id="1527" class="Symbol">)</a>
<a id="1529" href="univalent-combinatorics.2-element-subtypes.html#1455" class="Function">2-Element-Subtype</a> <a id="1547" href="univalent-combinatorics.2-element-subtypes.html#1547" class="Bound">l2</a> <a id="1550" href="univalent-combinatorics.2-element-subtypes.html#1550" class="Bound">X</a> <a id="1552" class="Symbol">=</a>
  <a id="1556" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1558" class="Symbol">(</a><a id="1559" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1567" href="univalent-combinatorics.2-element-subtypes.html#1547" class="Bound">l2</a> <a id="1570" href="univalent-combinatorics.2-element-subtypes.html#1550" class="Bound">X</a><a id="1571" class="Symbol">)</a> <a id="1573" class="Symbol">(λ</a> <a id="1576" href="univalent-combinatorics.2-element-subtypes.html#1576" class="Bound">P</a> <a id="1578" class="Symbol">→</a> <a id="1580" href="univalent-combinatorics.2-element-types.html#2556" class="Function">has-two-elements</a> <a id="1597" class="Symbol">(</a><a id="1598" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="1611" href="univalent-combinatorics.2-element-subtypes.html#1576" class="Bound">P</a><a id="1612" class="Symbol">))</a>

<a id="1616" class="Keyword">module</a> <a id="1623" href="univalent-combinatorics.2-element-subtypes.html#1623" class="Module">_</a>
  <a id="1627" class="Symbol">{</a><a id="1628" href="univalent-combinatorics.2-element-subtypes.html#1628" class="Bound">l1</a> <a id="1631" href="univalent-combinatorics.2-element-subtypes.html#1631" class="Bound">l2</a> <a id="1634" class="Symbol">:</a> <a id="1636" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1641" class="Symbol">}</a> <a id="1643" class="Symbol">{</a><a id="1644" href="univalent-combinatorics.2-element-subtypes.html#1644" class="Bound">X</a> <a id="1646" class="Symbol">:</a> <a id="1648" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1651" href="univalent-combinatorics.2-element-subtypes.html#1628" class="Bound">l1</a><a id="1653" class="Symbol">}</a> <a id="1655" class="Symbol">(</a><a id="1656" href="univalent-combinatorics.2-element-subtypes.html#1656" class="Bound">P</a> <a id="1658" class="Symbol">:</a> <a id="1660" href="univalent-combinatorics.2-element-subtypes.html#1455" class="Function">2-Element-Subtype</a> <a id="1678" href="univalent-combinatorics.2-element-subtypes.html#1631" class="Bound">l2</a> <a id="1681" href="univalent-combinatorics.2-element-subtypes.html#1644" class="Bound">X</a><a id="1682" class="Symbol">)</a>
  <a id="1686" class="Keyword">where</a>

  <a id="1695" href="univalent-combinatorics.2-element-subtypes.html#1695" class="Function">subtype-2-Element-Subtype</a> <a id="1721" class="Symbol">:</a> <a id="1723" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1731" href="univalent-combinatorics.2-element-subtypes.html#1631" class="Bound">l2</a> <a id="1734" href="univalent-combinatorics.2-element-subtypes.html#1644" class="Bound">X</a>
  <a id="1738" href="univalent-combinatorics.2-element-subtypes.html#1695" class="Function">subtype-2-Element-Subtype</a> <a id="1764" class="Symbol">=</a> <a id="1766" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1770" href="univalent-combinatorics.2-element-subtypes.html#1656" class="Bound">P</a>

  <a id="1775" href="univalent-combinatorics.2-element-subtypes.html#1775" class="Function">type-prop-2-Element-Subtype</a> <a id="1803" class="Symbol">:</a> <a id="1805" href="univalent-combinatorics.2-element-subtypes.html#1644" class="Bound">X</a> <a id="1807" class="Symbol">→</a> <a id="1809" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1812" href="univalent-combinatorics.2-element-subtypes.html#1631" class="Bound">l2</a>
  <a id="1817" href="univalent-combinatorics.2-element-subtypes.html#1775" class="Function">type-prop-2-Element-Subtype</a> <a id="1845" href="univalent-combinatorics.2-element-subtypes.html#1845" class="Bound">x</a> <a id="1847" class="Symbol">=</a> <a id="1849" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1859" class="Symbol">(</a><a id="1860" href="univalent-combinatorics.2-element-subtypes.html#1695" class="Function">subtype-2-Element-Subtype</a> <a id="1886" href="univalent-combinatorics.2-element-subtypes.html#1845" class="Bound">x</a><a id="1887" class="Symbol">)</a>

  <a id="1892" href="univalent-combinatorics.2-element-subtypes.html#1892" class="Function">is-prop-type-prop-2-Element-Subtype</a> <a id="1928" class="Symbol">:</a>
    <a id="1934" class="Symbol">(</a><a id="1935" href="univalent-combinatorics.2-element-subtypes.html#1935" class="Bound">x</a> <a id="1937" class="Symbol">:</a> <a id="1939" href="univalent-combinatorics.2-element-subtypes.html#1644" class="Bound">X</a><a id="1940" class="Symbol">)</a> <a id="1942" class="Symbol">→</a> <a id="1944" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1952" class="Symbol">(</a><a id="1953" href="univalent-combinatorics.2-element-subtypes.html#1775" class="Function">type-prop-2-Element-Subtype</a> <a id="1981" href="univalent-combinatorics.2-element-subtypes.html#1935" class="Bound">x</a><a id="1982" class="Symbol">)</a>
  <a id="1986" href="univalent-combinatorics.2-element-subtypes.html#1892" class="Function">is-prop-type-prop-2-Element-Subtype</a> <a id="2022" href="univalent-combinatorics.2-element-subtypes.html#2022" class="Bound">x</a> <a id="2024" class="Symbol">=</a>
    <a id="2030" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2048" class="Symbol">(</a><a id="2049" href="univalent-combinatorics.2-element-subtypes.html#1695" class="Function">subtype-2-Element-Subtype</a> <a id="2075" href="univalent-combinatorics.2-element-subtypes.html#2022" class="Bound">x</a><a id="2076" class="Symbol">)</a>

  <a id="2081" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a> <a id="2104" class="Symbol">:</a> <a id="2106" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2109" class="Symbol">(</a><a id="2110" href="univalent-combinatorics.2-element-subtypes.html#1628" class="Bound">l1</a> <a id="2113" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2115" href="univalent-combinatorics.2-element-subtypes.html#1631" class="Bound">l2</a><a id="2117" class="Symbol">)</a>
  <a id="2121" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a> <a id="2144" class="Symbol">=</a> <a id="2146" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="2159" href="univalent-combinatorics.2-element-subtypes.html#1695" class="Function">subtype-2-Element-Subtype</a>

  <a id="2188" href="univalent-combinatorics.2-element-subtypes.html#2188" class="Function">inclusion-2-Element-Subtype</a> <a id="2216" class="Symbol">:</a> <a id="2218" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a> <a id="2241" class="Symbol">→</a> <a id="2243" href="univalent-combinatorics.2-element-subtypes.html#1644" class="Bound">X</a>
  <a id="2247" href="univalent-combinatorics.2-element-subtypes.html#2188" class="Function">inclusion-2-Element-Subtype</a> <a id="2275" class="Symbol">=</a> <a id="2277" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a> <a id="2295" href="univalent-combinatorics.2-element-subtypes.html#1695" class="Function">subtype-2-Element-Subtype</a>

  <a id="2324" href="univalent-combinatorics.2-element-subtypes.html#2324" class="Function">is-emb-inclusion-2-Element-Subtype</a> <a id="2359" class="Symbol">:</a> <a id="2361" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="2368" href="univalent-combinatorics.2-element-subtypes.html#2188" class="Function">inclusion-2-Element-Subtype</a>
  <a id="2398" href="univalent-combinatorics.2-element-subtypes.html#2324" class="Function">is-emb-inclusion-2-Element-Subtype</a> <a id="2433" class="Symbol">=</a>
    <a id="2439" href="foundation-core.subtypes.html#4868" class="Function">is-emb-inclusion-subtype</a> <a id="2464" href="univalent-combinatorics.2-element-subtypes.html#1695" class="Function">subtype-2-Element-Subtype</a>

  <a id="2493" href="univalent-combinatorics.2-element-subtypes.html#2493" class="Function">is-injective-inclusion-2-Element-Subtype</a> <a id="2534" class="Symbol">:</a>
    <a id="2540" href="foundation-core.injective-maps.html#1182" class="Function">is-injective</a> <a id="2553" href="univalent-combinatorics.2-element-subtypes.html#2188" class="Function">inclusion-2-Element-Subtype</a>
  <a id="2583" href="univalent-combinatorics.2-element-subtypes.html#2493" class="Function">is-injective-inclusion-2-Element-Subtype</a> <a id="2624" class="Symbol">=</a>
    <a id="2630" href="foundation.subtypes.html#1644" class="Function">is-injective-inclusion-subtype</a> <a id="2661" href="univalent-combinatorics.2-element-subtypes.html#1695" class="Function">subtype-2-Element-Subtype</a>

  <a id="2690" href="univalent-combinatorics.2-element-subtypes.html#2690" class="Function">has-two-elements-type-2-Element-Subtype</a> <a id="2730" class="Symbol">:</a>
    <a id="2736" href="univalent-combinatorics.2-element-types.html#2556" class="Function">has-two-elements</a> <a id="2753" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a>
  <a id="2778" href="univalent-combinatorics.2-element-subtypes.html#2690" class="Function">has-two-elements-type-2-Element-Subtype</a> <a id="2818" class="Symbol">=</a> <a id="2820" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2824" href="univalent-combinatorics.2-element-subtypes.html#1656" class="Bound">P</a>

  <a id="2829" href="univalent-combinatorics.2-element-subtypes.html#2829" class="Function">2-element-type-2-Element-Subtype</a> <a id="2862" class="Symbol">:</a> <a id="2864" href="univalent-combinatorics.2-element-types.html#2893" class="Function">2-Element-Type</a> <a id="2879" class="Symbol">(</a><a id="2880" href="univalent-combinatorics.2-element-subtypes.html#1628" class="Bound">l1</a> <a id="2883" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2885" href="univalent-combinatorics.2-element-subtypes.html#1631" class="Bound">l2</a><a id="2887" class="Symbol">)</a>
  <a id="2891" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2895" href="univalent-combinatorics.2-element-subtypes.html#2829" class="Function">2-element-type-2-Element-Subtype</a> <a id="2928" class="Symbol">=</a> <a id="2930" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a>
  <a id="2955" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2959" href="univalent-combinatorics.2-element-subtypes.html#2829" class="Function">2-element-type-2-Element-Subtype</a> <a id="2992" class="Symbol">=</a> <a id="2994" href="univalent-combinatorics.2-element-subtypes.html#2690" class="Function">has-two-elements-type-2-Element-Subtype</a>

  <a id="3037" href="univalent-combinatorics.2-element-subtypes.html#3037" class="Function">is-inhabited-type-2-Element-Subtype</a> <a id="3073" class="Symbol">:</a> <a id="3075" href="foundation.propositional-truncations.html#1578" class="Function">type-trunc-Prop</a> <a id="3091" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a>
  <a id="3116" href="univalent-combinatorics.2-element-subtypes.html#3037" class="Function">is-inhabited-type-2-Element-Subtype</a> <a id="3152" class="Symbol">=</a>
    <a id="3158" href="univalent-combinatorics.2-element-types.html#4728" class="Function">is-inhabited-2-Element-Type</a> <a id="3186" href="univalent-combinatorics.2-element-subtypes.html#2829" class="Function">2-element-type-2-Element-Subtype</a>
</pre>
### The standard 2-element subtype of a pair of distinct elements in a set

<pre class="Agda"><a id="3308" class="Keyword">module</a> <a id="3315" href="univalent-combinatorics.2-element-subtypes.html#3315" class="Module">_</a>
  <a id="3319" class="Symbol">{</a><a id="3320" href="univalent-combinatorics.2-element-subtypes.html#3320" class="Bound">l</a> <a id="3322" class="Symbol">:</a> <a id="3324" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3329" class="Symbol">}</a> <a id="3331" class="Symbol">(</a><a id="3332" href="univalent-combinatorics.2-element-subtypes.html#3332" class="Bound">X</a> <a id="3334" class="Symbol">:</a> <a id="3336" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="3340" href="univalent-combinatorics.2-element-subtypes.html#3320" class="Bound">l</a><a id="3341" class="Symbol">)</a> <a id="3343" class="Symbol">{</a><a id="3344" href="univalent-combinatorics.2-element-subtypes.html#3344" class="Bound">x</a> <a id="3346" href="univalent-combinatorics.2-element-subtypes.html#3346" class="Bound">y</a> <a id="3348" class="Symbol">:</a> <a id="3350" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="3359" href="univalent-combinatorics.2-element-subtypes.html#3332" class="Bound">X</a><a id="3360" class="Symbol">}</a> <a id="3362" class="Symbol">(</a><a id="3363" href="univalent-combinatorics.2-element-subtypes.html#3363" class="Bound">np</a> <a id="3366" class="Symbol">:</a> <a id="3368" href="univalent-combinatorics.2-element-subtypes.html#3344" class="Bound">x</a> <a id="3370" href="foundation.negated-equality.html#733" class="Function Operator">≠</a> <a id="3372" href="univalent-combinatorics.2-element-subtypes.html#3346" class="Bound">y</a><a id="3373" class="Symbol">)</a>
  <a id="3377" class="Keyword">where</a>

  <a id="3386" href="univalent-combinatorics.2-element-subtypes.html#3386" class="Function">type-prop-standard-2-Element-Subtype</a> <a id="3423" class="Symbol">:</a> <a id="3425" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="3434" href="univalent-combinatorics.2-element-subtypes.html#3332" class="Bound">X</a> <a id="3436" class="Symbol">→</a> <a id="3438" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3441" href="univalent-combinatorics.2-element-subtypes.html#3320" class="Bound">l</a>
  <a id="3445" href="univalent-combinatorics.2-element-subtypes.html#3386" class="Function">type-prop-standard-2-Element-Subtype</a> <a id="3482" href="univalent-combinatorics.2-element-subtypes.html#3482" class="Bound">z</a> <a id="3484" class="Symbol">=</a> <a id="3486" class="Symbol">(</a><a id="3487" href="univalent-combinatorics.2-element-subtypes.html#3344" class="Bound">x</a> <a id="3489" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3491" href="univalent-combinatorics.2-element-subtypes.html#3482" class="Bound">z</a><a id="3492" class="Symbol">)</a> <a id="3494" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="3496" class="Symbol">(</a><a id="3497" href="univalent-combinatorics.2-element-subtypes.html#3346" class="Bound">y</a> <a id="3499" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3501" href="univalent-combinatorics.2-element-subtypes.html#3482" class="Bound">z</a><a id="3502" class="Symbol">)</a>

  <a id="3507" href="univalent-combinatorics.2-element-subtypes.html#3507" class="Function">is-prop-type-prop-standard-2-Element-Subtype</a> <a id="3552" class="Symbol">:</a>
    <a id="3558" class="Symbol">(</a><a id="3559" href="univalent-combinatorics.2-element-subtypes.html#3559" class="Bound">z</a> <a id="3561" class="Symbol">:</a> <a id="3563" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="3572" href="univalent-combinatorics.2-element-subtypes.html#3332" class="Bound">X</a><a id="3573" class="Symbol">)</a> <a id="3575" class="Symbol">→</a> <a id="3577" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3585" class="Symbol">(</a><a id="3586" href="univalent-combinatorics.2-element-subtypes.html#3386" class="Function">type-prop-standard-2-Element-Subtype</a> <a id="3623" href="univalent-combinatorics.2-element-subtypes.html#3559" class="Bound">z</a><a id="3624" class="Symbol">)</a>
  <a id="3628" href="univalent-combinatorics.2-element-subtypes.html#3507" class="Function">is-prop-type-prop-standard-2-Element-Subtype</a> <a id="3673" href="univalent-combinatorics.2-element-subtypes.html#3673" class="Bound">z</a> <a id="3675" class="Symbol">=</a>
    <a id="3681" href="foundation.coproduct-types.html#6530" class="Function">is-prop-coproduct</a>
      <a id="3705" class="Symbol">(</a> <a id="3707" class="Symbol">λ</a> <a id="3709" href="univalent-combinatorics.2-element-subtypes.html#3709" class="Bound">p</a> <a id="3711" href="univalent-combinatorics.2-element-subtypes.html#3711" class="Bound">q</a> <a id="3713" class="Symbol">→</a> <a id="3715" href="univalent-combinatorics.2-element-subtypes.html#3363" class="Bound">np</a> <a id="3718" class="Symbol">(</a><a id="3719" href="univalent-combinatorics.2-element-subtypes.html#3709" class="Bound">p</a> <a id="3721" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a> <a id="3723" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="3727" href="univalent-combinatorics.2-element-subtypes.html#3711" class="Bound">q</a><a id="3728" class="Symbol">))</a>
      <a id="3737" class="Symbol">(</a> <a id="3739" href="foundation-core.sets.html#1076" class="Function">is-set-type-Set</a> <a id="3755" href="univalent-combinatorics.2-element-subtypes.html#3332" class="Bound">X</a> <a id="3757" href="univalent-combinatorics.2-element-subtypes.html#3344" class="Bound">x</a> <a id="3759" href="univalent-combinatorics.2-element-subtypes.html#3673" class="Bound">z</a><a id="3760" class="Symbol">)</a>
      <a id="3768" class="Symbol">(</a> <a id="3770" href="foundation-core.sets.html#1076" class="Function">is-set-type-Set</a> <a id="3786" href="univalent-combinatorics.2-element-subtypes.html#3332" class="Bound">X</a> <a id="3788" href="univalent-combinatorics.2-element-subtypes.html#3346" class="Bound">y</a> <a id="3790" href="univalent-combinatorics.2-element-subtypes.html#3673" class="Bound">z</a><a id="3791" class="Symbol">)</a>

  <a id="3796" href="univalent-combinatorics.2-element-subtypes.html#3796" class="Function">subtype-standard-2-Element-Subtype</a> <a id="3831" class="Symbol">:</a> <a id="3833" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="3841" href="univalent-combinatorics.2-element-subtypes.html#3320" class="Bound">l</a> <a id="3843" class="Symbol">(</a><a id="3844" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="3853" href="univalent-combinatorics.2-element-subtypes.html#3332" class="Bound">X</a><a id="3854" class="Symbol">)</a>
  <a id="3858" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3862" class="Symbol">(</a><a id="3863" href="univalent-combinatorics.2-element-subtypes.html#3796" class="Function">subtype-standard-2-Element-Subtype</a> <a id="3898" href="univalent-combinatorics.2-element-subtypes.html#3898" class="Bound">z</a><a id="3899" class="Symbol">)</a> <a id="3901" class="Symbol">=</a>
    <a id="3907" href="univalent-combinatorics.2-element-subtypes.html#3386" class="Function">type-prop-standard-2-Element-Subtype</a> <a id="3944" href="univalent-combinatorics.2-element-subtypes.html#3898" class="Bound">z</a>
  <a id="3948" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3952" class="Symbol">(</a><a id="3953" href="univalent-combinatorics.2-element-subtypes.html#3796" class="Function">subtype-standard-2-Element-Subtype</a> <a id="3988" href="univalent-combinatorics.2-element-subtypes.html#3988" class="Bound">z</a><a id="3989" class="Symbol">)</a> <a id="3991" class="Symbol">=</a>
    <a id="3997" href="univalent-combinatorics.2-element-subtypes.html#3507" class="Function">is-prop-type-prop-standard-2-Element-Subtype</a> <a id="4042" href="univalent-combinatorics.2-element-subtypes.html#3988" class="Bound">z</a>

  <a id="4047" href="univalent-combinatorics.2-element-subtypes.html#4047" class="Function">type-standard-2-Element-Subtype</a> <a id="4079" class="Symbol">:</a> <a id="4081" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4084" href="univalent-combinatorics.2-element-subtypes.html#3320" class="Bound">l</a>
  <a id="4088" href="univalent-combinatorics.2-element-subtypes.html#4047" class="Function">type-standard-2-Element-Subtype</a> <a id="4120" class="Symbol">=</a>
    <a id="4126" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="4139" href="univalent-combinatorics.2-element-subtypes.html#3796" class="Function">subtype-standard-2-Element-Subtype</a>

  <a id="4177" href="univalent-combinatorics.2-element-subtypes.html#4177" class="Function">equiv-type-standard-2-Element-Subtype</a> <a id="4215" class="Symbol">:</a>
    <a id="4221" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="4225" class="Number">2</a> <a id="4227" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="4229" href="univalent-combinatorics.2-element-subtypes.html#4047" class="Function">type-standard-2-Element-Subtype</a>
  <a id="4263" href="univalent-combinatorics.2-element-subtypes.html#4177" class="Function">equiv-type-standard-2-Element-Subtype</a> <a id="4301" class="Symbol">=</a>
    <a id="4307" class="Symbol">(</a> <a id="4309" href="foundation-core.equivalences.html#8859" class="Function">inv-equiv</a>
      <a id="4325" class="Symbol">(</a> <a id="4327" href="foundation.type-arithmetic-coproduct-types.html#7817" class="Function">left-distributive-Σ-coproduct</a> <a id="4357" class="Symbol">(</a><a id="4358" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="4367" href="univalent-combinatorics.2-element-subtypes.html#3332" class="Bound">X</a><a id="4368" class="Symbol">)</a> <a id="4370" class="Symbol">(</a><a id="4371" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a> <a id="4374" href="univalent-combinatorics.2-element-subtypes.html#3344" class="Bound">x</a><a id="4375" class="Symbol">)</a> <a id="4377" class="Symbol">(</a><a id="4378" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a> <a id="4381" href="univalent-combinatorics.2-element-subtypes.html#3346" class="Bound">y</a><a id="4382" class="Symbol">)))</a> <a id="4386" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
    <a id="4393" class="Symbol">(</a> <a id="4395" href="foundation.functoriality-coproduct-types.html#8707" class="Function">equiv-coproduct</a>
      <a id="4417" class="Symbol">(</a> <a id="4419" href="foundation-core.contractible-types.html#3405" class="Function">equiv-is-contr</a>
        <a id="4442" class="Symbol">(</a> <a id="4444" href="univalent-combinatorics.standard-finite-types.html#5116" class="Function">is-contr-Fin-1</a><a id="4458" class="Symbol">)</a>
        <a id="4468" class="Symbol">(</a> <a id="4470" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a> <a id="4486" href="univalent-combinatorics.2-element-subtypes.html#3344" class="Bound">x</a><a id="4487" class="Symbol">))</a>
      <a id="4496" class="Symbol">(</a> <a id="4498" href="foundation-core.contractible-types.html#3405" class="Function">equiv-is-contr</a>
        <a id="4521" class="Symbol">(</a> <a id="4523" href="foundation.unit-type.html#2082" class="Function">is-contr-unit</a><a id="4536" class="Symbol">)</a>
        <a id="4546" class="Symbol">(</a> <a id="4548" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a> <a id="4564" href="univalent-combinatorics.2-element-subtypes.html#3346" class="Bound">y</a><a id="4565" class="Symbol">)))</a>

  <a id="4572" href="univalent-combinatorics.2-element-subtypes.html#4572" class="Function">has-two-elements-type-standard-2-Element-Subtype</a> <a id="4621" class="Symbol">:</a>
    <a id="4627" href="univalent-combinatorics.2-element-types.html#2556" class="Function">has-two-elements</a> <a id="4644" href="univalent-combinatorics.2-element-subtypes.html#4047" class="Function">type-standard-2-Element-Subtype</a>
  <a id="4678" href="univalent-combinatorics.2-element-subtypes.html#4572" class="Function">has-two-elements-type-standard-2-Element-Subtype</a> <a id="4727" class="Symbol">=</a>
    <a id="4733" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="4749" href="univalent-combinatorics.2-element-subtypes.html#4177" class="Function">equiv-type-standard-2-Element-Subtype</a>
</pre>
### Morphisms of 2-element-subtypes

A moprhism of 2-element subtypes `P` and `Q` is just a family of maps
`P x → Q x`.

<pre class="Agda"><a id="4921" class="Comment">{-
module _
  {l1 l2 l3 : Level} {X : UU l1}
  (P : 2-Element-Subtype l2 X) (Q : 2-Element-Subtype l3 X)
  where

  hom-2-Element-Subtype : UU (l1 ⊔ l2 ⊔ l3)
  hom-2-Element-Subtype =
    (x : X) → type-prop-2-Element-Subtype P x → type-prop-2-Element-Subtype Q x

  map-hom-2-Element-Subtype :
    hom-2-Element-Subtype → type-2-Element-Subtype P → type-2-Element-Subtype Q
  map-hom-2-Element-Subtype f = tot f

  is-emb-map-hom-2-Element-Subtype :
    (f : hom-2-Element-Subtype) → is-emb (map-hom-2-Element-Subtype f)
  is-emb-map-hom-2-Element-Subtype f =
    is-emb-tot
      ( λ x →
        is-emb-is-prop
          ( is-prop-type-prop-2-Element-Subtype P x)
          ( is-prop-type-prop-2-Element-Subtype Q x))

  is-surjective-map-hom-2-Element-Subtype :
    (f : hom-2-Element-Subtype) → is-surjective (map-hom-2-Element-Subtype f)
  is-surjective-map-hom-2-Element-Subtype f (pair x q) = {! type-subtype (P ∘ map-inv-equiv e) !}

  is-equiv-map-hom-2-Element-Subtype :
    (f : hom-2-Element-Subtype) → is-equiv (map-hom-2-Element-Subtype f)
  is-equiv-map-hom-2-Element-Subtype f = {!!}
-}</a>
</pre>
### Swapping the elements in a 2-element subtype

<pre class="Agda"><a id="6087" class="Keyword">module</a> <a id="6094" href="univalent-combinatorics.2-element-subtypes.html#6094" class="Module">_</a>
  <a id="6098" class="Symbol">{</a><a id="6099" href="univalent-combinatorics.2-element-subtypes.html#6099" class="Bound">l1</a> <a id="6102" href="univalent-combinatorics.2-element-subtypes.html#6102" class="Bound">l2</a> <a id="6105" class="Symbol">:</a> <a id="6107" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6112" class="Symbol">}</a> <a id="6114" class="Symbol">{</a><a id="6115" href="univalent-combinatorics.2-element-subtypes.html#6115" class="Bound">X</a> <a id="6117" class="Symbol">:</a> <a id="6119" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6122" href="univalent-combinatorics.2-element-subtypes.html#6099" class="Bound">l1</a><a id="6124" class="Symbol">}</a> <a id="6126" class="Symbol">(</a><a id="6127" href="univalent-combinatorics.2-element-subtypes.html#6127" class="Bound">P</a> <a id="6129" class="Symbol">:</a> <a id="6131" href="univalent-combinatorics.2-element-subtypes.html#1455" class="Function">2-Element-Subtype</a> <a id="6149" href="univalent-combinatorics.2-element-subtypes.html#6102" class="Bound">l2</a> <a id="6152" href="univalent-combinatorics.2-element-subtypes.html#6115" class="Bound">X</a><a id="6153" class="Symbol">)</a>
  <a id="6157" class="Keyword">where</a>

  <a id="6166" href="univalent-combinatorics.2-element-subtypes.html#6166" class="Function">swap-2-Element-Subtype</a> <a id="6189" class="Symbol">:</a> <a id="6191" href="foundation.automorphisms.html#538" class="Function">Aut</a> <a id="6195" class="Symbol">(</a><a id="6196" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a> <a id="6219" href="univalent-combinatorics.2-element-subtypes.html#6127" class="Bound">P</a><a id="6220" class="Symbol">)</a>
  <a id="6224" href="univalent-combinatorics.2-element-subtypes.html#6166" class="Function">swap-2-Element-Subtype</a> <a id="6247" class="Symbol">=</a>
    <a id="6253" href="univalent-combinatorics.2-element-types.html#20524" class="Function">swap-2-Element-Type</a> <a id="6273" class="Symbol">(</a><a id="6274" href="univalent-combinatorics.2-element-subtypes.html#2829" class="Function">2-element-type-2-Element-Subtype</a> <a id="6307" href="univalent-combinatorics.2-element-subtypes.html#6127" class="Bound">P</a><a id="6308" class="Symbol">)</a>

  <a id="6313" href="univalent-combinatorics.2-element-subtypes.html#6313" class="Function">map-swap-2-Element-Subtype</a> <a id="6340" class="Symbol">:</a>
    <a id="6346" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a> <a id="6369" href="univalent-combinatorics.2-element-subtypes.html#6127" class="Bound">P</a> <a id="6371" class="Symbol">→</a> <a id="6373" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a> <a id="6396" href="univalent-combinatorics.2-element-subtypes.html#6127" class="Bound">P</a>
  <a id="6400" href="univalent-combinatorics.2-element-subtypes.html#6313" class="Function">map-swap-2-Element-Subtype</a> <a id="6427" class="Symbol">=</a>
    <a id="6433" href="univalent-combinatorics.2-element-types.html#20761" class="Function">map-swap-2-Element-Type</a> <a id="6457" class="Symbol">(</a><a id="6458" href="univalent-combinatorics.2-element-subtypes.html#2829" class="Function">2-element-type-2-Element-Subtype</a> <a id="6491" href="univalent-combinatorics.2-element-subtypes.html#6127" class="Bound">P</a><a id="6492" class="Symbol">)</a>

  <a id="6497" href="univalent-combinatorics.2-element-subtypes.html#6497" class="Function">compute-swap-2-Element-Subtype</a> <a id="6528" class="Symbol">:</a>
    <a id="6534" class="Symbol">(</a><a id="6535" href="univalent-combinatorics.2-element-subtypes.html#6535" class="Bound">x</a> <a id="6537" href="univalent-combinatorics.2-element-subtypes.html#6537" class="Bound">y</a> <a id="6539" class="Symbol">:</a> <a id="6541" href="univalent-combinatorics.2-element-subtypes.html#2081" class="Function">type-2-Element-Subtype</a> <a id="6564" href="univalent-combinatorics.2-element-subtypes.html#6127" class="Bound">P</a><a id="6565" class="Symbol">)</a> <a id="6567" class="Symbol">→</a> <a id="6569" href="univalent-combinatorics.2-element-subtypes.html#6535" class="Bound">x</a> <a id="6571" href="foundation.negated-equality.html#733" class="Function Operator">≠</a> <a id="6573" href="univalent-combinatorics.2-element-subtypes.html#6537" class="Bound">y</a> <a id="6575" class="Symbol">→</a>
    <a id="6581" href="univalent-combinatorics.2-element-subtypes.html#6313" class="Function">map-swap-2-Element-Subtype</a> <a id="6608" href="univalent-combinatorics.2-element-subtypes.html#6535" class="Bound">x</a> <a id="6610" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6612" href="univalent-combinatorics.2-element-subtypes.html#6537" class="Bound">y</a>
  <a id="6616" href="univalent-combinatorics.2-element-subtypes.html#6497" class="Function">compute-swap-2-Element-Subtype</a> <a id="6647" class="Symbol">=</a>
    <a id="6653" href="univalent-combinatorics.2-element-types.html#21518" class="Function">compute-swap-2-Element-Type</a> <a id="6681" class="Symbol">(</a><a id="6682" href="univalent-combinatorics.2-element-subtypes.html#2829" class="Function">2-element-type-2-Element-Subtype</a> <a id="6715" href="univalent-combinatorics.2-element-subtypes.html#6127" class="Bound">P</a><a id="6716" class="Symbol">)</a>
</pre>
### 2-element subtypes are closed under precomposition with an equivalence

<pre class="Agda"><a id="precomp-equiv-2-Element-Subtype"></a><a id="6807" href="univalent-combinatorics.2-element-subtypes.html#6807" class="Function">precomp-equiv-2-Element-Subtype</a> <a id="6839" class="Symbol">:</a>
  <a id="6843" class="Symbol">{</a><a id="6844" href="univalent-combinatorics.2-element-subtypes.html#6844" class="Bound">l1</a> <a id="6847" href="univalent-combinatorics.2-element-subtypes.html#6847" class="Bound">l2</a> <a id="6850" href="univalent-combinatorics.2-element-subtypes.html#6850" class="Bound">l3</a> <a id="6853" class="Symbol">:</a> <a id="6855" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6860" class="Symbol">}</a> <a id="6862" class="Symbol">{</a><a id="6863" href="univalent-combinatorics.2-element-subtypes.html#6863" class="Bound">X</a> <a id="6865" class="Symbol">:</a> <a id="6867" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6870" href="univalent-combinatorics.2-element-subtypes.html#6844" class="Bound">l1</a><a id="6872" class="Symbol">}</a> <a id="6874" class="Symbol">{</a><a id="6875" href="univalent-combinatorics.2-element-subtypes.html#6875" class="Bound">Y</a> <a id="6877" class="Symbol">:</a> <a id="6879" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6882" href="univalent-combinatorics.2-element-subtypes.html#6847" class="Bound">l2</a><a id="6884" class="Symbol">}</a> <a id="6886" class="Symbol">→</a> <a id="6888" href="univalent-combinatorics.2-element-subtypes.html#6863" class="Bound">X</a> <a id="6890" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="6892" href="univalent-combinatorics.2-element-subtypes.html#6875" class="Bound">Y</a> <a id="6894" class="Symbol">→</a>
    <a id="6900" href="univalent-combinatorics.2-element-subtypes.html#1455" class="Function">2-Element-Subtype</a> <a id="6918" href="univalent-combinatorics.2-element-subtypes.html#6850" class="Bound">l3</a> <a id="6921" href="univalent-combinatorics.2-element-subtypes.html#6863" class="Bound">X</a> <a id="6923" class="Symbol">→</a> <a id="6925" href="univalent-combinatorics.2-element-subtypes.html#1455" class="Function">2-Element-Subtype</a> <a id="6943" href="univalent-combinatorics.2-element-subtypes.html#6850" class="Bound">l3</a> <a id="6946" href="univalent-combinatorics.2-element-subtypes.html#6875" class="Bound">Y</a>
<a id="6948" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="6952" class="Symbol">(</a><a id="6953" href="univalent-combinatorics.2-element-subtypes.html#6807" class="Function">precomp-equiv-2-Element-Subtype</a> <a id="6985" href="univalent-combinatorics.2-element-subtypes.html#6985" class="Bound">e</a> <a id="6987" class="Symbol">(</a><a id="6988" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="6993" href="univalent-combinatorics.2-element-subtypes.html#6993" class="Bound">P</a> <a id="6995" href="univalent-combinatorics.2-element-subtypes.html#6995" class="Bound">H</a><a id="6996" class="Symbol">))</a> <a id="6999" class="Symbol">=</a>
  <a id="7003" href="univalent-combinatorics.2-element-subtypes.html#6993" class="Bound">P</a> <a id="7005" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="7007" class="Symbol">(</a><a id="7008" href="foundation-core.equivalences.html#8070" class="Function">map-inv-equiv</a> <a id="7022" href="univalent-combinatorics.2-element-subtypes.html#6985" class="Bound">e</a><a id="7023" class="Symbol">)</a>
<a id="7025" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7029" class="Symbol">(</a><a id="7030" href="univalent-combinatorics.2-element-subtypes.html#6807" class="Function">precomp-equiv-2-Element-Subtype</a> <a id="7062" href="univalent-combinatorics.2-element-subtypes.html#7062" class="Bound">e</a> <a id="7064" class="Symbol">(</a><a id="7065" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="7070" href="univalent-combinatorics.2-element-subtypes.html#7070" class="Bound">P</a> <a id="7072" href="univalent-combinatorics.2-element-subtypes.html#7072" class="Bound">H</a><a id="7073" class="Symbol">))</a> <a id="7076" class="Symbol">=</a>
  <a id="7080" href="foundation.mere-equivalences.html#1788" class="Function">transitive-mere-equiv</a> <a id="7102" class="Symbol">_</a> <a id="7104" class="Symbol">_</a> <a id="7106" class="Symbol">_</a>
    <a id="7112" class="Symbol">(</a> <a id="7114" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a>
      <a id="7136" class="Symbol">(</a> <a id="7138" href="foundation-core.subtypes.html#9226" class="Function">equiv-subtype-equiv</a>
        <a id="7166" class="Symbol">(</a> <a id="7168" href="univalent-combinatorics.2-element-subtypes.html#7062" class="Bound">e</a><a id="7169" class="Symbol">)</a>
        <a id="7179" class="Symbol">(</a> <a id="7181" href="univalent-combinatorics.2-element-subtypes.html#7070" class="Bound">P</a><a id="7182" class="Symbol">)</a>
        <a id="7192" class="Symbol">(</a> <a id="7194" href="univalent-combinatorics.2-element-subtypes.html#7070" class="Bound">P</a> <a id="7196" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="7198" class="Symbol">(</a><a id="7199" href="foundation-core.equivalences.html#8070" class="Function">map-inv-equiv</a> <a id="7213" href="univalent-combinatorics.2-element-subtypes.html#7062" class="Bound">e</a><a id="7214" class="Symbol">))</a>
        <a id="7225" class="Symbol">(</a> <a id="7227" class="Symbol">λ</a> <a id="7229" href="univalent-combinatorics.2-element-subtypes.html#7229" class="Bound">x</a> <a id="7231" class="Symbol">→</a>
          <a id="7243" href="foundation.logical-equivalences.html#5651" class="Function">iff-equiv</a>
            <a id="7265" class="Symbol">(</a> <a id="7267" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a>
              <a id="7284" class="Symbol">(</a> <a id="7286" class="Symbol">λ</a> <a id="7288" href="univalent-combinatorics.2-element-subtypes.html#7288" class="Bound">g</a> <a id="7290" class="Symbol">→</a> <a id="7292" class="Symbol">(</a><a id="7293" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="7303" class="Symbol">(</a><a id="7304" href="univalent-combinatorics.2-element-subtypes.html#7070" class="Bound">P</a> <a id="7306" href="univalent-combinatorics.2-element-subtypes.html#7229" class="Bound">x</a><a id="7307" class="Symbol">))</a> <a id="7310" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="7312" class="Symbol">(</a><a id="7313" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="7323" class="Symbol">(</a><a id="7324" href="univalent-combinatorics.2-element-subtypes.html#7070" class="Bound">P</a> <a id="7326" class="Symbol">(</a><a id="7327" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="7337" href="univalent-combinatorics.2-element-subtypes.html#7288" class="Bound">g</a> <a id="7339" href="univalent-combinatorics.2-element-subtypes.html#7229" class="Bound">x</a><a id="7340" class="Symbol">))))</a>
              <a id="7359" class="Symbol">(</a> <a id="7361" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="7365" class="Symbol">(</a><a id="7366" href="foundation.equivalences.html#14851" class="Function">left-inverse-law-equiv</a> <a id="7389" href="univalent-combinatorics.2-element-subtypes.html#7062" class="Bound">e</a><a id="7390" class="Symbol">))</a>
              <a id="7407" class="Symbol">(</a> <a id="7409" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a><a id="7417" class="Symbol">)))))</a>
    <a id="7427" class="Symbol">(</a> <a id="7429" href="univalent-combinatorics.2-element-subtypes.html#7072" class="Bound">H</a><a id="7430" class="Symbol">)</a>

<a id="7433" class="Comment">{-
module _
  {l : Level} {A : UU l}
  where

  is-injective-map-Fin-2 :
    (f : Fin 2 → A) → f zero-Fin ≠ f one-Fin → is-injective f
  is-injective-map-Fin-2 f H {inl (inr star)} {inl (inr star)} p = refl
  is-injective-map-Fin-2 f H {inl (inr star)} {inr star} p = ex-falso (H p)
  is-injective-map-Fin-2 f H {inr star} {inl (inr star)} p =
    ex-falso (H (inv p))
  is-injective-map-Fin-2 f H {inr star} {inr star} p = refl

  is-injective-element-unordered-pair :
    (p : unordered-pair A) →
    ¬ ( (x y : type-unordered-pair p) →
        Id (element-unordered-pair p x) (element-unordered-pair p y)) →
    is-injective (element-unordered-pair p)
  is-injective-element-unordered-pair (pair X f) H {x} {y} p =
    apply-universal-property-trunc-Prop
      ( has-two-elements-type-unordered-pair (pair X f))
      ( Id-Prop (set-Type-With-Cardinality-ℕ X) x y)
      ( λ h → {!!})
    where
    first-element : (Fin 2 ≃ (type-2-Element-Type X)) →
      Σ ( type-2-Element-Type X)
        ( λ x → ¬ ((y : type-2-Element-Type X) → Id (f x) (f y)))
    first-element h =
      exists-not-not-for-all-count (λ z → (w : type-2-Element-Type X) →
      Id (f z) (f w)) (λ z → {!!})
        {!!} {!!}
    two-elements-different-image :
      Σ ( type-2-Element-Type X)
        ( λ x → Σ (type-2-Element-Type X) (λ y → f x ≠ f y))
    two-elements-different-image = {!!}
-}</a>
</pre>