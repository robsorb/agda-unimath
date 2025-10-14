# The loop homotopy on the circle

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="synthetic-homotopy-theory.loop-homotopy-circle.html" class="Module">synthetic-homotopy-theory.loop-homotopy-circle</a> <a id="98" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="213" class="Keyword">open</a> <a id="218" class="Keyword">import</a> <a id="225" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="foundation.negated-equality.html" class="Module">foundation.negated-equality</a>
<a id="454" class="Keyword">open</a> <a id="459" class="Keyword">import</a> <a id="466" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="581" class="Keyword">open</a> <a id="586" class="Keyword">import</a> <a id="593" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="629" class="Keyword">open</a> <a id="634" class="Keyword">import</a> <a id="641" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>

<a id="672" class="Keyword">open</a> <a id="677" class="Keyword">import</a> <a id="684" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
</pre>
</details>

## Idea

The
{{#concept "loop homotopy" Disambiguation="on the circle type" Agda=loop-htpy-𝕊¹}}
on the [circle](synthetic-homotopy-theory.circle.md) is the family of
[equalities](foundation-core.identity-types.md)

```text
  loop-htpy-𝕊¹ : (x : 𝕊¹) → x ＝ x
```

defined by [transporting](foundation-core.transport-along-identifications.md)
along the loop of the circle. This [homotopy](foundation-core.homotopies.md) is
distinct from the constant homotopy and has winding number 1.

## Definitions

### The loop homotopy on the circle

<pre class="Agda"><a id="loop-htpy-𝕊¹"></a><a id="1278" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1278" class="Function">loop-htpy-𝕊¹</a> <a id="1291" class="Symbol">:</a> <a id="1293" class="Symbol">(</a><a id="1294" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1294" class="Bound">x</a> <a id="1296" class="Symbol">:</a> <a id="1298" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a><a id="1300" class="Symbol">)</a> <a id="1302" class="Symbol">→</a> <a id="1304" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1294" class="Bound">x</a> <a id="1306" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1308" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1294" class="Bound">x</a>
<a id="1310" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1278" class="Function">loop-htpy-𝕊¹</a> <a id="1323" class="Symbol">=</a>
  <a id="1327" href="synthetic-homotopy-theory.circle.html#3217" class="Function">function-apply-dependent-universal-property-𝕊¹</a>
    <a id="1378" class="Symbol">(</a> <a id="1380" href="foundation-core.homotopies.html#795" class="Function">eq-value</a> <a id="1389" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="1392" href="foundation-core.function-types.html#307" class="Function">id</a><a id="1394" class="Symbol">)</a>
    <a id="1400" class="Symbol">(</a> <a id="1402" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a><a id="1409" class="Symbol">)</a>
    <a id="1415" class="Symbol">(</a> <a id="1417" href="foundation-core.homotopies.html#1759" class="Function">map-compute-dependent-identification-eq-value-id-id</a>
      <a id="1475" class="Symbol">(</a> <a id="1477" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a><a id="1484" class="Symbol">)</a>
      <a id="1492" class="Symbol">(</a> <a id="1494" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a><a id="1501" class="Symbol">)</a>
      <a id="1509" class="Symbol">(</a> <a id="1511" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a><a id="1518" class="Symbol">)</a>
      <a id="1526" class="Symbol">(</a> <a id="1528" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1532" class="Symbol">))</a>

<a id="compute-base-loop-htpy-𝕊¹"></a><a id="1536" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1536" class="Function">compute-base-loop-htpy-𝕊¹</a> <a id="1562" class="Symbol">:</a> <a id="1564" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1278" class="Function">loop-htpy-𝕊¹</a> <a id="1577" href="synthetic-homotopy-theory.circle.html#1854" class="Postulate">base-𝕊¹</a> <a id="1585" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1587" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a>
<a id="1595" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1536" class="Function">compute-base-loop-htpy-𝕊¹</a> <a id="1621" class="Symbol">=</a>
  <a id="1625" href="synthetic-homotopy-theory.circle.html#3381" class="Function">base-dependent-universal-property-𝕊¹</a>
    <a id="1666" class="Symbol">(</a> <a id="1668" href="foundation-core.homotopies.html#795" class="Function">eq-value</a> <a id="1677" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="1680" href="foundation-core.function-types.html#307" class="Function">id</a><a id="1682" class="Symbol">)</a>
    <a id="1688" class="Symbol">(</a> <a id="1690" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a><a id="1697" class="Symbol">)</a>
    <a id="1703" class="Symbol">(</a> <a id="1705" href="foundation-core.homotopies.html#1759" class="Function">map-compute-dependent-identification-eq-value-id-id</a>
      <a id="1763" class="Symbol">(</a> <a id="1765" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a><a id="1772" class="Symbol">)</a>
      <a id="1780" class="Symbol">(</a> <a id="1782" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a><a id="1789" class="Symbol">)</a>
      <a id="1797" class="Symbol">(</a> <a id="1799" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a><a id="1806" class="Symbol">)</a>
      <a id="1814" class="Symbol">(</a> <a id="1816" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1820" class="Symbol">))</a>
</pre>
## Properties

### The loop homotopy on the circle is nontrivial

<pre class="Agda"><a id="1902" class="Keyword">abstract</a>
  <a id="is-not-refl-ev-base-loop-htpy-𝕊¹"></a><a id="1913" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1913" class="Function">is-not-refl-ev-base-loop-htpy-𝕊¹</a> <a id="1946" class="Symbol">:</a> <a id="1948" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1278" class="Function">loop-htpy-𝕊¹</a> <a id="1961" href="synthetic-homotopy-theory.circle.html#1854" class="Postulate">base-𝕊¹</a> <a id="1969" href="foundation.negated-equality.html#733" class="Function Operator">≠</a> <a id="1971" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
  <a id="1978" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1913" class="Function">is-not-refl-ev-base-loop-htpy-𝕊¹</a> <a id="2011" href="synthetic-homotopy-theory.loop-homotopy-circle.html#2011" class="Bound">p</a> <a id="2013" class="Symbol">=</a>
    <a id="2019" href="synthetic-homotopy-theory.circle.html#5286" class="Function">is-nontrivial-loop-𝕊¹</a> <a id="2041" class="Symbol">(</a><a id="2042" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="2046" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1536" class="Function">compute-base-loop-htpy-𝕊¹</a> <a id="2072" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a> <a id="2074" href="synthetic-homotopy-theory.loop-homotopy-circle.html#2011" class="Bound">p</a><a id="2075" class="Symbol">)</a>

<a id="is-nontrivial-loop-htpy-𝕊¹&#39;"></a><a id="2078" href="synthetic-homotopy-theory.loop-homotopy-circle.html#2078" class="Function">is-nontrivial-loop-htpy-𝕊¹&#39;</a> <a id="2106" class="Symbol">:</a> <a id="2108" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2110" class="Symbol">(</a><a id="2111" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1278" class="Function">loop-htpy-𝕊¹</a> <a id="2124" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="2126" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="2135" class="Symbol">)</a>
<a id="2137" href="synthetic-homotopy-theory.loop-homotopy-circle.html#2078" class="Function">is-nontrivial-loop-htpy-𝕊¹&#39;</a> <a id="2165" href="synthetic-homotopy-theory.loop-homotopy-circle.html#2165" class="Bound">H</a> <a id="2167" class="Symbol">=</a>
  <a id="2171" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1913" class="Function">is-not-refl-ev-base-loop-htpy-𝕊¹</a> <a id="2204" class="Symbol">(</a><a id="2205" href="synthetic-homotopy-theory.loop-homotopy-circle.html#2165" class="Bound">H</a> <a id="2207" href="synthetic-homotopy-theory.circle.html#1854" class="Postulate">base-𝕊¹</a><a id="2214" class="Symbol">)</a>

<a id="is-nontrivial-loop-htpy-𝕊¹"></a><a id="2217" href="synthetic-homotopy-theory.loop-homotopy-circle.html#2217" class="Function">is-nontrivial-loop-htpy-𝕊¹</a> <a id="2244" class="Symbol">:</a> <a id="2246" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1278" class="Function">loop-htpy-𝕊¹</a> <a id="2259" href="foundation.negated-equality.html#733" class="Function Operator">≠</a> <a id="2261" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
<a id="2271" href="synthetic-homotopy-theory.loop-homotopy-circle.html#2217" class="Function">is-nontrivial-loop-htpy-𝕊¹</a> <a id="2298" class="Symbol">=</a>
  <a id="2302" href="foundation.negated-equality.html#1672" class="Function">nonequal-Π</a> <a id="2313" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1278" class="Function">loop-htpy-𝕊¹</a> <a id="2326" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a> <a id="2336" href="synthetic-homotopy-theory.circle.html#1854" class="Postulate">base-𝕊¹</a> <a id="2344" href="synthetic-homotopy-theory.loop-homotopy-circle.html#1913" class="Function">is-not-refl-ev-base-loop-htpy-𝕊¹</a>
</pre>