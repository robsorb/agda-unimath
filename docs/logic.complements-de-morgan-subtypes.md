# Complements of De Morgan subtypes

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="logic.complements-de-morgan-subtypes.html" class="Module">logic.complements-de-morgan-subtypes</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.complements-subtypes.html" class="Module">foundation.complements-subtypes</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="276" class="Keyword">open</a> <a id="281" class="Keyword">import</a> <a id="288" href="foundation.double-negation.html" class="Module">foundation.double-negation</a>
<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="foundation.full-subtypes.html" class="Module">foundation.full-subtypes</a>
<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="foundation.postcomposition-functions.html" class="Module">foundation.postcomposition-functions</a>
<a id="468" class="Keyword">open</a> <a id="473" class="Keyword">import</a> <a id="480" href="foundation.powersets.html" class="Module">foundation.powersets</a>
<a id="501" class="Keyword">open</a> <a id="506" class="Keyword">import</a> <a id="513" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="550" class="Keyword">open</a> <a id="555" class="Keyword">import</a> <a id="562" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="582" class="Keyword">open</a> <a id="587" class="Keyword">import</a> <a id="594" href="foundation.unions-subtypes.html" class="Module">foundation.unions-subtypes</a>
<a id="621" class="Keyword">open</a> <a id="626" class="Keyword">import</a> <a id="633" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="661" class="Keyword">open</a> <a id="666" class="Keyword">import</a> <a id="673" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>

<a id="705" class="Keyword">open</a> <a id="710" class="Keyword">import</a> <a id="717" href="logic.complements-decidable-subtypes.html" class="Module">logic.complements-decidable-subtypes</a>
<a id="754" class="Keyword">open</a> <a id="759" class="Keyword">import</a> <a id="766" href="logic.de-morgan-propositions.html" class="Module">logic.de-morgan-propositions</a>
<a id="795" class="Keyword">open</a> <a id="800" class="Keyword">import</a> <a id="807" href="logic.de-morgan-subtypes.html" class="Module">logic.de-morgan-subtypes</a>
</pre>
</details>

## Idea

The
{{#concept "complement" Disambiguation="of a De Morgan subtype" Agda=complement-de-morgan-subtype}}
of a [De Morgan subtype](logic.de-morgan-subtypes.md) `B ⊆ A` consists of the
elements that are not in `B`.

## Definition

### Complements of De Morgan subtypes

<pre class="Agda"><a id="complement-de-morgan-subtype"></a><a id="1133" href="logic.complements-de-morgan-subtypes.html#1133" class="Function">complement-de-morgan-subtype</a> <a id="1162" class="Symbol">:</a>
  <a id="1166" class="Symbol">{</a><a id="1167" href="logic.complements-de-morgan-subtypes.html#1167" class="Bound">l1</a> <a id="1170" href="logic.complements-de-morgan-subtypes.html#1170" class="Bound">l2</a> <a id="1173" class="Symbol">:</a> <a id="1175" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1180" class="Symbol">}</a> <a id="1182" class="Symbol">{</a><a id="1183" href="logic.complements-de-morgan-subtypes.html#1183" class="Bound">A</a> <a id="1185" class="Symbol">:</a> <a id="1187" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1190" href="logic.complements-de-morgan-subtypes.html#1167" class="Bound">l1</a><a id="1192" class="Symbol">}</a> <a id="1194" class="Symbol">→</a> <a id="1196" href="logic.de-morgan-subtypes.html#2054" class="Function">de-morgan-subtype</a> <a id="1214" href="logic.complements-de-morgan-subtypes.html#1170" class="Bound">l2</a> <a id="1217" href="logic.complements-de-morgan-subtypes.html#1183" class="Bound">A</a> <a id="1219" class="Symbol">→</a> <a id="1221" href="logic.de-morgan-subtypes.html#2054" class="Function">de-morgan-subtype</a> <a id="1239" href="logic.complements-de-morgan-subtypes.html#1170" class="Bound">l2</a> <a id="1242" href="logic.complements-de-morgan-subtypes.html#1183" class="Bound">A</a>
<a id="1244" href="logic.complements-de-morgan-subtypes.html#1133" class="Function">complement-de-morgan-subtype</a> <a id="1273" href="logic.complements-de-morgan-subtypes.html#1273" class="Bound">P</a> <a id="1275" href="logic.complements-de-morgan-subtypes.html#1275" class="Bound">x</a> <a id="1277" class="Symbol">=</a> <a id="1279" href="logic.de-morgan-propositions.html#8639" class="Function">neg-De-Morgan-Prop</a> <a id="1298" class="Symbol">(</a><a id="1299" href="logic.complements-de-morgan-subtypes.html#1273" class="Bound">P</a> <a id="1301" href="logic.complements-de-morgan-subtypes.html#1275" class="Bound">x</a><a id="1302" class="Symbol">)</a>
</pre>
## Properties

### Complement of De Morgan subtypes are decidable

<pre class="Agda"><a id="is-decidable-complement-de-morgan-subtype"></a><a id="1384" href="logic.complements-de-morgan-subtypes.html#1384" class="Function">is-decidable-complement-de-morgan-subtype</a> <a id="1426" class="Symbol">:</a>
  <a id="1430" class="Symbol">{</a><a id="1431" href="logic.complements-de-morgan-subtypes.html#1431" class="Bound">l1</a> <a id="1434" href="logic.complements-de-morgan-subtypes.html#1434" class="Bound">l2</a> <a id="1437" class="Symbol">:</a> <a id="1439" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1444" class="Symbol">}</a> <a id="1446" class="Symbol">{</a><a id="1447" href="logic.complements-de-morgan-subtypes.html#1447" class="Bound">A</a> <a id="1449" class="Symbol">:</a> <a id="1451" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1454" href="logic.complements-de-morgan-subtypes.html#1431" class="Bound">l1</a><a id="1456" class="Symbol">}</a> <a id="1458" class="Symbol">(</a><a id="1459" href="logic.complements-de-morgan-subtypes.html#1459" class="Bound">P</a> <a id="1461" class="Symbol">:</a> <a id="1463" href="logic.de-morgan-subtypes.html#2054" class="Function">de-morgan-subtype</a> <a id="1481" href="logic.complements-de-morgan-subtypes.html#1434" class="Bound">l2</a> <a id="1484" href="logic.complements-de-morgan-subtypes.html#1447" class="Bound">A</a><a id="1485" class="Symbol">)</a> <a id="1487" class="Symbol">→</a>
  <a id="1491" href="foundation.decidable-subtypes.html#2381" class="Function">is-decidable-subtype</a>
    <a id="1516" class="Symbol">(</a> <a id="1518" href="logic.de-morgan-subtypes.html#2320" class="Function">subtype-de-morgan-subtype</a> <a id="1544" class="Symbol">(</a><a id="1545" href="logic.complements-de-morgan-subtypes.html#1133" class="Function">complement-de-morgan-subtype</a> <a id="1574" href="logic.complements-de-morgan-subtypes.html#1459" class="Bound">P</a><a id="1575" class="Symbol">))</a>
<a id="1578" href="logic.complements-de-morgan-subtypes.html#1384" class="Function">is-decidable-complement-de-morgan-subtype</a> <a id="1620" href="logic.complements-de-morgan-subtypes.html#1620" class="Bound">P</a> <a id="1622" class="Symbol">=</a> <a id="1624" href="logic.de-morgan-subtypes.html#2426" class="Function">is-de-morgan-de-morgan-subtype</a> <a id="1655" href="logic.complements-de-morgan-subtypes.html#1620" class="Bound">P</a>
</pre>
### The union of the complement of a subtype `P` with its double complement is the full subtype if and only if `P` is De Morgan

<pre class="Agda"><a id="1799" class="Keyword">module</a> <a id="1806" href="logic.complements-de-morgan-subtypes.html#1806" class="Module">_</a>
  <a id="1810" class="Symbol">{</a><a id="1811" href="logic.complements-de-morgan-subtypes.html#1811" class="Bound">l1</a> <a id="1814" href="logic.complements-de-morgan-subtypes.html#1814" class="Bound">l2</a> <a id="1817" class="Symbol">:</a> <a id="1819" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1824" class="Symbol">}</a> <a id="1826" class="Symbol">{</a><a id="1827" href="logic.complements-de-morgan-subtypes.html#1827" class="Bound">A</a> <a id="1829" class="Symbol">:</a> <a id="1831" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1834" href="logic.complements-de-morgan-subtypes.html#1811" class="Bound">l1</a><a id="1836" class="Symbol">}</a>
  <a id="1840" class="Keyword">where</a>

  <a id="1849" href="logic.complements-de-morgan-subtypes.html#1849" class="Function">is-full-union-complement-subtype-double-complement-subtype</a> <a id="1908" class="Symbol">:</a>
    <a id="1914" class="Symbol">(</a><a id="1915" href="logic.complements-de-morgan-subtypes.html#1915" class="Bound">P</a> <a id="1917" class="Symbol">:</a> <a id="1919" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1927" href="logic.complements-de-morgan-subtypes.html#1814" class="Bound">l2</a> <a id="1930" href="logic.complements-de-morgan-subtypes.html#1827" class="Bound">A</a><a id="1931" class="Symbol">)</a> <a id="1933" class="Symbol">→</a> <a id="1935" href="logic.de-morgan-subtypes.html#1702" class="Function">is-de-morgan-subtype</a> <a id="1956" href="logic.complements-de-morgan-subtypes.html#1915" class="Bound">P</a> <a id="1958" class="Symbol">→</a>
    <a id="1964" href="foundation.full-subtypes.html#794" class="Function">is-full-subtype</a>
      <a id="1986" class="Symbol">(</a> <a id="1988" href="foundation.unions-subtypes.html#961" class="Function">union-subtype</a>
        <a id="2010" class="Symbol">(</a> <a id="2012" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2031" href="logic.complements-de-morgan-subtypes.html#1915" class="Bound">P</a><a id="2032" class="Symbol">)</a>
        <a id="2042" class="Symbol">(</a> <a id="2044" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2063" class="Symbol">(</a><a id="2064" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2083" href="logic.complements-de-morgan-subtypes.html#1915" class="Bound">P</a><a id="2084" class="Symbol">)))</a>
  <a id="2090" href="logic.complements-de-morgan-subtypes.html#1849" class="Function">is-full-union-complement-subtype-double-complement-subtype</a> <a id="2149" href="logic.complements-de-morgan-subtypes.html#2149" class="Bound">P</a> <a id="2151" class="Symbol">=</a>
    <a id="2157" href="logic.complements-decidable-subtypes.html#2380" class="Function">is-full-union-subtype-complement-subtype</a> <a id="2198" class="Symbol">(</a><a id="2199" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2218" href="logic.complements-de-morgan-subtypes.html#2149" class="Bound">P</a><a id="2219" class="Symbol">)</a>

  <a id="2224" href="logic.complements-de-morgan-subtypes.html#2224" class="Function">is-de-morgan-subtype-is-full-union-complement-subtype-double-complement-subtype</a> <a id="2304" class="Symbol">:</a>
    <a id="2310" class="Symbol">(</a><a id="2311" href="logic.complements-de-morgan-subtypes.html#2311" class="Bound">P</a> <a id="2313" class="Symbol">:</a> <a id="2315" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="2323" href="logic.complements-de-morgan-subtypes.html#1814" class="Bound">l2</a> <a id="2326" href="logic.complements-de-morgan-subtypes.html#1827" class="Bound">A</a><a id="2327" class="Symbol">)</a> <a id="2329" class="Symbol">→</a>
    <a id="2335" href="foundation.full-subtypes.html#794" class="Function">is-full-subtype</a>
      <a id="2357" class="Symbol">(</a> <a id="2359" href="foundation.unions-subtypes.html#961" class="Function">union-subtype</a>
        <a id="2381" class="Symbol">(</a> <a id="2383" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2402" href="logic.complements-de-morgan-subtypes.html#2311" class="Bound">P</a><a id="2403" class="Symbol">)</a>
        <a id="2413" class="Symbol">(</a> <a id="2415" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2434" class="Symbol">(</a><a id="2435" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2454" href="logic.complements-de-morgan-subtypes.html#2311" class="Bound">P</a><a id="2455" class="Symbol">)))</a> <a id="2459" class="Symbol">→</a>
    <a id="2465" href="logic.de-morgan-subtypes.html#1702" class="Function">is-de-morgan-subtype</a> <a id="2486" href="logic.complements-de-morgan-subtypes.html#2311" class="Bound">P</a>
  <a id="2490" href="logic.complements-de-morgan-subtypes.html#2224" class="Function">is-de-morgan-subtype-is-full-union-complement-subtype-double-complement-subtype</a>
    <a id="2574" href="logic.complements-de-morgan-subtypes.html#2574" class="Bound">P</a> <a id="2576" class="Symbol">=</a>
    <a id="2582" href="logic.complements-decidable-subtypes.html#2614" class="Function">is-decidable-subtype-is-full-union-subtype-complement-subtype</a>
      <a id="2650" class="Symbol">(</a> <a id="2652" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2671" href="logic.complements-de-morgan-subtypes.html#2574" class="Bound">P</a><a id="2672" class="Symbol">)</a>

  <a id="2677" href="logic.complements-de-morgan-subtypes.html#2677" class="Function">is-full-union-subtype-complement-de-morgan-subtype</a> <a id="2728" class="Symbol">:</a>
    <a id="2734" class="Symbol">(</a><a id="2735" href="logic.complements-de-morgan-subtypes.html#2735" class="Bound">P</a> <a id="2737" class="Symbol">:</a> <a id="2739" href="logic.de-morgan-subtypes.html#2054" class="Function">de-morgan-subtype</a> <a id="2757" href="logic.complements-de-morgan-subtypes.html#1814" class="Bound">l2</a> <a id="2760" href="logic.complements-de-morgan-subtypes.html#1827" class="Bound">A</a><a id="2761" class="Symbol">)</a> <a id="2763" class="Symbol">→</a>
    <a id="2769" href="foundation.full-subtypes.html#794" class="Function">is-full-subtype</a>
      <a id="2791" class="Symbol">(</a> <a id="2793" href="foundation.unions-subtypes.html#961" class="Function">union-subtype</a>
        <a id="2815" class="Symbol">(</a> <a id="2817" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2836" class="Symbol">(</a><a id="2837" href="logic.de-morgan-subtypes.html#2320" class="Function">subtype-de-morgan-subtype</a> <a id="2863" href="logic.complements-de-morgan-subtypes.html#2735" class="Bound">P</a><a id="2864" class="Symbol">))</a>
        <a id="2875" class="Symbol">(</a> <a id="2877" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a>
          <a id="2906" class="Symbol">(</a> <a id="2908" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2927" class="Symbol">(</a><a id="2928" href="logic.de-morgan-subtypes.html#2320" class="Function">subtype-de-morgan-subtype</a> <a id="2954" href="logic.complements-de-morgan-subtypes.html#2735" class="Bound">P</a><a id="2955" class="Symbol">))))</a>
  <a id="2962" href="logic.complements-de-morgan-subtypes.html#2677" class="Function">is-full-union-subtype-complement-de-morgan-subtype</a> <a id="3013" href="logic.complements-de-morgan-subtypes.html#3013" class="Bound">P</a> <a id="3015" class="Symbol">=</a>
    <a id="3021" href="logic.complements-de-morgan-subtypes.html#1849" class="Function">is-full-union-complement-subtype-double-complement-subtype</a>
      <a id="3086" class="Symbol">(</a> <a id="3088" href="logic.de-morgan-subtypes.html#2320" class="Function">subtype-de-morgan-subtype</a> <a id="3114" href="logic.complements-de-morgan-subtypes.html#3013" class="Bound">P</a><a id="3115" class="Symbol">)</a>
      <a id="3123" class="Symbol">(</a> <a id="3125" href="logic.de-morgan-subtypes.html#2426" class="Function">is-de-morgan-de-morgan-subtype</a> <a id="3156" href="logic.complements-de-morgan-subtypes.html#3013" class="Bound">P</a><a id="3157" class="Symbol">)</a>
</pre>