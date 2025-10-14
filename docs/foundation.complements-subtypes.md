# Complements of subtypes

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation.complements-subtypes.html" class="Module">foundation.complements-subtypes</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="foundation.decidable-propositions.html" class="Module">foundation.decidable-propositions</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.double-negation-stable-propositions.html" class="Module">foundation.double-negation-stable-propositions</a>
<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="foundation.full-subtypes.html" class="Module">foundation.full-subtypes</a>
<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="foundation.postcomposition-functions.html" class="Module">foundation.postcomposition-functions</a>
<a id="396" class="Keyword">open</a> <a id="401" class="Keyword">import</a> <a id="408" href="foundation.powersets.html" class="Module">foundation.powersets</a>
<a id="429" class="Keyword">open</a> <a id="434" class="Keyword">import</a> <a id="441" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="478" class="Keyword">open</a> <a id="483" class="Keyword">import</a> <a id="490" href="foundation.unions-subtypes.html" class="Module">foundation.unions-subtypes</a>
<a id="517" class="Keyword">open</a> <a id="522" class="Keyword">import</a> <a id="529" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="557" class="Keyword">open</a> <a id="562" class="Keyword">import</a> <a id="569" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="600" class="Keyword">open</a> <a id="605" class="Keyword">import</a> <a id="612" href="foundation-core.subtypes.html" class="Module">foundation-core.subtypes</a>

<a id="638" class="Keyword">open</a> <a id="643" class="Keyword">import</a> <a id="650" href="logic.double-negation-stable-subtypes.html" class="Module">logic.double-negation-stable-subtypes</a>

<a id="689" class="Keyword">open</a> <a id="694" class="Keyword">import</a> <a id="701" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>
<a id="727" class="Keyword">open</a> <a id="732" class="Keyword">import</a> <a id="739" href="order-theory.opposite-large-posets.html" class="Module">order-theory.opposite-large-posets</a>
<a id="774" class="Keyword">open</a> <a id="779" class="Keyword">import</a> <a id="786" href="order-theory.order-preserving-maps-large-posets.html" class="Module">order-theory.order-preserving-maps-large-posets</a>
<a id="834" class="Keyword">open</a> <a id="839" class="Keyword">import</a> <a id="846" href="order-theory.order-preserving-maps-large-preorders.html" class="Module">order-theory.order-preserving-maps-large-preorders</a>
<a id="897" class="Keyword">open</a> <a id="902" class="Keyword">import</a> <a id="909" href="order-theory.order-preserving-maps-posets.html" class="Module">order-theory.order-preserving-maps-posets</a>
<a id="951" class="Keyword">open</a> <a id="956" class="Keyword">import</a> <a id="963" href="order-theory.order-preserving-maps-preorders.html" class="Module">order-theory.order-preserving-maps-preorders</a>
<a id="1008" class="Keyword">open</a> <a id="1013" class="Keyword">import</a> <a id="1020" href="order-theory.posets.html" class="Module">order-theory.posets</a>
</pre>
</details>

## Idea

The
{{#concept "complement" Disambiguation="of a subtype" Agda=complement-subtype}}
of a [subtype](foundation-core.subtypes.md) `P ⊆ A` consists of the elements
that are [not](foundation-core.negation.md) in `P`.

## Definition

### Complements of subtypes

<pre class="Agda"><a id="complement-subtype"></a><a id="1332" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="1351" class="Symbol">:</a>
  <a id="1355" class="Symbol">{</a><a id="1356" href="foundation.complements-subtypes.html#1356" class="Bound">l1</a> <a id="1359" href="foundation.complements-subtypes.html#1359" class="Bound">l2</a> <a id="1362" class="Symbol">:</a> <a id="1364" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1369" class="Symbol">}</a> <a id="1371" class="Symbol">{</a><a id="1372" href="foundation.complements-subtypes.html#1372" class="Bound">A</a> <a id="1374" class="Symbol">:</a> <a id="1376" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1379" href="foundation.complements-subtypes.html#1356" class="Bound">l1</a><a id="1381" class="Symbol">}</a> <a id="1383" class="Symbol">→</a> <a id="1385" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1393" href="foundation.complements-subtypes.html#1359" class="Bound">l2</a> <a id="1396" href="foundation.complements-subtypes.html#1372" class="Bound">A</a> <a id="1398" class="Symbol">→</a> <a id="1400" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1408" href="foundation.complements-subtypes.html#1359" class="Bound">l2</a> <a id="1411" href="foundation.complements-subtypes.html#1372" class="Bound">A</a>
<a id="1413" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="1432" href="foundation.complements-subtypes.html#1432" class="Bound">P</a> <a id="1434" href="foundation.complements-subtypes.html#1434" class="Bound">x</a> <a id="1436" class="Symbol">=</a> <a id="1438" href="foundation.negation.html#981" class="Function">neg-Prop</a> <a id="1447" class="Symbol">(</a><a id="1448" href="foundation.complements-subtypes.html#1432" class="Bound">P</a> <a id="1450" href="foundation.complements-subtypes.html#1434" class="Bound">x</a><a id="1451" class="Symbol">)</a>
</pre>
## Properties

### Complements of subtypes are double negation stable

<pre class="Agda"><a id="complement-double-negation-stable-subtype&#39;"></a><a id="1537" href="foundation.complements-subtypes.html#1537" class="Function">complement-double-negation-stable-subtype&#39;</a> <a id="1580" class="Symbol">:</a>
  <a id="1584" class="Symbol">{</a><a id="1585" href="foundation.complements-subtypes.html#1585" class="Bound">l1</a> <a id="1588" href="foundation.complements-subtypes.html#1588" class="Bound">l2</a> <a id="1591" class="Symbol">:</a> <a id="1593" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1598" class="Symbol">}</a> <a id="1600" class="Symbol">{</a><a id="1601" href="foundation.complements-subtypes.html#1601" class="Bound">A</a> <a id="1603" class="Symbol">:</a> <a id="1605" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1608" href="foundation.complements-subtypes.html#1585" class="Bound">l1</a><a id="1610" class="Symbol">}</a> <a id="1612" class="Symbol">→</a>
  <a id="1616" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1624" href="foundation.complements-subtypes.html#1588" class="Bound">l2</a> <a id="1627" href="foundation.complements-subtypes.html#1601" class="Bound">A</a> <a id="1629" class="Symbol">→</a> <a id="1631" href="logic.double-negation-stable-subtypes.html#2451" class="Function">double-negation-stable-subtype</a> <a id="1662" href="foundation.complements-subtypes.html#1588" class="Bound">l2</a> <a id="1665" href="foundation.complements-subtypes.html#1601" class="Bound">A</a>
<a id="1667" href="foundation.complements-subtypes.html#1537" class="Function">complement-double-negation-stable-subtype&#39;</a> <a id="1710" href="foundation.complements-subtypes.html#1710" class="Bound">P</a> <a id="1712" href="foundation.complements-subtypes.html#1712" class="Bound">x</a> <a id="1714" class="Symbol">=</a>
  <a id="1718" href="foundation.double-negation-stable-propositions.html#8463" class="Function">neg-type-Double-Negation-Stable-Prop</a> <a id="1755" class="Symbol">(</a><a id="1756" href="foundation-core.subtypes.html#1596" class="Function">is-in-subtype</a> <a id="1770" href="foundation.complements-subtypes.html#1710" class="Bound">P</a> <a id="1772" href="foundation.complements-subtypes.html#1712" class="Bound">x</a><a id="1773" class="Symbol">)</a>
</pre>
### Taking complements gives a contravariant endooperator on the powerset posets

<pre class="Agda"><a id="neg-hom-powerset"></a><a id="1870" href="foundation.complements-subtypes.html#1870" class="Function">neg-hom-powerset</a> <a id="1887" class="Symbol">:</a>
  <a id="1891" class="Symbol">{</a><a id="1892" href="foundation.complements-subtypes.html#1892" class="Bound">l1</a> <a id="1895" class="Symbol">:</a> <a id="1897" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1902" class="Symbol">}</a> <a id="1904" class="Symbol">{</a><a id="1905" href="foundation.complements-subtypes.html#1905" class="Bound">A</a> <a id="1907" class="Symbol">:</a> <a id="1909" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1912" href="foundation.complements-subtypes.html#1892" class="Bound">l1</a><a id="1914" class="Symbol">}</a> <a id="1916" class="Symbol">→</a>
  <a id="1920" href="order-theory.order-preserving-maps-large-posets.html#1692" class="Function">hom-Large-Poset</a>
    <a id="1940" class="Symbol">(</a> <a id="1942" class="Symbol">λ</a> <a id="1944" href="foundation.complements-subtypes.html#1944" class="Bound">l</a> <a id="1946" class="Symbol">→</a> <a id="1948" href="foundation.complements-subtypes.html#1944" class="Bound">l</a><a id="1949" class="Symbol">)</a>
    <a id="1955" class="Symbol">(</a> <a id="1957" href="foundation.powersets.html#2632" class="Function">powerset-Large-Poset</a> <a id="1978" href="foundation.complements-subtypes.html#1905" class="Bound">A</a><a id="1979" class="Symbol">)</a>
    <a id="1985" class="Symbol">(</a> <a id="1987" href="order-theory.opposite-large-posets.html#2671" class="Function">opposite-Large-Poset</a> <a id="2008" class="Symbol">(</a><a id="2009" href="foundation.powersets.html#2632" class="Function">powerset-Large-Poset</a> <a id="2030" href="foundation.complements-subtypes.html#1905" class="Bound">A</a><a id="2031" class="Symbol">))</a>
<a id="2034" href="foundation.complements-subtypes.html#1870" class="Function">neg-hom-powerset</a> <a id="2051" class="Symbol">=</a>
  <a id="2055" href="order-theory.order-preserving-maps-large-preorders.html#1916" class="InductiveConstructor">make-hom-Large-Preorder</a>
    <a id="2083" class="Symbol">(</a> <a id="2085" class="Symbol">λ</a> <a id="2087" href="foundation.complements-subtypes.html#2087" class="Bound">P</a> <a id="2089" href="foundation.complements-subtypes.html#2089" class="Bound">x</a> <a id="2091" class="Symbol">→</a> <a id="2093" href="foundation.negation.html#981" class="Function">neg-Prop</a> <a id="2102" class="Symbol">(</a><a id="2103" href="foundation.complements-subtypes.html#2087" class="Bound">P</a> <a id="2105" href="foundation.complements-subtypes.html#2089" class="Bound">x</a><a id="2106" class="Symbol">))</a>
    <a id="2113" class="Symbol">(</a> <a id="2115" class="Symbol">λ</a> <a id="2117" href="foundation.complements-subtypes.html#2117" class="Bound">P</a> <a id="2119" href="foundation.complements-subtypes.html#2119" class="Bound">Q</a> <a id="2121" href="foundation.complements-subtypes.html#2121" class="Bound">f</a> <a id="2123" href="foundation.complements-subtypes.html#2123" class="Bound">x</a> <a id="2125" class="Symbol">→</a> <a id="2127" href="foundation-core.negation.html#643" class="Function">map-neg</a> <a id="2135" class="Symbol">(</a><a id="2136" href="foundation.complements-subtypes.html#2121" class="Bound">f</a> <a id="2138" href="foundation.complements-subtypes.html#2123" class="Bound">x</a><a id="2139" class="Symbol">))</a>
</pre>
### Complementation reverses the containment order on subsets

<pre class="Agda"><a id="2218" class="Keyword">module</a> <a id="2225" href="foundation.complements-subtypes.html#2225" class="Module">_</a>
  <a id="2229" class="Symbol">{</a><a id="2230" href="foundation.complements-subtypes.html#2230" class="Bound">l1</a> <a id="2233" href="foundation.complements-subtypes.html#2233" class="Bound">l2</a> <a id="2236" href="foundation.complements-subtypes.html#2236" class="Bound">l3</a> <a id="2239" class="Symbol">:</a> <a id="2241" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2246" class="Symbol">}</a>
  <a id="2250" class="Symbol">{</a><a id="2251" href="foundation.complements-subtypes.html#2251" class="Bound">A</a> <a id="2253" class="Symbol">:</a> <a id="2255" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2258" href="foundation.complements-subtypes.html#2230" class="Bound">l1</a><a id="2260" class="Symbol">}</a>
  <a id="2264" class="Symbol">(</a><a id="2265" href="foundation.complements-subtypes.html#2265" class="Bound">B</a> <a id="2267" class="Symbol">:</a> <a id="2269" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="2277" href="foundation.complements-subtypes.html#2233" class="Bound">l2</a> <a id="2280" href="foundation.complements-subtypes.html#2251" class="Bound">A</a><a id="2281" class="Symbol">)</a>
  <a id="2285" class="Symbol">(</a><a id="2286" href="foundation.complements-subtypes.html#2286" class="Bound">C</a> <a id="2288" class="Symbol">:</a> <a id="2290" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="2298" href="foundation.complements-subtypes.html#2236" class="Bound">l3</a> <a id="2301" href="foundation.complements-subtypes.html#2251" class="Bound">A</a><a id="2302" class="Symbol">)</a>
  <a id="2306" class="Keyword">where</a>

  <a id="2315" href="foundation.complements-subtypes.html#2315" class="Function">reverses-order-complement-subtype</a> <a id="2349" class="Symbol">:</a>
    <a id="2355" href="foundation.complements-subtypes.html#2265" class="Bound">B</a> <a id="2357" href="foundation-core.subtypes.html#2877" class="Function Operator">⊆</a> <a id="2359" href="foundation.complements-subtypes.html#2286" class="Bound">C</a> <a id="2361" class="Symbol">→</a>
    <a id="2367" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2386" href="foundation.complements-subtypes.html#2286" class="Bound">C</a> <a id="2388" href="foundation-core.subtypes.html#2877" class="Function Operator">⊆</a> <a id="2390" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="2409" href="foundation.complements-subtypes.html#2265" class="Bound">B</a>
  <a id="2413" href="foundation.complements-subtypes.html#2315" class="Function">reverses-order-complement-subtype</a> <a id="2447" href="foundation.complements-subtypes.html#2447" class="Bound">B⊆C</a> <a id="2451" href="foundation.complements-subtypes.html#2451" class="Bound">x</a> <a id="2453" href="foundation.complements-subtypes.html#2453" class="Bound">x∉C</a> <a id="2457" href="foundation.complements-subtypes.html#2457" class="Bound">x∈B</a> <a id="2461" class="Symbol">=</a> <a id="2463" href="foundation.complements-subtypes.html#2453" class="Bound">x∉C</a> <a id="2467" class="Symbol">(</a><a id="2468" href="foundation.complements-subtypes.html#2447" class="Bound">B⊆C</a> <a id="2472" href="foundation.complements-subtypes.html#2451" class="Bound">x</a> <a id="2474" href="foundation.complements-subtypes.html#2457" class="Bound">x∈B</a><a id="2477" class="Symbol">)</a>
</pre>