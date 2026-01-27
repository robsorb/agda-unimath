# Meet-suplattices

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="order-theory.meet-suplattices.html" class="Module">order-theory.meet-suplattices</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="order-theory.meet-semilattices.html" class="Module">order-theory.meet-semilattices</a>
<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="385" class="Keyword">open</a> <a id="390" class="Keyword">import</a> <a id="397" href="order-theory.suplattices.html" class="Module">order-theory.suplattices</a>
</pre>
</details>

## Idea

An **`l`-meet-suplattice** is a meet-semilattice `L` which has least upper
bounds for all families of elements `x : I → L` indexed by a type `I : UU l`.

Note that meet-suplattices are not required to satisfy a distributive law. Such
meet-suplattices are called [frames](order-theory.frames.md).

## Definitions

### The predicate on meet-semilattices of being a meet-suplattice

<pre class="Agda"><a id="836" class="Keyword">module</a> <a id="843" href="order-theory.meet-suplattices.html#843" class="Module">_</a>
  <a id="847" class="Symbol">{</a><a id="848" href="order-theory.meet-suplattices.html#848" class="Bound">l1</a> <a id="851" class="Symbol">:</a> <a id="853" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="858" class="Symbol">}</a> <a id="860" class="Symbol">(</a><a id="861" href="order-theory.meet-suplattices.html#861" class="Bound">l2</a> <a id="864" class="Symbol">:</a> <a id="866" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="871" class="Symbol">)</a> <a id="873" class="Symbol">(</a><a id="874" href="order-theory.meet-suplattices.html#874" class="Bound">X</a> <a id="876" class="Symbol">:</a> <a id="878" href="order-theory.meet-semilattices.html#2461" class="Function">Meet-Semilattice</a> <a id="895" href="order-theory.meet-suplattices.html#848" class="Bound">l1</a><a id="897" class="Symbol">)</a>
  <a id="901" class="Keyword">where</a>

  <a id="910" href="order-theory.meet-suplattices.html#910" class="Function">is-meet-suplattice-Meet-Semilattice-Prop</a> <a id="951" class="Symbol">:</a> <a id="953" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="958" class="Symbol">(</a><a id="959" href="order-theory.meet-suplattices.html#848" class="Bound">l1</a> <a id="962" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="964" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="969" href="order-theory.meet-suplattices.html#861" class="Bound">l2</a><a id="971" class="Symbol">)</a>
  <a id="975" href="order-theory.meet-suplattices.html#910" class="Function">is-meet-suplattice-Meet-Semilattice-Prop</a> <a id="1016" class="Symbol">=</a>
    <a id="1022" href="order-theory.suplattices.html#1054" class="Function">is-suplattice-Poset-Prop</a> <a id="1047" href="order-theory.meet-suplattices.html#861" class="Bound">l2</a> <a id="1050" class="Symbol">(</a><a id="1051" href="order-theory.meet-semilattices.html#5978" class="Function">poset-Meet-Semilattice</a> <a id="1074" href="order-theory.meet-suplattices.html#874" class="Bound">X</a><a id="1075" class="Symbol">)</a>

  <a id="1080" href="order-theory.meet-suplattices.html#1080" class="Function">is-meet-suplattice-Meet-Semilattice</a> <a id="1116" class="Symbol">:</a> <a id="1118" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1121" class="Symbol">(</a><a id="1122" href="order-theory.meet-suplattices.html#848" class="Bound">l1</a> <a id="1125" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1127" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1132" href="order-theory.meet-suplattices.html#861" class="Bound">l2</a><a id="1134" class="Symbol">)</a>
  <a id="1138" href="order-theory.meet-suplattices.html#1080" class="Function">is-meet-suplattice-Meet-Semilattice</a> <a id="1174" class="Symbol">=</a>
    <a id="1180" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1190" href="order-theory.meet-suplattices.html#910" class="Function">is-meet-suplattice-Meet-Semilattice-Prop</a>

  <a id="1234" href="order-theory.meet-suplattices.html#1234" class="Function">is-prop-is-meet-suplattice-Meet-Semilattice</a> <a id="1278" class="Symbol">:</a>
    <a id="1284" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1292" href="order-theory.meet-suplattices.html#1080" class="Function">is-meet-suplattice-Meet-Semilattice</a>
  <a id="1330" href="order-theory.meet-suplattices.html#1234" class="Function">is-prop-is-meet-suplattice-Meet-Semilattice</a> <a id="1374" class="Symbol">=</a>
    <a id="1380" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1398" href="order-theory.meet-suplattices.html#910" class="Function">is-meet-suplattice-Meet-Semilattice-Prop</a>
</pre>
### Meet-suplattices

<pre class="Agda"><a id="Meet-Suplattice"></a><a id="1474" href="order-theory.meet-suplattices.html#1474" class="Function">Meet-Suplattice</a> <a id="1490" class="Symbol">:</a> <a id="1492" class="Symbol">(</a><a id="1493" href="order-theory.meet-suplattices.html#1493" class="Bound">l1</a> <a id="1496" href="order-theory.meet-suplattices.html#1496" class="Bound">l2</a> <a id="1499" class="Symbol">:</a> <a id="1501" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1506" class="Symbol">)</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1513" class="Symbol">(</a><a id="1514" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1519" href="order-theory.meet-suplattices.html#1493" class="Bound">l1</a> <a id="1522" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1524" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1529" href="order-theory.meet-suplattices.html#1496" class="Bound">l2</a><a id="1531" class="Symbol">)</a>
<a id="1533" href="order-theory.meet-suplattices.html#1474" class="Function">Meet-Suplattice</a> <a id="1549" href="order-theory.meet-suplattices.html#1549" class="Bound">l1</a> <a id="1552" href="order-theory.meet-suplattices.html#1552" class="Bound">l2</a> <a id="1555" class="Symbol">=</a>
  <a id="1559" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1561" class="Symbol">(</a><a id="1562" href="order-theory.meet-semilattices.html#2461" class="Function">Meet-Semilattice</a> <a id="1579" href="order-theory.meet-suplattices.html#1549" class="Bound">l1</a><a id="1581" class="Symbol">)</a> <a id="1583" class="Symbol">(</a><a id="1584" href="order-theory.meet-suplattices.html#1080" class="Function">is-meet-suplattice-Meet-Semilattice</a> <a id="1620" href="order-theory.meet-suplattices.html#1552" class="Bound">l2</a><a id="1622" class="Symbol">)</a>

<a id="1625" class="Keyword">module</a> <a id="1632" href="order-theory.meet-suplattices.html#1632" class="Module">_</a>
  <a id="1636" class="Symbol">{</a><a id="1637" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a> <a id="1640" href="order-theory.meet-suplattices.html#1640" class="Bound">l2</a> <a id="1643" class="Symbol">:</a> <a id="1645" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1650" class="Symbol">}</a> <a id="1652" class="Symbol">(</a><a id="1653" href="order-theory.meet-suplattices.html#1653" class="Bound">A</a> <a id="1655" class="Symbol">:</a> <a id="1657" href="order-theory.meet-suplattices.html#1474" class="Function">Meet-Suplattice</a> <a id="1673" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a> <a id="1676" href="order-theory.meet-suplattices.html#1640" class="Bound">l2</a><a id="1678" class="Symbol">)</a>
  <a id="1682" class="Keyword">where</a>

  <a id="1691" href="order-theory.meet-suplattices.html#1691" class="Function">meet-semilattice-Meet-Suplattice</a> <a id="1724" class="Symbol">:</a> <a id="1726" href="order-theory.meet-semilattices.html#2461" class="Function">Meet-Semilattice</a> <a id="1743" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a>
  <a id="1748" href="order-theory.meet-suplattices.html#1691" class="Function">meet-semilattice-Meet-Suplattice</a> <a id="1781" class="Symbol">=</a> <a id="1783" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1787" href="order-theory.meet-suplattices.html#1653" class="Bound">A</a>

  <a id="1792" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a> <a id="1814" class="Symbol">:</a> <a id="1816" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1822" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a> <a id="1825" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a>
  <a id="1830" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a> <a id="1852" class="Symbol">=</a>
    <a id="1858" href="order-theory.meet-semilattices.html#5978" class="Function">poset-Meet-Semilattice</a> <a id="1881" href="order-theory.meet-suplattices.html#1691" class="Function">meet-semilattice-Meet-Suplattice</a>

  <a id="1917" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a> <a id="1938" class="Symbol">:</a> <a id="1940" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1943" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a>
  <a id="1948" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a> <a id="1969" class="Symbol">=</a>
    <a id="1975" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1986" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="2011" href="order-theory.meet-suplattices.html#2011" class="Function">leq-meet-suplattice-Prop</a> <a id="2036" class="Symbol">:</a> <a id="2038" class="Symbol">(</a><a id="2039" href="order-theory.meet-suplattices.html#2039" class="Bound">x</a> <a id="2041" href="order-theory.meet-suplattices.html#2041" class="Bound">y</a> <a id="2043" class="Symbol">:</a> <a id="2045" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a><a id="2065" class="Symbol">)</a> <a id="2067" class="Symbol">→</a> <a id="2069" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2074" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a>
  <a id="2079" href="order-theory.meet-suplattices.html#2011" class="Function">leq-meet-suplattice-Prop</a> <a id="2104" class="Symbol">=</a> <a id="2106" href="order-theory.posets.html#1413" class="Function">leq-prop-Poset</a> <a id="2121" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="2146" href="order-theory.meet-suplattices.html#2146" class="Function">leq-Meet-Suplattice</a> <a id="2166" class="Symbol">:</a> <a id="2168" class="Symbol">(</a><a id="2169" href="order-theory.meet-suplattices.html#2169" class="Bound">x</a> <a id="2171" href="order-theory.meet-suplattices.html#2171" class="Bound">y</a> <a id="2173" class="Symbol">:</a> <a id="2175" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a><a id="2195" class="Symbol">)</a> <a id="2197" class="Symbol">→</a> <a id="2199" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2202" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a>
  <a id="2207" href="order-theory.meet-suplattices.html#2146" class="Function">leq-Meet-Suplattice</a> <a id="2227" class="Symbol">=</a> <a id="2229" href="order-theory.posets.html#1514" class="Function">leq-Poset</a> <a id="2239" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="2264" href="order-theory.meet-suplattices.html#2264" class="Function">is-prop-leq-Meet-Suplattice</a> <a id="2292" class="Symbol">:</a>
    <a id="2298" class="Symbol">(</a><a id="2299" href="order-theory.meet-suplattices.html#2299" class="Bound">x</a> <a id="2301" href="order-theory.meet-suplattices.html#2301" class="Bound">y</a> <a id="2303" class="Symbol">:</a> <a id="2305" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a><a id="2325" class="Symbol">)</a> <a id="2327" class="Symbol">→</a> <a id="2329" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2337" class="Symbol">(</a><a id="2338" href="order-theory.meet-suplattices.html#2146" class="Function">leq-Meet-Suplattice</a> <a id="2358" href="order-theory.meet-suplattices.html#2299" class="Bound">x</a> <a id="2360" href="order-theory.meet-suplattices.html#2301" class="Bound">y</a><a id="2361" class="Symbol">)</a>
  <a id="2365" href="order-theory.meet-suplattices.html#2264" class="Function">is-prop-leq-Meet-Suplattice</a> <a id="2393" class="Symbol">=</a> <a id="2395" href="order-theory.posets.html#1598" class="Function">is-prop-leq-Poset</a> <a id="2413" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="2438" href="order-theory.meet-suplattices.html#2438" class="Function">refl-leq-Meet-Suplattice</a> <a id="2463" class="Symbol">:</a> <a id="2465" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="2478" href="order-theory.meet-suplattices.html#2146" class="Function">leq-Meet-Suplattice</a>
  <a id="2500" href="order-theory.meet-suplattices.html#2438" class="Function">refl-leq-Meet-Suplattice</a> <a id="2525" class="Symbol">=</a> <a id="2527" href="order-theory.posets.html#2603" class="Function">refl-leq-Poset</a> <a id="2542" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="2567" href="order-theory.meet-suplattices.html#2567" class="Function">antisymmetric-leq-Meet-Suplattice</a> <a id="2601" class="Symbol">:</a> <a id="2603" href="foundation.binary-relations.html#6436" class="Function">is-antisymmetric</a> <a id="2620" href="order-theory.meet-suplattices.html#2146" class="Function">leq-Meet-Suplattice</a>
  <a id="2642" href="order-theory.meet-suplattices.html#2567" class="Function">antisymmetric-leq-Meet-Suplattice</a> <a id="2676" class="Symbol">=</a>
    <a id="2682" href="order-theory.posets.html#3131" class="Function">antisymmetric-leq-Poset</a> <a id="2706" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="2731" href="order-theory.meet-suplattices.html#2731" class="Function">transitive-leq-Meet-Suplattice</a> <a id="2762" class="Symbol">:</a> <a id="2764" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2778" href="order-theory.meet-suplattices.html#2146" class="Function">leq-Meet-Suplattice</a>
  <a id="2800" href="order-theory.meet-suplattices.html#2731" class="Function">transitive-leq-Meet-Suplattice</a> <a id="2831" class="Symbol">=</a> <a id="2833" href="order-theory.posets.html#2698" class="Function">transitive-leq-Poset</a> <a id="2854" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="2879" href="order-theory.meet-suplattices.html#2879" class="Function">is-set-type-Meet-Suplattice</a> <a id="2907" class="Symbol">:</a> <a id="2909" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="2916" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a>
  <a id="2939" href="order-theory.meet-suplattices.html#2879" class="Function">is-set-type-Meet-Suplattice</a> <a id="2967" class="Symbol">=</a> <a id="2969" href="order-theory.posets.html#3221" class="Function">is-set-type-Poset</a> <a id="2987" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="3012" href="order-theory.meet-suplattices.html#3012" class="Function">set-Meet-Suplattice</a> <a id="3032" class="Symbol">:</a> <a id="3034" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="3038" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a>
  <a id="3043" href="order-theory.meet-suplattices.html#3012" class="Function">set-Meet-Suplattice</a> <a id="3063" class="Symbol">=</a> <a id="3065" href="order-theory.posets.html#3542" class="Function">set-Poset</a> <a id="3075" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>

  <a id="3100" href="order-theory.meet-suplattices.html#3100" class="Function">is-suplattice-Meet-Suplattice</a> <a id="3130" class="Symbol">:</a>
    <a id="3136" href="order-theory.suplattices.html#1290" class="Function">is-suplattice-Poset</a> <a id="3156" href="order-theory.meet-suplattices.html#1640" class="Bound">l2</a> <a id="3159" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a>
  <a id="3183" href="order-theory.meet-suplattices.html#3100" class="Function">is-suplattice-Meet-Suplattice</a> <a id="3213" class="Symbol">=</a> <a id="3215" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3219" href="order-theory.meet-suplattices.html#1653" class="Bound">A</a>

  <a id="3224" href="order-theory.meet-suplattices.html#3224" class="Function">suplattice-Meet-Suplattice</a> <a id="3251" class="Symbol">:</a> <a id="3253" href="order-theory.suplattices.html#2026" class="Function">Suplattice</a> <a id="3264" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a> <a id="3267" href="order-theory.meet-suplattices.html#1637" class="Bound">l1</a> <a id="3270" href="order-theory.meet-suplattices.html#1640" class="Bound">l2</a>
  <a id="3275" href="order-theory.meet-suplattices.html#3224" class="Function">suplattice-Meet-Suplattice</a> <a id="3302" class="Symbol">=</a>
    <a id="3308" class="Symbol">(</a> <a id="3310" href="order-theory.meet-suplattices.html#1792" class="Function">poset-Meet-Suplattice</a> <a id="3332" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3334" href="order-theory.meet-suplattices.html#3100" class="Function">is-suplattice-Meet-Suplattice</a><a id="3363" class="Symbol">)</a>

  <a id="3368" href="order-theory.meet-suplattices.html#3368" class="Function">meet-Meet-Suplattice</a> <a id="3389" class="Symbol">:</a>
    <a id="3395" class="Symbol">(</a><a id="3396" href="order-theory.meet-suplattices.html#3396" class="Bound">x</a> <a id="3398" href="order-theory.meet-suplattices.html#3398" class="Bound">y</a> <a id="3400" class="Symbol">:</a> <a id="3402" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a><a id="3422" class="Symbol">)</a> <a id="3424" class="Symbol">→</a>
    <a id="3430" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a>
  <a id="3453" href="order-theory.meet-suplattices.html#3368" class="Function">meet-Meet-Suplattice</a> <a id="3474" class="Symbol">=</a>
    <a id="3480" href="order-theory.meet-semilattices.html#3261" class="Function">meet-Meet-Semilattice</a> <a id="3502" href="order-theory.meet-suplattices.html#1691" class="Function">meet-semilattice-Meet-Suplattice</a>

  <a id="3538" href="order-theory.meet-suplattices.html#3538" class="Function">sup-Meet-Suplattice</a> <a id="3558" class="Symbol">:</a>
    <a id="3564" class="Symbol">{</a><a id="3565" href="order-theory.meet-suplattices.html#3565" class="Bound">I</a> <a id="3567" class="Symbol">:</a> <a id="3569" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3572" href="order-theory.meet-suplattices.html#1640" class="Bound">l2</a><a id="3574" class="Symbol">}</a> <a id="3576" class="Symbol">→</a> <a id="3578" class="Symbol">(</a><a id="3579" href="order-theory.meet-suplattices.html#3565" class="Bound">I</a> <a id="3581" class="Symbol">→</a> <a id="3583" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a><a id="3603" class="Symbol">)</a> <a id="3605" class="Symbol">→</a>
    <a id="3611" href="order-theory.meet-suplattices.html#1917" class="Function">type-Meet-Suplattice</a>
  <a id="3634" href="order-theory.meet-suplattices.html#3538" class="Function">sup-Meet-Suplattice</a> <a id="3654" class="Symbol">{</a><a id="3655" href="order-theory.meet-suplattices.html#3655" class="Bound">I</a><a id="3656" class="Symbol">}</a> <a id="3658" href="order-theory.meet-suplattices.html#3658" class="Bound">f</a> <a id="3660" class="Symbol">=</a> <a id="3662" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3666" class="Symbol">(</a><a id="3667" href="order-theory.meet-suplattices.html#3100" class="Function">is-suplattice-Meet-Suplattice</a> <a id="3697" href="order-theory.meet-suplattices.html#3655" class="Bound">I</a> <a id="3699" href="order-theory.meet-suplattices.html#3658" class="Bound">f</a><a id="3700" class="Symbol">)</a>
</pre>