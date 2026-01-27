# Opposite posets

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="order-theory.opposite-posets.html" class="Module">order-theory.opposite-posets</a> <a id="64" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="120" class="Keyword">open</a> <a id="125" class="Keyword">import</a> <a id="132" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="164" class="Keyword">open</a> <a id="169" class="Keyword">import</a> <a id="176" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="234" class="Keyword">open</a> <a id="239" class="Keyword">import</a> <a id="246" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="order-theory.opposite-preorders.html" class="Module">order-theory.opposite-preorders</a>
<a id="420" class="Keyword">open</a> <a id="425" class="Keyword">import</a> <a id="432" href="order-theory.order-preserving-maps-posets.html" class="Module">order-theory.order-preserving-maps-posets</a>
<a id="474" class="Keyword">open</a> <a id="479" class="Keyword">import</a> <a id="486" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="506" class="Keyword">open</a> <a id="511" class="Keyword">import</a> <a id="518" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
</pre>
</details>

## Idea

Let `X` be a [poset](order-theory.posets.md), its
{{#concept "opposite" Disambiguation="poset" Agda=opposite-Poset}} `Xᵒᵖ` is
given by reversing the relation.

## Definition

### The opposite poset

<pre class="Agda"><a id="774" class="Keyword">module</a> <a id="781" href="order-theory.opposite-posets.html#781" class="Module">_</a>
  <a id="785" class="Symbol">{</a><a id="786" href="order-theory.opposite-posets.html#786" class="Bound">l1</a> <a id="789" href="order-theory.opposite-posets.html#789" class="Bound">l2</a> <a id="792" class="Symbol">:</a> <a id="794" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="799" class="Symbol">}</a> <a id="801" class="Symbol">(</a><a id="802" href="order-theory.opposite-posets.html#802" class="Bound">P</a> <a id="804" class="Symbol">:</a> <a id="806" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="812" href="order-theory.opposite-posets.html#786" class="Bound">l1</a> <a id="815" href="order-theory.opposite-posets.html#789" class="Bound">l2</a><a id="817" class="Symbol">)</a>
  <a id="821" class="Keyword">where</a>

  <a id="830" href="order-theory.opposite-posets.html#830" class="Function">preorder-opposite-Poset</a> <a id="854" class="Symbol">:</a> <a id="856" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="865" href="order-theory.opposite-posets.html#786" class="Bound">l1</a> <a id="868" href="order-theory.opposite-posets.html#789" class="Bound">l2</a>
  <a id="873" href="order-theory.opposite-posets.html#830" class="Function">preorder-opposite-Poset</a> <a id="897" class="Symbol">=</a>
    <a id="903" href="order-theory.opposite-preorders.html#1543" class="Function">opposite-Preorder</a> <a id="921" class="Symbol">(</a><a id="922" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="937" href="order-theory.opposite-posets.html#802" class="Bound">P</a><a id="938" class="Symbol">)</a>

  <a id="943" href="order-theory.opposite-posets.html#943" class="Function">type-opposite-Poset</a> <a id="963" class="Symbol">:</a> <a id="965" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="968" href="order-theory.opposite-posets.html#786" class="Bound">l1</a>
  <a id="973" href="order-theory.opposite-posets.html#943" class="Function">type-opposite-Poset</a> <a id="993" class="Symbol">=</a> <a id="995" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1009" href="order-theory.opposite-posets.html#830" class="Function">preorder-opposite-Poset</a>

  <a id="1036" href="order-theory.opposite-posets.html#1036" class="Function">leq-prop-opposite-Poset</a> <a id="1060" class="Symbol">:</a> <a id="1062" class="Symbol">(</a><a id="1063" href="order-theory.opposite-posets.html#1063" class="Bound">X</a> <a id="1065" href="order-theory.opposite-posets.html#1065" class="Bound">Y</a> <a id="1067" class="Symbol">:</a> <a id="1069" href="order-theory.opposite-posets.html#943" class="Function">type-opposite-Poset</a><a id="1088" class="Symbol">)</a> <a id="1090" class="Symbol">→</a> <a id="1092" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1097" href="order-theory.opposite-posets.html#789" class="Bound">l2</a>
  <a id="1102" href="order-theory.opposite-posets.html#1036" class="Function">leq-prop-opposite-Poset</a> <a id="1126" class="Symbol">=</a>
    <a id="1132" href="order-theory.preorders.html#1322" class="Function">leq-prop-Preorder</a> <a id="1150" href="order-theory.opposite-posets.html#830" class="Function">preorder-opposite-Poset</a>

  <a id="1177" href="order-theory.opposite-posets.html#1177" class="Function">leq-opposite-Poset</a> <a id="1196" class="Symbol">:</a> <a id="1198" class="Symbol">(</a><a id="1199" href="order-theory.opposite-posets.html#1199" class="Bound">X</a> <a id="1201" href="order-theory.opposite-posets.html#1201" class="Bound">Y</a> <a id="1203" class="Symbol">:</a> <a id="1205" href="order-theory.opposite-posets.html#943" class="Function">type-opposite-Poset</a><a id="1224" class="Symbol">)</a> <a id="1226" class="Symbol">→</a> <a id="1228" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1231" href="order-theory.opposite-posets.html#789" class="Bound">l2</a>
  <a id="1236" href="order-theory.opposite-posets.html#1177" class="Function">leq-opposite-Poset</a> <a id="1255" class="Symbol">=</a>
    <a id="1261" href="order-theory.preorders.html#1410" class="Function">leq-Preorder</a> <a id="1274" href="order-theory.opposite-posets.html#830" class="Function">preorder-opposite-Poset</a>

  <a id="1301" href="order-theory.opposite-posets.html#1301" class="Function">transitive-leq-opposite-Poset</a> <a id="1331" class="Symbol">:</a>
    <a id="1337" class="Symbol">(</a><a id="1338" href="order-theory.opposite-posets.html#1338" class="Bound">X</a> <a id="1340" href="order-theory.opposite-posets.html#1340" class="Bound">Y</a> <a id="1342" href="order-theory.opposite-posets.html#1342" class="Bound">Z</a> <a id="1344" class="Symbol">:</a> <a id="1346" href="order-theory.opposite-posets.html#943" class="Function">type-opposite-Poset</a><a id="1365" class="Symbol">)</a> <a id="1367" class="Symbol">→</a>
    <a id="1373" href="order-theory.opposite-posets.html#1177" class="Function">leq-opposite-Poset</a> <a id="1392" href="order-theory.opposite-posets.html#1340" class="Bound">Y</a> <a id="1394" href="order-theory.opposite-posets.html#1342" class="Bound">Z</a> <a id="1396" class="Symbol">→</a>
    <a id="1402" href="order-theory.opposite-posets.html#1177" class="Function">leq-opposite-Poset</a> <a id="1421" href="order-theory.opposite-posets.html#1338" class="Bound">X</a> <a id="1423" href="order-theory.opposite-posets.html#1340" class="Bound">Y</a> <a id="1425" class="Symbol">→</a>
    <a id="1431" href="order-theory.opposite-posets.html#1177" class="Function">leq-opposite-Poset</a> <a id="1450" href="order-theory.opposite-posets.html#1338" class="Bound">X</a> <a id="1452" href="order-theory.opposite-posets.html#1342" class="Bound">Z</a>
  <a id="1456" href="order-theory.opposite-posets.html#1301" class="Function">transitive-leq-opposite-Poset</a> <a id="1486" class="Symbol">=</a>
    <a id="1492" href="order-theory.preorders.html#3361" class="Function">transitive-leq-Preorder</a> <a id="1516" href="order-theory.opposite-posets.html#830" class="Function">preorder-opposite-Poset</a>

  <a id="1543" href="order-theory.opposite-posets.html#1543" class="Function">refl-leq-opposite-Poset</a> <a id="1567" class="Symbol">:</a>
    <a id="1573" class="Symbol">(</a><a id="1574" href="order-theory.opposite-posets.html#1574" class="Bound">X</a> <a id="1576" class="Symbol">:</a> <a id="1578" href="order-theory.opposite-posets.html#943" class="Function">type-opposite-Poset</a><a id="1597" class="Symbol">)</a> <a id="1599" class="Symbol">→</a> <a id="1601" href="order-theory.opposite-posets.html#1177" class="Function">leq-opposite-Poset</a> <a id="1620" href="order-theory.opposite-posets.html#1574" class="Bound">X</a> <a id="1622" href="order-theory.opposite-posets.html#1574" class="Bound">X</a>
  <a id="1626" href="order-theory.opposite-posets.html#1543" class="Function">refl-leq-opposite-Poset</a> <a id="1650" class="Symbol">=</a>
    <a id="1656" href="order-theory.preorders.html#3156" class="Function">refl-leq-Preorder</a> <a id="1674" href="order-theory.opposite-posets.html#830" class="Function">preorder-opposite-Poset</a>

  <a id="1701" href="order-theory.opposite-posets.html#1701" class="Function">antisymmetric-leq-opposite-Poset</a> <a id="1734" class="Symbol">:</a>
    <a id="1740" class="Symbol">(</a><a id="1741" href="order-theory.opposite-posets.html#1741" class="Bound">X</a> <a id="1743" href="order-theory.opposite-posets.html#1743" class="Bound">Y</a> <a id="1745" class="Symbol">:</a> <a id="1747" href="order-theory.opposite-posets.html#943" class="Function">type-opposite-Poset</a><a id="1766" class="Symbol">)</a> <a id="1768" class="Symbol">→</a>
    <a id="1774" href="order-theory.opposite-posets.html#1177" class="Function">leq-opposite-Poset</a> <a id="1793" href="order-theory.opposite-posets.html#1741" class="Bound">X</a> <a id="1795" href="order-theory.opposite-posets.html#1743" class="Bound">Y</a> <a id="1797" class="Symbol">→</a>
    <a id="1803" href="order-theory.opposite-posets.html#1177" class="Function">leq-opposite-Poset</a> <a id="1822" href="order-theory.opposite-posets.html#1743" class="Bound">Y</a> <a id="1824" href="order-theory.opposite-posets.html#1741" class="Bound">X</a> <a id="1826" class="Symbol">→</a>
    <a id="1832" href="order-theory.opposite-posets.html#1741" class="Bound">X</a> <a id="1834" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1836" href="order-theory.opposite-posets.html#1743" class="Bound">Y</a>
  <a id="1840" href="order-theory.opposite-posets.html#1701" class="Function">antisymmetric-leq-opposite-Poset</a> <a id="1873" href="order-theory.opposite-posets.html#1873" class="Bound">X</a> <a id="1875" href="order-theory.opposite-posets.html#1875" class="Bound">Y</a> <a id="1877" href="order-theory.opposite-posets.html#1877" class="Bound">p</a> <a id="1879" href="order-theory.opposite-posets.html#1879" class="Bound">q</a> <a id="1881" class="Symbol">=</a>
    <a id="1887" href="order-theory.posets.html#3131" class="Function">antisymmetric-leq-Poset</a> <a id="1911" href="order-theory.opposite-posets.html#802" class="Bound">P</a> <a id="1913" href="order-theory.opposite-posets.html#1873" class="Bound">X</a> <a id="1915" href="order-theory.opposite-posets.html#1875" class="Bound">Y</a> <a id="1917" href="order-theory.opposite-posets.html#1879" class="Bound">q</a> <a id="1919" href="order-theory.opposite-posets.html#1877" class="Bound">p</a>

  <a id="1924" href="order-theory.opposite-posets.html#1924" class="Function">opposite-Poset</a> <a id="1939" class="Symbol">:</a> <a id="1941" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1947" href="order-theory.opposite-posets.html#786" class="Bound">l1</a> <a id="1950" href="order-theory.opposite-posets.html#789" class="Bound">l2</a>
  <a id="1955" href="order-theory.opposite-posets.html#1924" class="Function">opposite-Poset</a> <a id="1970" class="Symbol">=</a>
    <a id="1976" class="Symbol">(</a> <a id="1978" href="order-theory.opposite-posets.html#830" class="Function">preorder-opposite-Poset</a> <a id="2002" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2004" href="order-theory.opposite-posets.html#1701" class="Function">antisymmetric-leq-opposite-Poset</a><a id="2036" class="Symbol">)</a>
</pre>
### The opposite functorial action on order preserving maps of posets

<pre class="Agda"><a id="2122" class="Keyword">module</a> <a id="2129" href="order-theory.opposite-posets.html#2129" class="Module">_</a>
  <a id="2133" class="Symbol">{</a><a id="2134" href="order-theory.opposite-posets.html#2134" class="Bound">l1</a> <a id="2137" href="order-theory.opposite-posets.html#2137" class="Bound">l2</a> <a id="2140" href="order-theory.opposite-posets.html#2140" class="Bound">l3</a> <a id="2143" href="order-theory.opposite-posets.html#2143" class="Bound">l4</a> <a id="2146" class="Symbol">:</a> <a id="2148" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2153" class="Symbol">}</a> <a id="2155" class="Symbol">(</a><a id="2156" href="order-theory.opposite-posets.html#2156" class="Bound">P</a> <a id="2158" class="Symbol">:</a> <a id="2160" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2166" href="order-theory.opposite-posets.html#2134" class="Bound">l1</a> <a id="2169" href="order-theory.opposite-posets.html#2137" class="Bound">l2</a><a id="2171" class="Symbol">)</a> <a id="2173" class="Symbol">(</a><a id="2174" href="order-theory.opposite-posets.html#2174" class="Bound">Q</a> <a id="2176" class="Symbol">:</a> <a id="2178" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2184" href="order-theory.opposite-posets.html#2140" class="Bound">l3</a> <a id="2187" href="order-theory.opposite-posets.html#2143" class="Bound">l4</a><a id="2189" class="Symbol">)</a>
  <a id="2193" class="Keyword">where</a>

  <a id="2202" href="order-theory.opposite-posets.html#2202" class="Function">opposite-hom-Poset</a> <a id="2221" class="Symbol">:</a>
    <a id="2227" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="2237" href="order-theory.opposite-posets.html#2156" class="Bound">P</a> <a id="2239" href="order-theory.opposite-posets.html#2174" class="Bound">Q</a> <a id="2241" class="Symbol">→</a> <a id="2243" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="2253" class="Symbol">(</a><a id="2254" href="order-theory.opposite-posets.html#1924" class="Function">opposite-Poset</a> <a id="2269" href="order-theory.opposite-posets.html#2156" class="Bound">P</a><a id="2270" class="Symbol">)</a> <a id="2272" class="Symbol">(</a><a id="2273" href="order-theory.opposite-posets.html#1924" class="Function">opposite-Poset</a> <a id="2288" href="order-theory.opposite-posets.html#2174" class="Bound">Q</a><a id="2289" class="Symbol">)</a>
  <a id="2293" href="order-theory.opposite-posets.html#2202" class="Function">opposite-hom-Poset</a> <a id="2312" class="Symbol">=</a>
    <a id="2318" href="order-theory.opposite-preorders.html#1914" class="Function">opposite-hom-Preorder</a> <a id="2340" class="Symbol">(</a><a id="2341" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2356" href="order-theory.opposite-posets.html#2156" class="Bound">P</a><a id="2357" class="Symbol">)</a> <a id="2359" class="Symbol">(</a><a id="2360" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="2375" href="order-theory.opposite-posets.html#2174" class="Bound">Q</a><a id="2376" class="Symbol">)</a>
</pre>
## Properties

### The opposite poset construction is a strict involution

<pre class="Agda"><a id="2466" class="Keyword">module</a> <a id="2473" href="order-theory.opposite-posets.html#2473" class="Module">_</a>
  <a id="2477" class="Symbol">{</a><a id="2478" href="order-theory.opposite-posets.html#2478" class="Bound">l1</a> <a id="2481" href="order-theory.opposite-posets.html#2481" class="Bound">l2</a> <a id="2484" class="Symbol">:</a> <a id="2486" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2491" class="Symbol">}</a> <a id="2493" class="Symbol">(</a><a id="2494" href="order-theory.opposite-posets.html#2494" class="Bound">P</a> <a id="2496" class="Symbol">:</a> <a id="2498" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2504" href="order-theory.opposite-posets.html#2478" class="Bound">l1</a> <a id="2507" href="order-theory.opposite-posets.html#2481" class="Bound">l2</a><a id="2509" class="Symbol">)</a>
  <a id="2513" class="Keyword">where</a>

  <a id="2522" href="order-theory.opposite-posets.html#2522" class="Function">is-involution-opposite-Poset</a> <a id="2551" class="Symbol">:</a> <a id="2553" href="order-theory.opposite-posets.html#1924" class="Function">opposite-Poset</a> <a id="2568" class="Symbol">(</a><a id="2569" href="order-theory.opposite-posets.html#1924" class="Function">opposite-Poset</a> <a id="2584" href="order-theory.opposite-posets.html#2494" class="Bound">P</a><a id="2585" class="Symbol">)</a> <a id="2587" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2589" href="order-theory.opposite-posets.html#2494" class="Bound">P</a>
  <a id="2593" href="order-theory.opposite-posets.html#2522" class="Function">is-involution-opposite-Poset</a> <a id="2622" class="Symbol">=</a> <a id="2624" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="2630" class="Keyword">module</a> <a id="2637" href="order-theory.opposite-posets.html#2637" class="Module">_</a>
  <a id="2641" class="Symbol">{</a><a id="2642" href="order-theory.opposite-posets.html#2642" class="Bound">l1</a> <a id="2645" href="order-theory.opposite-posets.html#2645" class="Bound">l2</a> <a id="2648" href="order-theory.opposite-posets.html#2648" class="Bound">l3</a> <a id="2651" href="order-theory.opposite-posets.html#2651" class="Bound">l4</a> <a id="2654" class="Symbol">:</a> <a id="2656" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2661" class="Symbol">}</a>
  <a id="2665" class="Symbol">(</a><a id="2666" href="order-theory.opposite-posets.html#2666" class="Bound">P</a> <a id="2668" class="Symbol">:</a> <a id="2670" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2676" href="order-theory.opposite-posets.html#2642" class="Bound">l1</a> <a id="2679" href="order-theory.opposite-posets.html#2645" class="Bound">l2</a><a id="2681" class="Symbol">)</a> <a id="2683" class="Symbol">(</a><a id="2684" href="order-theory.opposite-posets.html#2684" class="Bound">Q</a> <a id="2686" class="Symbol">:</a> <a id="2688" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2694" href="order-theory.opposite-posets.html#2648" class="Bound">l3</a> <a id="2697" href="order-theory.opposite-posets.html#2651" class="Bound">l4</a><a id="2699" class="Symbol">)</a>
  <a id="2703" class="Symbol">(</a><a id="2704" href="order-theory.opposite-posets.html#2704" class="Bound">f</a> <a id="2706" class="Symbol">:</a> <a id="2708" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="2718" href="order-theory.opposite-posets.html#2666" class="Bound">P</a> <a id="2720" href="order-theory.opposite-posets.html#2684" class="Bound">Q</a><a id="2721" class="Symbol">)</a>
  <a id="2725" class="Keyword">where</a>

  <a id="2734" href="order-theory.opposite-posets.html#2734" class="Function">is-involution-opposite-hom-Poset</a> <a id="2767" class="Symbol">:</a>
    <a id="2773" href="order-theory.opposite-posets.html#2202" class="Function">opposite-hom-Poset</a>
      <a id="2798" class="Symbol">(</a> <a id="2800" href="order-theory.opposite-posets.html#1924" class="Function">opposite-Poset</a> <a id="2815" href="order-theory.opposite-posets.html#2666" class="Bound">P</a><a id="2816" class="Symbol">)</a>
      <a id="2824" class="Symbol">(</a> <a id="2826" href="order-theory.opposite-posets.html#1924" class="Function">opposite-Poset</a> <a id="2841" href="order-theory.opposite-posets.html#2684" class="Bound">Q</a><a id="2842" class="Symbol">)</a>
      <a id="2850" class="Symbol">(</a> <a id="2852" href="order-theory.opposite-posets.html#2202" class="Function">opposite-hom-Poset</a> <a id="2871" href="order-theory.opposite-posets.html#2666" class="Bound">P</a> <a id="2873" href="order-theory.opposite-posets.html#2684" class="Bound">Q</a> <a id="2875" href="order-theory.opposite-posets.html#2704" class="Bound">f</a><a id="2876" class="Symbol">)</a> <a id="2878" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2884" href="order-theory.opposite-posets.html#2704" class="Bound">f</a>
  <a id="2888" href="order-theory.opposite-posets.html#2734" class="Function">is-involution-opposite-hom-Poset</a> <a id="2921" class="Symbol">=</a> <a id="2923" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>