# Cores of categories

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="category-theory.cores-categories.html" class="Module">category-theory.cores-categories</a> <a id="72" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="category-theory.cores-precategories.html" class="Module">category-theory.cores-precategories</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="category-theory.groupoids.html" class="Module">category-theory.groupoids</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="category-theory.isomorphisms-in-categories.html" class="Module">category-theory.isomorphisms-in-categories</a>
<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
<a id="350" class="Keyword">open</a> <a id="355" class="Keyword">import</a> <a id="362" href="category-theory.pregroupoids.html" class="Module">category-theory.pregroupoids</a>
<a id="391" class="Keyword">open</a> <a id="396" class="Keyword">import</a> <a id="403" href="category-theory.subcategories.html" class="Module">category-theory.subcategories</a>
<a id="433" class="Keyword">open</a> <a id="438" class="Keyword">import</a> <a id="445" href="category-theory.wide-subcategories.html" class="Module">category-theory.wide-subcategories</a>

<a id="481" class="Keyword">open</a> <a id="486" class="Keyword">import</a> <a id="493" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The **core of a [category](category-theory.categories.md)** `C` is the maximal
subgroupoid of it. It consists of all objects and
[isomorphisms](category-theory.isomorphisms-in-categories.md) in `C`.

## Definitions

### The core wide subcategory

<pre class="Agda"><a id="881" class="Keyword">module</a> <a id="888" href="category-theory.cores-categories.html#888" class="Module">_</a>
  <a id="892" class="Symbol">{</a><a id="893" href="category-theory.cores-categories.html#893" class="Bound">l1</a> <a id="896" href="category-theory.cores-categories.html#896" class="Bound">l2</a> <a id="899" class="Symbol">:</a> <a id="901" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="906" class="Symbol">}</a> <a id="908" class="Symbol">(</a><a id="909" href="category-theory.cores-categories.html#909" class="Bound">C</a> <a id="911" class="Symbol">:</a> <a id="913" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="922" href="category-theory.cores-categories.html#893" class="Bound">l1</a> <a id="925" href="category-theory.cores-categories.html#896" class="Bound">l2</a><a id="927" class="Symbol">)</a>
  <a id="931" class="Keyword">where</a>

  <a id="940" href="category-theory.cores-categories.html#940" class="Function">core-wide-subcategory-Category</a> <a id="971" class="Symbol">:</a> <a id="973" href="category-theory.wide-subcategories.html#5724" class="Function">Wide-Subcategory</a> <a id="990" href="category-theory.cores-categories.html#896" class="Bound">l2</a> <a id="993" href="category-theory.cores-categories.html#909" class="Bound">C</a>
  <a id="997" href="category-theory.cores-categories.html#940" class="Function">core-wide-subcategory-Category</a> <a id="1028" class="Symbol">=</a>
    <a id="1034" href="category-theory.cores-precategories.html#1268" class="Function">core-wide-subprecategory-Precategory</a> <a id="1071" class="Symbol">(</a><a id="1072" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1093" href="category-theory.cores-categories.html#909" class="Bound">C</a><a id="1094" class="Symbol">)</a>
</pre>
### The core subcategory

<pre class="Agda"><a id="1135" class="Keyword">module</a> <a id="1142" href="category-theory.cores-categories.html#1142" class="Module">_</a>
  <a id="1146" class="Symbol">{</a><a id="1147" href="category-theory.cores-categories.html#1147" class="Bound">l1</a> <a id="1150" href="category-theory.cores-categories.html#1150" class="Bound">l2</a> <a id="1153" class="Symbol">:</a> <a id="1155" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1160" class="Symbol">}</a> <a id="1162" class="Symbol">(</a><a id="1163" href="category-theory.cores-categories.html#1163" class="Bound">C</a> <a id="1165" class="Symbol">:</a> <a id="1167" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1176" href="category-theory.cores-categories.html#1147" class="Bound">l1</a> <a id="1179" href="category-theory.cores-categories.html#1150" class="Bound">l2</a><a id="1181" class="Symbol">)</a>
  <a id="1185" class="Keyword">where</a>

  <a id="1194" href="category-theory.cores-categories.html#1194" class="Function">core-subcategory-Category</a> <a id="1220" class="Symbol">:</a> <a id="1222" href="category-theory.subcategories.html#4548" class="Function">Subcategory</a> <a id="1234" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1240" href="category-theory.cores-categories.html#1150" class="Bound">l2</a> <a id="1243" href="category-theory.cores-categories.html#1163" class="Bound">C</a>
  <a id="1247" href="category-theory.cores-categories.html#1194" class="Function">core-subcategory-Category</a> <a id="1273" class="Symbol">=</a>
    <a id="1279" href="category-theory.cores-precategories.html#1690" class="Function">core-subprecategory-Precategory</a> <a id="1311" class="Symbol">(</a><a id="1312" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1333" href="category-theory.cores-categories.html#1163" class="Bound">C</a><a id="1334" class="Symbol">)</a>

  <a id="1339" href="category-theory.cores-categories.html#1339" class="Function">is-wide-core-Category</a> <a id="1361" class="Symbol">:</a> <a id="1363" href="category-theory.wide-subcategories.html#2474" class="Function">is-wide-Subcategory</a> <a id="1383" href="category-theory.cores-categories.html#1163" class="Bound">C</a> <a id="1385" href="category-theory.cores-categories.html#1194" class="Function">core-subcategory-Category</a>
  <a id="1413" href="category-theory.cores-categories.html#1339" class="Function">is-wide-core-Category</a> <a id="1435" class="Symbol">=</a> <a id="1437" href="category-theory.cores-precategories.html#1878" class="Function">is-wide-core-Precategory</a> <a id="1462" class="Symbol">(</a><a id="1463" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1484" href="category-theory.cores-categories.html#1163" class="Bound">C</a><a id="1485" class="Symbol">)</a>
</pre>
### The core precategory

<pre class="Agda"><a id="core-precategory-Category"></a><a id="1526" href="category-theory.cores-categories.html#1526" class="Function">core-precategory-Category</a> <a id="1552" class="Symbol">:</a>
  <a id="1556" class="Symbol">{</a><a id="1557" href="category-theory.cores-categories.html#1557" class="Bound">l1</a> <a id="1560" href="category-theory.cores-categories.html#1560" class="Bound">l2</a> <a id="1563" class="Symbol">:</a> <a id="1565" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1570" class="Symbol">}</a> <a id="1572" class="Symbol">(</a><a id="1573" href="category-theory.cores-categories.html#1573" class="Bound">C</a> <a id="1575" class="Symbol">:</a> <a id="1577" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1586" href="category-theory.cores-categories.html#1557" class="Bound">l1</a> <a id="1589" href="category-theory.cores-categories.html#1560" class="Bound">l2</a><a id="1591" class="Symbol">)</a> <a id="1593" class="Symbol">→</a> <a id="1595" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1607" href="category-theory.cores-categories.html#1557" class="Bound">l1</a> <a id="1610" href="category-theory.cores-categories.html#1560" class="Bound">l2</a>
<a id="1613" href="category-theory.cores-categories.html#1526" class="Function">core-precategory-Category</a> <a id="1639" href="category-theory.cores-categories.html#1639" class="Bound">C</a> <a id="1641" class="Symbol">=</a>
  <a id="1645" href="category-theory.cores-precategories.html#2109" class="Function">core-precategory-Precategory</a> <a id="1674" class="Symbol">(</a><a id="1675" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1696" href="category-theory.cores-categories.html#1639" class="Bound">C</a><a id="1697" class="Symbol">)</a>
</pre>
### The core category

<pre class="Agda"><a id="core-category-Category"></a><a id="1735" href="category-theory.cores-categories.html#1735" class="Function">core-category-Category</a> <a id="1758" class="Symbol">:</a>
  <a id="1762" class="Symbol">{</a><a id="1763" href="category-theory.cores-categories.html#1763" class="Bound">l1</a> <a id="1766" href="category-theory.cores-categories.html#1766" class="Bound">l2</a> <a id="1769" class="Symbol">:</a> <a id="1771" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1776" class="Symbol">}</a> <a id="1778" class="Symbol">(</a><a id="1779" href="category-theory.cores-categories.html#1779" class="Bound">C</a> <a id="1781" class="Symbol">:</a> <a id="1783" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1792" href="category-theory.cores-categories.html#1763" class="Bound">l1</a> <a id="1795" href="category-theory.cores-categories.html#1766" class="Bound">l2</a><a id="1797" class="Symbol">)</a> <a id="1799" class="Symbol">→</a> <a id="1801" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1810" href="category-theory.cores-categories.html#1763" class="Bound">l1</a> <a id="1813" href="category-theory.cores-categories.html#1766" class="Bound">l2</a>
<a id="1816" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1820" class="Symbol">(</a><a id="1821" href="category-theory.cores-categories.html#1735" class="Function">core-category-Category</a> <a id="1844" href="category-theory.cores-categories.html#1844" class="Bound">C</a><a id="1845" class="Symbol">)</a> <a id="1847" class="Symbol">=</a> <a id="1849" href="category-theory.cores-categories.html#1526" class="Function">core-precategory-Category</a> <a id="1875" href="category-theory.cores-categories.html#1844" class="Bound">C</a>
<a id="1877" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1881" class="Symbol">(</a><a id="1882" href="category-theory.cores-categories.html#1735" class="Function">core-category-Category</a> <a id="1905" href="category-theory.cores-categories.html#1905" class="Bound">C</a><a id="1906" class="Symbol">)</a> <a id="1908" class="Symbol">=</a>
  <a id="1912" href="category-theory.cores-precategories.html#5193" class="Function">is-category-core-is-category-Precategory</a>
    <a id="1957" class="Symbol">(</a> <a id="1959" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1980" href="category-theory.cores-categories.html#1905" class="Bound">C</a><a id="1981" class="Symbol">)</a>
    <a id="1987" class="Symbol">(</a> <a id="1989" href="category-theory.categories.html#4963" class="Function">is-category-Category</a> <a id="2010" href="category-theory.cores-categories.html#1905" class="Bound">C</a><a id="2011" class="Symbol">)</a>
</pre>
### The core pregroupoid

<pre class="Agda"><a id="2052" class="Keyword">module</a> <a id="2059" href="category-theory.cores-categories.html#2059" class="Module">_</a>
  <a id="2063" class="Symbol">{</a><a id="2064" href="category-theory.cores-categories.html#2064" class="Bound">l1</a> <a id="2067" href="category-theory.cores-categories.html#2067" class="Bound">l2</a> <a id="2070" class="Symbol">:</a> <a id="2072" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2077" class="Symbol">}</a> <a id="2079" class="Symbol">(</a><a id="2080" href="category-theory.cores-categories.html#2080" class="Bound">C</a> <a id="2082" class="Symbol">:</a> <a id="2084" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="2093" href="category-theory.cores-categories.html#2064" class="Bound">l1</a> <a id="2096" href="category-theory.cores-categories.html#2067" class="Bound">l2</a><a id="2098" class="Symbol">)</a>
  <a id="2102" class="Keyword">where</a>

  <a id="2111" href="category-theory.cores-categories.html#2111" class="Function">is-pregroupoid-core-Category</a> <a id="2140" class="Symbol">:</a>
    <a id="2146" href="category-theory.pregroupoids.html#951" class="Function">is-pregroupoid-Precategory</a> <a id="2173" class="Symbol">(</a><a id="2174" href="category-theory.cores-categories.html#1526" class="Function">core-precategory-Category</a> <a id="2200" href="category-theory.cores-categories.html#2080" class="Bound">C</a><a id="2201" class="Symbol">)</a>
  <a id="2205" href="category-theory.cores-categories.html#2111" class="Function">is-pregroupoid-core-Category</a> <a id="2234" class="Symbol">=</a>
    <a id="2240" href="category-theory.cores-precategories.html#2413" class="Function">is-pregroupoid-core-Precategory</a> <a id="2272" class="Symbol">(</a><a id="2273" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2294" href="category-theory.cores-categories.html#2080" class="Bound">C</a><a id="2295" class="Symbol">)</a>

  <a id="2300" href="category-theory.cores-categories.html#2300" class="Function">core-pregroupoid-Category</a> <a id="2326" class="Symbol">:</a> <a id="2328" href="category-theory.pregroupoids.html#1526" class="Function">Pregroupoid</a> <a id="2340" href="category-theory.cores-categories.html#2064" class="Bound">l1</a> <a id="2343" href="category-theory.cores-categories.html#2067" class="Bound">l2</a>
  <a id="2348" href="category-theory.cores-categories.html#2300" class="Function">core-pregroupoid-Category</a> <a id="2374" class="Symbol">=</a>
    <a id="2380" href="category-theory.cores-precategories.html#3075" class="Function">core-pregroupoid-Precategory</a> <a id="2409" class="Symbol">(</a><a id="2410" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="2431" href="category-theory.cores-categories.html#2080" class="Bound">C</a><a id="2432" class="Symbol">)</a>
</pre>
### The core groupoid

<pre class="Agda"><a id="2470" class="Keyword">module</a> <a id="2477" href="category-theory.cores-categories.html#2477" class="Module">_</a>
  <a id="2481" class="Symbol">{</a><a id="2482" href="category-theory.cores-categories.html#2482" class="Bound">l1</a> <a id="2485" href="category-theory.cores-categories.html#2485" class="Bound">l2</a> <a id="2488" class="Symbol">:</a> <a id="2490" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2495" class="Symbol">}</a> <a id="2497" class="Symbol">(</a><a id="2498" href="category-theory.cores-categories.html#2498" class="Bound">C</a> <a id="2500" class="Symbol">:</a> <a id="2502" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="2511" href="category-theory.cores-categories.html#2482" class="Bound">l1</a> <a id="2514" href="category-theory.cores-categories.html#2485" class="Bound">l2</a><a id="2516" class="Symbol">)</a>
  <a id="2520" class="Keyword">where</a>

  <a id="2529" href="category-theory.cores-categories.html#2529" class="Function">is-groupoid-core-Category</a> <a id="2555" class="Symbol">:</a> <a id="2557" href="category-theory.groupoids.html#1442" class="Function">is-groupoid-Category</a> <a id="2578" class="Symbol">(</a><a id="2579" href="category-theory.cores-categories.html#1735" class="Function">core-category-Category</a> <a id="2602" href="category-theory.cores-categories.html#2498" class="Bound">C</a><a id="2603" class="Symbol">)</a>
  <a id="2607" href="category-theory.cores-categories.html#2529" class="Function">is-groupoid-core-Category</a> <a id="2633" class="Symbol">=</a> <a id="2635" href="category-theory.cores-categories.html#2111" class="Function">is-pregroupoid-core-Category</a> <a id="2664" href="category-theory.cores-categories.html#2498" class="Bound">C</a>

  <a id="2669" href="category-theory.cores-categories.html#2669" class="Function">core-groupoid-Category</a> <a id="2692" class="Symbol">:</a> <a id="2694" href="category-theory.groupoids.html#1599" class="Function">Groupoid</a> <a id="2703" href="category-theory.cores-categories.html#2482" class="Bound">l1</a> <a id="2706" href="category-theory.cores-categories.html#2485" class="Bound">l2</a>
  <a id="2711" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2715" href="category-theory.cores-categories.html#2669" class="Function">core-groupoid-Category</a> <a id="2738" class="Symbol">=</a> <a id="2740" href="category-theory.cores-categories.html#1735" class="Function">core-category-Category</a> <a id="2763" href="category-theory.cores-categories.html#2498" class="Bound">C</a>
  <a id="2767" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2771" href="category-theory.cores-categories.html#2669" class="Function">core-groupoid-Category</a> <a id="2794" class="Symbol">=</a> <a id="2796" href="category-theory.cores-categories.html#2529" class="Function">is-groupoid-core-Category</a>
</pre>
## Properties

### Computing isomorphisms in the core

<pre class="Agda"><a id="2890" class="Keyword">module</a> <a id="2897" href="category-theory.cores-categories.html#2897" class="Module">_</a>
  <a id="2901" class="Symbol">{</a><a id="2902" href="category-theory.cores-categories.html#2902" class="Bound">l1</a> <a id="2905" href="category-theory.cores-categories.html#2905" class="Bound">l2</a> <a id="2908" class="Symbol">:</a> <a id="2910" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2915" class="Symbol">}</a> <a id="2917" class="Symbol">(</a><a id="2918" href="category-theory.cores-categories.html#2918" class="Bound">C</a> <a id="2920" class="Symbol">:</a> <a id="2922" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="2931" href="category-theory.cores-categories.html#2902" class="Bound">l1</a> <a id="2934" href="category-theory.cores-categories.html#2905" class="Bound">l2</a><a id="2936" class="Symbol">)</a> <a id="2938" class="Symbol">{</a><a id="2939" href="category-theory.cores-categories.html#2939" class="Bound">x</a> <a id="2941" href="category-theory.cores-categories.html#2941" class="Bound">y</a> <a id="2943" class="Symbol">:</a> <a id="2945" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="2958" href="category-theory.cores-categories.html#2918" class="Bound">C</a><a id="2959" class="Symbol">}</a>
  <a id="2963" class="Keyword">where</a>

  <a id="2972" href="category-theory.cores-categories.html#2972" class="Function">compute-iso-core-Category</a> <a id="2998" class="Symbol">:</a>
    <a id="3004" href="category-theory.isomorphisms-in-categories.html#2140" class="Function">iso-Category</a> <a id="3017" href="category-theory.cores-categories.html#2918" class="Bound">C</a> <a id="3019" href="category-theory.cores-categories.html#2939" class="Bound">x</a> <a id="3021" href="category-theory.cores-categories.html#2941" class="Bound">y</a> <a id="3023" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="3025" href="category-theory.isomorphisms-in-categories.html#2140" class="Function">iso-Category</a> <a id="3038" class="Symbol">(</a><a id="3039" href="category-theory.cores-categories.html#1735" class="Function">core-category-Category</a> <a id="3062" href="category-theory.cores-categories.html#2918" class="Bound">C</a><a id="3063" class="Symbol">)</a> <a id="3065" href="category-theory.cores-categories.html#2939" class="Bound">x</a> <a id="3067" href="category-theory.cores-categories.html#2941" class="Bound">y</a>
  <a id="3071" href="category-theory.cores-categories.html#2972" class="Function">compute-iso-core-Category</a> <a id="3097" class="Symbol">=</a>
    <a id="3103" href="category-theory.cores-precategories.html#3417" class="Function">compute-iso-core-Precategory</a> <a id="3132" class="Symbol">(</a><a id="3133" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3154" href="category-theory.cores-categories.html#2918" class="Bound">C</a><a id="3155" class="Symbol">)</a>

  <a id="3160" href="category-theory.cores-categories.html#3160" class="Function">inv-compute-iso-core-Category</a> <a id="3190" class="Symbol">:</a>
    <a id="3196" href="category-theory.isomorphisms-in-categories.html#2140" class="Function">iso-Category</a> <a id="3209" class="Symbol">(</a><a id="3210" href="category-theory.cores-categories.html#1735" class="Function">core-category-Category</a> <a id="3233" href="category-theory.cores-categories.html#2918" class="Bound">C</a><a id="3234" class="Symbol">)</a> <a id="3236" href="category-theory.cores-categories.html#2939" class="Bound">x</a> <a id="3238" href="category-theory.cores-categories.html#2941" class="Bound">y</a> <a id="3240" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="3242" href="category-theory.isomorphisms-in-categories.html#2140" class="Function">iso-Category</a> <a id="3255" href="category-theory.cores-categories.html#2918" class="Bound">C</a> <a id="3257" href="category-theory.cores-categories.html#2939" class="Bound">x</a> <a id="3259" href="category-theory.cores-categories.html#2941" class="Bound">y</a>
  <a id="3263" href="category-theory.cores-categories.html#3160" class="Function">inv-compute-iso-core-Category</a> <a id="3293" class="Symbol">=</a>
    <a id="3299" href="category-theory.cores-precategories.html#3626" class="Function">inv-compute-iso-core-Precategory</a> <a id="3332" class="Symbol">(</a><a id="3333" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="3354" href="category-theory.cores-categories.html#2918" class="Bound">C</a><a id="3355" class="Symbol">)</a>
</pre>
## See also

- [Cores of monoids](group-theory.cores-monoids.md)
- [Restrictions of functors to cores of precategories](category-theory.restrictions-functors-cores-precategories.md)

## External links

- [The core of a category](https://1lab.dev/Cat.Instances.Core.html) at 1lab
- [core groupoid](https://ncatlab.org/nlab/show/core+groupoid) at $n$Lab
