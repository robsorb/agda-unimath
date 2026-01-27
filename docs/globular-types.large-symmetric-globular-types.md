# Large symmetric globular types

<pre class="Agda"><a id="43" class="Symbol">{-#</a> <a id="47" class="Keyword">OPTIONS</a> <a id="55" class="Pragma">--guardedness</a> <a id="69" class="Symbol">#-}</a>

<a id="74" class="Keyword">module</a> <a id="81" href="globular-types.large-symmetric-globular-types.html" class="Module">globular-types.large-symmetric-globular-types</a> <a id="127" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.large-binary-relations.html" class="Module">foundation.large-binary-relations</a>
<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="269" class="Keyword">open</a> <a id="274" class="Keyword">import</a> <a id="281" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="globular-types.large-globular-types.html" class="Module">globular-types.large-globular-types</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="globular-types.symmetric-globular-types.html" class="Module">globular-types.symmetric-globular-types</a>
</pre>
</details>

## Idea

We say that a [large globular type](globular-types.large-globular-types.md) is
{{#concept "symmetric" Disambiguation="large globular type" Agda=is-symmetric-Large-Globular-Type}}
if there is a symmetry action on its $n$-cells for positive $n$, mapping
$n$-cells from `x` to `y` to $n$-cells from `y` to `x`.

## Definitions

### Symmetry structure on a large globular type

<pre class="Agda"><a id="819" class="Keyword">record</a>
  <a id="is-symmetric-Large-Globular-Type"></a><a id="828" href="globular-types.large-symmetric-globular-types.html#828" class="Record">is-symmetric-Large-Globular-Type</a>
    <a id="865" class="Symbol">{</a><a id="866" href="globular-types.large-symmetric-globular-types.html#866" class="Bound">α</a> <a id="868" class="Symbol">:</a> <a id="870" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="876" class="Symbol">→</a> <a id="878" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="883" class="Symbol">}</a> <a id="885" class="Symbol">{</a><a id="886" href="globular-types.large-symmetric-globular-types.html#886" class="Bound">β</a> <a id="888" class="Symbol">:</a> <a id="890" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="896" class="Symbol">→</a> <a id="898" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="904" class="Symbol">→</a> <a id="906" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="911" class="Symbol">}</a>
    <a id="917" class="Symbol">(</a><a id="918" href="globular-types.large-symmetric-globular-types.html#918" class="Bound">G</a> <a id="920" class="Symbol">:</a> <a id="922" href="globular-types.large-globular-types.html#4432" class="Record">Large-Globular-Type</a> <a id="942" href="globular-types.large-symmetric-globular-types.html#866" class="Bound">α</a> <a id="944" href="globular-types.large-symmetric-globular-types.html#886" class="Bound">β</a><a id="945" class="Symbol">)</a> <a id="947" class="Symbol">:</a>
    <a id="953" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="959" class="Keyword">where</a>

  <a id="968" class="Keyword">field</a>
    <a id="is-symmetric-Large-Globular-Type.inv-1-cell-is-symmetric-Large-Globular-Type"></a><a id="978" href="globular-types.large-symmetric-globular-types.html#978" class="Field">inv-1-cell-is-symmetric-Large-Globular-Type</a> <a id="1022" class="Symbol">:</a>
      <a id="1030" href="foundation.large-binary-relations.html#3354" class="Function">is-symmetric-Large-Relation</a>
        <a id="1066" class="Symbol">(</a> <a id="1068" href="globular-types.large-globular-types.html#4526" class="Field">0-cell-Large-Globular-Type</a> <a id="1095" href="globular-types.large-symmetric-globular-types.html#918" class="Bound">G</a><a id="1096" class="Symbol">)</a>
        <a id="1106" class="Symbol">(</a> <a id="1108" href="globular-types.large-globular-types.html#5322" class="Function">1-cell-Large-Globular-Type</a> <a id="1135" href="globular-types.large-symmetric-globular-types.html#918" class="Bound">G</a><a id="1136" class="Symbol">)</a>

  <a id="1141" class="Keyword">field</a>
    <a id="is-symmetric-Large-Globular-Type.is-symmetric-1-cell-globular-type-is-symmetric-Large-Globular-Type"></a><a id="1151" href="globular-types.large-symmetric-globular-types.html#1151" class="Field">is-symmetric-1-cell-globular-type-is-symmetric-Large-Globular-Type</a> <a id="1218" class="Symbol">:</a>
      <a id="1226" class="Symbol">{</a><a id="1227" href="globular-types.large-symmetric-globular-types.html#1227" class="Bound">l1</a> <a id="1230" href="globular-types.large-symmetric-globular-types.html#1230" class="Bound">l2</a> <a id="1233" class="Symbol">:</a> <a id="1235" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1240" class="Symbol">}</a>
      <a id="1248" class="Symbol">(</a><a id="1249" href="globular-types.large-symmetric-globular-types.html#1249" class="Bound">x</a> <a id="1251" class="Symbol">:</a> <a id="1253" href="globular-types.large-globular-types.html#4526" class="Field">0-cell-Large-Globular-Type</a> <a id="1280" href="globular-types.large-symmetric-globular-types.html#918" class="Bound">G</a> <a id="1282" href="globular-types.large-symmetric-globular-types.html#1227" class="Bound">l1</a><a id="1284" class="Symbol">)</a> <a id="1286" class="Symbol">→</a>
      <a id="1294" class="Symbol">(</a><a id="1295" href="globular-types.large-symmetric-globular-types.html#1295" class="Bound">y</a> <a id="1297" class="Symbol">:</a> <a id="1299" href="globular-types.large-globular-types.html#4526" class="Field">0-cell-Large-Globular-Type</a> <a id="1326" href="globular-types.large-symmetric-globular-types.html#918" class="Bound">G</a> <a id="1328" href="globular-types.large-symmetric-globular-types.html#1230" class="Bound">l2</a><a id="1330" class="Symbol">)</a> <a id="1332" class="Symbol">→</a>
      <a id="1340" href="globular-types.symmetric-globular-types.html#756" class="Record">is-symmetric-Globular-Type</a>
        <a id="1375" class="Symbol">(</a> <a id="1377" href="globular-types.large-globular-types.html#4588" class="Field">1-cell-globular-type-Large-Globular-Type</a> <a id="1418" href="globular-types.large-symmetric-globular-types.html#918" class="Bound">G</a> <a id="1420" href="globular-types.large-symmetric-globular-types.html#1249" class="Bound">x</a> <a id="1422" href="globular-types.large-symmetric-globular-types.html#1295" class="Bound">y</a><a id="1423" class="Symbol">)</a>

<a id="1426" class="Keyword">open</a> <a id="1431" href="globular-types.large-symmetric-globular-types.html#828" class="Module">is-symmetric-Large-Globular-Type</a> <a id="1464" class="Keyword">public</a>
</pre>
### Large symmetric globular types

<pre class="Agda"><a id="1520" class="Keyword">record</a>
  <a id="Large-Symmetric-Globular-Type"></a><a id="1529" href="globular-types.large-symmetric-globular-types.html#1529" class="Record">Large-Symmetric-Globular-Type</a>
    <a id="1563" class="Symbol">(</a><a id="1564" href="globular-types.large-symmetric-globular-types.html#1564" class="Bound">α</a> <a id="1566" class="Symbol">:</a> <a id="1568" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1574" class="Symbol">→</a> <a id="1576" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1581" class="Symbol">)</a> <a id="1583" class="Symbol">(</a><a id="1584" href="globular-types.large-symmetric-globular-types.html#1584" class="Bound">β</a> <a id="1586" class="Symbol">:</a> <a id="1588" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1594" class="Symbol">→</a> <a id="1596" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1602" class="Symbol">→</a> <a id="1604" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1609" class="Symbol">)</a> <a id="1611" class="Symbol">:</a>
    <a id="1617" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1623" class="Keyword">where</a>

  <a id="1632" class="Keyword">field</a>
    <a id="Large-Symmetric-Globular-Type.large-globular-type-Large-Symmetric-Globular-Type"></a><a id="1642" href="globular-types.large-symmetric-globular-types.html#1642" class="Field">large-globular-type-Large-Symmetric-Globular-Type</a> <a id="1692" class="Symbol">:</a>
      <a id="1700" href="globular-types.large-globular-types.html#4432" class="Record">Large-Globular-Type</a> <a id="1720" href="globular-types.large-symmetric-globular-types.html#1564" class="Bound">α</a> <a id="1722" href="globular-types.large-symmetric-globular-types.html#1584" class="Bound">β</a>

  <a id="Large-Symmetric-Globular-Type.0-cell-Large-Symmetric-Globular-Type"></a><a id="1727" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="1764" class="Symbol">:</a>
    <a id="1770" class="Symbol">(</a><a id="1771" href="globular-types.large-symmetric-globular-types.html#1771" class="Bound">l1</a> <a id="1774" class="Symbol">:</a> <a id="1776" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1781" class="Symbol">)</a> <a id="1783" class="Symbol">→</a> <a id="1785" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1788" class="Symbol">(</a><a id="1789" href="globular-types.large-symmetric-globular-types.html#1564" class="Bound">α</a> <a id="1791" href="globular-types.large-symmetric-globular-types.html#1771" class="Bound">l1</a><a id="1793" class="Symbol">)</a>
  <a id="1797" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="1834" class="Symbol">=</a>
    <a id="1840" href="globular-types.large-globular-types.html#4526" class="Field">0-cell-Large-Globular-Type</a> <a id="1867" href="globular-types.large-symmetric-globular-types.html#1642" class="Field">large-globular-type-Large-Symmetric-Globular-Type</a>

  <a id="Large-Symmetric-Globular-Type.1-cell-globular-type-Large-Symmetric-Globular-Type"></a><a id="1920" href="globular-types.large-symmetric-globular-types.html#1920" class="Function">1-cell-globular-type-Large-Symmetric-Globular-Type</a> <a id="1971" class="Symbol">:</a>
    <a id="1977" class="Symbol">{</a><a id="1978" href="globular-types.large-symmetric-globular-types.html#1978" class="Bound">l1</a> <a id="1981" href="globular-types.large-symmetric-globular-types.html#1981" class="Bound">l2</a> <a id="1984" class="Symbol">:</a> <a id="1986" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1991" class="Symbol">}</a>
    <a id="1997" class="Symbol">(</a><a id="1998" href="globular-types.large-symmetric-globular-types.html#1998" class="Bound">x</a> <a id="2000" class="Symbol">:</a> <a id="2002" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="2039" href="globular-types.large-symmetric-globular-types.html#1978" class="Bound">l1</a><a id="2041" class="Symbol">)</a>
    <a id="2047" class="Symbol">(</a><a id="2048" href="globular-types.large-symmetric-globular-types.html#2048" class="Bound">y</a> <a id="2050" class="Symbol">:</a> <a id="2052" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="2089" href="globular-types.large-symmetric-globular-types.html#1981" class="Bound">l2</a><a id="2091" class="Symbol">)</a> <a id="2093" class="Symbol">→</a>
    <a id="2099" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="2113" class="Symbol">(</a><a id="2114" href="globular-types.large-symmetric-globular-types.html#1584" class="Bound">β</a> <a id="2116" href="globular-types.large-symmetric-globular-types.html#1978" class="Bound">l1</a> <a id="2119" href="globular-types.large-symmetric-globular-types.html#1981" class="Bound">l2</a><a id="2121" class="Symbol">)</a> <a id="2123" class="Symbol">(</a><a id="2124" href="globular-types.large-symmetric-globular-types.html#1584" class="Bound">β</a> <a id="2126" href="globular-types.large-symmetric-globular-types.html#1978" class="Bound">l1</a> <a id="2129" href="globular-types.large-symmetric-globular-types.html#1981" class="Bound">l2</a><a id="2131" class="Symbol">)</a>
  <a id="2135" href="globular-types.large-symmetric-globular-types.html#1920" class="Function">1-cell-globular-type-Large-Symmetric-Globular-Type</a> <a id="2186" class="Symbol">=</a>
    <a id="2192" href="globular-types.large-globular-types.html#4588" class="Field">1-cell-globular-type-Large-Globular-Type</a>
      <a id="2239" href="globular-types.large-symmetric-globular-types.html#1642" class="Field">large-globular-type-Large-Symmetric-Globular-Type</a>

  <a id="Large-Symmetric-Globular-Type.1-cell-Large-Symmetric-Globular-Type"></a><a id="2292" href="globular-types.large-symmetric-globular-types.html#2292" class="Function">1-cell-Large-Symmetric-Globular-Type</a> <a id="2329" class="Symbol">:</a>
    <a id="2335" class="Symbol">{</a><a id="2336" href="globular-types.large-symmetric-globular-types.html#2336" class="Bound">l1</a> <a id="2339" href="globular-types.large-symmetric-globular-types.html#2339" class="Bound">l2</a> <a id="2342" class="Symbol">:</a> <a id="2344" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2349" class="Symbol">}</a>
    <a id="2355" class="Symbol">(</a><a id="2356" href="globular-types.large-symmetric-globular-types.html#2356" class="Bound">x</a> <a id="2358" class="Symbol">:</a> <a id="2360" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="2397" href="globular-types.large-symmetric-globular-types.html#2336" class="Bound">l1</a><a id="2399" class="Symbol">)</a>
    <a id="2405" class="Symbol">(</a><a id="2406" href="globular-types.large-symmetric-globular-types.html#2406" class="Bound">y</a> <a id="2408" class="Symbol">:</a> <a id="2410" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="2447" href="globular-types.large-symmetric-globular-types.html#2339" class="Bound">l2</a><a id="2449" class="Symbol">)</a> <a id="2451" class="Symbol">→</a>
    <a id="2457" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2460" class="Symbol">(</a><a id="2461" href="globular-types.large-symmetric-globular-types.html#1584" class="Bound">β</a> <a id="2463" href="globular-types.large-symmetric-globular-types.html#2336" class="Bound">l1</a> <a id="2466" href="globular-types.large-symmetric-globular-types.html#2339" class="Bound">l2</a><a id="2468" class="Symbol">)</a>
  <a id="2472" href="globular-types.large-symmetric-globular-types.html#2292" class="Function">1-cell-Large-Symmetric-Globular-Type</a> <a id="2509" class="Symbol">=</a>
    <a id="2515" href="globular-types.large-globular-types.html#5322" class="Function">1-cell-Large-Globular-Type</a> <a id="2542" href="globular-types.large-symmetric-globular-types.html#1642" class="Field">large-globular-type-Large-Symmetric-Globular-Type</a>

  <a id="2595" class="Keyword">field</a>
    <a id="Large-Symmetric-Globular-Type.is-symmetric-Large-Symmetric-Globular-Type"></a><a id="2605" href="globular-types.large-symmetric-globular-types.html#2605" class="Field">is-symmetric-Large-Symmetric-Globular-Type</a> <a id="2648" class="Symbol">:</a>
      <a id="2656" href="globular-types.large-symmetric-globular-types.html#828" class="Record">is-symmetric-Large-Globular-Type</a>
        <a id="2697" href="globular-types.large-symmetric-globular-types.html#1642" class="Field">large-globular-type-Large-Symmetric-Globular-Type</a>

  <a id="Large-Symmetric-Globular-Type.inv-1-cell-Large-Symmetric-Globular-Type"></a><a id="2750" href="globular-types.large-symmetric-globular-types.html#2750" class="Function">inv-1-cell-Large-Symmetric-Globular-Type</a> <a id="2791" class="Symbol">:</a>
    <a id="2797" class="Symbol">{</a><a id="2798" href="globular-types.large-symmetric-globular-types.html#2798" class="Bound">l1</a> <a id="2801" href="globular-types.large-symmetric-globular-types.html#2801" class="Bound">l2</a> <a id="2804" class="Symbol">:</a> <a id="2806" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2811" class="Symbol">}</a>
    <a id="2817" class="Symbol">{</a><a id="2818" href="globular-types.large-symmetric-globular-types.html#2818" class="Bound">x</a> <a id="2820" class="Symbol">:</a> <a id="2822" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="2859" href="globular-types.large-symmetric-globular-types.html#2798" class="Bound">l1</a><a id="2861" class="Symbol">}</a>
    <a id="2867" class="Symbol">{</a><a id="2868" href="globular-types.large-symmetric-globular-types.html#2868" class="Bound">y</a> <a id="2870" class="Symbol">:</a> <a id="2872" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="2909" href="globular-types.large-symmetric-globular-types.html#2801" class="Bound">l2</a><a id="2911" class="Symbol">}</a> <a id="2913" class="Symbol">→</a>
    <a id="2919" href="globular-types.large-symmetric-globular-types.html#2292" class="Function">1-cell-Large-Symmetric-Globular-Type</a> <a id="2956" href="globular-types.large-symmetric-globular-types.html#2818" class="Bound">x</a> <a id="2958" href="globular-types.large-symmetric-globular-types.html#2868" class="Bound">y</a> <a id="2960" class="Symbol">→</a>
    <a id="2966" href="globular-types.large-symmetric-globular-types.html#2292" class="Function">1-cell-Large-Symmetric-Globular-Type</a> <a id="3003" href="globular-types.large-symmetric-globular-types.html#2868" class="Bound">y</a> <a id="3005" href="globular-types.large-symmetric-globular-types.html#2818" class="Bound">x</a>
  <a id="3009" href="globular-types.large-symmetric-globular-types.html#2750" class="Function">inv-1-cell-Large-Symmetric-Globular-Type</a> <a id="3050" class="Symbol">=</a>
    <a id="3056" href="globular-types.large-symmetric-globular-types.html#978" class="Field">inv-1-cell-is-symmetric-Large-Globular-Type</a>
      <a id="3106" href="globular-types.large-symmetric-globular-types.html#2605" class="Field">is-symmetric-Large-Symmetric-Globular-Type</a>
      <a id="3155" class="Symbol">_</a>
      <a id="3163" class="Symbol">_</a>

  <a id="Large-Symmetric-Globular-Type.is-symmetric-1-cell-globular-type-Large-Symmetric-Globular-Type"></a><a id="3168" href="globular-types.large-symmetric-globular-types.html#3168" class="Function">is-symmetric-1-cell-globular-type-Large-Symmetric-Globular-Type</a> <a id="3232" class="Symbol">:</a>
    <a id="3238" class="Symbol">{</a><a id="3239" href="globular-types.large-symmetric-globular-types.html#3239" class="Bound">l1</a> <a id="3242" href="globular-types.large-symmetric-globular-types.html#3242" class="Bound">l2</a> <a id="3245" class="Symbol">:</a> <a id="3247" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3252" class="Symbol">}</a>
    <a id="3258" class="Symbol">(</a><a id="3259" href="globular-types.large-symmetric-globular-types.html#3259" class="Bound">x</a> <a id="3261" class="Symbol">:</a> <a id="3263" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="3300" href="globular-types.large-symmetric-globular-types.html#3239" class="Bound">l1</a><a id="3302" class="Symbol">)</a>
    <a id="3308" class="Symbol">(</a><a id="3309" href="globular-types.large-symmetric-globular-types.html#3309" class="Bound">y</a> <a id="3311" class="Symbol">:</a> <a id="3313" href="globular-types.large-symmetric-globular-types.html#1727" class="Function">0-cell-Large-Symmetric-Globular-Type</a> <a id="3350" href="globular-types.large-symmetric-globular-types.html#3242" class="Bound">l2</a><a id="3352" class="Symbol">)</a> <a id="3354" class="Symbol">→</a>
    <a id="3360" href="globular-types.symmetric-globular-types.html#756" class="Record">is-symmetric-Globular-Type</a>
      <a id="3393" class="Symbol">(</a> <a id="3395" href="globular-types.large-symmetric-globular-types.html#1920" class="Function">1-cell-globular-type-Large-Symmetric-Globular-Type</a> <a id="3446" href="globular-types.large-symmetric-globular-types.html#3259" class="Bound">x</a> <a id="3448" href="globular-types.large-symmetric-globular-types.html#3309" class="Bound">y</a><a id="3449" class="Symbol">)</a>
  <a id="3453" href="globular-types.large-symmetric-globular-types.html#3168" class="Function">is-symmetric-1-cell-globular-type-Large-Symmetric-Globular-Type</a> <a id="3517" class="Symbol">=</a>
    <a id="3523" href="globular-types.large-symmetric-globular-types.html#1151" class="Field">is-symmetric-1-cell-globular-type-is-symmetric-Large-Globular-Type</a>
      <a id="3596" href="globular-types.large-symmetric-globular-types.html#2605" class="Field">is-symmetric-Large-Symmetric-Globular-Type</a>

<a id="3640" class="Keyword">open</a> <a id="3645" href="globular-types.large-symmetric-globular-types.html#1529" class="Module">Large-Symmetric-Globular-Type</a> <a id="3675" class="Keyword">public</a>
</pre>