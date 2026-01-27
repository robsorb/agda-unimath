# Wild representations of monoids

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="group-theory.wild-representations-monoids.html" class="Module">group-theory.wild-representations-monoids</a> <a id="93" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="foundation.endomorphisms.html" class="Module">foundation.endomorphisms</a>
<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="306" class="Keyword">open</a> <a id="311" class="Keyword">import</a> <a id="318" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="346" class="Keyword">open</a> <a id="351" class="Keyword">import</a> <a id="358" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>

<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="structured-types.morphisms-wild-monoids.html" class="Module">structured-types.morphisms-wild-monoids</a>
</pre>
</details>

## Idea

A coherent action of a [monoid](group-theory.monoids.md) `M` on a type `X`
requires an infinite hierarchy of explicit coherences. Instead, as a first order
approximation, we can consider **wild representations** of `M` on `X`,
consisting of a
[wild monoid homomorphism](structured-types.morphisms-wild-monoids.md) from `M`
to the [wild monoid](structured-types.wild-monoids.md) of
[endomorphisms](foundation.endomorphisms.md) on `X`.

## Definition

### Wild representations of a monoid in a type

<pre class="Agda"><a id="wild-representation-type-Monoid"></a><a id="964" href="group-theory.wild-representations-monoids.html#964" class="Function">wild-representation-type-Monoid</a> <a id="996" class="Symbol">:</a>
  <a id="1000" class="Symbol">(</a><a id="1001" href="group-theory.wild-representations-monoids.html#1001" class="Bound">l1</a> <a id="1004" class="Symbol">:</a> <a id="1006" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1011" class="Symbol">)</a> <a id="1013" class="Symbol">{</a><a id="1014" href="group-theory.wild-representations-monoids.html#1014" class="Bound">l2</a> <a id="1017" class="Symbol">:</a> <a id="1019" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1024" class="Symbol">}</a> <a id="1026" class="Symbol">(</a><a id="1027" href="group-theory.wild-representations-monoids.html#1027" class="Bound">M</a> <a id="1029" class="Symbol">:</a> <a id="1031" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="1038" href="group-theory.wild-representations-monoids.html#1014" class="Bound">l2</a><a id="1040" class="Symbol">)</a> <a id="1042" class="Symbol">→</a> <a id="1044" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1047" class="Symbol">(</a><a id="1048" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1053" href="group-theory.wild-representations-monoids.html#1001" class="Bound">l1</a> <a id="1056" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1058" href="group-theory.wild-representations-monoids.html#1014" class="Bound">l2</a><a id="1060" class="Symbol">)</a>
<a id="1062" href="group-theory.wild-representations-monoids.html#964" class="Function">wild-representation-type-Monoid</a> <a id="1094" href="group-theory.wild-representations-monoids.html#1094" class="Bound">l1</a> <a id="1097" href="group-theory.wild-representations-monoids.html#1097" class="Bound">M</a> <a id="1099" class="Symbol">=</a>
  <a id="1103" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1105" class="Symbol">(</a> <a id="1107" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1110" href="group-theory.wild-representations-monoids.html#1094" class="Bound">l1</a><a id="1112" class="Symbol">)</a>
    <a id="1118" class="Symbol">(</a> <a id="1120" class="Symbol">λ</a> <a id="1122" href="group-theory.wild-representations-monoids.html#1122" class="Bound">X</a> <a id="1124" class="Symbol">→</a> <a id="1126" href="structured-types.morphisms-wild-monoids.html#932" class="Function">hom-Wild-Monoid</a> <a id="1142" class="Symbol">(</a><a id="1143" href="group-theory.monoids.html#4714" class="Function">wild-monoid-Monoid</a> <a id="1162" href="group-theory.wild-representations-monoids.html#1097" class="Bound">M</a><a id="1163" class="Symbol">)</a> <a id="1165" class="Symbol">(</a><a id="1166" href="foundation.endomorphisms.html#648" class="Function">endo-Wild-Monoid</a> <a id="1183" href="group-theory.wild-representations-monoids.html#1122" class="Bound">X</a><a id="1184" class="Symbol">))</a>

<a id="1188" class="Keyword">module</a> <a id="1195" href="group-theory.wild-representations-monoids.html#1195" class="Module">_</a>
  <a id="1199" class="Symbol">{</a><a id="1200" href="group-theory.wild-representations-monoids.html#1200" class="Bound">l1</a> <a id="1203" href="group-theory.wild-representations-monoids.html#1203" class="Bound">l2</a> <a id="1206" class="Symbol">:</a> <a id="1208" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1213" class="Symbol">}</a> <a id="1215" class="Symbol">(</a><a id="1216" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a> <a id="1218" class="Symbol">:</a> <a id="1220" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="1227" href="group-theory.wild-representations-monoids.html#1200" class="Bound">l1</a><a id="1229" class="Symbol">)</a>
  <a id="1233" class="Symbol">(</a><a id="1234" href="group-theory.wild-representations-monoids.html#1234" class="Bound">ρ</a> <a id="1236" class="Symbol">:</a> <a id="1238" href="group-theory.wild-representations-monoids.html#964" class="Function">wild-representation-type-Monoid</a> <a id="1270" href="group-theory.wild-representations-monoids.html#1203" class="Bound">l2</a> <a id="1273" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a><a id="1274" class="Symbol">)</a>
  <a id="1278" class="Keyword">where</a>

  <a id="1287" href="group-theory.wild-representations-monoids.html#1287" class="Function">type-wild-representation-type-Monoid</a> <a id="1324" class="Symbol">:</a> <a id="1326" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1329" href="group-theory.wild-representations-monoids.html#1203" class="Bound">l2</a>
  <a id="1334" href="group-theory.wild-representations-monoids.html#1287" class="Function">type-wild-representation-type-Monoid</a> <a id="1371" class="Symbol">=</a> <a id="1373" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1377" href="group-theory.wild-representations-monoids.html#1234" class="Bound">ρ</a>

  <a id="1382" href="group-theory.wild-representations-monoids.html#1382" class="Function">hom-action-wild-representation-type-Monoid</a> <a id="1425" class="Symbol">:</a>
    <a id="1431" href="structured-types.morphisms-wild-monoids.html#932" class="Function">hom-Wild-Monoid</a>
      <a id="1453" class="Symbol">(</a> <a id="1455" href="group-theory.monoids.html#4714" class="Function">wild-monoid-Monoid</a> <a id="1474" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a><a id="1475" class="Symbol">)</a>
      <a id="1483" class="Symbol">(</a> <a id="1485" href="foundation.endomorphisms.html#648" class="Function">endo-Wild-Monoid</a> <a id="1502" href="group-theory.wild-representations-monoids.html#1287" class="Function">type-wild-representation-type-Monoid</a><a id="1538" class="Symbol">)</a>
  <a id="1542" href="group-theory.wild-representations-monoids.html#1382" class="Function">hom-action-wild-representation-type-Monoid</a> <a id="1585" class="Symbol">=</a> <a id="1587" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1591" href="group-theory.wild-representations-monoids.html#1234" class="Bound">ρ</a>

  <a id="1596" href="group-theory.wild-representations-monoids.html#1596" class="Function">action-wild-representation-type-Monoid</a> <a id="1635" class="Symbol">:</a>
    <a id="1641" href="group-theory.monoids.html#1116" class="Function">type-Monoid</a> <a id="1653" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a> <a id="1655" class="Symbol">→</a> <a id="1657" href="foundation-core.endomorphisms.html#506" class="Function">endo</a> <a id="1662" href="group-theory.wild-representations-monoids.html#1287" class="Function">type-wild-representation-type-Monoid</a>
  <a id="1701" href="group-theory.wild-representations-monoids.html#1596" class="Function">action-wild-representation-type-Monoid</a> <a id="1740" class="Symbol">=</a>
    <a id="1746" href="structured-types.morphisms-wild-monoids.html#1220" class="Function">map-hom-Wild-Monoid</a>
      <a id="1772" class="Symbol">(</a> <a id="1774" href="group-theory.monoids.html#4714" class="Function">wild-monoid-Monoid</a> <a id="1793" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a><a id="1794" class="Symbol">)</a>
      <a id="1802" class="Symbol">(</a> <a id="1804" href="foundation.endomorphisms.html#648" class="Function">endo-Wild-Monoid</a> <a id="1821" href="group-theory.wild-representations-monoids.html#1287" class="Function">type-wild-representation-type-Monoid</a><a id="1857" class="Symbol">)</a>
      <a id="1865" class="Symbol">(</a> <a id="1867" href="group-theory.wild-representations-monoids.html#1382" class="Function">hom-action-wild-representation-type-Monoid</a><a id="1909" class="Symbol">)</a>

  <a id="1914" href="group-theory.wild-representations-monoids.html#1914" class="Function">preserves-mul-action-wild-representation-type-Monoid</a> <a id="1967" class="Symbol">:</a>
    <a id="1973" class="Symbol">{</a> <a id="1975" href="group-theory.wild-representations-monoids.html#1975" class="Bound">x</a> <a id="1977" href="group-theory.wild-representations-monoids.html#1977" class="Bound">y</a> <a id="1979" class="Symbol">:</a> <a id="1981" href="group-theory.monoids.html#1116" class="Function">type-Monoid</a> <a id="1993" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a><a id="1994" class="Symbol">}</a> <a id="1996" class="Symbol">→</a>
    <a id="2002" class="Symbol">(</a> <a id="2004" href="group-theory.wild-representations-monoids.html#1596" class="Function">action-wild-representation-type-Monoid</a> <a id="2043" class="Symbol">(</a><a id="2044" href="group-theory.monoids.html#1359" class="Function">mul-Monoid</a> <a id="2055" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a> <a id="2057" href="group-theory.wild-representations-monoids.html#1975" class="Bound">x</a> <a id="2059" href="group-theory.wild-representations-monoids.html#1977" class="Bound">y</a><a id="2060" class="Symbol">))</a> <a id="2063" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2069" class="Symbol">(</a> <a id="2071" class="Symbol">(</a> <a id="2073" href="group-theory.wild-representations-monoids.html#1596" class="Function">action-wild-representation-type-Monoid</a> <a id="2112" href="group-theory.wild-representations-monoids.html#1975" class="Bound">x</a><a id="2113" class="Symbol">)</a> <a id="2115" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
      <a id="2123" class="Symbol">(</a> <a id="2125" href="group-theory.wild-representations-monoids.html#1596" class="Function">action-wild-representation-type-Monoid</a> <a id="2164" href="group-theory.wild-representations-monoids.html#1977" class="Bound">y</a><a id="2165" class="Symbol">))</a>
  <a id="2170" href="group-theory.wild-representations-monoids.html#1914" class="Function">preserves-mul-action-wild-representation-type-Monoid</a> <a id="2223" class="Symbol">=</a>
    <a id="2229" href="structured-types.morphisms-wild-monoids.html#1811" class="Function">preserves-mul-hom-Wild-Monoid</a>
      <a id="2265" class="Symbol">(</a> <a id="2267" href="group-theory.monoids.html#4714" class="Function">wild-monoid-Monoid</a> <a id="2286" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a><a id="2287" class="Symbol">)</a>
      <a id="2295" class="Symbol">(</a> <a id="2297" href="foundation.endomorphisms.html#648" class="Function">endo-Wild-Monoid</a> <a id="2314" href="group-theory.wild-representations-monoids.html#1287" class="Function">type-wild-representation-type-Monoid</a><a id="2350" class="Symbol">)</a>
      <a id="2358" class="Symbol">(</a> <a id="2360" href="group-theory.wild-representations-monoids.html#1382" class="Function">hom-action-wild-representation-type-Monoid</a><a id="2402" class="Symbol">)</a>

  <a id="2407" href="group-theory.wild-representations-monoids.html#2407" class="Function">preserves-unit-action-wild-representation-type-Monoid</a> <a id="2461" class="Symbol">:</a>
    <a id="2467" href="group-theory.wild-representations-monoids.html#1596" class="Function">action-wild-representation-type-Monoid</a> <a id="2506" class="Symbol">(</a><a id="2507" href="group-theory.monoids.html#1972" class="Function">unit-Monoid</a> <a id="2519" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a><a id="2520" class="Symbol">)</a> <a id="2522" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2524" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="2529" href="group-theory.wild-representations-monoids.html#2407" class="Function">preserves-unit-action-wild-representation-type-Monoid</a> <a id="2583" class="Symbol">=</a>
    <a id="2589" href="structured-types.morphisms-wild-monoids.html#1345" class="Function">preserves-unit-map-hom-Wild-Monoid</a>
      <a id="2630" class="Symbol">(</a> <a id="2632" href="group-theory.monoids.html#4714" class="Function">wild-monoid-Monoid</a> <a id="2651" href="group-theory.wild-representations-monoids.html#1216" class="Bound">M</a><a id="2652" class="Symbol">)</a>
      <a id="2660" class="Symbol">(</a> <a id="2662" href="foundation.endomorphisms.html#648" class="Function">endo-Wild-Monoid</a> <a id="2679" href="group-theory.wild-representations-monoids.html#1287" class="Function">type-wild-representation-type-Monoid</a><a id="2715" class="Symbol">)</a>
      <a id="2723" class="Symbol">(</a> <a id="2725" href="group-theory.wild-representations-monoids.html#1382" class="Function">hom-action-wild-representation-type-Monoid</a><a id="2767" class="Symbol">)</a>
</pre>