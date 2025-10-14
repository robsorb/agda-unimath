# Groups of order `2`

<pre class="Agda"><a id="32" class="Symbol">{-#</a> <a id="36" class="Keyword">OPTIONS</a> <a id="44" class="Pragma">--lossy-unification</a> <a id="64" class="Symbol">#-}</a>

<a id="69" class="Keyword">module</a> <a id="76" href="finite-group-theory.groups-of-order-2.html" class="Module">finite-group-theory.groups-of-order-2</a> <a id="114" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="elementary-number-theory.standard-cyclic-groups.html" class="Module">elementary-number-theory.standard-cyclic-groups</a>

<a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="finite-group-theory.finite-groups.html" class="Module">finite-group-theory.finite-groups</a>

<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="478" class="Keyword">open</a> <a id="483" class="Keyword">import</a> <a id="490" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="516" class="Keyword">open</a> <a id="521" class="Keyword">import</a> <a id="528" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="557" class="Keyword">open</a> <a id="562" class="Keyword">import</a> <a id="569" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="606" class="Keyword">open</a> <a id="611" class="Keyword">import</a> <a id="618" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="634" class="Keyword">open</a> <a id="639" class="Keyword">import</a> <a id="646" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="684" class="Keyword">open</a> <a id="689" class="Keyword">import</a> <a id="696" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="731" class="Keyword">open</a> <a id="736" class="Keyword">import</a> <a id="743" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="771" class="Keyword">open</a> <a id="776" class="Keyword">import</a> <a id="783" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="803" class="Keyword">open</a> <a id="808" class="Keyword">import</a> <a id="815" href="group-theory.isomorphisms-groups.html" class="Module">group-theory.isomorphisms-groups</a>
<a id="848" class="Keyword">open</a> <a id="853" class="Keyword">import</a> <a id="860" href="group-theory.symmetric-groups.html" class="Module">group-theory.symmetric-groups</a>

<a id="891" class="Keyword">open</a> <a id="896" class="Keyword">import</a> <a id="903" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="943" class="Keyword">open</a> <a id="948" class="Keyword">import</a> <a id="955" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The type of groups of order 2 is contractible

## Definitions

### The type of groups of order 2

<pre class="Agda"><a id="Group-of-Order-2"></a><a id="1133" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="1150" class="Symbol">:</a> <a id="1152" class="Symbol">(</a><a id="1153" href="finite-group-theory.groups-of-order-2.html#1153" class="Bound">l</a> <a id="1155" class="Symbol">:</a> <a id="1157" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1162" class="Symbol">)</a> <a id="1164" class="Symbol">→</a> <a id="1166" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1169" class="Symbol">(</a><a id="1170" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1175" href="finite-group-theory.groups-of-order-2.html#1153" class="Bound">l</a><a id="1176" class="Symbol">)</a>
<a id="1178" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="1195" href="finite-group-theory.groups-of-order-2.html#1195" class="Bound">l</a> <a id="1197" class="Symbol">=</a> <a id="1199" href="finite-group-theory.finite-groups.html#12158" class="Function">Group-of-Order</a> <a id="1214" href="finite-group-theory.groups-of-order-2.html#1195" class="Bound">l</a> <a id="1216" class="Number">2</a>

<a id="1219" class="Keyword">module</a> <a id="1226" href="finite-group-theory.groups-of-order-2.html#1226" class="Module">_</a>
  <a id="1230" class="Symbol">{</a><a id="1231" href="finite-group-theory.groups-of-order-2.html#1231" class="Bound">l</a> <a id="1233" class="Symbol">:</a> <a id="1235" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1240" class="Symbol">}</a> <a id="1242" class="Symbol">(</a><a id="1243" href="finite-group-theory.groups-of-order-2.html#1243" class="Bound">G</a> <a id="1245" class="Symbol">:</a> <a id="1247" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="1264" href="finite-group-theory.groups-of-order-2.html#1231" class="Bound">l</a><a id="1265" class="Symbol">)</a>
  <a id="1269" class="Keyword">where</a>

  <a id="1278" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="1301" class="Symbol">:</a> <a id="1303" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1309" href="finite-group-theory.groups-of-order-2.html#1231" class="Bound">l</a>
  <a id="1313" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="1336" class="Symbol">=</a> <a id="1338" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1342" href="finite-group-theory.groups-of-order-2.html#1243" class="Bound">G</a>

  <a id="1347" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1374" href="finite-group-theory.groups-of-order-2.html#1231" class="Bound">l</a>
  <a id="1378" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a> <a id="1400" class="Symbol">=</a> <a id="1402" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1413" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a>

  <a id="1439" href="finite-group-theory.groups-of-order-2.html#1439" class="Function">is-set-type-Group-of-Order-2</a> <a id="1468" class="Symbol">:</a> <a id="1470" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="1477" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a>
  <a id="1501" href="finite-group-theory.groups-of-order-2.html#1439" class="Function">is-set-type-Group-of-Order-2</a> <a id="1530" class="Symbol">=</a> <a id="1532" href="group-theory.groups.html#2640" class="Function">is-set-type-Group</a> <a id="1550" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a>

  <a id="1576" href="finite-group-theory.groups-of-order-2.html#1576" class="Function">mul-Group-of-Order-2</a> <a id="1597" class="Symbol">:</a> <a id="1599" class="Symbol">(</a><a id="1600" href="finite-group-theory.groups-of-order-2.html#1600" class="Bound">x</a> <a id="1602" href="finite-group-theory.groups-of-order-2.html#1602" class="Bound">y</a> <a id="1604" class="Symbol">:</a> <a id="1606" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a><a id="1627" class="Symbol">)</a> <a id="1629" class="Symbol">→</a> <a id="1631" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a>
  <a id="1655" href="finite-group-theory.groups-of-order-2.html#1576" class="Function">mul-Group-of-Order-2</a> <a id="1676" class="Symbol">=</a> <a id="1678" href="group-theory.groups.html#2829" class="Function">mul-Group</a> <a id="1688" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a>

  <a id="1714" href="finite-group-theory.groups-of-order-2.html#1714" class="Function">unit-Group-of-Order-2</a> <a id="1736" class="Symbol">:</a> <a id="1738" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a>
  <a id="1762" href="finite-group-theory.groups-of-order-2.html#1714" class="Function">unit-Group-of-Order-2</a> <a id="1784" class="Symbol">=</a> <a id="1786" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="1797" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a>

  <a id="1823" href="finite-group-theory.groups-of-order-2.html#1823" class="Function">has-two-elements-Group-of-Order-2</a> <a id="1857" class="Symbol">:</a> <a id="1859" href="univalent-combinatorics.2-element-types.html#2556" class="Function">has-two-elements</a> <a id="1876" class="Symbol">(</a><a id="1877" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a><a id="1898" class="Symbol">)</a>
  <a id="1902" href="finite-group-theory.groups-of-order-2.html#1823" class="Function">has-two-elements-Group-of-Order-2</a> <a id="1936" class="Symbol">=</a> <a id="1938" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1942" href="finite-group-theory.groups-of-order-2.html#1243" class="Bound">G</a>

  <a id="1947" href="finite-group-theory.groups-of-order-2.html#1947" class="Function">2-element-type-Group-of-Order-2</a> <a id="1979" class="Symbol">:</a> <a id="1981" href="univalent-combinatorics.2-element-types.html#2893" class="Function">2-Element-Type</a> <a id="1996" href="finite-group-theory.groups-of-order-2.html#1231" class="Bound">l</a>
  <a id="2000" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2004" href="finite-group-theory.groups-of-order-2.html#1947" class="Function">2-element-type-Group-of-Order-2</a> <a id="2036" class="Symbol">=</a> <a id="2038" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a>
  <a id="2062" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2066" href="finite-group-theory.groups-of-order-2.html#1947" class="Function">2-element-type-Group-of-Order-2</a> <a id="2098" class="Symbol">=</a> <a id="2100" href="finite-group-theory.groups-of-order-2.html#1823" class="Function">has-two-elements-Group-of-Order-2</a>
</pre>
### The group ℤ/2 of order 2

<pre class="Agda"><a id="ℤ-Mod-2-Group-of-Order-2"></a><a id="2177" href="finite-group-theory.groups-of-order-2.html#2177" class="Function">ℤ-Mod-2-Group-of-Order-2</a> <a id="2202" class="Symbol">:</a> <a id="2204" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="2221" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2227" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2231" href="finite-group-theory.groups-of-order-2.html#2177" class="Function">ℤ-Mod-2-Group-of-Order-2</a> <a id="2256" class="Symbol">=</a> <a id="2258" href="elementary-number-theory.standard-cyclic-groups.html#1219" class="Function">ℤ-Mod-Group</a> <a id="2270" class="Number">2</a>
<a id="2272" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2276" href="finite-group-theory.groups-of-order-2.html#2177" class="Function">ℤ-Mod-2-Group-of-Order-2</a> <a id="2301" class="Symbol">=</a> <a id="2303" href="foundation.mere-equivalences.html#1316" class="Function">refl-mere-equiv</a> <a id="2319" class="Symbol">(</a><a id="2320" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="2324" class="Number">2</a><a id="2325" class="Symbol">)</a>
</pre>
### The permutation group S₂ of order 2

<pre class="Agda"><a id="symmetric-Group-of-Order-2"></a><a id="2381" href="finite-group-theory.groups-of-order-2.html#2381" class="Function">symmetric-Group-of-Order-2</a> <a id="2408" class="Symbol">:</a> <a id="2410" class="Symbol">(</a><a id="2411" href="finite-group-theory.groups-of-order-2.html#2411" class="Bound">l</a> <a id="2413" class="Symbol">:</a> <a id="2415" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2420" class="Symbol">)</a> <a id="2422" class="Symbol">→</a> <a id="2424" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="2441" href="finite-group-theory.groups-of-order-2.html#2411" class="Bound">l</a>
<a id="2443" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2447" class="Symbol">(</a><a id="2448" href="finite-group-theory.groups-of-order-2.html#2381" class="Function">symmetric-Group-of-Order-2</a> <a id="2475" href="finite-group-theory.groups-of-order-2.html#2475" class="Bound">l</a><a id="2476" class="Symbol">)</a> <a id="2478" class="Symbol">=</a>
  <a id="2482" href="group-theory.symmetric-groups.html#2342" class="Function">symmetric-Group</a> <a id="2498" class="Symbol">(</a><a id="2499" href="univalent-combinatorics.standard-finite-types.html#3993" class="Function">raise-Fin-Set</a> <a id="2513" href="finite-group-theory.groups-of-order-2.html#2475" class="Bound">l</a> <a id="2515" class="Number">2</a><a id="2516" class="Symbol">)</a>
<a id="2518" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2522" class="Symbol">(</a><a id="2523" href="finite-group-theory.groups-of-order-2.html#2381" class="Function">symmetric-Group-of-Order-2</a> <a id="2550" href="finite-group-theory.groups-of-order-2.html#2550" class="Bound">l</a><a id="2551" class="Symbol">)</a> <a id="2553" class="Symbol">=</a>
  <a id="2557" href="univalent-combinatorics.2-element-types.html#14853" class="Function">has-two-elements-Aut-2-Element-Type</a>
    <a id="2597" class="Symbol">(</a> <a id="2599" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="2604" class="Symbol">(</a><a id="2605" href="univalent-combinatorics.standard-finite-types.html#3717" class="Function">raise-Fin</a> <a id="2615" href="finite-group-theory.groups-of-order-2.html#2550" class="Bound">l</a> <a id="2617" class="Number">2</a><a id="2618" class="Symbol">)</a> <a id="2620" class="Symbol">(</a><a id="2621" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="2637" class="Symbol">(</a><a id="2638" href="univalent-combinatorics.standard-finite-types.html#3789" class="Function">compute-raise-Fin</a> <a id="2656" href="finite-group-theory.groups-of-order-2.html#2550" class="Bound">l</a> <a id="2658" class="Number">2</a><a id="2659" class="Symbol">)))</a>
</pre>
## Properties

### Characterization of the identity type of the type of groups of order 2

<pre class="Agda"><a id="iso-Group-of-Order-2"></a><a id="2767" href="finite-group-theory.groups-of-order-2.html#2767" class="Function">iso-Group-of-Order-2</a> <a id="2788" class="Symbol">:</a>
  <a id="2792" class="Symbol">{</a><a id="2793" href="finite-group-theory.groups-of-order-2.html#2793" class="Bound">l1</a> <a id="2796" href="finite-group-theory.groups-of-order-2.html#2796" class="Bound">l2</a> <a id="2799" class="Symbol">:</a> <a id="2801" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2806" class="Symbol">}</a> <a id="2808" class="Symbol">(</a><a id="2809" href="finite-group-theory.groups-of-order-2.html#2809" class="Bound">G</a> <a id="2811" class="Symbol">:</a> <a id="2813" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="2830" href="finite-group-theory.groups-of-order-2.html#2793" class="Bound">l1</a><a id="2832" class="Symbol">)</a> <a id="2834" class="Symbol">(</a><a id="2835" href="finite-group-theory.groups-of-order-2.html#2835" class="Bound">H</a> <a id="2837" class="Symbol">:</a> <a id="2839" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="2856" href="finite-group-theory.groups-of-order-2.html#2796" class="Bound">l2</a><a id="2858" class="Symbol">)</a> <a id="2860" class="Symbol">→</a>
  <a id="2864" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2867" class="Symbol">(</a><a id="2868" href="finite-group-theory.groups-of-order-2.html#2793" class="Bound">l1</a> <a id="2871" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2873" href="finite-group-theory.groups-of-order-2.html#2796" class="Bound">l2</a><a id="2875" class="Symbol">)</a>
<a id="2877" href="finite-group-theory.groups-of-order-2.html#2767" class="Function">iso-Group-of-Order-2</a> <a id="2898" href="finite-group-theory.groups-of-order-2.html#2898" class="Bound">G</a> <a id="2900" href="finite-group-theory.groups-of-order-2.html#2900" class="Bound">H</a> <a id="2902" class="Symbol">=</a>
  <a id="2906" href="group-theory.isomorphisms-groups.html#3368" class="Function">iso-Group</a> <a id="2916" class="Symbol">(</a><a id="2917" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="2940" href="finite-group-theory.groups-of-order-2.html#2898" class="Bound">G</a><a id="2941" class="Symbol">)</a> <a id="2943" class="Symbol">(</a><a id="2944" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="2967" href="finite-group-theory.groups-of-order-2.html#2900" class="Bound">H</a><a id="2968" class="Symbol">)</a>

<a id="2971" class="Keyword">module</a> <a id="2978" href="finite-group-theory.groups-of-order-2.html#2978" class="Module">_</a>
  <a id="2982" class="Symbol">{</a><a id="2983" href="finite-group-theory.groups-of-order-2.html#2983" class="Bound">l</a> <a id="2985" class="Symbol">:</a> <a id="2987" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2992" class="Symbol">}</a> <a id="2994" class="Symbol">(</a><a id="2995" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a> <a id="2997" class="Symbol">:</a> <a id="2999" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="3016" href="finite-group-theory.groups-of-order-2.html#2983" class="Bound">l</a><a id="3017" class="Symbol">)</a>
  <a id="3021" class="Keyword">where</a>

  <a id="3030" href="finite-group-theory.groups-of-order-2.html#3030" class="Function">iso-eq-Group-of-Order-2</a> <a id="3054" class="Symbol">:</a>
    <a id="3060" class="Symbol">(</a><a id="3061" href="finite-group-theory.groups-of-order-2.html#3061" class="Bound">H</a> <a id="3063" class="Symbol">:</a> <a id="3065" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="3082" href="finite-group-theory.groups-of-order-2.html#2983" class="Bound">l</a><a id="3083" class="Symbol">)</a> <a id="3085" class="Symbol">→</a> <a id="3087" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a> <a id="3090" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a> <a id="3092" href="finite-group-theory.groups-of-order-2.html#3061" class="Bound">H</a> <a id="3094" class="Symbol">→</a> <a id="3096" href="finite-group-theory.groups-of-order-2.html#2767" class="Function">iso-Group-of-Order-2</a> <a id="3117" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a> <a id="3119" href="finite-group-theory.groups-of-order-2.html#3061" class="Bound">H</a>
  <a id="3123" href="finite-group-theory.groups-of-order-2.html#3030" class="Function">iso-eq-Group-of-Order-2</a> <a id="3147" href="finite-group-theory.groups-of-order-2.html#3147" class="Bound">H</a> <a id="3149" href="finite-group-theory.groups-of-order-2.html#3149" class="Bound">p</a> <a id="3151" class="Symbol">=</a>
    <a id="3157" href="group-theory.isomorphisms-groups.html#6718" class="Function">iso-eq-Group</a>
      <a id="3176" class="Symbol">(</a> <a id="3178" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="3201" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a><a id="3202" class="Symbol">)</a>
      <a id="3210" class="Symbol">(</a> <a id="3212" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="3235" href="finite-group-theory.groups-of-order-2.html#3147" class="Bound">H</a><a id="3236" class="Symbol">)</a>
      <a id="3244" class="Symbol">(</a> <a id="3246" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="3249" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3253" href="finite-group-theory.groups-of-order-2.html#3149" class="Bound">p</a><a id="3254" class="Symbol">)</a>

  <a id="3259" href="finite-group-theory.groups-of-order-2.html#3259" class="Function">is-torsorial-iso-Group-of-Order-2</a> <a id="3293" class="Symbol">:</a>
    <a id="3299" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="3312" class="Symbol">(</a><a id="3313" href="finite-group-theory.groups-of-order-2.html#2767" class="Function">iso-Group-of-Order-2</a> <a id="3334" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a><a id="3335" class="Symbol">)</a>
  <a id="3339" href="finite-group-theory.groups-of-order-2.html#3259" class="Function">is-torsorial-iso-Group-of-Order-2</a> <a id="3373" class="Symbol">=</a>
    <a id="3379" href="foundation.subtype-identity-principle.html#1328" class="Function">is-torsorial-Eq-subtype</a>
      <a id="3409" class="Symbol">(</a> <a id="3411" href="group-theory.isomorphisms-groups.html#7118" class="Function">is-torsorial-iso-Group</a> <a id="3434" class="Symbol">(</a><a id="3435" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="3458" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a><a id="3459" class="Symbol">))</a>
      <a id="3468" class="Symbol">(</a> <a id="3470" class="Symbol">λ</a> <a id="3472" href="finite-group-theory.groups-of-order-2.html#3472" class="Bound">H</a> <a id="3474" class="Symbol">→</a> <a id="3476" href="foundation.propositional-truncations.html#1806" class="Function">is-prop-type-trunc-Prop</a><a id="3499" class="Symbol">)</a>
      <a id="3507" class="Symbol">(</a> <a id="3509" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="3532" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a><a id="3533" class="Symbol">)</a>
      <a id="3541" class="Symbol">(</a> <a id="3543" href="group-theory.isomorphisms-groups.html#6457" class="Function">id-iso-Group</a> <a id="3556" class="Symbol">(</a><a id="3557" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="3580" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a><a id="3581" class="Symbol">))</a>
      <a id="3590" class="Symbol">(</a> <a id="3592" href="finite-group-theory.groups-of-order-2.html#1823" class="Function">has-two-elements-Group-of-Order-2</a> <a id="3626" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a><a id="3627" class="Symbol">)</a>

  <a id="3632" href="finite-group-theory.groups-of-order-2.html#3632" class="Function">is-equiv-iso-eq-Group-of-Order-2</a> <a id="3665" class="Symbol">:</a>
    <a id="3671" class="Symbol">(</a><a id="3672" href="finite-group-theory.groups-of-order-2.html#3672" class="Bound">H</a> <a id="3674" class="Symbol">:</a> <a id="3676" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="3693" href="finite-group-theory.groups-of-order-2.html#2983" class="Bound">l</a><a id="3694" class="Symbol">)</a> <a id="3696" class="Symbol">→</a> <a id="3698" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="3707" class="Symbol">(</a><a id="3708" href="finite-group-theory.groups-of-order-2.html#3030" class="Function">iso-eq-Group-of-Order-2</a> <a id="3732" href="finite-group-theory.groups-of-order-2.html#3672" class="Bound">H</a><a id="3733" class="Symbol">)</a>
  <a id="3737" href="finite-group-theory.groups-of-order-2.html#3632" class="Function">is-equiv-iso-eq-Group-of-Order-2</a> <a id="3770" class="Symbol">=</a>
    <a id="3776" href="foundation.fundamental-theorem-of-identity-types.html#2039" class="Function">fundamental-theorem-id</a>
      <a id="3805" class="Symbol">(</a> <a id="3807" href="finite-group-theory.groups-of-order-2.html#3259" class="Function">is-torsorial-iso-Group-of-Order-2</a><a id="3840" class="Symbol">)</a>
      <a id="3848" class="Symbol">(</a> <a id="3850" href="finite-group-theory.groups-of-order-2.html#3030" class="Function">iso-eq-Group-of-Order-2</a><a id="3873" class="Symbol">)</a>

  <a id="3878" href="finite-group-theory.groups-of-order-2.html#3878" class="Function">eq-iso-Group-of-Order-2</a> <a id="3902" class="Symbol">:</a>
    <a id="3908" class="Symbol">(</a><a id="3909" href="finite-group-theory.groups-of-order-2.html#3909" class="Bound">H</a> <a id="3911" class="Symbol">:</a> <a id="3913" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="3930" href="finite-group-theory.groups-of-order-2.html#2983" class="Bound">l</a><a id="3931" class="Symbol">)</a> <a id="3933" class="Symbol">→</a> <a id="3935" href="finite-group-theory.groups-of-order-2.html#2767" class="Function">iso-Group-of-Order-2</a> <a id="3956" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a> <a id="3958" href="finite-group-theory.groups-of-order-2.html#3909" class="Bound">H</a> <a id="3960" class="Symbol">→</a> <a id="3962" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a> <a id="3965" href="finite-group-theory.groups-of-order-2.html#2995" class="Bound">G</a> <a id="3967" href="finite-group-theory.groups-of-order-2.html#3909" class="Bound">H</a>
  <a id="3971" href="finite-group-theory.groups-of-order-2.html#3878" class="Function">eq-iso-Group-of-Order-2</a> <a id="3995" href="finite-group-theory.groups-of-order-2.html#3995" class="Bound">H</a> <a id="3997" class="Symbol">=</a>
    <a id="4003" href="foundation-core.equivalences.html#6985" class="Function">map-inv-is-equiv</a> <a id="4020" class="Symbol">(</a><a id="4021" href="finite-group-theory.groups-of-order-2.html#3632" class="Function">is-equiv-iso-eq-Group-of-Order-2</a> <a id="4054" href="finite-group-theory.groups-of-order-2.html#3995" class="Bound">H</a><a id="4055" class="Symbol">)</a>
</pre>
### A homomorphism from any group of order 2 to any group of order 2

<pre class="Agda"><a id="4140" class="Keyword">module</a> <a id="4147" href="finite-group-theory.groups-of-order-2.html#4147" class="Module">_</a>
  <a id="4151" class="Symbol">{</a><a id="4152" href="finite-group-theory.groups-of-order-2.html#4152" class="Bound">l1</a> <a id="4155" href="finite-group-theory.groups-of-order-2.html#4155" class="Bound">l2</a> <a id="4158" class="Symbol">:</a> <a id="4160" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4165" class="Symbol">}</a> <a id="4167" class="Symbol">(</a><a id="4168" href="finite-group-theory.groups-of-order-2.html#4168" class="Bound">G</a> <a id="4170" class="Symbol">:</a> <a id="4172" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="4189" href="finite-group-theory.groups-of-order-2.html#4152" class="Bound">l1</a><a id="4191" class="Symbol">)</a> <a id="4193" class="Symbol">(</a><a id="4194" href="finite-group-theory.groups-of-order-2.html#4194" class="Bound">H</a> <a id="4196" class="Symbol">:</a> <a id="4198" href="finite-group-theory.groups-of-order-2.html#1133" class="Function">Group-of-Order-2</a> <a id="4215" href="finite-group-theory.groups-of-order-2.html#4155" class="Bound">l2</a><a id="4217" class="Symbol">)</a>
  <a id="4221" class="Keyword">where</a>

  <a id="4230" href="finite-group-theory.groups-of-order-2.html#4230" class="Function">equiv-Group-of-Order-2</a> <a id="4253" class="Symbol">:</a>
    <a id="4259" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a> <a id="4281" href="finite-group-theory.groups-of-order-2.html#4168" class="Bound">G</a> <a id="4283" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="4285" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a> <a id="4307" href="finite-group-theory.groups-of-order-2.html#4194" class="Bound">H</a>
  <a id="4311" href="finite-group-theory.groups-of-order-2.html#4230" class="Function">equiv-Group-of-Order-2</a> <a id="4334" class="Symbol">=</a>
    <a id="4340" class="Symbol">(</a> <a id="4342" href="univalent-combinatorics.2-element-types.html#10595" class="Function">equiv-point-2-Element-Type</a>
      <a id="4375" class="Symbol">(</a> <a id="4377" href="finite-group-theory.groups-of-order-2.html#1947" class="Function">2-element-type-Group-of-Order-2</a> <a id="4409" href="finite-group-theory.groups-of-order-2.html#4194" class="Bound">H</a><a id="4410" class="Symbol">)</a>
      <a id="4418" class="Symbol">(</a> <a id="4420" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="4431" class="Symbol">(</a><a id="4432" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="4455" href="finite-group-theory.groups-of-order-2.html#4194" class="Bound">H</a><a id="4456" class="Symbol">)))</a> <a id="4460" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
    <a id="4467" class="Symbol">(</a> <a id="4469" href="foundation-core.equivalences.html#8859" class="Function">inv-equiv</a>
      <a id="4485" class="Symbol">(</a> <a id="4487" href="univalent-combinatorics.2-element-types.html#10595" class="Function">equiv-point-2-Element-Type</a>
        <a id="4522" class="Symbol">(</a> <a id="4524" href="finite-group-theory.groups-of-order-2.html#1947" class="Function">2-element-type-Group-of-Order-2</a> <a id="4556" href="finite-group-theory.groups-of-order-2.html#4168" class="Bound">G</a><a id="4557" class="Symbol">)</a>
        <a id="4567" class="Symbol">(</a> <a id="4569" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="4580" class="Symbol">(</a><a id="4581" href="finite-group-theory.groups-of-order-2.html#1278" class="Function">group-Group-of-Order-2</a> <a id="4604" href="finite-group-theory.groups-of-order-2.html#4168" class="Bound">G</a><a id="4605" class="Symbol">))))</a>

  <a id="4613" href="finite-group-theory.groups-of-order-2.html#4613" class="Function">map-specified-hom-Group-of-Order-2</a> <a id="4648" class="Symbol">:</a>
    <a id="4654" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a> <a id="4676" href="finite-group-theory.groups-of-order-2.html#4168" class="Bound">G</a> <a id="4678" class="Symbol">→</a> <a id="4680" href="finite-group-theory.groups-of-order-2.html#1347" class="Function">type-Group-of-Order-2</a> <a id="4702" href="finite-group-theory.groups-of-order-2.html#4194" class="Bound">H</a>
  <a id="4706" href="finite-group-theory.groups-of-order-2.html#4613" class="Function">map-specified-hom-Group-of-Order-2</a> <a id="4741" class="Symbol">=</a>
    <a id="4747" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="4757" href="finite-group-theory.groups-of-order-2.html#4230" class="Function">equiv-Group-of-Order-2</a>
</pre>
```text
  specified-hom-Group-of-Order-2 :
    hom-Group (group-Group-of-Order-2 G) (group-Group-of-Order-2 H)
  specified-hom-Group-of-Order-2 = {!!}
```

### The type of groups of order 2 is contractible

```text
is-contr-Group-of-Order-2 : (l : Level) → is-contr (Group-of-Order-2 l)
pr1 (is-contr-Group-of-Order-2 l) = symmetric-Group-of-Order-2 l
pr2 (is-contr-Group-of-Order-2 l) G =
  eq-iso-Group-of-Order-2
    ( symmetric-Group-of-Order-2 l)
    ( G)
    {!!}
```
