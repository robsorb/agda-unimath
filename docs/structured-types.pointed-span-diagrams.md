# Pointed span diagrams

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="structured-types.pointed-span-diagrams.html" class="Module">structured-types.pointed-span-diagrams</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="298" class="Keyword">open</a> <a id="303" class="Keyword">import</a> <a id="310" href="structured-types.morphisms-pointed-arrows.html" class="Module">structured-types.morphisms-pointed-arrows</a>
<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="structured-types.pointed-spans.html" class="Module">structured-types.pointed-spans</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

A {{#concept "(binary) pointed span diagram" Agda=pointed-span-diagram}} is a
diagram of [pointed maps](structured-types.pointed-maps.md) of the form

```text
       f       g
  A <----- S -----> B.
```

In other words, a pointed span diagram consists of two
[pointed types](structured-types.pointed-types.md) `A` and `B` and a
[pointed span](structured-types.pointed-spans.md) from `A` to `B`.

### (Binary) span diagrams of pointed types

<pre class="Agda"><a id="pointed-span-diagram"></a><a id="955" href="structured-types.pointed-span-diagrams.html#955" class="Function">pointed-span-diagram</a> <a id="976" class="Symbol">:</a>
  <a id="980" class="Symbol">(</a><a id="981" href="structured-types.pointed-span-diagrams.html#981" class="Bound">l1</a> <a id="984" href="structured-types.pointed-span-diagrams.html#984" class="Bound">l2</a> <a id="987" href="structured-types.pointed-span-diagrams.html#987" class="Bound">l3</a> <a id="990" class="Symbol">:</a> <a id="992" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="997" class="Symbol">)</a> <a id="999" class="Symbol">→</a> <a id="1001" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1004" class="Symbol">(</a><a id="1005" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1010" href="structured-types.pointed-span-diagrams.html#981" class="Bound">l1</a> <a id="1013" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1015" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1020" href="structured-types.pointed-span-diagrams.html#984" class="Bound">l2</a> <a id="1023" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1025" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1030" href="structured-types.pointed-span-diagrams.html#987" class="Bound">l3</a><a id="1032" class="Symbol">)</a>
<a id="1034" href="structured-types.pointed-span-diagrams.html#955" class="Function">pointed-span-diagram</a> <a id="1055" href="structured-types.pointed-span-diagrams.html#1055" class="Bound">l1</a> <a id="1058" href="structured-types.pointed-span-diagrams.html#1058" class="Bound">l2</a> <a id="1061" href="structured-types.pointed-span-diagrams.html#1061" class="Bound">l3</a> <a id="1064" class="Symbol">=</a>
  <a id="1068" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1070" class="Symbol">(</a> <a id="1072" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1085" href="structured-types.pointed-span-diagrams.html#1055" class="Bound">l1</a><a id="1087" class="Symbol">)</a>
    <a id="1093" class="Symbol">(</a> <a id="1095" class="Symbol">λ</a> <a id="1097" href="structured-types.pointed-span-diagrams.html#1097" class="Bound">A</a> <a id="1099" class="Symbol">→</a> <a id="1101" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1103" class="Symbol">(</a><a id="1104" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1117" href="structured-types.pointed-span-diagrams.html#1058" class="Bound">l2</a><a id="1119" class="Symbol">)</a> <a id="1121" class="Symbol">(</a><a id="1122" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="1135" href="structured-types.pointed-span-diagrams.html#1061" class="Bound">l3</a> <a id="1138" href="structured-types.pointed-span-diagrams.html#1097" class="Bound">A</a><a id="1139" class="Symbol">))</a>

<a id="1143" class="Keyword">module</a> <a id="1150" href="structured-types.pointed-span-diagrams.html#1150" class="Module">_</a>
  <a id="1154" class="Symbol">{</a><a id="1155" href="structured-types.pointed-span-diagrams.html#1155" class="Bound">l1</a> <a id="1158" href="structured-types.pointed-span-diagrams.html#1158" class="Bound">l2</a> <a id="1161" href="structured-types.pointed-span-diagrams.html#1161" class="Bound">l3</a> <a id="1164" class="Symbol">:</a> <a id="1166" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1171" class="Symbol">}</a> <a id="1173" class="Symbol">{</a><a id="1174" href="structured-types.pointed-span-diagrams.html#1174" class="Bound">S</a> <a id="1176" class="Symbol">:</a> <a id="1178" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1191" href="structured-types.pointed-span-diagrams.html#1155" class="Bound">l1</a><a id="1193" class="Symbol">}</a>
  <a id="1197" class="Symbol">{</a><a id="1198" href="structured-types.pointed-span-diagrams.html#1198" class="Bound">A</a> <a id="1200" class="Symbol">:</a> <a id="1202" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1215" href="structured-types.pointed-span-diagrams.html#1158" class="Bound">l2</a><a id="1217" class="Symbol">}</a> <a id="1219" class="Symbol">{</a><a id="1220" href="structured-types.pointed-span-diagrams.html#1220" class="Bound">B</a> <a id="1222" class="Symbol">:</a> <a id="1224" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1237" href="structured-types.pointed-span-diagrams.html#1161" class="Bound">l3</a><a id="1239" class="Symbol">}</a>
  <a id="1243" class="Keyword">where</a>

  <a id="1252" href="structured-types.pointed-span-diagrams.html#1252" class="Function">make-pointed-span-diagram</a> <a id="1278" class="Symbol">:</a>
    <a id="1284" class="Symbol">(</a><a id="1285" href="structured-types.pointed-span-diagrams.html#1174" class="Bound">S</a> <a id="1287" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1290" href="structured-types.pointed-span-diagrams.html#1198" class="Bound">A</a><a id="1291" class="Symbol">)</a> <a id="1293" class="Symbol">→</a> <a id="1295" class="Symbol">(</a><a id="1296" href="structured-types.pointed-span-diagrams.html#1174" class="Bound">S</a> <a id="1298" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1301" href="structured-types.pointed-span-diagrams.html#1220" class="Bound">B</a><a id="1302" class="Symbol">)</a> <a id="1304" class="Symbol">→</a> <a id="1306" href="structured-types.pointed-span-diagrams.html#955" class="Function">pointed-span-diagram</a> <a id="1327" href="structured-types.pointed-span-diagrams.html#1158" class="Bound">l2</a> <a id="1330" href="structured-types.pointed-span-diagrams.html#1161" class="Bound">l3</a> <a id="1333" href="structured-types.pointed-span-diagrams.html#1155" class="Bound">l1</a>
  <a id="1338" href="structured-types.pointed-span-diagrams.html#1252" class="Function">make-pointed-span-diagram</a> <a id="1364" href="structured-types.pointed-span-diagrams.html#1364" class="Bound">f</a> <a id="1366" href="structured-types.pointed-span-diagrams.html#1366" class="Bound">g</a> <a id="1368" class="Symbol">=</a> <a id="1370" class="Symbol">(</a><a id="1371" href="structured-types.pointed-span-diagrams.html#1198" class="Bound">A</a> <a id="1373" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1375" href="structured-types.pointed-span-diagrams.html#1220" class="Bound">B</a> <a id="1377" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1379" href="structured-types.pointed-span-diagrams.html#1174" class="Bound">S</a> <a id="1381" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1383" href="structured-types.pointed-span-diagrams.html#1364" class="Bound">f</a> <a id="1385" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1387" href="structured-types.pointed-span-diagrams.html#1366" class="Bound">g</a><a id="1388" class="Symbol">)</a>

<a id="1391" class="Keyword">module</a> <a id="1398" href="structured-types.pointed-span-diagrams.html#1398" class="Module">_</a>
  <a id="1402" class="Symbol">{</a><a id="1403" href="structured-types.pointed-span-diagrams.html#1403" class="Bound">l1</a> <a id="1406" href="structured-types.pointed-span-diagrams.html#1406" class="Bound">l2</a> <a id="1409" href="structured-types.pointed-span-diagrams.html#1409" class="Bound">l3</a> <a id="1412" class="Symbol">:</a> <a id="1414" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1419" class="Symbol">}</a> <a id="1421" class="Symbol">(</a><a id="1422" href="structured-types.pointed-span-diagrams.html#1422" class="Bound">𝒮</a> <a id="1424" class="Symbol">:</a> <a id="1426" href="structured-types.pointed-span-diagrams.html#955" class="Function">pointed-span-diagram</a> <a id="1447" href="structured-types.pointed-span-diagrams.html#1403" class="Bound">l1</a> <a id="1450" href="structured-types.pointed-span-diagrams.html#1406" class="Bound">l2</a> <a id="1453" href="structured-types.pointed-span-diagrams.html#1409" class="Bound">l3</a><a id="1455" class="Symbol">)</a>
  <a id="1459" class="Keyword">where</a>

  <a id="1468" href="structured-types.pointed-span-diagrams.html#1468" class="Function">pointed-domain-pointed-span-diagram</a> <a id="1504" class="Symbol">:</a> <a id="1506" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1519" href="structured-types.pointed-span-diagrams.html#1403" class="Bound">l1</a>
  <a id="1524" href="structured-types.pointed-span-diagrams.html#1468" class="Function">pointed-domain-pointed-span-diagram</a> <a id="1560" class="Symbol">=</a> <a id="1562" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1566" href="structured-types.pointed-span-diagrams.html#1422" class="Bound">𝒮</a>

  <a id="1571" href="structured-types.pointed-span-diagrams.html#1571" class="Function">domain-pointed-span-diagram</a> <a id="1599" class="Symbol">:</a> <a id="1601" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1604" href="structured-types.pointed-span-diagrams.html#1403" class="Bound">l1</a>
  <a id="1609" href="structured-types.pointed-span-diagrams.html#1571" class="Function">domain-pointed-span-diagram</a> <a id="1637" class="Symbol">=</a>
    <a id="1643" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1661" href="structured-types.pointed-span-diagrams.html#1468" class="Function">pointed-domain-pointed-span-diagram</a>

  <a id="1700" href="structured-types.pointed-span-diagrams.html#1700" class="Function">point-domain-pointed-span-diagram</a> <a id="1734" class="Symbol">:</a>
    <a id="1740" href="structured-types.pointed-span-diagrams.html#1571" class="Function">domain-pointed-span-diagram</a>
  <a id="1770" href="structured-types.pointed-span-diagrams.html#1700" class="Function">point-domain-pointed-span-diagram</a> <a id="1804" class="Symbol">=</a>
    <a id="1810" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1829" href="structured-types.pointed-span-diagrams.html#1468" class="Function">pointed-domain-pointed-span-diagram</a>

  <a id="1868" href="structured-types.pointed-span-diagrams.html#1868" class="Function">pointed-codomain-pointed-span-diagram</a> <a id="1906" class="Symbol">:</a> <a id="1908" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1921" href="structured-types.pointed-span-diagrams.html#1406" class="Bound">l2</a>
  <a id="1926" href="structured-types.pointed-span-diagrams.html#1868" class="Function">pointed-codomain-pointed-span-diagram</a> <a id="1964" class="Symbol">=</a> <a id="1966" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1970" class="Symbol">(</a><a id="1971" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1975" href="structured-types.pointed-span-diagrams.html#1422" class="Bound">𝒮</a><a id="1976" class="Symbol">)</a>

  <a id="1981" href="structured-types.pointed-span-diagrams.html#1981" class="Function">codomain-pointed-span-diagram</a> <a id="2011" class="Symbol">:</a> <a id="2013" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2016" href="structured-types.pointed-span-diagrams.html#1406" class="Bound">l2</a>
  <a id="2021" href="structured-types.pointed-span-diagrams.html#1981" class="Function">codomain-pointed-span-diagram</a> <a id="2051" class="Symbol">=</a>
    <a id="2057" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="2075" href="structured-types.pointed-span-diagrams.html#1868" class="Function">pointed-codomain-pointed-span-diagram</a>

  <a id="2116" href="structured-types.pointed-span-diagrams.html#2116" class="Function">point-codomain-pointed-span-diagram</a> <a id="2152" class="Symbol">:</a>
    <a id="2158" href="structured-types.pointed-span-diagrams.html#1981" class="Function">codomain-pointed-span-diagram</a>
  <a id="2190" href="structured-types.pointed-span-diagrams.html#2116" class="Function">point-codomain-pointed-span-diagram</a> <a id="2226" class="Symbol">=</a>
    <a id="2232" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="2251" href="structured-types.pointed-span-diagrams.html#1868" class="Function">pointed-codomain-pointed-span-diagram</a>

  <a id="2292" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a> <a id="2326" class="Symbol">:</a>
    <a id="2332" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="2345" href="structured-types.pointed-span-diagrams.html#1409" class="Bound">l3</a>
      <a id="2354" class="Symbol">(</a> <a id="2356" href="structured-types.pointed-span-diagrams.html#1468" class="Function">pointed-domain-pointed-span-diagram</a><a id="2391" class="Symbol">)</a>
      <a id="2399" class="Symbol">(</a> <a id="2401" href="structured-types.pointed-span-diagrams.html#1868" class="Function">pointed-codomain-pointed-span-diagram</a><a id="2438" class="Symbol">)</a>
  <a id="2442" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a> <a id="2476" class="Symbol">=</a> <a id="2478" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2482" class="Symbol">(</a><a id="2483" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2487" href="structured-types.pointed-span-diagrams.html#1422" class="Bound">𝒮</a><a id="2488" class="Symbol">)</a>

  <a id="2493" href="structured-types.pointed-span-diagrams.html#2493" class="Function">spanning-pointed-type-pointed-span-diagram</a> <a id="2536" class="Symbol">:</a> <a id="2538" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2551" href="structured-types.pointed-span-diagrams.html#1409" class="Bound">l3</a>
  <a id="2556" href="structured-types.pointed-span-diagrams.html#2493" class="Function">spanning-pointed-type-pointed-span-diagram</a> <a id="2599" class="Symbol">=</a>
    <a id="2605" href="structured-types.pointed-spans.html#1465" class="Function">spanning-pointed-type-pointed-span</a>
      <a id="2646" class="Symbol">(</a> <a id="2648" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a><a id="2681" class="Symbol">)</a>

  <a id="2686" href="structured-types.pointed-span-diagrams.html#2686" class="Function">spanning-type-pointed-span-diagram</a> <a id="2721" class="Symbol">:</a> <a id="2723" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2726" href="structured-types.pointed-span-diagrams.html#1409" class="Bound">l3</a>
  <a id="2731" href="structured-types.pointed-span-diagrams.html#2686" class="Function">spanning-type-pointed-span-diagram</a> <a id="2766" class="Symbol">=</a>
    <a id="2772" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="2790" href="structured-types.pointed-span-diagrams.html#2493" class="Function">spanning-pointed-type-pointed-span-diagram</a>

  <a id="2836" href="structured-types.pointed-span-diagrams.html#2836" class="Function">point-spanning-type-pointed-span-diagram</a> <a id="2877" class="Symbol">:</a>
    <a id="2883" href="structured-types.pointed-span-diagrams.html#2686" class="Function">spanning-type-pointed-span-diagram</a>
  <a id="2920" href="structured-types.pointed-span-diagrams.html#2836" class="Function">point-spanning-type-pointed-span-diagram</a> <a id="2961" class="Symbol">=</a>
    <a id="2967" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="2986" href="structured-types.pointed-span-diagrams.html#2493" class="Function">spanning-pointed-type-pointed-span-diagram</a>

  <a id="3032" href="structured-types.pointed-span-diagrams.html#3032" class="Function">left-pointed-map-pointed-span-diagram</a> <a id="3070" class="Symbol">:</a>
    <a id="3076" href="structured-types.pointed-span-diagrams.html#2493" class="Function">spanning-pointed-type-pointed-span-diagram</a> <a id="3119" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a>
    <a id="3126" href="structured-types.pointed-span-diagrams.html#1468" class="Function">pointed-domain-pointed-span-diagram</a>
  <a id="3164" href="structured-types.pointed-span-diagrams.html#3032" class="Function">left-pointed-map-pointed-span-diagram</a> <a id="3202" class="Symbol">=</a>
    <a id="3208" href="structured-types.pointed-spans.html#1852" class="Function">left-pointed-map-pointed-span</a>
      <a id="3244" class="Symbol">(</a> <a id="3246" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a><a id="3279" class="Symbol">)</a>

  <a id="3284" href="structured-types.pointed-span-diagrams.html#3284" class="Function">left-map-pointed-span-diagram</a> <a id="3314" class="Symbol">:</a>
    <a id="3320" href="structured-types.pointed-span-diagrams.html#2686" class="Function">spanning-type-pointed-span-diagram</a> <a id="3355" class="Symbol">→</a> <a id="3357" href="structured-types.pointed-span-diagrams.html#1571" class="Function">domain-pointed-span-diagram</a>
  <a id="3387" href="structured-types.pointed-span-diagrams.html#3284" class="Function">left-map-pointed-span-diagram</a> <a id="3417" class="Symbol">=</a>
    <a id="3423" href="structured-types.pointed-spans.html#1977" class="Function">left-map-pointed-span</a>
      <a id="3451" class="Symbol">(</a> <a id="3453" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a><a id="3486" class="Symbol">)</a>

  <a id="3491" href="structured-types.pointed-span-diagrams.html#3491" class="Function">preserves-point-left-map-pointed-span-diagram</a> <a id="3537" class="Symbol">:</a>
    <a id="3543" href="structured-types.pointed-span-diagrams.html#3284" class="Function">left-map-pointed-span-diagram</a>
      <a id="3579" class="Symbol">(</a> <a id="3581" href="structured-types.pointed-span-diagrams.html#2836" class="Function">point-spanning-type-pointed-span-diagram</a><a id="3621" class="Symbol">)</a> <a id="3623" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="3629" href="structured-types.pointed-span-diagrams.html#1700" class="Function">point-domain-pointed-span-diagram</a>
  <a id="3665" href="structured-types.pointed-span-diagrams.html#3491" class="Function">preserves-point-left-map-pointed-span-diagram</a> <a id="3711" class="Symbol">=</a>
    <a id="3717" href="structured-types.pointed-spans.html#2133" class="Function">preserves-point-left-map-pointed-span</a>
      <a id="3761" class="Symbol">(</a> <a id="3763" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a><a id="3796" class="Symbol">)</a>

  <a id="3801" href="structured-types.pointed-span-diagrams.html#3801" class="Function">right-pointed-map-pointed-span-diagram</a> <a id="3840" class="Symbol">:</a>
    <a id="3846" href="structured-types.pointed-span-diagrams.html#2493" class="Function">spanning-pointed-type-pointed-span-diagram</a> <a id="3889" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a>
    <a id="3896" href="structured-types.pointed-span-diagrams.html#1868" class="Function">pointed-codomain-pointed-span-diagram</a>
  <a id="3936" href="structured-types.pointed-span-diagrams.html#3801" class="Function">right-pointed-map-pointed-span-diagram</a> <a id="3975" class="Symbol">=</a>
    <a id="3981" href="structured-types.pointed-spans.html#2366" class="Function">right-pointed-map-pointed-span</a>
      <a id="4018" class="Symbol">(</a> <a id="4020" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a><a id="4053" class="Symbol">)</a>

  <a id="4058" href="structured-types.pointed-span-diagrams.html#4058" class="Function">right-map-pointed-span-diagram</a> <a id="4089" class="Symbol">:</a>
    <a id="4095" href="structured-types.pointed-span-diagrams.html#2686" class="Function">spanning-type-pointed-span-diagram</a> <a id="4130" class="Symbol">→</a> <a id="4132" href="structured-types.pointed-span-diagrams.html#1981" class="Function">codomain-pointed-span-diagram</a>
  <a id="4164" href="structured-types.pointed-span-diagrams.html#4058" class="Function">right-map-pointed-span-diagram</a> <a id="4195" class="Symbol">=</a>
    <a id="4201" href="structured-types.pointed-spans.html#2493" class="Function">right-map-pointed-span</a>
      <a id="4230" class="Symbol">(</a> <a id="4232" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a><a id="4265" class="Symbol">)</a>

  <a id="4270" href="structured-types.pointed-span-diagrams.html#4270" class="Function">preserves-point-right-map-pointed-span-diagram</a> <a id="4317" class="Symbol">:</a>
    <a id="4323" href="structured-types.pointed-span-diagrams.html#4058" class="Function">right-map-pointed-span-diagram</a>
      <a id="4360" class="Symbol">(</a> <a id="4362" href="structured-types.pointed-span-diagrams.html#2836" class="Function">point-spanning-type-pointed-span-diagram</a><a id="4402" class="Symbol">)</a> <a id="4404" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="4410" href="structured-types.pointed-span-diagrams.html#2116" class="Function">point-codomain-pointed-span-diagram</a>
  <a id="4448" href="structured-types.pointed-span-diagrams.html#4270" class="Function">preserves-point-right-map-pointed-span-diagram</a> <a id="4495" class="Symbol">=</a>
    <a id="4501" href="structured-types.pointed-spans.html#2652" class="Function">preserves-point-right-map-pointed-span</a>
      <a id="4546" class="Symbol">(</a> <a id="4548" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a><a id="4581" class="Symbol">)</a>
</pre>
### The pointed span diagram obtained from a morphism of pointed arrows

Given pointed maps `f : A →∗ B` and `g : X →∗ Y` and a morphism of pointed
arrows `α : f →∗ g`, the pointed span diagram associated to `α` is the pointed
span diagram

```text
       f       α₀
  B <----- A -----> X.
```

<pre class="Agda"><a id="4891" class="Keyword">module</a> <a id="4898" href="structured-types.pointed-span-diagrams.html#4898" class="Module">_</a>
  <a id="4902" class="Symbol">{</a><a id="4903" href="structured-types.pointed-span-diagrams.html#4903" class="Bound">l1</a> <a id="4906" href="structured-types.pointed-span-diagrams.html#4906" class="Bound">l2</a> <a id="4909" href="structured-types.pointed-span-diagrams.html#4909" class="Bound">l3</a> <a id="4912" href="structured-types.pointed-span-diagrams.html#4912" class="Bound">l4</a> <a id="4915" class="Symbol">:</a> <a id="4917" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4922" class="Symbol">}</a>
  <a id="4926" class="Symbol">{</a><a id="4927" href="structured-types.pointed-span-diagrams.html#4927" class="Bound">A</a> <a id="4929" class="Symbol">:</a> <a id="4931" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4944" href="structured-types.pointed-span-diagrams.html#4903" class="Bound">l1</a><a id="4946" class="Symbol">}</a> <a id="4948" class="Symbol">{</a><a id="4949" href="structured-types.pointed-span-diagrams.html#4949" class="Bound">B</a> <a id="4951" class="Symbol">:</a> <a id="4953" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4966" href="structured-types.pointed-span-diagrams.html#4906" class="Bound">l2</a><a id="4968" class="Symbol">}</a>
  <a id="4972" class="Symbol">{</a><a id="4973" href="structured-types.pointed-span-diagrams.html#4973" class="Bound">X</a> <a id="4975" class="Symbol">:</a> <a id="4977" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4990" href="structured-types.pointed-span-diagrams.html#4909" class="Bound">l3</a><a id="4992" class="Symbol">}</a> <a id="4994" class="Symbol">{</a><a id="4995" href="structured-types.pointed-span-diagrams.html#4995" class="Bound">Y</a> <a id="4997" class="Symbol">:</a> <a id="4999" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="5012" href="structured-types.pointed-span-diagrams.html#4912" class="Bound">l4</a><a id="5014" class="Symbol">}</a>
  <a id="5018" class="Symbol">(</a><a id="5019" href="structured-types.pointed-span-diagrams.html#5019" class="Bound">f</a> <a id="5021" class="Symbol">:</a> <a id="5023" href="structured-types.pointed-span-diagrams.html#4927" class="Bound">A</a> <a id="5025" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="5028" href="structured-types.pointed-span-diagrams.html#4949" class="Bound">B</a><a id="5029" class="Symbol">)</a> <a id="5031" class="Symbol">(</a><a id="5032" href="structured-types.pointed-span-diagrams.html#5032" class="Bound">g</a> <a id="5034" class="Symbol">:</a> <a id="5036" href="structured-types.pointed-span-diagrams.html#4973" class="Bound">X</a> <a id="5038" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="5041" href="structured-types.pointed-span-diagrams.html#4995" class="Bound">Y</a><a id="5042" class="Symbol">)</a> <a id="5044" class="Symbol">(</a><a id="5045" href="structured-types.pointed-span-diagrams.html#5045" class="Bound">α</a> <a id="5047" class="Symbol">:</a> <a id="5049" href="structured-types.morphisms-pointed-arrows.html#2648" class="Function">hom-pointed-arrow</a> <a id="5067" href="structured-types.pointed-span-diagrams.html#5019" class="Bound">f</a> <a id="5069" href="structured-types.pointed-span-diagrams.html#5032" class="Bound">g</a><a id="5070" class="Symbol">)</a>
  <a id="5074" class="Keyword">where</a>

  <a id="5083" href="structured-types.pointed-span-diagrams.html#5083" class="Function">domain-span-diagram-hom-pointed-arrow</a> <a id="5121" class="Symbol">:</a> <a id="5123" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="5136" href="structured-types.pointed-span-diagrams.html#4906" class="Bound">l2</a>
  <a id="5141" href="structured-types.pointed-span-diagrams.html#5083" class="Function">domain-span-diagram-hom-pointed-arrow</a> <a id="5179" class="Symbol">=</a> <a id="5181" href="structured-types.pointed-span-diagrams.html#4949" class="Bound">B</a>

  <a id="5186" href="structured-types.pointed-span-diagrams.html#5186" class="Function">type-domain-span-diagram-hom-pointed-arrow</a> <a id="5229" class="Symbol">:</a> <a id="5231" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5234" href="structured-types.pointed-span-diagrams.html#4906" class="Bound">l2</a>
  <a id="5239" href="structured-types.pointed-span-diagrams.html#5186" class="Function">type-domain-span-diagram-hom-pointed-arrow</a> <a id="5282" class="Symbol">=</a>
    <a id="5288" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="5306" href="structured-types.pointed-span-diagrams.html#5083" class="Function">domain-span-diagram-hom-pointed-arrow</a>

  <a id="5347" href="structured-types.pointed-span-diagrams.html#5347" class="Function">point-domain-span-diagram-hom-pointed-arrow</a> <a id="5391" class="Symbol">:</a>
    <a id="5397" href="structured-types.pointed-span-diagrams.html#5186" class="Function">type-domain-span-diagram-hom-pointed-arrow</a>
  <a id="5442" href="structured-types.pointed-span-diagrams.html#5347" class="Function">point-domain-span-diagram-hom-pointed-arrow</a> <a id="5486" class="Symbol">=</a>
    <a id="5492" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5511" href="structured-types.pointed-span-diagrams.html#5083" class="Function">domain-span-diagram-hom-pointed-arrow</a>

  <a id="5552" href="structured-types.pointed-span-diagrams.html#5552" class="Function">codomain-span-diagram-hom-pointed-arrow</a> <a id="5592" class="Symbol">:</a> <a id="5594" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="5607" href="structured-types.pointed-span-diagrams.html#4909" class="Bound">l3</a>
  <a id="5612" href="structured-types.pointed-span-diagrams.html#5552" class="Function">codomain-span-diagram-hom-pointed-arrow</a> <a id="5652" class="Symbol">=</a> <a id="5654" href="structured-types.pointed-span-diagrams.html#4973" class="Bound">X</a>

  <a id="5659" href="structured-types.pointed-span-diagrams.html#5659" class="Function">type-codomain-span-diagram-hom-pointed-arrow</a> <a id="5704" class="Symbol">:</a> <a id="5706" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5709" href="structured-types.pointed-span-diagrams.html#4909" class="Bound">l3</a>
  <a id="5714" href="structured-types.pointed-span-diagrams.html#5659" class="Function">type-codomain-span-diagram-hom-pointed-arrow</a> <a id="5759" class="Symbol">=</a>
    <a id="5765" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="5783" href="structured-types.pointed-span-diagrams.html#5552" class="Function">codomain-span-diagram-hom-pointed-arrow</a>

  <a id="5826" href="structured-types.pointed-span-diagrams.html#5826" class="Function">point-codomain-span-diagram-hom-pointed-arrow</a> <a id="5872" class="Symbol">:</a>
    <a id="5878" href="structured-types.pointed-span-diagrams.html#5659" class="Function">type-codomain-span-diagram-hom-pointed-arrow</a>
  <a id="5925" href="structured-types.pointed-span-diagrams.html#5826" class="Function">point-codomain-span-diagram-hom-pointed-arrow</a> <a id="5971" class="Symbol">=</a>
    <a id="5977" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5996" href="structured-types.pointed-span-diagrams.html#5552" class="Function">codomain-span-diagram-hom-pointed-arrow</a>

  <a id="6039" href="structured-types.pointed-span-diagrams.html#6039" class="Function">pointed-spanning-type-hom-pointed-arrow</a> <a id="6079" class="Symbol">:</a> <a id="6081" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6094" href="structured-types.pointed-span-diagrams.html#4903" class="Bound">l1</a>
  <a id="6099" href="structured-types.pointed-span-diagrams.html#6039" class="Function">pointed-spanning-type-hom-pointed-arrow</a> <a id="6139" class="Symbol">=</a> <a id="6141" href="structured-types.pointed-span-diagrams.html#4927" class="Bound">A</a>

  <a id="6146" href="structured-types.pointed-span-diagrams.html#6146" class="Function">spanning-type-hom-pointed-arrow</a> <a id="6178" class="Symbol">:</a> <a id="6180" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6183" href="structured-types.pointed-span-diagrams.html#4903" class="Bound">l1</a>
  <a id="6188" href="structured-types.pointed-span-diagrams.html#6146" class="Function">spanning-type-hom-pointed-arrow</a> <a id="6220" class="Symbol">=</a>
    <a id="6226" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="6244" href="structured-types.pointed-span-diagrams.html#6039" class="Function">pointed-spanning-type-hom-pointed-arrow</a>

  <a id="6287" href="structured-types.pointed-span-diagrams.html#6287" class="Function">point-spanning-type-hom-pointed-arrow</a> <a id="6325" class="Symbol">:</a>
    <a id="6331" href="structured-types.pointed-span-diagrams.html#6146" class="Function">spanning-type-hom-pointed-arrow</a>
  <a id="6365" href="structured-types.pointed-span-diagrams.html#6287" class="Function">point-spanning-type-hom-pointed-arrow</a> <a id="6403" class="Symbol">=</a>
    <a id="6409" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="6428" href="structured-types.pointed-span-diagrams.html#6039" class="Function">pointed-spanning-type-hom-pointed-arrow</a>

  <a id="6471" href="structured-types.pointed-span-diagrams.html#6471" class="Function">left-pointed-map-span-diagram-hom-pointed-arrow</a> <a id="6519" class="Symbol">:</a>
    <a id="6525" href="structured-types.pointed-span-diagrams.html#6039" class="Function">pointed-spanning-type-hom-pointed-arrow</a> <a id="6565" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a>
    <a id="6572" href="structured-types.pointed-span-diagrams.html#5083" class="Function">domain-span-diagram-hom-pointed-arrow</a>
  <a id="6612" href="structured-types.pointed-span-diagrams.html#6471" class="Function">left-pointed-map-span-diagram-hom-pointed-arrow</a> <a id="6660" class="Symbol">=</a> <a id="6662" href="structured-types.pointed-span-diagrams.html#5019" class="Bound">f</a>

  <a id="6667" href="structured-types.pointed-span-diagrams.html#6667" class="Function">left-map-span-diagram-hom-pointed-arrow</a> <a id="6707" class="Symbol">:</a>
    <a id="6713" href="structured-types.pointed-span-diagrams.html#6146" class="Function">spanning-type-hom-pointed-arrow</a> <a id="6745" class="Symbol">→</a> <a id="6747" href="structured-types.pointed-span-diagrams.html#5186" class="Function">type-domain-span-diagram-hom-pointed-arrow</a>
  <a id="6792" href="structured-types.pointed-span-diagrams.html#6667" class="Function">left-map-span-diagram-hom-pointed-arrow</a> <a id="6832" class="Symbol">=</a>
    <a id="6838" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="6854" href="structured-types.pointed-span-diagrams.html#6471" class="Function">left-pointed-map-span-diagram-hom-pointed-arrow</a>

  <a id="6905" href="structured-types.pointed-span-diagrams.html#6905" class="Function">preserves-point-left-map-span-diagram-hom-pointed-arrow</a> <a id="6961" class="Symbol">:</a>
    <a id="6967" href="structured-types.pointed-span-diagrams.html#6667" class="Function">left-map-span-diagram-hom-pointed-arrow</a>
      <a id="7013" class="Symbol">(</a> <a id="7015" href="structured-types.pointed-span-diagrams.html#6287" class="Function">point-spanning-type-hom-pointed-arrow</a><a id="7052" class="Symbol">)</a> <a id="7054" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="7060" href="structured-types.pointed-span-diagrams.html#5347" class="Function">point-domain-span-diagram-hom-pointed-arrow</a>
  <a id="7106" href="structured-types.pointed-span-diagrams.html#6905" class="Function">preserves-point-left-map-span-diagram-hom-pointed-arrow</a> <a id="7162" class="Symbol">=</a>
    <a id="7168" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a>
      <a id="7202" class="Symbol">(</a> <a id="7204" href="structured-types.pointed-span-diagrams.html#6471" class="Function">left-pointed-map-span-diagram-hom-pointed-arrow</a><a id="7251" class="Symbol">)</a>

  <a id="7256" href="structured-types.pointed-span-diagrams.html#7256" class="Function">right-pointed-map-span-diagram-hom-pointed-arrow</a> <a id="7305" class="Symbol">:</a>
    <a id="7311" href="structured-types.pointed-span-diagrams.html#6039" class="Function">pointed-spanning-type-hom-pointed-arrow</a> <a id="7351" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a>
    <a id="7358" href="structured-types.pointed-span-diagrams.html#5552" class="Function">codomain-span-diagram-hom-pointed-arrow</a>
  <a id="7400" href="structured-types.pointed-span-diagrams.html#7256" class="Function">right-pointed-map-span-diagram-hom-pointed-arrow</a> <a id="7449" class="Symbol">=</a>
    <a id="7455" href="structured-types.morphisms-pointed-arrows.html#2782" class="Function">pointed-map-domain-hom-pointed-arrow</a> <a id="7492" href="structured-types.pointed-span-diagrams.html#5019" class="Bound">f</a> <a id="7494" href="structured-types.pointed-span-diagrams.html#5032" class="Bound">g</a> <a id="7496" href="structured-types.pointed-span-diagrams.html#5045" class="Bound">α</a>

  <a id="7501" href="structured-types.pointed-span-diagrams.html#7501" class="Function">right-map-span-diagram-hom-pointed-arrow</a> <a id="7542" class="Symbol">:</a>
    <a id="7548" href="structured-types.pointed-span-diagrams.html#6146" class="Function">spanning-type-hom-pointed-arrow</a> <a id="7580" class="Symbol">→</a>
    <a id="7586" href="structured-types.pointed-span-diagrams.html#5659" class="Function">type-codomain-span-diagram-hom-pointed-arrow</a>
  <a id="7633" href="structured-types.pointed-span-diagrams.html#7501" class="Function">right-map-span-diagram-hom-pointed-arrow</a> <a id="7674" class="Symbol">=</a>
    <a id="7680" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="7696" href="structured-types.pointed-span-diagrams.html#7256" class="Function">right-pointed-map-span-diagram-hom-pointed-arrow</a>

  <a id="7748" href="structured-types.pointed-span-diagrams.html#7748" class="Function">preserves-point-right-map-span-diagram-hom-pointed-arrow</a> <a id="7805" class="Symbol">:</a>
    <a id="7811" href="structured-types.pointed-span-diagrams.html#7501" class="Function">right-map-span-diagram-hom-pointed-arrow</a>
      <a id="7858" class="Symbol">(</a> <a id="7860" href="structured-types.pointed-span-diagrams.html#6287" class="Function">point-spanning-type-hom-pointed-arrow</a><a id="7897" class="Symbol">)</a> <a id="7899" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="7905" href="structured-types.pointed-span-diagrams.html#5826" class="Function">point-codomain-span-diagram-hom-pointed-arrow</a>
  <a id="7953" href="structured-types.pointed-span-diagrams.html#7748" class="Function">preserves-point-right-map-span-diagram-hom-pointed-arrow</a> <a id="8010" class="Symbol">=</a>
    <a id="8016" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a>
      <a id="8050" class="Symbol">(</a> <a id="8052" href="structured-types.pointed-span-diagrams.html#7256" class="Function">right-pointed-map-span-diagram-hom-pointed-arrow</a><a id="8100" class="Symbol">)</a>

  <a id="8105" href="structured-types.pointed-span-diagrams.html#8105" class="Function">span-hom-pointed-arrow</a> <a id="8128" class="Symbol">:</a>
    <a id="8134" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="8147" href="structured-types.pointed-span-diagrams.html#4903" class="Bound">l1</a> <a id="8150" href="structured-types.pointed-span-diagrams.html#4949" class="Bound">B</a> <a id="8152" href="structured-types.pointed-span-diagrams.html#4973" class="Bound">X</a>
  <a id="8156" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8160" href="structured-types.pointed-span-diagrams.html#8105" class="Function">span-hom-pointed-arrow</a> <a id="8183" class="Symbol">=</a>
    <a id="8189" href="structured-types.pointed-span-diagrams.html#4927" class="Bound">A</a>
  <a id="8193" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8197" class="Symbol">(</a><a id="8198" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8202" href="structured-types.pointed-span-diagrams.html#8105" class="Function">span-hom-pointed-arrow</a><a id="8224" class="Symbol">)</a> <a id="8226" class="Symbol">=</a>
    <a id="8232" href="structured-types.pointed-span-diagrams.html#6471" class="Function">left-pointed-map-span-diagram-hom-pointed-arrow</a>
  <a id="8282" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8286" class="Symbol">(</a><a id="8287" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8291" href="structured-types.pointed-span-diagrams.html#8105" class="Function">span-hom-pointed-arrow</a><a id="8313" class="Symbol">)</a> <a id="8315" class="Symbol">=</a>
    <a id="8321" href="structured-types.pointed-span-diagrams.html#7256" class="Function">right-pointed-map-span-diagram-hom-pointed-arrow</a>

  <a id="8373" href="structured-types.pointed-span-diagrams.html#8373" class="Function">span-diagram-hom-pointed-arrow</a> <a id="8404" class="Symbol">:</a> <a id="8406" href="structured-types.pointed-span-diagrams.html#955" class="Function">pointed-span-diagram</a> <a id="8427" href="structured-types.pointed-span-diagrams.html#4906" class="Bound">l2</a> <a id="8430" href="structured-types.pointed-span-diagrams.html#4909" class="Bound">l3</a> <a id="8433" href="structured-types.pointed-span-diagrams.html#4903" class="Bound">l1</a>
  <a id="8438" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8442" href="structured-types.pointed-span-diagrams.html#8373" class="Function">span-diagram-hom-pointed-arrow</a> <a id="8473" class="Symbol">=</a>
    <a id="8479" href="structured-types.pointed-span-diagrams.html#5083" class="Function">domain-span-diagram-hom-pointed-arrow</a>
  <a id="8519" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8523" class="Symbol">(</a><a id="8524" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8528" href="structured-types.pointed-span-diagrams.html#8373" class="Function">span-diagram-hom-pointed-arrow</a><a id="8558" class="Symbol">)</a> <a id="8560" class="Symbol">=</a>
    <a id="8566" href="structured-types.pointed-span-diagrams.html#5552" class="Function">codomain-span-diagram-hom-pointed-arrow</a>
  <a id="8608" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8612" class="Symbol">(</a><a id="8613" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8617" href="structured-types.pointed-span-diagrams.html#8373" class="Function">span-diagram-hom-pointed-arrow</a><a id="8647" class="Symbol">)</a> <a id="8649" class="Symbol">=</a>
    <a id="8655" href="structured-types.pointed-span-diagrams.html#8105" class="Function">span-hom-pointed-arrow</a>
</pre>
## See also

- [Transposition of pointed span diagrams](structured-types.transposition-pointed-span-diagrams.md)
