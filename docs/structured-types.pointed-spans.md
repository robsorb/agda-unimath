# Pointed spans

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="structured-types.pointed-spans.html" class="Module">structured-types.pointed-spans</a> <a id="64" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="120" class="Keyword">open</a> <a id="125" class="Keyword">import</a> <a id="132" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="318" class="Keyword">open</a> <a id="323" class="Keyword">import</a> <a id="330" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="360" class="Keyword">open</a> <a id="365" class="Keyword">import</a> <a id="372" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

Consider two [pointed types](structured-types.pointed-types.md) `A` and `B`. A
{{#concept "(binary) pointed span" Agda=pointed-span}} from `A` to `B` consists
of a
{{#concept "spanning pointed type" Disambiguation="binary pointed span" Agda=spanning-pointed-type-pointed-span}}
`S` and a [pair](foundation.dependent-pair-types.md) of
[pointed maps](structured-types.pointed-maps.md) `f : S →∗ A` and `g : S →∗ B`.
The pointed types `A` and `B` in the specification of a binary span of pointed
types are also referred to as the
{{#concept "domain" Disambiguation="binary pointed span"}} and
{{#concept "codomain" Disambiguation="binary pointed span"}} of the pointed
span, respectively.

## Definitions

### (Binary) pointed spans

<pre class="Agda"><a id="pointed-span"></a><a id="1168" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="1181" class="Symbol">:</a>
  <a id="1185" class="Symbol">{</a><a id="1186" href="structured-types.pointed-spans.html#1186" class="Bound">l1</a> <a id="1189" href="structured-types.pointed-spans.html#1189" class="Bound">l2</a> <a id="1192" class="Symbol">:</a> <a id="1194" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1199" class="Symbol">}</a> <a id="1201" class="Symbol">(</a><a id="1202" href="structured-types.pointed-spans.html#1202" class="Bound">l</a> <a id="1204" class="Symbol">:</a> <a id="1206" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1211" class="Symbol">)</a> <a id="1213" class="Symbol">(</a><a id="1214" href="structured-types.pointed-spans.html#1214" class="Bound">A</a> <a id="1216" class="Symbol">:</a> <a id="1218" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1231" href="structured-types.pointed-spans.html#1186" class="Bound">l1</a><a id="1233" class="Symbol">)</a> <a id="1235" class="Symbol">(</a><a id="1236" href="structured-types.pointed-spans.html#1236" class="Bound">B</a> <a id="1238" class="Symbol">:</a> <a id="1240" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1253" href="structured-types.pointed-spans.html#1189" class="Bound">l2</a><a id="1255" class="Symbol">)</a> <a id="1257" class="Symbol">→</a>
  <a id="1261" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1264" class="Symbol">(</a><a id="1265" href="structured-types.pointed-spans.html#1186" class="Bound">l1</a> <a id="1268" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1270" href="structured-types.pointed-spans.html#1189" class="Bound">l2</a> <a id="1273" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1275" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1280" href="structured-types.pointed-spans.html#1202" class="Bound">l</a><a id="1281" class="Symbol">)</a>
<a id="1283" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="1296" href="structured-types.pointed-spans.html#1296" class="Bound">l</a> <a id="1298" href="structured-types.pointed-spans.html#1298" class="Bound">A</a> <a id="1300" href="structured-types.pointed-spans.html#1300" class="Bound">B</a> <a id="1302" class="Symbol">=</a> <a id="1304" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1306" class="Symbol">(</a><a id="1307" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1320" href="structured-types.pointed-spans.html#1296" class="Bound">l</a><a id="1321" class="Symbol">)</a> <a id="1323" class="Symbol">(λ</a> <a id="1326" href="structured-types.pointed-spans.html#1326" class="Bound">S</a> <a id="1328" class="Symbol">→</a> <a id="1330" class="Symbol">(</a><a id="1331" href="structured-types.pointed-spans.html#1326" class="Bound">S</a> <a id="1333" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1336" href="structured-types.pointed-spans.html#1298" class="Bound">A</a><a id="1337" class="Symbol">)</a> <a id="1339" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1341" class="Symbol">(</a><a id="1342" href="structured-types.pointed-spans.html#1326" class="Bound">S</a> <a id="1344" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1347" href="structured-types.pointed-spans.html#1300" class="Bound">B</a><a id="1348" class="Symbol">))</a>

<a id="1352" class="Keyword">module</a> <a id="1359" href="structured-types.pointed-spans.html#1359" class="Module">_</a>
  <a id="1363" class="Symbol">{</a><a id="1364" href="structured-types.pointed-spans.html#1364" class="Bound">l1</a> <a id="1367" href="structured-types.pointed-spans.html#1367" class="Bound">l2</a> <a id="1370" href="structured-types.pointed-spans.html#1370" class="Bound">l3</a> <a id="1373" class="Symbol">:</a> <a id="1375" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1380" class="Symbol">}</a> <a id="1382" class="Symbol">{</a><a id="1383" href="structured-types.pointed-spans.html#1383" class="Bound">A</a> <a id="1385" class="Symbol">:</a> <a id="1387" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1400" href="structured-types.pointed-spans.html#1364" class="Bound">l1</a><a id="1402" class="Symbol">}</a> <a id="1404" class="Symbol">{</a><a id="1405" href="structured-types.pointed-spans.html#1405" class="Bound">B</a> <a id="1407" class="Symbol">:</a> <a id="1409" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1422" href="structured-types.pointed-spans.html#1367" class="Bound">l2</a><a id="1424" class="Symbol">}</a>
  <a id="1428" class="Symbol">(</a><a id="1429" href="structured-types.pointed-spans.html#1429" class="Bound">𝒮</a> <a id="1431" class="Symbol">:</a> <a id="1433" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="1446" href="structured-types.pointed-spans.html#1370" class="Bound">l3</a> <a id="1449" href="structured-types.pointed-spans.html#1383" class="Bound">A</a> <a id="1451" href="structured-types.pointed-spans.html#1405" class="Bound">B</a><a id="1452" class="Symbol">)</a>
  <a id="1456" class="Keyword">where</a>

  <a id="1465" href="structured-types.pointed-spans.html#1465" class="Function">spanning-pointed-type-pointed-span</a> <a id="1500" class="Symbol">:</a> <a id="1502" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1515" href="structured-types.pointed-spans.html#1370" class="Bound">l3</a>
  <a id="1520" href="structured-types.pointed-spans.html#1465" class="Function">spanning-pointed-type-pointed-span</a> <a id="1555" class="Symbol">=</a> <a id="1557" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1561" href="structured-types.pointed-spans.html#1429" class="Bound">𝒮</a>

  <a id="1566" href="structured-types.pointed-spans.html#1566" class="Function">spanning-type-pointed-span</a> <a id="1593" class="Symbol">:</a> <a id="1595" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1598" href="structured-types.pointed-spans.html#1370" class="Bound">l3</a>
  <a id="1603" href="structured-types.pointed-spans.html#1566" class="Function">spanning-type-pointed-span</a> <a id="1630" class="Symbol">=</a>
    <a id="1636" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1654" href="structured-types.pointed-spans.html#1465" class="Function">spanning-pointed-type-pointed-span</a>

  <a id="1692" href="structured-types.pointed-spans.html#1692" class="Function">point-spanning-type-pointed-span</a> <a id="1725" class="Symbol">:</a> <a id="1727" href="structured-types.pointed-spans.html#1566" class="Function">spanning-type-pointed-span</a>
  <a id="1756" href="structured-types.pointed-spans.html#1692" class="Function">point-spanning-type-pointed-span</a> <a id="1789" class="Symbol">=</a>
    <a id="1795" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1814" href="structured-types.pointed-spans.html#1465" class="Function">spanning-pointed-type-pointed-span</a>

  <a id="1852" href="structured-types.pointed-spans.html#1852" class="Function">left-pointed-map-pointed-span</a> <a id="1882" class="Symbol">:</a>
    <a id="1888" href="structured-types.pointed-spans.html#1465" class="Function">spanning-pointed-type-pointed-span</a> <a id="1923" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1926" href="structured-types.pointed-spans.html#1383" class="Bound">A</a>
  <a id="1930" href="structured-types.pointed-spans.html#1852" class="Function">left-pointed-map-pointed-span</a> <a id="1960" class="Symbol">=</a> <a id="1962" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1966" class="Symbol">(</a><a id="1967" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1971" href="structured-types.pointed-spans.html#1429" class="Bound">𝒮</a><a id="1972" class="Symbol">)</a>

  <a id="1977" href="structured-types.pointed-spans.html#1977" class="Function">left-map-pointed-span</a> <a id="1999" class="Symbol">:</a>
    <a id="2005" href="structured-types.pointed-spans.html#1566" class="Function">spanning-type-pointed-span</a> <a id="2032" class="Symbol">→</a> <a id="2034" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="2052" href="structured-types.pointed-spans.html#1383" class="Bound">A</a>
  <a id="2056" href="structured-types.pointed-spans.html#1977" class="Function">left-map-pointed-span</a> <a id="2078" class="Symbol">=</a>
    <a id="2084" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2100" href="structured-types.pointed-spans.html#1852" class="Function">left-pointed-map-pointed-span</a>

  <a id="2133" href="structured-types.pointed-spans.html#2133" class="Function">preserves-point-left-map-pointed-span</a> <a id="2171" class="Symbol">:</a>
    <a id="2177" href="structured-types.pointed-spans.html#1977" class="Function">left-map-pointed-span</a> <a id="2199" href="structured-types.pointed-spans.html#1692" class="Function">point-spanning-type-pointed-span</a> <a id="2232" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2238" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="2257" href="structured-types.pointed-spans.html#1383" class="Bound">A</a>
  <a id="2261" href="structured-types.pointed-spans.html#2133" class="Function">preserves-point-left-map-pointed-span</a> <a id="2299" class="Symbol">=</a>
    <a id="2305" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="2333" href="structured-types.pointed-spans.html#1852" class="Function">left-pointed-map-pointed-span</a>

  <a id="2366" href="structured-types.pointed-spans.html#2366" class="Function">right-pointed-map-pointed-span</a> <a id="2397" class="Symbol">:</a>
    <a id="2403" href="structured-types.pointed-spans.html#1465" class="Function">spanning-pointed-type-pointed-span</a> <a id="2438" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2441" href="structured-types.pointed-spans.html#1405" class="Bound">B</a>
  <a id="2445" href="structured-types.pointed-spans.html#2366" class="Function">right-pointed-map-pointed-span</a> <a id="2476" class="Symbol">=</a> <a id="2478" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2482" class="Symbol">(</a><a id="2483" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2487" href="structured-types.pointed-spans.html#1429" class="Bound">𝒮</a><a id="2488" class="Symbol">)</a>

  <a id="2493" href="structured-types.pointed-spans.html#2493" class="Function">right-map-pointed-span</a> <a id="2516" class="Symbol">:</a>
    <a id="2522" href="structured-types.pointed-spans.html#1566" class="Function">spanning-type-pointed-span</a> <a id="2549" class="Symbol">→</a> <a id="2551" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="2569" href="structured-types.pointed-spans.html#1405" class="Bound">B</a>
  <a id="2573" href="structured-types.pointed-spans.html#2493" class="Function">right-map-pointed-span</a> <a id="2596" class="Symbol">=</a>
    <a id="2602" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2618" href="structured-types.pointed-spans.html#2366" class="Function">right-pointed-map-pointed-span</a>

  <a id="2652" href="structured-types.pointed-spans.html#2652" class="Function">preserves-point-right-map-pointed-span</a> <a id="2691" class="Symbol">:</a>
    <a id="2697" href="structured-types.pointed-spans.html#2493" class="Function">right-map-pointed-span</a> <a id="2720" href="structured-types.pointed-spans.html#1692" class="Function">point-spanning-type-pointed-span</a> <a id="2753" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2759" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="2778" href="structured-types.pointed-spans.html#1405" class="Bound">B</a>
  <a id="2782" href="structured-types.pointed-spans.html#2652" class="Function">preserves-point-right-map-pointed-span</a> <a id="2821" class="Symbol">=</a>
    <a id="2827" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="2855" href="structured-types.pointed-spans.html#2366" class="Function">right-pointed-map-pointed-span</a>

  <a id="2889" href="structured-types.pointed-spans.html#2889" class="Function">span-pointed-span</a> <a id="2907" class="Symbol">:</a> <a id="2909" href="foundation.spans.html#1830" class="Function">span</a> <a id="2914" href="structured-types.pointed-spans.html#1370" class="Bound">l3</a> <a id="2917" class="Symbol">(</a><a id="2918" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="2936" href="structured-types.pointed-spans.html#1383" class="Bound">A</a><a id="2937" class="Symbol">)</a> <a id="2939" class="Symbol">(</a><a id="2940" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="2958" href="structured-types.pointed-spans.html#1405" class="Bound">B</a><a id="2959" class="Symbol">)</a>
  <a id="2963" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2967" href="structured-types.pointed-spans.html#2889" class="Function">span-pointed-span</a> <a id="2985" class="Symbol">=</a> <a id="2987" href="structured-types.pointed-spans.html#1566" class="Function">spanning-type-pointed-span</a>
  <a id="3016" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3020" class="Symbol">(</a><a id="3021" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3025" href="structured-types.pointed-spans.html#2889" class="Function">span-pointed-span</a><a id="3042" class="Symbol">)</a> <a id="3044" class="Symbol">=</a> <a id="3046" href="structured-types.pointed-spans.html#1977" class="Function">left-map-pointed-span</a>
  <a id="3070" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3074" class="Symbol">(</a><a id="3075" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3079" href="structured-types.pointed-spans.html#2889" class="Function">span-pointed-span</a><a id="3096" class="Symbol">)</a> <a id="3098" class="Symbol">=</a> <a id="3100" href="structured-types.pointed-spans.html#2493" class="Function">right-map-pointed-span</a>
</pre>
### Identity pointed spans

<pre class="Agda"><a id="3164" class="Keyword">module</a> <a id="3171" href="structured-types.pointed-spans.html#3171" class="Module">_</a>
  <a id="3175" class="Symbol">{</a><a id="3176" href="structured-types.pointed-spans.html#3176" class="Bound">l1</a> <a id="3179" class="Symbol">:</a> <a id="3181" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3186" class="Symbol">}</a> <a id="3188" class="Symbol">{</a><a id="3189" href="structured-types.pointed-spans.html#3189" class="Bound">X</a> <a id="3191" class="Symbol">:</a> <a id="3193" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="3206" href="structured-types.pointed-spans.html#3176" class="Bound">l1</a><a id="3208" class="Symbol">}</a>
  <a id="3212" class="Keyword">where</a>

  <a id="3221" href="structured-types.pointed-spans.html#3221" class="Function">id-pointed-span</a> <a id="3237" class="Symbol">:</a> <a id="3239" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="3252" href="structured-types.pointed-spans.html#3176" class="Bound">l1</a> <a id="3255" href="structured-types.pointed-spans.html#3189" class="Bound">X</a> <a id="3257" href="structured-types.pointed-spans.html#3189" class="Bound">X</a>
  <a id="3261" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3265" href="structured-types.pointed-spans.html#3221" class="Function">id-pointed-span</a> <a id="3281" class="Symbol">=</a> <a id="3283" href="structured-types.pointed-spans.html#3189" class="Bound">X</a>
  <a id="3287" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3291" class="Symbol">(</a><a id="3292" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3296" href="structured-types.pointed-spans.html#3221" class="Function">id-pointed-span</a><a id="3311" class="Symbol">)</a> <a id="3313" class="Symbol">=</a> <a id="3315" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a>
  <a id="3332" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3336" class="Symbol">(</a><a id="3337" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3341" href="structured-types.pointed-spans.html#3221" class="Function">id-pointed-span</a><a id="3356" class="Symbol">)</a> <a id="3358" class="Symbol">=</a> <a id="3360" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a>
</pre>
## See also

- [Opposite pointed spans](structured-types.opposite-pointed-spans.md)
- [Pointed span diagrams](structured-types.pointed-span-diagrams.md)
- [Spans](foundation.spans.md)
