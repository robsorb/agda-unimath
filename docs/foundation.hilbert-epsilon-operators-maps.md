# Hilbert ε-operators on maps

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="foundation.hilbert-epsilon-operators-maps.html" class="Module">foundation.hilbert-epsilon-operators-maps</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.hilberts-epsilon-operators.html" class="Module">foundation.hilberts-epsilon-operators</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation.images.html" class="Module">foundation.images</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="427" class="Keyword">open</a> <a id="432" class="Keyword">import</a> <a id="439" href="foundation-core.injective-maps.html" class="Module">foundation-core.injective-maps</a>
<a id="470" class="Keyword">open</a> <a id="475" class="Keyword">import</a> <a id="482" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
</pre>
</details>

## Idea

A
{{#concept "Hilbert ε-operator" Disambiguation="on a map" Agda=ε-operator-map}}
on a map $f : A → B$ is a family of
[Hilbert ε-operators](foundation.hilberts-epsilon-operators.md) on its
[fibers](foundation-core.fibers-of-maps.md). I.e., for every `y : B` there is an
operator

```text
  ε_y : ║ fiber f y ║₋₁ → fiber f y.
```

Some authors also refer to this as _split support_ {{#cite KECA17}}. Contrary to
Hilbert, we do not assume that such an operator exists for every map.

## Definitions

### The structure of a Hilbert ε-operator on a map

<pre class="Agda"><a id="ε-operator-map"></a><a id="1091" href="foundation.hilbert-epsilon-operators-maps.html#1091" class="Function">ε-operator-map</a> <a id="1106" class="Symbol">:</a>
  <a id="1110" class="Symbol">{</a><a id="1111" href="foundation.hilbert-epsilon-operators-maps.html#1111" class="Bound">l1</a> <a id="1114" href="foundation.hilbert-epsilon-operators-maps.html#1114" class="Bound">l2</a> <a id="1117" class="Symbol">:</a> <a id="1119" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1124" class="Symbol">}</a> <a id="1126" class="Symbol">{</a><a id="1127" href="foundation.hilbert-epsilon-operators-maps.html#1127" class="Bound">A</a> <a id="1129" class="Symbol">:</a> <a id="1131" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1134" href="foundation.hilbert-epsilon-operators-maps.html#1111" class="Bound">l1</a><a id="1136" class="Symbol">}</a> <a id="1138" class="Symbol">{</a><a id="1139" href="foundation.hilbert-epsilon-operators-maps.html#1139" class="Bound">B</a> <a id="1141" class="Symbol">:</a> <a id="1143" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1146" href="foundation.hilbert-epsilon-operators-maps.html#1114" class="Bound">l2</a><a id="1148" class="Symbol">}</a> <a id="1150" class="Symbol">→</a> <a id="1152" class="Symbol">(</a><a id="1153" href="foundation.hilbert-epsilon-operators-maps.html#1127" class="Bound">A</a> <a id="1155" class="Symbol">→</a> <a id="1157" href="foundation.hilbert-epsilon-operators-maps.html#1139" class="Bound">B</a><a id="1158" class="Symbol">)</a> <a id="1160" class="Symbol">→</a> <a id="1162" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1165" class="Symbol">(</a><a id="1166" href="foundation.hilbert-epsilon-operators-maps.html#1111" class="Bound">l1</a> <a id="1169" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1171" href="foundation.hilbert-epsilon-operators-maps.html#1114" class="Bound">l2</a><a id="1173" class="Symbol">)</a>
<a id="1175" href="foundation.hilbert-epsilon-operators-maps.html#1091" class="Function">ε-operator-map</a> <a id="1190" class="Symbol">{</a><a id="1191" class="Argument">B</a> <a id="1193" class="Symbol">=</a> <a id="1195" href="foundation.hilbert-epsilon-operators-maps.html#1195" class="Bound">B</a><a id="1196" class="Symbol">}</a> <a id="1198" href="foundation.hilbert-epsilon-operators-maps.html#1198" class="Bound">f</a> <a id="1200" class="Symbol">=</a> <a id="1202" class="Symbol">(</a><a id="1203" href="foundation.hilbert-epsilon-operators-maps.html#1203" class="Bound">y</a> <a id="1205" class="Symbol">:</a> <a id="1207" href="foundation.hilbert-epsilon-operators-maps.html#1195" class="Bound">B</a><a id="1208" class="Symbol">)</a> <a id="1210" class="Symbol">→</a> <a id="1212" href="foundation.hilberts-epsilon-operators.html#716" class="Function">ε-operator-Hilbert</a> <a id="1231" class="Symbol">(</a><a id="1232" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="1238" href="foundation.hilbert-epsilon-operators-maps.html#1198" class="Bound">f</a> <a id="1240" href="foundation.hilbert-epsilon-operators-maps.html#1203" class="Bound">y</a><a id="1241" class="Symbol">)</a>
</pre>
## Properties

### ε-operators on maps are sections of the image-unit

<pre class="Agda"><a id="1327" class="Keyword">module</a> <a id="1334" href="foundation.hilbert-epsilon-operators-maps.html#1334" class="Module">_</a>
  <a id="1338" class="Symbol">{</a><a id="1339" href="foundation.hilbert-epsilon-operators-maps.html#1339" class="Bound">l1</a> <a id="1342" href="foundation.hilbert-epsilon-operators-maps.html#1342" class="Bound">l2</a> <a id="1345" class="Symbol">:</a> <a id="1347" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1352" class="Symbol">}</a> <a id="1354" class="Symbol">{</a><a id="1355" href="foundation.hilbert-epsilon-operators-maps.html#1355" class="Bound">A</a> <a id="1357" class="Symbol">:</a> <a id="1359" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1362" href="foundation.hilbert-epsilon-operators-maps.html#1339" class="Bound">l1</a><a id="1364" class="Symbol">}</a> <a id="1366" class="Symbol">{</a><a id="1367" href="foundation.hilbert-epsilon-operators-maps.html#1367" class="Bound">B</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1374" href="foundation.hilbert-epsilon-operators-maps.html#1342" class="Bound">l2</a><a id="1376" class="Symbol">}</a> <a id="1378" class="Symbol">{</a><a id="1379" href="foundation.hilbert-epsilon-operators-maps.html#1379" class="Bound">f</a> <a id="1381" class="Symbol">:</a> <a id="1383" href="foundation.hilbert-epsilon-operators-maps.html#1355" class="Bound">A</a> <a id="1385" class="Symbol">→</a> <a id="1387" href="foundation.hilbert-epsilon-operators-maps.html#1367" class="Bound">B</a><a id="1388" class="Symbol">}</a>
  <a id="1392" class="Keyword">where</a>

  <a id="1401" href="foundation.hilbert-epsilon-operators-maps.html#1401" class="Function">map-section-map-unit-im-ε-operator-map</a> <a id="1440" class="Symbol">:</a> <a id="1442" href="foundation.hilbert-epsilon-operators-maps.html#1091" class="Function">ε-operator-map</a> <a id="1457" href="foundation.hilbert-epsilon-operators-maps.html#1379" class="Bound">f</a> <a id="1459" class="Symbol">→</a> <a id="1461" href="foundation.images.html#1761" class="Function">im</a> <a id="1464" href="foundation.hilbert-epsilon-operators-maps.html#1379" class="Bound">f</a> <a id="1466" class="Symbol">→</a> <a id="1468" href="foundation.hilbert-epsilon-operators-maps.html#1355" class="Bound">A</a>
  <a id="1472" href="foundation.hilbert-epsilon-operators-maps.html#1401" class="Function">map-section-map-unit-im-ε-operator-map</a> <a id="1511" href="foundation.hilbert-epsilon-operators-maps.html#1511" class="Bound">ε</a> <a id="1513" class="Symbol">(</a><a id="1514" href="foundation.hilbert-epsilon-operators-maps.html#1514" class="Bound">y</a> <a id="1516" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1518" href="foundation.hilbert-epsilon-operators-maps.html#1518" class="Bound">p</a><a id="1519" class="Symbol">)</a> <a id="1521" class="Symbol">=</a> <a id="1523" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1527" class="Symbol">(</a><a id="1528" href="foundation.hilbert-epsilon-operators-maps.html#1511" class="Bound">ε</a> <a id="1530" href="foundation.hilbert-epsilon-operators-maps.html#1514" class="Bound">y</a> <a id="1532" href="foundation.hilbert-epsilon-operators-maps.html#1518" class="Bound">p</a><a id="1533" class="Symbol">)</a>

  <a id="1538" href="foundation.hilbert-epsilon-operators-maps.html#1538" class="Function">is-section-map-section-map-unit-im-ε-operator-map</a> <a id="1588" class="Symbol">:</a>
    <a id="1594" class="Symbol">(</a><a id="1595" href="foundation.hilbert-epsilon-operators-maps.html#1595" class="Bound">ε</a> <a id="1597" class="Symbol">:</a> <a id="1599" href="foundation.hilbert-epsilon-operators-maps.html#1091" class="Function">ε-operator-map</a> <a id="1614" href="foundation.hilbert-epsilon-operators-maps.html#1379" class="Bound">f</a><a id="1615" class="Symbol">)</a> <a id="1617" class="Symbol">→</a>
    <a id="1623" href="foundation-core.sections.html#1194" class="Function">is-section</a> <a id="1634" class="Symbol">(</a><a id="1635" href="foundation.images.html#1884" class="Function">map-unit-im</a> <a id="1647" href="foundation.hilbert-epsilon-operators-maps.html#1379" class="Bound">f</a><a id="1648" class="Symbol">)</a> <a id="1650" class="Symbol">(</a><a id="1651" href="foundation.hilbert-epsilon-operators-maps.html#1401" class="Function">map-section-map-unit-im-ε-operator-map</a> <a id="1690" href="foundation.hilbert-epsilon-operators-maps.html#1595" class="Bound">ε</a><a id="1691" class="Symbol">)</a>
  <a id="1695" href="foundation.hilbert-epsilon-operators-maps.html#1538" class="Function">is-section-map-section-map-unit-im-ε-operator-map</a> <a id="1745" href="foundation.hilbert-epsilon-operators-maps.html#1745" class="Bound">ε</a> <a id="1747" class="Symbol">(</a><a id="1748" href="foundation.hilbert-epsilon-operators-maps.html#1748" class="Bound">y</a> <a id="1750" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1752" href="foundation.hilbert-epsilon-operators-maps.html#1752" class="Bound">p</a><a id="1753" class="Symbol">)</a> <a id="1755" class="Symbol">=</a>
    <a id="1761" href="foundation.images.html#3134" class="Function">eq-Eq-im</a> <a id="1770" href="foundation.hilbert-epsilon-operators-maps.html#1379" class="Bound">f</a> <a id="1772" class="Symbol">_</a> <a id="1774" class="Symbol">_</a> <a id="1776" class="Symbol">(</a><a id="1777" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1781" class="Symbol">(</a><a id="1782" href="foundation.hilbert-epsilon-operators-maps.html#1745" class="Bound">ε</a> <a id="1784" href="foundation.hilbert-epsilon-operators-maps.html#1748" class="Bound">y</a> <a id="1786" href="foundation.hilbert-epsilon-operators-maps.html#1752" class="Bound">p</a><a id="1787" class="Symbol">))</a>

  <a id="1793" href="foundation.hilbert-epsilon-operators-maps.html#1793" class="Function">section-map-unit-im-ε-operator-map</a> <a id="1828" class="Symbol">:</a>
    <a id="1834" href="foundation.hilbert-epsilon-operators-maps.html#1091" class="Function">ε-operator-map</a> <a id="1849" href="foundation.hilbert-epsilon-operators-maps.html#1379" class="Bound">f</a> <a id="1851" class="Symbol">→</a> <a id="1853" href="foundation-core.sections.html#1373" class="Function">section</a> <a id="1861" class="Symbol">(</a><a id="1862" href="foundation.images.html#1884" class="Function">map-unit-im</a> <a id="1874" href="foundation.hilbert-epsilon-operators-maps.html#1379" class="Bound">f</a><a id="1875" class="Symbol">)</a>
  <a id="1879" href="foundation.hilbert-epsilon-operators-maps.html#1793" class="Function">section-map-unit-im-ε-operator-map</a> <a id="1914" href="foundation.hilbert-epsilon-operators-maps.html#1914" class="Bound">ε</a> <a id="1916" class="Symbol">=</a>
    <a id="1922" class="Symbol">(</a> <a id="1924" href="foundation.hilbert-epsilon-operators-maps.html#1401" class="Function">map-section-map-unit-im-ε-operator-map</a> <a id="1963" href="foundation.hilbert-epsilon-operators-maps.html#1914" class="Bound">ε</a> <a id="1965" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="1973" href="foundation.hilbert-epsilon-operators-maps.html#1538" class="Function">is-section-map-section-map-unit-im-ε-operator-map</a> <a id="2023" href="foundation.hilbert-epsilon-operators-maps.html#1914" class="Bound">ε</a><a id="2024" class="Symbol">)</a>
</pre>
### Injective maps with ε-operators are embeddings

**Proof.** Given a map `f : A → B` equipped with an ε-operator, then we have a
section of the image projection map `A ↠ im f` given by the Hilbert ε-operator.
Now, by injectivity of `f` we the image projection map must be an equivalence.
Hence, `f` is a composite of embeddings and so must be an embedding as well.

```text
    im f
    ↟ ⋮   \
    │ ⋮ ~   \
    │ ↓       ∨
     A ──────→ B
          f
```

<pre class="Agda"><a id="2500" class="Keyword">module</a> <a id="2507" href="foundation.hilbert-epsilon-operators-maps.html#2507" class="Module">_</a>
  <a id="2511" class="Symbol">{</a><a id="2512" href="foundation.hilbert-epsilon-operators-maps.html#2512" class="Bound">l1</a> <a id="2515" href="foundation.hilbert-epsilon-operators-maps.html#2515" class="Bound">l2</a> <a id="2518" class="Symbol">:</a> <a id="2520" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2525" class="Symbol">}</a> <a id="2527" class="Symbol">{</a><a id="2528" href="foundation.hilbert-epsilon-operators-maps.html#2528" class="Bound">A</a> <a id="2530" class="Symbol">:</a> <a id="2532" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2535" href="foundation.hilbert-epsilon-operators-maps.html#2512" class="Bound">l1</a><a id="2537" class="Symbol">}</a> <a id="2539" class="Symbol">{</a><a id="2540" href="foundation.hilbert-epsilon-operators-maps.html#2540" class="Bound">B</a> <a id="2542" class="Symbol">:</a> <a id="2544" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2547" href="foundation.hilbert-epsilon-operators-maps.html#2515" class="Bound">l2</a><a id="2549" class="Symbol">}</a> <a id="2551" class="Symbol">{</a><a id="2552" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a> <a id="2554" class="Symbol">:</a> <a id="2556" href="foundation.hilbert-epsilon-operators-maps.html#2528" class="Bound">A</a> <a id="2558" class="Symbol">→</a> <a id="2560" href="foundation.hilbert-epsilon-operators-maps.html#2540" class="Bound">B</a><a id="2561" class="Symbol">}</a>
  <a id="2565" class="Keyword">where</a>

  <a id="2574" href="foundation.hilbert-epsilon-operators-maps.html#2574" class="Function">is-emb-is-injective-ε-operator-map</a> <a id="2609" class="Symbol">:</a>
    <a id="2615" href="foundation.hilbert-epsilon-operators-maps.html#1091" class="Function">ε-operator-map</a> <a id="2630" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a> <a id="2632" class="Symbol">→</a> <a id="2634" href="foundation-core.injective-maps.html#1182" class="Function">is-injective</a> <a id="2647" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a> <a id="2649" class="Symbol">→</a> <a id="2651" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="2658" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a>
  <a id="2662" href="foundation.hilbert-epsilon-operators-maps.html#2574" class="Function">is-emb-is-injective-ε-operator-map</a> <a id="2697" href="foundation.hilbert-epsilon-operators-maps.html#2697" class="Bound">ε</a> <a id="2699" href="foundation.hilbert-epsilon-operators-maps.html#2699" class="Bound">H</a> <a id="2701" class="Symbol">=</a>
    <a id="2707" href="foundation.embeddings.html#3096" class="Function">is-emb-comp</a>
      <a id="2725" class="Symbol">(</a> <a id="2727" href="foundation.images.html#1813" class="Function">inclusion-im</a> <a id="2740" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a><a id="2741" class="Symbol">)</a>
      <a id="2749" class="Symbol">(</a> <a id="2751" href="foundation.images.html#1884" class="Function">map-unit-im</a> <a id="2763" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a><a id="2764" class="Symbol">)</a>
      <a id="2772" class="Symbol">(</a> <a id="2774" href="foundation.images.html#3301" class="Function">is-emb-inclusion-im</a> <a id="2794" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a><a id="2795" class="Symbol">)</a>
      <a id="2803" class="Symbol">(</a> <a id="2805" href="foundation-core.equivalences.html#20409" class="Function">is-emb-is-equiv</a>
        <a id="2829" class="Symbol">(</a> <a id="2831" href="foundation-core.injective-maps.html#4942" class="Function">is-equiv-is-injective</a>
          <a id="2863" class="Symbol">(</a> <a id="2865" href="foundation.hilbert-epsilon-operators-maps.html#1793" class="Function">section-map-unit-im-ε-operator-map</a> <a id="2900" href="foundation.hilbert-epsilon-operators-maps.html#2697" class="Bound">ε</a><a id="2901" class="Symbol">)</a>
          <a id="2913" class="Symbol">(</a> <a id="2915" href="foundation-core.injective-maps.html#2091" class="Function">is-injective-right-factor</a> <a id="2941" class="Symbol">(</a><a id="2942" href="foundation.images.html#1813" class="Function">inclusion-im</a> <a id="2955" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a><a id="2956" class="Symbol">)</a> <a id="2958" class="Symbol">(</a><a id="2959" href="foundation.images.html#1884" class="Function">map-unit-im</a> <a id="2971" href="foundation.hilbert-epsilon-operators-maps.html#2552" class="Bound">f</a><a id="2972" class="Symbol">)</a> <a id="2974" href="foundation.hilbert-epsilon-operators-maps.html#2699" class="Bound">H</a><a id="2975" class="Symbol">)))</a>
</pre>