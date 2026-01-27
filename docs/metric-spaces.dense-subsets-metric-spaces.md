# Dense subsets of metric spaces

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="metric-spaces.dense-subsets-metric-spaces.html" class="Module">metric-spaces.dense-subsets-metric-spaces</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>

<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="306" class="Keyword">open</a> <a id="311" class="Keyword">import</a> <a id="318" href="foundation.full-subtypes.html" class="Module">foundation.full-subtypes</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="426" class="Keyword">open</a> <a id="431" class="Keyword">import</a> <a id="438" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="458" class="Keyword">open</a> <a id="463" class="Keyword">import</a> <a id="470" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="491" class="Keyword">open</a> <a id="496" class="Keyword">import</a> <a id="503" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="531" class="Keyword">open</a> <a id="536" class="Keyword">import</a> <a id="543" href="metric-spaces.closure-subsets-metric-spaces.html" class="Module">metric-spaces.closure-subsets-metric-spaces</a>
<a id="587" class="Keyword">open</a> <a id="592" class="Keyword">import</a> <a id="599" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="627" class="Keyword">open</a> <a id="632" class="Keyword">import</a> <a id="639" href="metric-spaces.subspaces-metric-spaces.html" class="Module">metric-spaces.subspaces-metric-spaces</a>
</pre>
</details>

## Idea

A [subset](foundation.subtypes.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) is
{{#concept "dense" disambiguation="in a metric space" WDID=Q673444 WD="dense set" Agda=is-dense-subset-Metric-Space}}
if its [closure](metric-spaces.closure-subsets-metric-spaces.md) is
[full](foundation.full-subtypes.md).

## Definition

<pre class="Agda"><a id="1044" class="Keyword">module</a> <a id="1051" href="metric-spaces.dense-subsets-metric-spaces.html#1051" class="Module">_</a>
  <a id="1055" class="Symbol">{</a><a id="1056" href="metric-spaces.dense-subsets-metric-spaces.html#1056" class="Bound">l1</a> <a id="1059" href="metric-spaces.dense-subsets-metric-spaces.html#1059" class="Bound">l2</a> <a id="1062" href="metric-spaces.dense-subsets-metric-spaces.html#1062" class="Bound">l3</a> <a id="1065" class="Symbol">:</a> <a id="1067" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1072" class="Symbol">}</a> <a id="1074" class="Symbol">(</a><a id="1075" href="metric-spaces.dense-subsets-metric-spaces.html#1075" class="Bound">X</a> <a id="1077" class="Symbol">:</a> <a id="1079" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1092" href="metric-spaces.dense-subsets-metric-spaces.html#1056" class="Bound">l1</a> <a id="1095" href="metric-spaces.dense-subsets-metric-spaces.html#1059" class="Bound">l2</a><a id="1097" class="Symbol">)</a> <a id="1099" class="Symbol">(</a><a id="1100" href="metric-spaces.dense-subsets-metric-spaces.html#1100" class="Bound">S</a> <a id="1102" class="Symbol">:</a> <a id="1104" href="metric-spaces.subspaces-metric-spaces.html#1619" class="Function">subset-Metric-Space</a> <a id="1124" href="metric-spaces.dense-subsets-metric-spaces.html#1062" class="Bound">l3</a> <a id="1127" href="metric-spaces.dense-subsets-metric-spaces.html#1075" class="Bound">X</a><a id="1128" class="Symbol">)</a>
  <a id="1132" class="Keyword">where</a>

  <a id="1141" href="metric-spaces.dense-subsets-metric-spaces.html#1141" class="Function">is-dense-prop-subset-Metric-Space</a> <a id="1175" class="Symbol">:</a> <a id="1177" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1182" class="Symbol">(</a><a id="1183" href="metric-spaces.dense-subsets-metric-spaces.html#1056" class="Bound">l1</a> <a id="1186" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1188" href="metric-spaces.dense-subsets-metric-spaces.html#1059" class="Bound">l2</a> <a id="1191" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1193" href="metric-spaces.dense-subsets-metric-spaces.html#1062" class="Bound">l3</a><a id="1195" class="Symbol">)</a>
  <a id="1199" href="metric-spaces.dense-subsets-metric-spaces.html#1141" class="Function">is-dense-prop-subset-Metric-Space</a> <a id="1233" class="Symbol">=</a>
    <a id="1239" href="foundation.full-subtypes.html#717" class="Function">is-full-subtype-Prop</a> <a id="1260" class="Symbol">(</a><a id="1261" href="metric-spaces.closure-subsets-metric-spaces.html#1610" class="Function">closure-subset-Metric-Space</a> <a id="1289" href="metric-spaces.dense-subsets-metric-spaces.html#1075" class="Bound">X</a> <a id="1291" href="metric-spaces.dense-subsets-metric-spaces.html#1100" class="Bound">S</a><a id="1292" class="Symbol">)</a>

  <a id="1297" href="metric-spaces.dense-subsets-metric-spaces.html#1297" class="Function">is-dense-subset-Metric-Space</a> <a id="1326" class="Symbol">:</a> <a id="1328" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1331" class="Symbol">(</a><a id="1332" href="metric-spaces.dense-subsets-metric-spaces.html#1056" class="Bound">l1</a> <a id="1335" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1337" href="metric-spaces.dense-subsets-metric-spaces.html#1059" class="Bound">l2</a> <a id="1340" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1342" href="metric-spaces.dense-subsets-metric-spaces.html#1062" class="Bound">l3</a><a id="1344" class="Symbol">)</a>
  <a id="1348" href="metric-spaces.dense-subsets-metric-spaces.html#1297" class="Function">is-dense-subset-Metric-Space</a> <a id="1377" class="Symbol">=</a> <a id="1379" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1389" href="metric-spaces.dense-subsets-metric-spaces.html#1141" class="Function">is-dense-prop-subset-Metric-Space</a>
</pre>
## Properties

### A metric space is dense in itself

<pre class="Agda"><a id="1490" class="Keyword">module</a> <a id="1497" href="metric-spaces.dense-subsets-metric-spaces.html#1497" class="Module">_</a>
  <a id="1501" class="Symbol">{</a><a id="1502" href="metric-spaces.dense-subsets-metric-spaces.html#1502" class="Bound">l1</a> <a id="1505" href="metric-spaces.dense-subsets-metric-spaces.html#1505" class="Bound">l2</a> <a id="1508" class="Symbol">:</a> <a id="1510" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1515" class="Symbol">}</a> <a id="1517" class="Symbol">(</a><a id="1518" href="metric-spaces.dense-subsets-metric-spaces.html#1518" class="Bound">X</a> <a id="1520" class="Symbol">:</a> <a id="1522" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1535" href="metric-spaces.dense-subsets-metric-spaces.html#1502" class="Bound">l1</a> <a id="1538" href="metric-spaces.dense-subsets-metric-spaces.html#1505" class="Bound">l2</a><a id="1540" class="Symbol">)</a>
  <a id="1544" class="Keyword">where</a>

  <a id="1553" href="metric-spaces.dense-subsets-metric-spaces.html#1553" class="Function">is-dense-full-subset-Metric-Space</a> <a id="1587" class="Symbol">:</a>
    <a id="1593" href="metric-spaces.dense-subsets-metric-spaces.html#1297" class="Function">is-dense-subset-Metric-Space</a> <a id="1622" href="metric-spaces.dense-subsets-metric-spaces.html#1518" class="Bound">X</a> <a id="1624" class="Symbol">(</a><a id="1625" href="metric-spaces.subspaces-metric-spaces.html#1909" class="Function">full-subset-Metric-Space</a> <a id="1650" href="metric-spaces.dense-subsets-metric-spaces.html#1518" class="Bound">X</a><a id="1651" class="Symbol">)</a>
  <a id="1655" href="metric-spaces.dense-subsets-metric-spaces.html#1553" class="Function">is-dense-full-subset-Metric-Space</a> <a id="1689" href="metric-spaces.dense-subsets-metric-spaces.html#1689" class="Bound">x</a> <a id="1691" href="metric-spaces.dense-subsets-metric-spaces.html#1691" class="Bound">ε</a> <a id="1693" class="Symbol">=</a>
    <a id="1699" href="foundation.existential-quantification.html#4482" class="Function">intro-exists</a> <a id="1712" href="metric-spaces.dense-subsets-metric-spaces.html#1689" class="Bound">x</a> <a id="1714" class="Symbol">(</a><a id="1715" href="metric-spaces.metric-spaces.html#6979" class="Function">refl-neighborhood-Metric-Space</a> <a id="1746" href="metric-spaces.dense-subsets-metric-spaces.html#1518" class="Bound">X</a> <a id="1748" href="metric-spaces.dense-subsets-metric-spaces.html#1691" class="Bound">ε</a> <a id="1750" href="metric-spaces.dense-subsets-metric-spaces.html#1689" class="Bound">x</a> <a id="1752" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1754" href="foundation.raising-universe-levels.html#1099" class="InductiveConstructor">map-raise</a> <a id="1764" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1768" class="Symbol">)</a>
</pre>