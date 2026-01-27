# Constant pointed maps

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="structured-types.constant-pointed-maps.html" class="Module">structured-types.constant-pointed-maps</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.constant-maps.html" class="Module">foundation.constant-maps</a>
<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

Given two [pointed types](structured-types.pointed-types.md) `A` and `B` the
{{#concept "constant pointed map" Agda=constant-pointed-map}} from `A` to `B` is
the [pointed map](structured-types.pointed-maps.md)
`constant-pointed-map : A →∗ B` mapping every element in `A` to the base point
of `B`.

## Definitions

### Constant pointed maps

<pre class="Agda"><a id="755" class="Keyword">module</a> <a id="762" href="structured-types.constant-pointed-maps.html#762" class="Module">_</a>
  <a id="766" class="Symbol">{</a><a id="767" href="structured-types.constant-pointed-maps.html#767" class="Bound">l1</a> <a id="770" href="structured-types.constant-pointed-maps.html#770" class="Bound">l2</a> <a id="773" class="Symbol">:</a> <a id="775" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="780" class="Symbol">}</a> <a id="782" class="Symbol">(</a><a id="783" href="structured-types.constant-pointed-maps.html#783" class="Bound">A</a> <a id="785" class="Symbol">:</a> <a id="787" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="800" href="structured-types.constant-pointed-maps.html#767" class="Bound">l1</a><a id="802" class="Symbol">)</a> <a id="804" class="Symbol">(</a><a id="805" href="structured-types.constant-pointed-maps.html#805" class="Bound">B</a> <a id="807" class="Symbol">:</a> <a id="809" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="822" href="structured-types.constant-pointed-maps.html#770" class="Bound">l2</a><a id="824" class="Symbol">)</a>
  <a id="828" class="Keyword">where</a>

  <a id="837" href="structured-types.constant-pointed-maps.html#837" class="Function">map-constant-pointed-map</a> <a id="862" class="Symbol">:</a> <a id="864" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="882" href="structured-types.constant-pointed-maps.html#783" class="Bound">A</a> <a id="884" class="Symbol">→</a> <a id="886" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="904" href="structured-types.constant-pointed-maps.html#805" class="Bound">B</a>
  <a id="908" href="structured-types.constant-pointed-maps.html#837" class="Function">map-constant-pointed-map</a> <a id="933" class="Symbol">=</a>
    <a id="939" href="foundation-core.constant-maps.html#472" class="Function">const</a> <a id="945" class="Symbol">(</a><a id="946" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="964" href="structured-types.constant-pointed-maps.html#783" class="Bound">A</a><a id="965" class="Symbol">)</a> <a id="967" class="Symbol">(</a><a id="968" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="987" href="structured-types.constant-pointed-maps.html#805" class="Bound">B</a><a id="988" class="Symbol">)</a>

  <a id="993" href="structured-types.constant-pointed-maps.html#993" class="Function">preserves-point-constant-pointed-map</a> <a id="1030" class="Symbol">:</a>
    <a id="1036" href="structured-types.constant-pointed-maps.html#837" class="Function">map-constant-pointed-map</a> <a id="1061" class="Symbol">(</a><a id="1062" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1081" href="structured-types.constant-pointed-maps.html#783" class="Bound">A</a><a id="1082" class="Symbol">)</a> <a id="1084" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1086" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1105" href="structured-types.constant-pointed-maps.html#805" class="Bound">B</a>
  <a id="1109" href="structured-types.constant-pointed-maps.html#993" class="Function">preserves-point-constant-pointed-map</a> <a id="1146" class="Symbol">=</a> <a id="1148" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="1156" href="structured-types.constant-pointed-maps.html#1156" class="Function">constant-pointed-map</a> <a id="1177" class="Symbol">:</a> <a id="1179" href="structured-types.constant-pointed-maps.html#783" class="Bound">A</a> <a id="1181" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1184" href="structured-types.constant-pointed-maps.html#805" class="Bound">B</a>
  <a id="1188" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1192" href="structured-types.constant-pointed-maps.html#1156" class="Function">constant-pointed-map</a> <a id="1213" class="Symbol">=</a> <a id="1215" href="structured-types.constant-pointed-maps.html#837" class="Function">map-constant-pointed-map</a>
  <a id="1242" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1246" href="structured-types.constant-pointed-maps.html#1156" class="Function">constant-pointed-map</a> <a id="1267" class="Symbol">=</a> <a id="1269" href="structured-types.constant-pointed-maps.html#993" class="Function">preserves-point-constant-pointed-map</a>
</pre>
### The pointed type of pointed maps

<pre class="Agda"><a id="1357" class="Keyword">module</a> <a id="1364" href="structured-types.constant-pointed-maps.html#1364" class="Module">_</a>
  <a id="1368" class="Symbol">{</a><a id="1369" href="structured-types.constant-pointed-maps.html#1369" class="Bound">l1</a> <a id="1372" href="structured-types.constant-pointed-maps.html#1372" class="Bound">l2</a> <a id="1375" class="Symbol">:</a> <a id="1377" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1382" class="Symbol">}</a> <a id="1384" class="Symbol">(</a><a id="1385" href="structured-types.constant-pointed-maps.html#1385" class="Bound">A</a> <a id="1387" class="Symbol">:</a> <a id="1389" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1402" href="structured-types.constant-pointed-maps.html#1369" class="Bound">l1</a><a id="1404" class="Symbol">)</a> <a id="1406" class="Symbol">(</a><a id="1407" href="structured-types.constant-pointed-maps.html#1407" class="Bound">B</a> <a id="1409" class="Symbol">:</a> <a id="1411" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1424" href="structured-types.constant-pointed-maps.html#1372" class="Bound">l2</a><a id="1426" class="Symbol">)</a>
  <a id="1430" class="Keyword">where</a>

  <a id="1439" href="structured-types.constant-pointed-maps.html#1439" class="Function">pointed-map-Pointed-Type</a> <a id="1464" class="Symbol">:</a> <a id="1466" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1479" class="Symbol">(</a><a id="1480" href="structured-types.constant-pointed-maps.html#1369" class="Bound">l1</a> <a id="1483" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1485" href="structured-types.constant-pointed-maps.html#1372" class="Bound">l2</a><a id="1487" class="Symbol">)</a>
  <a id="1491" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1495" href="structured-types.constant-pointed-maps.html#1439" class="Function">pointed-map-Pointed-Type</a> <a id="1520" class="Symbol">=</a> <a id="1522" href="structured-types.constant-pointed-maps.html#1385" class="Bound">A</a> <a id="1524" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1527" href="structured-types.constant-pointed-maps.html#1407" class="Bound">B</a>
  <a id="1531" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1535" href="structured-types.constant-pointed-maps.html#1439" class="Function">pointed-map-Pointed-Type</a> <a id="1560" class="Symbol">=</a> <a id="1562" href="structured-types.constant-pointed-maps.html#1156" class="Function">constant-pointed-map</a> <a id="1583" href="structured-types.constant-pointed-maps.html#1385" class="Bound">A</a> <a id="1585" href="structured-types.constant-pointed-maps.html#1407" class="Bound">B</a>
</pre>
## See also

- [Constant maps](foundation.constant-maps.md)
