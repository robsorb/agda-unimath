# The pointed unit type

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="structured-types.pointed-unit-type.html" class="Module">structured-types.pointed-unit-type</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="377" class="Keyword">open</a> <a id="382" class="Keyword">import</a> <a id="389" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The pointed unit type is the initial pointed type.

## Definition

<pre class="Agda"><a id="unit-Pointed-Type"></a><a id="521" href="structured-types.pointed-unit-type.html#521" class="Function">unit-Pointed-Type</a> <a id="539" class="Symbol">:</a> <a id="541" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="554" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="560" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="564" href="structured-types.pointed-unit-type.html#521" class="Function">unit-Pointed-Type</a> <a id="582" class="Symbol">=</a> <a id="584" href="foundation.unit-type.html#950" class="Record">unit</a>
<a id="589" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="593" href="structured-types.pointed-unit-type.html#521" class="Function">unit-Pointed-Type</a> <a id="611" class="Symbol">=</a> <a id="613" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a>
</pre>
## Properties

<pre class="Agda"><a id="646" class="Keyword">module</a> <a id="653" href="structured-types.pointed-unit-type.html#653" class="Module">_</a>
  <a id="657" class="Symbol">{</a><a id="658" href="structured-types.pointed-unit-type.html#658" class="Bound">l</a> <a id="660" class="Symbol">:</a> <a id="662" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="667" class="Symbol">}</a> <a id="669" class="Symbol">(</a><a id="670" href="structured-types.pointed-unit-type.html#670" class="Bound">X</a> <a id="672" class="Symbol">:</a> <a id="674" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="687" href="structured-types.pointed-unit-type.html#658" class="Bound">l</a><a id="688" class="Symbol">)</a>
  <a id="692" class="Keyword">where</a>

  <a id="701" href="structured-types.pointed-unit-type.html#701" class="Function">terminal-pointed-map</a> <a id="722" class="Symbol">:</a> <a id="724" href="structured-types.pointed-unit-type.html#670" class="Bound">X</a> <a id="726" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="729" href="structured-types.pointed-unit-type.html#521" class="Function">unit-Pointed-Type</a>
  <a id="749" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="753" href="structured-types.pointed-unit-type.html#701" class="Function">terminal-pointed-map</a> <a id="774" class="Symbol">_</a> <a id="776" class="Symbol">=</a> <a id="778" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a>
  <a id="785" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="789" href="structured-types.pointed-unit-type.html#701" class="Function">terminal-pointed-map</a> <a id="810" class="Symbol">=</a> <a id="812" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="820" href="structured-types.pointed-unit-type.html#820" class="Function">map-terminal-pointed-map</a> <a id="845" class="Symbol">:</a> <a id="847" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="865" href="structured-types.pointed-unit-type.html#670" class="Bound">X</a> <a id="867" class="Symbol">→</a> <a id="869" href="foundation.unit-type.html#950" class="Record">unit</a>
  <a id="876" href="structured-types.pointed-unit-type.html#820" class="Function">map-terminal-pointed-map</a> <a id="901" class="Symbol">=</a>
    <a id="907" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="923" class="Symbol">{</a><a id="924" class="Argument">A</a> <a id="926" class="Symbol">=</a> <a id="928" href="structured-types.pointed-unit-type.html#670" class="Bound">X</a><a id="929" class="Symbol">}</a> <a id="931" class="Symbol">{</a><a id="932" class="Argument">B</a> <a id="934" class="Symbol">=</a> <a id="936" href="structured-types.pointed-unit-type.html#521" class="Function">unit-Pointed-Type</a><a id="953" class="Symbol">}</a>
      <a id="961" href="structured-types.pointed-unit-type.html#701" class="Function">terminal-pointed-map</a>

  <a id="985" href="structured-types.pointed-unit-type.html#985" class="Function">inclusion-point-Pointed-Type</a> <a id="1014" class="Symbol">:</a>
    <a id="1020" href="structured-types.pointed-unit-type.html#521" class="Function">unit-Pointed-Type</a> <a id="1038" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1041" href="structured-types.pointed-unit-type.html#670" class="Bound">X</a>
  <a id="1045" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1049" href="structured-types.pointed-unit-type.html#985" class="Function">inclusion-point-Pointed-Type</a> <a id="1078" class="Symbol">=</a> <a id="1080" href="foundation.unit-type.html#1422" class="Function">point</a> <a id="1086" class="Symbol">(</a><a id="1087" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1106" href="structured-types.pointed-unit-type.html#670" class="Bound">X</a><a id="1107" class="Symbol">)</a>
  <a id="1111" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1115" href="structured-types.pointed-unit-type.html#985" class="Function">inclusion-point-Pointed-Type</a> <a id="1144" class="Symbol">=</a> <a id="1146" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="1154" href="structured-types.pointed-unit-type.html#1154" class="Function">is-initial-unit-Pointed-Type</a> <a id="1183" class="Symbol">:</a>
    <a id="1189" class="Symbol">(</a> <a id="1191" href="structured-types.pointed-unit-type.html#1191" class="Bound">f</a> <a id="1193" class="Symbol">:</a> <a id="1195" href="structured-types.pointed-unit-type.html#521" class="Function">unit-Pointed-Type</a> <a id="1213" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1216" href="structured-types.pointed-unit-type.html#670" class="Bound">X</a><a id="1217" class="Symbol">)</a> <a id="1219" class="Symbol">→</a> <a id="1221" href="structured-types.pointed-unit-type.html#1191" class="Bound">f</a> <a id="1223" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1226" href="structured-types.pointed-unit-type.html#985" class="Function">inclusion-point-Pointed-Type</a>
  <a id="1257" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1261" class="Symbol">(</a><a id="1262" href="structured-types.pointed-unit-type.html#1154" class="Function">is-initial-unit-Pointed-Type</a> <a id="1291" href="structured-types.pointed-unit-type.html#1291" class="Bound">f</a><a id="1292" class="Symbol">)</a> <a id="1294" class="Symbol">_</a> <a id="1296" class="Symbol">=</a> <a id="1298" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="1326" href="structured-types.pointed-unit-type.html#1291" class="Bound">f</a>
  <a id="1330" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1334" class="Symbol">(</a><a id="1335" href="structured-types.pointed-unit-type.html#1154" class="Function">is-initial-unit-Pointed-Type</a> <a id="1364" href="structured-types.pointed-unit-type.html#1364" class="Bound">f</a><a id="1365" class="Symbol">)</a> <a id="1367" class="Symbol">=</a> <a id="1369" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="1373" href="foundation-core.identity-types.html#8440" class="Function">right-unit</a>
</pre>