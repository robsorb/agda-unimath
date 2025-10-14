# Idempotent elements in rings

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="ring-theory.idempotent-elements-rings.html" class="Module">ring-theory.idempotent-elements-rings</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

An idempotent element in a ring is an element `x` such that `x² = x`.

## Definition

<pre class="Agda"><a id="428" class="Keyword">module</a> <a id="435" href="ring-theory.idempotent-elements-rings.html#435" class="Module">_</a>
  <a id="439" class="Symbol">{</a><a id="440" href="ring-theory.idempotent-elements-rings.html#440" class="Bound">l</a> <a id="442" class="Symbol">:</a> <a id="444" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="449" class="Symbol">}</a> <a id="451" class="Symbol">(</a><a id="452" href="ring-theory.idempotent-elements-rings.html#452" class="Bound">R</a> <a id="454" class="Symbol">:</a> <a id="456" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="461" href="ring-theory.idempotent-elements-rings.html#440" class="Bound">l</a><a id="462" class="Symbol">)</a> <a id="464" class="Symbol">(</a><a id="465" href="ring-theory.idempotent-elements-rings.html#465" class="Bound">x</a> <a id="467" class="Symbol">:</a> <a id="469" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="479" href="ring-theory.idempotent-elements-rings.html#452" class="Bound">R</a><a id="480" class="Symbol">)</a>
  <a id="484" class="Keyword">where</a>

  <a id="493" href="ring-theory.idempotent-elements-rings.html#493" class="Function">is-idempotent-element-ring-Prop</a> <a id="525" class="Symbol">:</a> <a id="527" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="532" href="ring-theory.idempotent-elements-rings.html#440" class="Bound">l</a>
  <a id="536" href="ring-theory.idempotent-elements-rings.html#493" class="Function">is-idempotent-element-ring-Prop</a> <a id="568" class="Symbol">=</a> <a id="570" href="foundation-core.sets.html#1141" class="Function">Id-Prop</a> <a id="578" class="Symbol">(</a><a id="579" href="ring-theory.rings.html#2468" class="Function">set-Ring</a> <a id="588" href="ring-theory.idempotent-elements-rings.html#452" class="Bound">R</a><a id="589" class="Symbol">)</a> <a id="591" class="Symbol">(</a><a id="592" href="ring-theory.rings.html#10669" class="Function">mul-Ring</a> <a id="601" href="ring-theory.idempotent-elements-rings.html#452" class="Bound">R</a> <a id="603" href="ring-theory.idempotent-elements-rings.html#465" class="Bound">x</a> <a id="605" href="ring-theory.idempotent-elements-rings.html#465" class="Bound">x</a><a id="606" class="Symbol">)</a> <a id="608" href="ring-theory.idempotent-elements-rings.html#465" class="Bound">x</a>

  <a id="613" href="ring-theory.idempotent-elements-rings.html#613" class="Function">is-idempotent-element-Ring</a> <a id="640" class="Symbol">:</a> <a id="642" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="645" href="ring-theory.idempotent-elements-rings.html#440" class="Bound">l</a>
  <a id="649" href="ring-theory.idempotent-elements-rings.html#613" class="Function">is-idempotent-element-Ring</a> <a id="676" class="Symbol">=</a> <a id="678" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="688" href="ring-theory.idempotent-elements-rings.html#493" class="Function">is-idempotent-element-ring-Prop</a>

  <a id="723" href="ring-theory.idempotent-elements-rings.html#723" class="Function">is-prop-is-idempotent-element-Ring</a> <a id="758" class="Symbol">:</a> <a id="760" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="768" href="ring-theory.idempotent-elements-rings.html#613" class="Function">is-idempotent-element-Ring</a>
  <a id="797" href="ring-theory.idempotent-elements-rings.html#723" class="Function">is-prop-is-idempotent-element-Ring</a> <a id="832" class="Symbol">=</a>
    <a id="838" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="856" href="ring-theory.idempotent-elements-rings.html#493" class="Function">is-idempotent-element-ring-Prop</a>

<a id="idempotent-element-Ring"></a><a id="889" href="ring-theory.idempotent-elements-rings.html#889" class="Function">idempotent-element-Ring</a> <a id="913" class="Symbol">:</a>
  <a id="917" class="Symbol">{</a><a id="918" href="ring-theory.idempotent-elements-rings.html#918" class="Bound">l</a> <a id="920" class="Symbol">:</a> <a id="922" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="927" class="Symbol">}</a> <a id="929" class="Symbol">(</a><a id="930" href="ring-theory.idempotent-elements-rings.html#930" class="Bound">R</a> <a id="932" class="Symbol">:</a> <a id="934" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="939" href="ring-theory.idempotent-elements-rings.html#918" class="Bound">l</a><a id="940" class="Symbol">)</a> <a id="942" class="Symbol">→</a> <a id="944" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="947" href="ring-theory.idempotent-elements-rings.html#918" class="Bound">l</a>
<a id="949" href="ring-theory.idempotent-elements-rings.html#889" class="Function">idempotent-element-Ring</a> <a id="973" href="ring-theory.idempotent-elements-rings.html#973" class="Bound">R</a> <a id="975" class="Symbol">=</a> <a id="977" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="990" class="Symbol">(</a><a id="991" href="ring-theory.idempotent-elements-rings.html#493" class="Function">is-idempotent-element-ring-Prop</a> <a id="1023" href="ring-theory.idempotent-elements-rings.html#973" class="Bound">R</a><a id="1024" class="Symbol">)</a>

<a id="1027" class="Keyword">module</a> <a id="1034" href="ring-theory.idempotent-elements-rings.html#1034" class="Module">_</a>
  <a id="1038" class="Symbol">{</a><a id="1039" href="ring-theory.idempotent-elements-rings.html#1039" class="Bound">l</a> <a id="1041" class="Symbol">:</a> <a id="1043" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1048" class="Symbol">}</a> <a id="1050" class="Symbol">(</a><a id="1051" href="ring-theory.idempotent-elements-rings.html#1051" class="Bound">R</a> <a id="1053" class="Symbol">:</a> <a id="1055" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1060" href="ring-theory.idempotent-elements-rings.html#1039" class="Bound">l</a><a id="1061" class="Symbol">)</a> <a id="1063" class="Symbol">(</a><a id="1064" href="ring-theory.idempotent-elements-rings.html#1064" class="Bound">x</a> <a id="1066" class="Symbol">:</a> <a id="1068" href="ring-theory.idempotent-elements-rings.html#889" class="Function">idempotent-element-Ring</a> <a id="1092" href="ring-theory.idempotent-elements-rings.html#1051" class="Bound">R</a><a id="1093" class="Symbol">)</a>
  <a id="1097" class="Keyword">where</a>

  <a id="1106" href="ring-theory.idempotent-elements-rings.html#1106" class="Function">element-idempotent-element-Ring</a> <a id="1138" class="Symbol">:</a> <a id="1140" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="1150" href="ring-theory.idempotent-elements-rings.html#1051" class="Bound">R</a>
  <a id="1154" href="ring-theory.idempotent-elements-rings.html#1106" class="Function">element-idempotent-element-Ring</a> <a id="1186" class="Symbol">=</a>
    <a id="1192" href="foundation-core.subtypes.html#1842" class="Function">inclusion-subtype</a> <a id="1210" class="Symbol">(</a><a id="1211" href="ring-theory.idempotent-elements-rings.html#493" class="Function">is-idempotent-element-ring-Prop</a> <a id="1243" href="ring-theory.idempotent-elements-rings.html#1051" class="Bound">R</a><a id="1244" class="Symbol">)</a> <a id="1246" href="ring-theory.idempotent-elements-rings.html#1064" class="Bound">x</a>

  <a id="1251" href="ring-theory.idempotent-elements-rings.html#1251" class="Function">is-idempotent-element-idempotent-element-Ring</a> <a id="1297" class="Symbol">:</a>
    <a id="1303" href="ring-theory.idempotent-elements-rings.html#613" class="Function">is-idempotent-element-Ring</a> <a id="1330" href="ring-theory.idempotent-elements-rings.html#1051" class="Bound">R</a> <a id="1332" href="ring-theory.idempotent-elements-rings.html#1106" class="Function">element-idempotent-element-Ring</a>
  <a id="1366" href="ring-theory.idempotent-elements-rings.html#1251" class="Function">is-idempotent-element-idempotent-element-Ring</a> <a id="1412" class="Symbol">=</a>
    <a id="1418" href="foundation-core.subtypes.html#2071" class="Function">is-in-subtype-inclusion-subtype</a> <a id="1450" class="Symbol">(</a><a id="1451" href="ring-theory.idempotent-elements-rings.html#493" class="Function">is-idempotent-element-ring-Prop</a> <a id="1483" href="ring-theory.idempotent-elements-rings.html#1051" class="Bound">R</a><a id="1484" class="Symbol">)</a> <a id="1486" href="ring-theory.idempotent-elements-rings.html#1064" class="Bound">x</a>
</pre>