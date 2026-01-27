# Disjoint subtypes

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="foundation.disjoint-subtypes.html" class="Module">foundation.disjoint-subtypes</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="213" class="Keyword">open</a> <a id="218" class="Keyword">import</a> <a id="225" href="foundation.empty-subtypes.html" class="Module">foundation.empty-subtypes</a>
<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation.intersections-subtypes.html" class="Module">foundation.intersections-subtypes</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Two [subtypes](foundation-core.subtypes.md) are
{{#concept "disjoint" WDID=Q215382 WD="disjoint sets" Agda=disjoint-subtype}} if
their [intersection](foundation.intersections-subtypes.md) is
[empty](foundation.empty-subtypes.md).

## Definition

<pre class="Agda"><a id="719" class="Keyword">module</a> <a id="726" href="foundation.disjoint-subtypes.html#726" class="Module">_</a>
  <a id="730" class="Symbol">{</a><a id="731" href="foundation.disjoint-subtypes.html#731" class="Bound">l1</a> <a id="734" href="foundation.disjoint-subtypes.html#734" class="Bound">l2</a> <a id="737" href="foundation.disjoint-subtypes.html#737" class="Bound">l3</a> <a id="740" class="Symbol">:</a> <a id="742" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="747" class="Symbol">}</a> <a id="749" class="Symbol">{</a><a id="750" href="foundation.disjoint-subtypes.html#750" class="Bound">A</a> <a id="752" class="Symbol">:</a> <a id="754" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="757" href="foundation.disjoint-subtypes.html#731" class="Bound">l1</a><a id="759" class="Symbol">}</a> <a id="761" class="Symbol">(</a><a id="762" href="foundation.disjoint-subtypes.html#762" class="Bound">B</a> <a id="764" class="Symbol">:</a> <a id="766" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="774" href="foundation.disjoint-subtypes.html#734" class="Bound">l2</a> <a id="777" href="foundation.disjoint-subtypes.html#750" class="Bound">A</a><a id="778" class="Symbol">)</a> <a id="780" class="Symbol">(</a><a id="781" href="foundation.disjoint-subtypes.html#781" class="Bound">C</a> <a id="783" class="Symbol">:</a> <a id="785" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="793" href="foundation.disjoint-subtypes.html#737" class="Bound">l3</a> <a id="796" href="foundation.disjoint-subtypes.html#750" class="Bound">A</a><a id="797" class="Symbol">)</a>
  <a id="801" class="Keyword">where</a>

  <a id="810" href="foundation.disjoint-subtypes.html#810" class="Function">disjoint-subtype-Prop</a> <a id="832" class="Symbol">:</a> <a id="834" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="839" class="Symbol">(</a><a id="840" href="foundation.disjoint-subtypes.html#731" class="Bound">l1</a> <a id="843" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="845" href="foundation.disjoint-subtypes.html#734" class="Bound">l2</a> <a id="848" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="850" href="foundation.disjoint-subtypes.html#737" class="Bound">l3</a><a id="852" class="Symbol">)</a>
  <a id="856" href="foundation.disjoint-subtypes.html#810" class="Function">disjoint-subtype-Prop</a> <a id="878" class="Symbol">=</a> <a id="880" href="foundation.empty-subtypes.html#1084" class="Function">is-empty-prop-subtype</a> <a id="902" class="Symbol">(</a><a id="903" href="foundation.intersections-subtypes.html#1281" class="Function">intersection-subtype</a> <a id="924" href="foundation.disjoint-subtypes.html#762" class="Bound">B</a> <a id="926" href="foundation.disjoint-subtypes.html#781" class="Bound">C</a><a id="927" class="Symbol">)</a>

  <a id="932" href="foundation.disjoint-subtypes.html#932" class="Function">disjoint-subtype</a> <a id="949" class="Symbol">:</a> <a id="951" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="954" class="Symbol">(</a><a id="955" href="foundation.disjoint-subtypes.html#731" class="Bound">l1</a> <a id="958" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="960" href="foundation.disjoint-subtypes.html#734" class="Bound">l2</a> <a id="963" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="965" href="foundation.disjoint-subtypes.html#737" class="Bound">l3</a><a id="967" class="Symbol">)</a>
  <a id="971" href="foundation.disjoint-subtypes.html#932" class="Function">disjoint-subtype</a> <a id="988" class="Symbol">=</a> <a id="990" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1000" href="foundation.disjoint-subtypes.html#810" class="Function">disjoint-subtype-Prop</a>
</pre>
## Properties

### A subtype disjoint from itself is empty

<pre class="Agda"><a id="1095" class="Keyword">module</a> <a id="1102" href="foundation.disjoint-subtypes.html#1102" class="Module">_</a>
  <a id="1106" class="Symbol">{</a><a id="1107" href="foundation.disjoint-subtypes.html#1107" class="Bound">l1</a> <a id="1110" href="foundation.disjoint-subtypes.html#1110" class="Bound">l2</a> <a id="1113" class="Symbol">:</a> <a id="1115" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1120" class="Symbol">}</a> <a id="1122" class="Symbol">{</a><a id="1123" href="foundation.disjoint-subtypes.html#1123" class="Bound">A</a> <a id="1125" class="Symbol">:</a> <a id="1127" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1130" href="foundation.disjoint-subtypes.html#1107" class="Bound">l1</a><a id="1132" class="Symbol">}</a> <a id="1134" class="Symbol">(</a><a id="1135" href="foundation.disjoint-subtypes.html#1135" class="Bound">B</a> <a id="1137" class="Symbol">:</a> <a id="1139" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="1147" href="foundation.disjoint-subtypes.html#1110" class="Bound">l2</a> <a id="1150" href="foundation.disjoint-subtypes.html#1123" class="Bound">A</a><a id="1151" class="Symbol">)</a>
  <a id="1155" class="Keyword">where</a>

  <a id="1164" href="foundation.disjoint-subtypes.html#1164" class="Function">is-empty-disjoint-subtype-self</a> <a id="1195" class="Symbol">:</a>
    <a id="1201" href="foundation.disjoint-subtypes.html#932" class="Function">disjoint-subtype</a> <a id="1218" href="foundation.disjoint-subtypes.html#1135" class="Bound">B</a> <a id="1220" href="foundation.disjoint-subtypes.html#1135" class="Bound">B</a> <a id="1222" class="Symbol">→</a> <a id="1224" href="foundation-core.empty-types.html#972" class="Function">is-empty</a> <a id="1233" class="Symbol">(</a><a id="1234" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="1247" href="foundation.disjoint-subtypes.html#1135" class="Bound">B</a><a id="1248" class="Symbol">)</a>
  <a id="1252" href="foundation.disjoint-subtypes.html#1164" class="Function">is-empty-disjoint-subtype-self</a> <a id="1283" href="foundation.disjoint-subtypes.html#1283" class="Bound">H</a> <a id="1285" class="Symbol">(</a><a id="1286" href="foundation.disjoint-subtypes.html#1286" class="Bound">b</a> <a id="1288" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1290" href="foundation.disjoint-subtypes.html#1290" class="Bound">b∈B</a><a id="1293" class="Symbol">)</a> <a id="1295" class="Symbol">=</a> <a id="1297" href="foundation.disjoint-subtypes.html#1283" class="Bound">H</a> <a id="1299" href="foundation.disjoint-subtypes.html#1286" class="Bound">b</a> <a id="1301" class="Symbol">(</a><a id="1302" href="foundation.disjoint-subtypes.html#1290" class="Bound">b∈B</a> <a id="1306" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1308" href="foundation.disjoint-subtypes.html#1290" class="Bound">b∈B</a><a id="1311" class="Symbol">)</a>
</pre>
## See also

- [Exclusive sums](foundation.exclusive-sum.md)
