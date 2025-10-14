# Discrete dependent reflexive globular types

<pre class="Agda"><a id="56" class="Symbol">{-#</a> <a id="60" class="Keyword">OPTIONS</a> <a id="68" class="Pragma">--guardedness</a> <a id="82" class="Symbol">#-}</a>

<a id="87" class="Keyword">module</a> <a id="94" href="globular-types.discrete-dependent-reflexive-globular-types.html" class="Module">globular-types.discrete-dependent-reflexive-globular-types</a> <a id="153" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="globular-types.dependent-reflexive-globular-types.html" class="Module">globular-types.dependent-reflexive-globular-types</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="globular-types.discrete-reflexive-globular-types.html" class="Module">globular-types.discrete-reflexive-globular-types</a>
<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="globular-types.points-reflexive-globular-types.html" class="Module">globular-types.points-reflexive-globular-types</a>
<a id="431" class="Keyword">open</a> <a id="436" class="Keyword">import</a> <a id="443" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
</pre>
</details>

## Idea

A
[dependent reflexive globular type](globular-types.dependent-reflexive-globular-types.md)
`H` over a [reflexive globular type](globular-types.reflexive-globular-types.md)
`G` is said to be
{{#concept "discrete" Disambiguation="dependent reflexive globular type" Agda=is-discrete-Dependent-Reflexive-Globular-Type}}
if the reflexive globular type

```text
  ev-point H x
```

is [discrete](globular-types.discrete-reflexive-globular-types.md) for every
[point](globular-types.points-reflexive-globular-types.md) of `G`.

## Definitions

### The predicate of being a discrete dependent reflexive globular type

<pre class="Agda"><a id="1128" class="Keyword">module</a> <a id="1135" href="globular-types.discrete-dependent-reflexive-globular-types.html#1135" class="Module">_</a>
  <a id="1139" class="Symbol">{</a><a id="1140" href="globular-types.discrete-dependent-reflexive-globular-types.html#1140" class="Bound">l1</a> <a id="1143" href="globular-types.discrete-dependent-reflexive-globular-types.html#1143" class="Bound">l2</a> <a id="1146" href="globular-types.discrete-dependent-reflexive-globular-types.html#1146" class="Bound">l3</a> <a id="1149" href="globular-types.discrete-dependent-reflexive-globular-types.html#1149" class="Bound">l4</a> <a id="1152" class="Symbol">:</a> <a id="1154" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1159" class="Symbol">}</a> <a id="1161" class="Symbol">{</a><a id="1162" href="globular-types.discrete-dependent-reflexive-globular-types.html#1162" class="Bound">G</a> <a id="1164" class="Symbol">:</a> <a id="1166" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="1190" href="globular-types.discrete-dependent-reflexive-globular-types.html#1140" class="Bound">l1</a> <a id="1193" href="globular-types.discrete-dependent-reflexive-globular-types.html#1143" class="Bound">l2</a><a id="1195" class="Symbol">}</a>
  <a id="1199" class="Symbol">(</a><a id="1200" href="globular-types.discrete-dependent-reflexive-globular-types.html#1200" class="Bound">H</a> <a id="1202" class="Symbol">:</a> <a id="1204" href="globular-types.dependent-reflexive-globular-types.html#2123" class="Record">Dependent-Reflexive-Globular-Type</a> <a id="1238" href="globular-types.discrete-dependent-reflexive-globular-types.html#1146" class="Bound">l3</a> <a id="1241" href="globular-types.discrete-dependent-reflexive-globular-types.html#1149" class="Bound">l4</a> <a id="1244" href="globular-types.discrete-dependent-reflexive-globular-types.html#1162" class="Bound">G</a><a id="1245" class="Symbol">)</a>
  <a id="1249" class="Keyword">where</a>

  <a id="1258" href="globular-types.discrete-dependent-reflexive-globular-types.html#1258" class="Function">is-discrete-Dependent-Reflexive-Globular-Type</a> <a id="1304" class="Symbol">:</a> <a id="1306" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1309" class="Symbol">(</a><a id="1310" href="globular-types.discrete-dependent-reflexive-globular-types.html#1140" class="Bound">l1</a> <a id="1313" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1315" href="globular-types.discrete-dependent-reflexive-globular-types.html#1146" class="Bound">l3</a> <a id="1318" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1320" href="globular-types.discrete-dependent-reflexive-globular-types.html#1149" class="Bound">l4</a><a id="1322" class="Symbol">)</a>
  <a id="1326" href="globular-types.discrete-dependent-reflexive-globular-types.html#1258" class="Function">is-discrete-Dependent-Reflexive-Globular-Type</a> <a id="1372" class="Symbol">=</a>
    <a id="1378" class="Symbol">(</a><a id="1379" href="globular-types.discrete-dependent-reflexive-globular-types.html#1379" class="Bound">x</a> <a id="1381" class="Symbol">:</a> <a id="1383" href="globular-types.points-reflexive-globular-types.html#1331" class="Function">point-Reflexive-Globular-Type</a> <a id="1413" href="globular-types.discrete-dependent-reflexive-globular-types.html#1162" class="Bound">G</a><a id="1414" class="Symbol">)</a> <a id="1416" class="Symbol">→</a>
    <a id="1422" href="globular-types.discrete-reflexive-globular-types.html#1479" class="Record">is-discrete-Reflexive-Globular-Type</a>
      <a id="1464" class="Symbol">(</a> <a id="1466" href="globular-types.dependent-reflexive-globular-types.html#9680" class="Function">ev-point-Dependent-Reflexive-Globular-Type</a> <a id="1509" href="globular-types.discrete-dependent-reflexive-globular-types.html#1200" class="Bound">H</a> <a id="1511" href="globular-types.discrete-dependent-reflexive-globular-types.html#1379" class="Bound">x</a><a id="1512" class="Symbol">)</a>
</pre>