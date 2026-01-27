# Base change of dependent directed graphs

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="graph-theory.base-change-dependent-directed-graphs.html" class="Module">graph-theory.base-change-dependent-directed-graphs</a> <a id="111" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="graph-theory.dependent-directed-graphs.html" class="Module">graph-theory.dependent-directed-graphs</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="graph-theory.morphisms-directed-graphs.html" class="Module">graph-theory.morphisms-directed-graphs</a>
</pre>
</details>

## Idea

Consider a [dependent directed graph](graph-theory.dependent-directed-graphs.md)
`B` over a [directed graph](graph-theory.directed-graphs.md) `A`, and consider a
[graph homomorphism](graph-theory.morphisms-directed-graphs.md) `f : C → A`. The
{{#concept "base change" Disambiguation="dependent directed graphs" Agda=base-change-Dependent-Directed-Graph}}
`f*B` of `B` along `f` is defined by substituting the values of `f` into `B`.
More precisely, `f*B` is defined by

```text
  (f*B)₀ c := B₀ (f₀ c)
  (f*B)₁ e := B₁ (f₁ e).
```

## Definitions

### Base change of dependent directed graphs

<pre class="Agda"><a id="1022" class="Keyword">module</a> <a id="1029" href="graph-theory.base-change-dependent-directed-graphs.html#1029" class="Module">_</a>
  <a id="1033" class="Symbol">{</a><a id="1034" href="graph-theory.base-change-dependent-directed-graphs.html#1034" class="Bound">l1</a> <a id="1037" href="graph-theory.base-change-dependent-directed-graphs.html#1037" class="Bound">l2</a> <a id="1040" href="graph-theory.base-change-dependent-directed-graphs.html#1040" class="Bound">l3</a> <a id="1043" href="graph-theory.base-change-dependent-directed-graphs.html#1043" class="Bound">l4</a> <a id="1046" href="graph-theory.base-change-dependent-directed-graphs.html#1046" class="Bound">l5</a> <a id="1049" href="graph-theory.base-change-dependent-directed-graphs.html#1049" class="Bound">l6</a> <a id="1052" class="Symbol">:</a> <a id="1054" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1059" class="Symbol">}</a>
  <a id="1063" class="Symbol">{</a><a id="1064" href="graph-theory.base-change-dependent-directed-graphs.html#1064" class="Bound">A</a> <a id="1066" class="Symbol">:</a> <a id="1068" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="1083" href="graph-theory.base-change-dependent-directed-graphs.html#1034" class="Bound">l1</a> <a id="1086" href="graph-theory.base-change-dependent-directed-graphs.html#1037" class="Bound">l2</a><a id="1088" class="Symbol">}</a>
  <a id="1092" class="Symbol">(</a><a id="1093" href="graph-theory.base-change-dependent-directed-graphs.html#1093" class="Bound">C</a> <a id="1095" class="Symbol">:</a> <a id="1097" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="1112" href="graph-theory.base-change-dependent-directed-graphs.html#1040" class="Bound">l3</a> <a id="1115" href="graph-theory.base-change-dependent-directed-graphs.html#1043" class="Bound">l4</a><a id="1117" class="Symbol">)</a> <a id="1119" class="Symbol">(</a><a id="1120" href="graph-theory.base-change-dependent-directed-graphs.html#1120" class="Bound">f</a> <a id="1122" class="Symbol">:</a> <a id="1124" href="graph-theory.morphisms-directed-graphs.html#1225" class="Function">hom-Directed-Graph</a> <a id="1143" href="graph-theory.base-change-dependent-directed-graphs.html#1093" class="Bound">C</a> <a id="1145" href="graph-theory.base-change-dependent-directed-graphs.html#1064" class="Bound">A</a><a id="1146" class="Symbol">)</a>
  <a id="1150" class="Symbol">(</a><a id="1151" href="graph-theory.base-change-dependent-directed-graphs.html#1151" class="Bound">B</a> <a id="1153" class="Symbol">:</a> <a id="1155" href="graph-theory.dependent-directed-graphs.html#1231" class="Function">Dependent-Directed-Graph</a> <a id="1180" href="graph-theory.base-change-dependent-directed-graphs.html#1046" class="Bound">l5</a> <a id="1183" href="graph-theory.base-change-dependent-directed-graphs.html#1049" class="Bound">l6</a> <a id="1186" href="graph-theory.base-change-dependent-directed-graphs.html#1064" class="Bound">A</a><a id="1187" class="Symbol">)</a>
  <a id="1191" class="Keyword">where</a>

  <a id="1200" href="graph-theory.base-change-dependent-directed-graphs.html#1200" class="Function">vertex-base-change-Dependent-Directed-Graph</a> <a id="1244" class="Symbol">:</a>
    <a id="1250" class="Symbol">(</a><a id="1251" href="graph-theory.base-change-dependent-directed-graphs.html#1251" class="Bound">c</a> <a id="1253" class="Symbol">:</a> <a id="1255" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1277" href="graph-theory.base-change-dependent-directed-graphs.html#1093" class="Bound">C</a><a id="1278" class="Symbol">)</a> <a id="1280" class="Symbol">→</a> <a id="1282" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1285" href="graph-theory.base-change-dependent-directed-graphs.html#1046" class="Bound">l5</a>
  <a id="1290" href="graph-theory.base-change-dependent-directed-graphs.html#1200" class="Function">vertex-base-change-Dependent-Directed-Graph</a> <a id="1334" href="graph-theory.base-change-dependent-directed-graphs.html#1334" class="Bound">c</a> <a id="1336" class="Symbol">=</a>
    <a id="1342" href="graph-theory.dependent-directed-graphs.html#1647" class="Function">vertex-Dependent-Directed-Graph</a> <a id="1374" href="graph-theory.base-change-dependent-directed-graphs.html#1151" class="Bound">B</a> <a id="1376" class="Symbol">(</a><a id="1377" href="graph-theory.morphisms-directed-graphs.html#1534" class="Function">vertex-hom-Directed-Graph</a> <a id="1403" href="graph-theory.base-change-dependent-directed-graphs.html#1093" class="Bound">C</a> <a id="1405" href="graph-theory.base-change-dependent-directed-graphs.html#1064" class="Bound">A</a> <a id="1407" href="graph-theory.base-change-dependent-directed-graphs.html#1120" class="Bound">f</a> <a id="1409" href="graph-theory.base-change-dependent-directed-graphs.html#1334" class="Bound">c</a><a id="1410" class="Symbol">)</a>

  <a id="1415" href="graph-theory.base-change-dependent-directed-graphs.html#1415" class="Function">edge-base-change-Dependent-Directed-Graph</a> <a id="1457" class="Symbol">:</a>
    <a id="1463" class="Symbol">{</a><a id="1464" href="graph-theory.base-change-dependent-directed-graphs.html#1464" class="Bound">x</a> <a id="1466" href="graph-theory.base-change-dependent-directed-graphs.html#1466" class="Bound">y</a> <a id="1468" class="Symbol">:</a> <a id="1470" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1492" href="graph-theory.base-change-dependent-directed-graphs.html#1093" class="Bound">C</a><a id="1493" class="Symbol">}</a> <a id="1495" class="Symbol">(</a><a id="1496" href="graph-theory.base-change-dependent-directed-graphs.html#1496" class="Bound">e</a> <a id="1498" class="Symbol">:</a> <a id="1500" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="1520" href="graph-theory.base-change-dependent-directed-graphs.html#1093" class="Bound">C</a> <a id="1522" href="graph-theory.base-change-dependent-directed-graphs.html#1464" class="Bound">x</a> <a id="1524" href="graph-theory.base-change-dependent-directed-graphs.html#1466" class="Bound">y</a><a id="1525" class="Symbol">)</a> <a id="1527" class="Symbol">→</a>
    <a id="1533" href="graph-theory.base-change-dependent-directed-graphs.html#1200" class="Function">vertex-base-change-Dependent-Directed-Graph</a> <a id="1577" href="graph-theory.base-change-dependent-directed-graphs.html#1464" class="Bound">x</a> <a id="1579" class="Symbol">→</a>
    <a id="1585" href="graph-theory.base-change-dependent-directed-graphs.html#1200" class="Function">vertex-base-change-Dependent-Directed-Graph</a> <a id="1629" href="graph-theory.base-change-dependent-directed-graphs.html#1466" class="Bound">y</a> <a id="1631" class="Symbol">→</a> <a id="1633" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1636" href="graph-theory.base-change-dependent-directed-graphs.html#1049" class="Bound">l6</a>
  <a id="1641" href="graph-theory.base-change-dependent-directed-graphs.html#1415" class="Function">edge-base-change-Dependent-Directed-Graph</a> <a id="1683" href="graph-theory.base-change-dependent-directed-graphs.html#1683" class="Bound">e</a> <a id="1685" class="Symbol">=</a>
    <a id="1691" href="graph-theory.dependent-directed-graphs.html#1758" class="Function">edge-Dependent-Directed-Graph</a> <a id="1721" href="graph-theory.base-change-dependent-directed-graphs.html#1151" class="Bound">B</a> <a id="1723" class="Symbol">(</a><a id="1724" href="graph-theory.morphisms-directed-graphs.html#1661" class="Function">edge-hom-Directed-Graph</a> <a id="1748" href="graph-theory.base-change-dependent-directed-graphs.html#1093" class="Bound">C</a> <a id="1750" href="graph-theory.base-change-dependent-directed-graphs.html#1064" class="Bound">A</a> <a id="1752" href="graph-theory.base-change-dependent-directed-graphs.html#1120" class="Bound">f</a> <a id="1754" href="graph-theory.base-change-dependent-directed-graphs.html#1683" class="Bound">e</a><a id="1755" class="Symbol">)</a>

  <a id="1760" href="graph-theory.base-change-dependent-directed-graphs.html#1760" class="Function">base-change-Dependent-Directed-Graph</a> <a id="1797" class="Symbol">:</a>
    <a id="1803" href="graph-theory.dependent-directed-graphs.html#1231" class="Function">Dependent-Directed-Graph</a> <a id="1828" href="graph-theory.base-change-dependent-directed-graphs.html#1046" class="Bound">l5</a> <a id="1831" href="graph-theory.base-change-dependent-directed-graphs.html#1049" class="Bound">l6</a> <a id="1834" href="graph-theory.base-change-dependent-directed-graphs.html#1093" class="Bound">C</a>
  <a id="1838" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1842" href="graph-theory.base-change-dependent-directed-graphs.html#1760" class="Function">base-change-Dependent-Directed-Graph</a> <a id="1879" class="Symbol">=</a>
    <a id="1885" href="graph-theory.base-change-dependent-directed-graphs.html#1200" class="Function">vertex-base-change-Dependent-Directed-Graph</a>
  <a id="1931" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1935" href="graph-theory.base-change-dependent-directed-graphs.html#1760" class="Function">base-change-Dependent-Directed-Graph</a> <a id="1972" class="Symbol">_</a> <a id="1974" class="Symbol">_</a> <a id="1976" class="Symbol">=</a>
    <a id="1982" href="graph-theory.base-change-dependent-directed-graphs.html#1415" class="Function">edge-base-change-Dependent-Directed-Graph</a>
</pre>