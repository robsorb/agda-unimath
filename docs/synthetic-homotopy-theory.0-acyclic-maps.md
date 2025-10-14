# `0`-acyclic maps

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="synthetic-homotopy-theory.0-acyclic-maps.html" class="Module">synthetic-homotopy-theory.0-acyclic-maps</a> <a id="77" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="133" class="Keyword">open</a> <a id="138" class="Keyword">import</a> <a id="145" href="foundation.epimorphisms-with-respect-to-sets.html" class="Module">foundation.epimorphisms-with-respect-to-sets</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="306" class="Keyword">open</a> <a id="311" class="Keyword">import</a> <a id="318" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="346" class="Keyword">open</a> <a id="351" class="Keyword">import</a> <a id="358" href="synthetic-homotopy-theory.truncated-acyclic-maps.html" class="Module">synthetic-homotopy-theory.truncated-acyclic-maps</a>
</pre>
</details>

## Idea

A **`0`-acyclic map** is a map whose [fibers](foundation-core.fibers-of-maps.md)
are [`0`-acyclic types](synthetic-homotopy-theory.0-acyclic-types.md), meaning
that their [suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`0`-connected](foundation.0-connected-types.md).

We can characterize the `0`-acyclic maps as the
[surjective maps](foundation.surjective-maps.md).

## Definition

### The predicate of being a `0`-acyclic map

<pre class="Agda"><a id="890" class="Keyword">module</a> <a id="897" href="synthetic-homotopy-theory.0-acyclic-maps.html#897" class="Module">_</a>
  <a id="901" class="Symbol">{</a><a id="902" href="synthetic-homotopy-theory.0-acyclic-maps.html#902" class="Bound">l1</a> <a id="905" href="synthetic-homotopy-theory.0-acyclic-maps.html#905" class="Bound">l2</a> <a id="908" class="Symbol">:</a> <a id="910" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="915" class="Symbol">}</a> <a id="917" class="Symbol">{</a><a id="918" href="synthetic-homotopy-theory.0-acyclic-maps.html#918" class="Bound">A</a> <a id="920" class="Symbol">:</a> <a id="922" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="925" href="synthetic-homotopy-theory.0-acyclic-maps.html#902" class="Bound">l1</a><a id="927" class="Symbol">}</a> <a id="929" class="Symbol">{</a><a id="930" href="synthetic-homotopy-theory.0-acyclic-maps.html#930" class="Bound">B</a> <a id="932" class="Symbol">:</a> <a id="934" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="937" href="synthetic-homotopy-theory.0-acyclic-maps.html#905" class="Bound">l2</a><a id="939" class="Symbol">}</a>
  <a id="943" class="Keyword">where</a>

  <a id="952" href="synthetic-homotopy-theory.0-acyclic-maps.html#952" class="Function">is-0-acyclic-map-Prop</a> <a id="974" class="Symbol">:</a> <a id="976" class="Symbol">(</a><a id="977" href="synthetic-homotopy-theory.0-acyclic-maps.html#918" class="Bound">A</a> <a id="979" class="Symbol">→</a> <a id="981" href="synthetic-homotopy-theory.0-acyclic-maps.html#930" class="Bound">B</a><a id="982" class="Symbol">)</a> <a id="984" class="Symbol">→</a> <a id="986" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="991" class="Symbol">(</a><a id="992" href="synthetic-homotopy-theory.0-acyclic-maps.html#902" class="Bound">l1</a> <a id="995" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="997" href="synthetic-homotopy-theory.0-acyclic-maps.html#905" class="Bound">l2</a><a id="999" class="Symbol">)</a>
  <a id="1003" href="synthetic-homotopy-theory.0-acyclic-maps.html#952" class="Function">is-0-acyclic-map-Prop</a> <a id="1025" class="Symbol">=</a> <a id="1027" href="synthetic-homotopy-theory.truncated-acyclic-maps.html#2709" class="Function">is-truncated-acyclic-map-Prop</a> <a id="1057" class="Symbol">(</a><a id="1058" href="foundation-core.truncation-levels.html#672" class="Function">zero-𝕋</a><a id="1064" class="Symbol">)</a>

  <a id="1069" href="synthetic-homotopy-theory.0-acyclic-maps.html#1069" class="Function">is-0-acyclic-map</a> <a id="1086" class="Symbol">:</a> <a id="1088" class="Symbol">(</a><a id="1089" href="synthetic-homotopy-theory.0-acyclic-maps.html#918" class="Bound">A</a> <a id="1091" class="Symbol">→</a> <a id="1093" href="synthetic-homotopy-theory.0-acyclic-maps.html#930" class="Bound">B</a><a id="1094" class="Symbol">)</a> <a id="1096" class="Symbol">→</a> <a id="1098" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1101" class="Symbol">(</a><a id="1102" href="synthetic-homotopy-theory.0-acyclic-maps.html#902" class="Bound">l1</a> <a id="1105" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1107" href="synthetic-homotopy-theory.0-acyclic-maps.html#905" class="Bound">l2</a><a id="1109" class="Symbol">)</a>
  <a id="1113" href="synthetic-homotopy-theory.0-acyclic-maps.html#1069" class="Function">is-0-acyclic-map</a> <a id="1130" href="synthetic-homotopy-theory.0-acyclic-maps.html#1130" class="Bound">f</a> <a id="1132" class="Symbol">=</a> <a id="1134" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1144" class="Symbol">(</a><a id="1145" href="synthetic-homotopy-theory.0-acyclic-maps.html#952" class="Function">is-0-acyclic-map-Prop</a> <a id="1167" href="synthetic-homotopy-theory.0-acyclic-maps.html#1130" class="Bound">f</a><a id="1168" class="Symbol">)</a>

  <a id="1173" href="synthetic-homotopy-theory.0-acyclic-maps.html#1173" class="Function">is-prop-is-0-acyclic-map</a> <a id="1198" class="Symbol">:</a>
    <a id="1204" class="Symbol">(</a><a id="1205" href="synthetic-homotopy-theory.0-acyclic-maps.html#1205" class="Bound">f</a> <a id="1207" class="Symbol">:</a> <a id="1209" href="synthetic-homotopy-theory.0-acyclic-maps.html#918" class="Bound">A</a> <a id="1211" class="Symbol">→</a> <a id="1213" href="synthetic-homotopy-theory.0-acyclic-maps.html#930" class="Bound">B</a><a id="1214" class="Symbol">)</a> <a id="1216" class="Symbol">→</a> <a id="1218" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1226" class="Symbol">(</a><a id="1227" href="synthetic-homotopy-theory.0-acyclic-maps.html#1069" class="Function">is-0-acyclic-map</a> <a id="1244" href="synthetic-homotopy-theory.0-acyclic-maps.html#1205" class="Bound">f</a><a id="1245" class="Symbol">)</a>
  <a id="1249" href="synthetic-homotopy-theory.0-acyclic-maps.html#1173" class="Function">is-prop-is-0-acyclic-map</a> <a id="1274" href="synthetic-homotopy-theory.0-acyclic-maps.html#1274" class="Bound">f</a> <a id="1276" class="Symbol">=</a>
    <a id="1282" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1300" class="Symbol">(</a><a id="1301" href="synthetic-homotopy-theory.0-acyclic-maps.html#952" class="Function">is-0-acyclic-map-Prop</a> <a id="1323" href="synthetic-homotopy-theory.0-acyclic-maps.html#1274" class="Bound">f</a><a id="1324" class="Symbol">)</a>
</pre>
## Properties

### A map is `0`-acyclic if and only if it is surjective

<pre class="Agda"><a id="1412" class="Keyword">module</a> <a id="1419" href="synthetic-homotopy-theory.0-acyclic-maps.html#1419" class="Module">_</a>
  <a id="1423" class="Symbol">{</a><a id="1424" href="synthetic-homotopy-theory.0-acyclic-maps.html#1424" class="Bound">l1</a> <a id="1427" href="synthetic-homotopy-theory.0-acyclic-maps.html#1427" class="Bound">l2</a> <a id="1430" class="Symbol">:</a> <a id="1432" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1437" class="Symbol">}</a> <a id="1439" class="Symbol">{</a><a id="1440" href="synthetic-homotopy-theory.0-acyclic-maps.html#1440" class="Bound">A</a> <a id="1442" class="Symbol">:</a> <a id="1444" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1447" href="synthetic-homotopy-theory.0-acyclic-maps.html#1424" class="Bound">l1</a><a id="1449" class="Symbol">}</a> <a id="1451" class="Symbol">{</a><a id="1452" href="synthetic-homotopy-theory.0-acyclic-maps.html#1452" class="Bound">B</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1459" href="synthetic-homotopy-theory.0-acyclic-maps.html#1427" class="Bound">l2</a><a id="1461" class="Symbol">}</a> <a id="1463" class="Symbol">(</a><a id="1464" href="synthetic-homotopy-theory.0-acyclic-maps.html#1464" class="Bound">f</a> <a id="1466" class="Symbol">:</a> <a id="1468" href="synthetic-homotopy-theory.0-acyclic-maps.html#1440" class="Bound">A</a> <a id="1470" class="Symbol">→</a> <a id="1472" href="synthetic-homotopy-theory.0-acyclic-maps.html#1452" class="Bound">B</a><a id="1473" class="Symbol">)</a>
  <a id="1477" class="Keyword">where</a>

  <a id="1486" href="synthetic-homotopy-theory.0-acyclic-maps.html#1486" class="Function">is-surjective-is-0-acyclic-map</a> <a id="1517" class="Symbol">:</a>
    <a id="1523" href="synthetic-homotopy-theory.0-acyclic-maps.html#1069" class="Function">is-0-acyclic-map</a> <a id="1540" href="synthetic-homotopy-theory.0-acyclic-maps.html#1464" class="Bound">f</a> <a id="1542" class="Symbol">→</a> <a id="1544" href="foundation.surjective-maps.html#2524" class="Function">is-surjective</a> <a id="1558" href="synthetic-homotopy-theory.0-acyclic-maps.html#1464" class="Bound">f</a>
  <a id="1562" href="synthetic-homotopy-theory.0-acyclic-maps.html#1486" class="Function">is-surjective-is-0-acyclic-map</a> <a id="1593" href="synthetic-homotopy-theory.0-acyclic-maps.html#1593" class="Bound">ac</a> <a id="1596" class="Symbol">=</a>
    <a id="1602" href="foundation.epimorphisms-with-respect-to-sets.html#2223" class="Function">is-surjective-is-epimorphism-Set</a>
      <a id="1641" class="Symbol">(</a> <a id="1643" href="synthetic-homotopy-theory.truncated-acyclic-maps.html#3877" class="Function">is-epimorphism-is-truncated-acyclic-map-Truncated-Type</a> <a id="1698" href="synthetic-homotopy-theory.0-acyclic-maps.html#1464" class="Bound">f</a> <a id="1700" href="synthetic-homotopy-theory.0-acyclic-maps.html#1593" class="Bound">ac</a><a id="1702" class="Symbol">)</a>

  <a id="1707" href="synthetic-homotopy-theory.0-acyclic-maps.html#1707" class="Function">is-0-acyclic-map-is-surjective</a> <a id="1738" class="Symbol">:</a>
    <a id="1744" href="foundation.surjective-maps.html#2524" class="Function">is-surjective</a> <a id="1758" href="synthetic-homotopy-theory.0-acyclic-maps.html#1464" class="Bound">f</a> <a id="1760" class="Symbol">→</a> <a id="1762" href="synthetic-homotopy-theory.0-acyclic-maps.html#1069" class="Function">is-0-acyclic-map</a> <a id="1779" href="synthetic-homotopy-theory.0-acyclic-maps.html#1464" class="Bound">f</a>
  <a id="1783" href="synthetic-homotopy-theory.0-acyclic-maps.html#1707" class="Function">is-0-acyclic-map-is-surjective</a> <a id="1814" href="synthetic-homotopy-theory.0-acyclic-maps.html#1814" class="Bound">s</a> <a id="1816" class="Symbol">=</a>
    <a id="1822" href="synthetic-homotopy-theory.truncated-acyclic-maps.html#3530" class="Function">is-truncated-acyclic-map-is-epimorphism-Truncated-Type</a> <a id="1877" href="synthetic-homotopy-theory.0-acyclic-maps.html#1464" class="Bound">f</a>
      <a id="1885" class="Symbol">(</a> <a id="1887" href="foundation.epimorphisms-with-respect-to-sets.html#1570" class="Function">is-epimorphism-is-surjective-Set</a> <a id="1920" href="synthetic-homotopy-theory.0-acyclic-maps.html#1814" class="Bound">s</a><a id="1921" class="Symbol">)</a>
</pre>
## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
