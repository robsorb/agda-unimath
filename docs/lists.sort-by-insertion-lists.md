# Sort by insertion for lists

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="lists.sort-by-insertion-lists.html" class="Module">lists.sort-by-insertion-lists</a> <a id="77" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="133" class="Keyword">open</a> <a id="138" class="Keyword">import</a> <a id="145" href="finite-group-theory.permutations-standard-finite-types.html" class="Module">finite-group-theory.permutations-standard-finite-types</a>

<a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="lists.arrays.html" class="Module">lists.arrays</a>
<a id="348" class="Keyword">open</a> <a id="353" class="Keyword">import</a> <a id="360" href="lists.lists.html" class="Module">lists.lists</a>
<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="lists.permutation-lists.html" class="Module">lists.permutation-lists</a>
<a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="lists.sort-by-insertion-tuples.html" class="Module">lists.sort-by-insertion-tuples</a>
<a id="451" class="Keyword">open</a> <a id="456" class="Keyword">import</a> <a id="463" href="lists.sorted-lists.html" class="Module">lists.sorted-lists</a>
<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="lists.sorting-algorithms-lists.html" class="Module">lists.sorting-algorithms-lists</a>

<a id="526" class="Keyword">open</a> <a id="531" class="Keyword">import</a> <a id="538" href="order-theory.decidable-total-orders.html" class="Module">order-theory.decidable-total-orders</a>
</pre>
</details>

## Idea

We use the definition of sort by insertion for tuples
([`lists.sort-by-insertion-tuples`](lists.sort-by-insertion-tuples.md)) and we
adapt it for lists.

## Definition

<pre class="Agda"><a id="777" class="Keyword">module</a> <a id="784" href="lists.sort-by-insertion-lists.html#784" class="Module">_</a>
  <a id="788" class="Symbol">{</a><a id="789" href="lists.sort-by-insertion-lists.html#789" class="Bound">l1</a> <a id="792" href="lists.sort-by-insertion-lists.html#792" class="Bound">l2</a> <a id="795" class="Symbol">:</a> <a id="797" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="802" class="Symbol">}</a> <a id="804" class="Symbol">(</a><a id="805" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a> <a id="807" class="Symbol">:</a> <a id="809" href="order-theory.decidable-total-orders.html#1986" class="Function">Decidable-Total-Order</a> <a id="831" href="lists.sort-by-insertion-lists.html#789" class="Bound">l1</a> <a id="834" href="lists.sort-by-insertion-lists.html#792" class="Bound">l2</a><a id="836" class="Symbol">)</a>
  <a id="840" class="Keyword">where</a>

  <a id="849" href="lists.sort-by-insertion-lists.html#849" class="Function">insertion-sort-list</a> <a id="869" class="Symbol">:</a>
    <a id="875" href="lists.lists.html#1328" class="Datatype">list</a> <a id="880" class="Symbol">(</a><a id="881" href="order-theory.decidable-total-orders.html#2759" class="Function">type-Decidable-Total-Order</a> <a id="908" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a><a id="909" class="Symbol">)</a> <a id="911" class="Symbol">→</a> <a id="913" href="lists.lists.html#1328" class="Datatype">list</a> <a id="918" class="Symbol">(</a><a id="919" href="order-theory.decidable-total-orders.html#2759" class="Function">type-Decidable-Total-Order</a> <a id="946" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a><a id="947" class="Symbol">)</a>
  <a id="951" href="lists.sort-by-insertion-lists.html#849" class="Function">insertion-sort-list</a> <a id="971" href="lists.sort-by-insertion-lists.html#971" class="Bound">l</a> <a id="973" class="Symbol">=</a>
    <a id="979" href="lists.arrays.html#2723" class="Function">list-tuple</a> <a id="990" class="Symbol">(</a><a id="991" href="lists.lists.html#2619" class="Function">length-list</a> <a id="1003" href="lists.sort-by-insertion-lists.html#971" class="Bound">l</a><a id="1004" class="Symbol">)</a> <a id="1006" class="Symbol">(</a><a id="1007" href="lists.sort-by-insertion-tuples.html#2017" class="Function">insertion-sort-tuple</a> <a id="1028" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a> <a id="1030" class="Symbol">(</a><a id="1031" href="lists.arrays.html#2856" class="Function">tuple-list</a> <a id="1042" href="lists.sort-by-insertion-lists.html#971" class="Bound">l</a><a id="1043" class="Symbol">))</a>
</pre>
## Properties

### Sort by insertion is a sort

<pre class="Agda">  <a id="1109" href="lists.sort-by-insertion-lists.html#1109" class="Function">is-sort-insertion-sort-list</a> <a id="1137" class="Symbol">:</a>
    <a id="1143" href="lists.sorting-algorithms-lists.html#1060" class="Function">is-sort-list</a> <a id="1156" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a> <a id="1158" href="lists.sort-by-insertion-lists.html#849" class="Function">insertion-sort-list</a>
  <a id="1180" href="lists.sort-by-insertion-lists.html#1109" class="Function">is-sort-insertion-sort-list</a> <a id="1208" class="Symbol">=</a>
    <a id="1214" href="lists.sorting-algorithms-lists.html#2250" class="Function">is-sort-list-is-sort-tuple</a>
      <a id="1247" class="Symbol">(</a> <a id="1249" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a><a id="1250" class="Symbol">)</a>
      <a id="1258" class="Symbol">(</a> <a id="1260" href="lists.sort-by-insertion-tuples.html#2017" class="Function">insertion-sort-tuple</a> <a id="1281" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a><a id="1282" class="Symbol">)</a>
      <a id="1290" class="Symbol">(</a> <a id="1292" href="lists.sort-by-insertion-tuples.html#11356" class="Function">is-sort-insertion-sort-tuple</a> <a id="1321" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a><a id="1322" class="Symbol">)</a>

  <a id="1327" href="lists.sort-by-insertion-lists.html#1327" class="Function">is-permutation-insertion-sort-list</a> <a id="1362" class="Symbol">:</a> <a id="1364" href="lists.permutation-lists.html#1456" class="Function">is-permutation-list</a> <a id="1384" href="lists.sort-by-insertion-lists.html#849" class="Function">insertion-sort-list</a>
  <a id="1406" href="lists.sort-by-insertion-lists.html#1327" class="Function">is-permutation-insertion-sort-list</a> <a id="1441" class="Symbol">=</a> <a id="1443" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1447" class="Symbol">(</a><a id="1448" href="lists.sort-by-insertion-lists.html#1109" class="Function">is-sort-insertion-sort-list</a><a id="1475" class="Symbol">)</a>

  <a id="1480" href="lists.sort-by-insertion-lists.html#1480" class="Function">permutation-insertion-sort-list</a> <a id="1512" class="Symbol">:</a>
    <a id="1518" class="Symbol">(</a><a id="1519" href="lists.sort-by-insertion-lists.html#1519" class="Bound">l</a> <a id="1521" class="Symbol">:</a> <a id="1523" href="lists.lists.html#1328" class="Datatype">list</a> <a id="1528" class="Symbol">(</a><a id="1529" href="order-theory.decidable-total-orders.html#2759" class="Function">type-Decidable-Total-Order</a> <a id="1556" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a><a id="1557" class="Symbol">))</a> <a id="1560" class="Symbol">→</a>
    <a id="1566" href="finite-group-theory.permutations-standard-finite-types.html#1586" class="Function">Permutation</a> <a id="1578" class="Symbol">(</a><a id="1579" href="lists.lists.html#2619" class="Function">length-list</a> <a id="1591" href="lists.sort-by-insertion-lists.html#1519" class="Bound">l</a><a id="1592" class="Symbol">)</a>
  <a id="1596" href="lists.sort-by-insertion-lists.html#1480" class="Function">permutation-insertion-sort-list</a> <a id="1628" class="Symbol">=</a>
    <a id="1634" href="lists.sorting-algorithms-lists.html#1335" class="Function">permutation-list-is-sort-list</a>
      <a id="1670" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a>
      <a id="1678" href="lists.sort-by-insertion-lists.html#849" class="Function">insertion-sort-list</a>
      <a id="1704" href="lists.sort-by-insertion-lists.html#1109" class="Function">is-sort-insertion-sort-list</a>

  <a id="1735" href="lists.sort-by-insertion-lists.html#1735" class="Function">eq-permute-list-permutation-insertion-sort-list</a> <a id="1783" class="Symbol">:</a>
    <a id="1789" class="Symbol">(</a><a id="1790" href="lists.sort-by-insertion-lists.html#1790" class="Bound">l</a> <a id="1792" class="Symbol">:</a> <a id="1794" href="lists.lists.html#1328" class="Datatype">list</a> <a id="1799" class="Symbol">(</a><a id="1800" href="order-theory.decidable-total-orders.html#2759" class="Function">type-Decidable-Total-Order</a> <a id="1827" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a><a id="1828" class="Symbol">))</a> <a id="1831" class="Symbol">→</a>
    <a id="1837" href="lists.sort-by-insertion-lists.html#849" class="Function">insertion-sort-list</a> <a id="1857" href="lists.sort-by-insertion-lists.html#1790" class="Bound">l</a> <a id="1859" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1861" href="lists.permutation-lists.html#1183" class="Function">permute-list</a> <a id="1874" href="lists.sort-by-insertion-lists.html#1790" class="Bound">l</a> <a id="1876" class="Symbol">(</a><a id="1877" href="lists.sort-by-insertion-lists.html#1480" class="Function">permutation-insertion-sort-list</a> <a id="1909" href="lists.sort-by-insertion-lists.html#1790" class="Bound">l</a><a id="1910" class="Symbol">)</a>
  <a id="1914" href="lists.sort-by-insertion-lists.html#1735" class="Function">eq-permute-list-permutation-insertion-sort-list</a> <a id="1962" class="Symbol">=</a>
    <a id="1968" href="lists.sorting-algorithms-lists.html#1580" class="Function">eq-permute-list-permutation-is-sort-list</a>
      <a id="2015" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a>
      <a id="2023" href="lists.sort-by-insertion-lists.html#849" class="Function">insertion-sort-list</a>
      <a id="2049" href="lists.sort-by-insertion-lists.html#1109" class="Function">is-sort-insertion-sort-list</a>

  <a id="2080" href="lists.sort-by-insertion-lists.html#2080" class="Function">is-sorting-insertion-sort-list</a> <a id="2111" class="Symbol">:</a>
    <a id="2117" class="Symbol">(</a><a id="2118" href="lists.sort-by-insertion-lists.html#2118" class="Bound">l</a> <a id="2120" class="Symbol">:</a> <a id="2122" href="lists.lists.html#1328" class="Datatype">list</a> <a id="2127" class="Symbol">(</a><a id="2128" href="order-theory.decidable-total-orders.html#2759" class="Function">type-Decidable-Total-Order</a> <a id="2155" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a><a id="2156" class="Symbol">))</a> <a id="2159" class="Symbol">→</a>
    <a id="2165" href="lists.sorted-lists.html#1084" class="Function">is-sorted-list</a> <a id="2180" href="lists.sort-by-insertion-lists.html#805" class="Bound">X</a> <a id="2182" class="Symbol">(</a><a id="2183" href="lists.sort-by-insertion-lists.html#849" class="Function">insertion-sort-list</a> <a id="2203" href="lists.sort-by-insertion-lists.html#2118" class="Bound">l</a><a id="2204" class="Symbol">)</a>
  <a id="2208" href="lists.sort-by-insertion-lists.html#2080" class="Function">is-sorting-insertion-sort-list</a> <a id="2239" class="Symbol">=</a> <a id="2241" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2245" class="Symbol">(</a><a id="2246" href="lists.sort-by-insertion-lists.html#1109" class="Function">is-sort-insertion-sort-list</a><a id="2273" class="Symbol">)</a>
</pre>