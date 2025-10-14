# Top elements in posets

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="order-theory.top-elements-posets.html" class="Module">order-theory.top-elements-posets</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="order-theory.top-elements-preorders.html" class="Module">order-theory.top-elements-preorders</a>
</pre>
</details>

## Idea

A
{{#concept "largest element" Disambiguation="in a poset" WD="maximal and minimal elements" WDID=Q1475294 Agda=is-top-element-Poset}}
in a [poset](order-theory.posets.md) is an element `t` such that `x ≤ t` holds
for every `x : P`.

## Definition

<pre class="Agda"><a id="646" class="Keyword">module</a> <a id="653" href="order-theory.top-elements-posets.html#653" class="Module">_</a>
  <a id="657" class="Symbol">{</a><a id="658" href="order-theory.top-elements-posets.html#658" class="Bound">l1</a> <a id="661" href="order-theory.top-elements-posets.html#661" class="Bound">l2</a> <a id="664" class="Symbol">:</a> <a id="666" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="671" class="Symbol">}</a> <a id="673" class="Symbol">(</a><a id="674" href="order-theory.top-elements-posets.html#674" class="Bound">X</a> <a id="676" class="Symbol">:</a> <a id="678" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="684" href="order-theory.top-elements-posets.html#658" class="Bound">l1</a> <a id="687" href="order-theory.top-elements-posets.html#661" class="Bound">l2</a><a id="689" class="Symbol">)</a>
  <a id="693" class="Keyword">where</a>

  <a id="702" href="order-theory.top-elements-posets.html#702" class="Function">is-top-element-prop-Poset</a> <a id="728" class="Symbol">:</a> <a id="730" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="741" href="order-theory.top-elements-posets.html#674" class="Bound">X</a> <a id="743" class="Symbol">→</a> <a id="745" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="750" class="Symbol">(</a><a id="751" href="order-theory.top-elements-posets.html#658" class="Bound">l1</a> <a id="754" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="756" href="order-theory.top-elements-posets.html#661" class="Bound">l2</a><a id="758" class="Symbol">)</a>
  <a id="762" href="order-theory.top-elements-posets.html#702" class="Function">is-top-element-prop-Poset</a> <a id="788" class="Symbol">=</a>
    <a id="794" href="order-theory.top-elements-preorders.html#650" class="Function">is-top-element-prop-Preorder</a> <a id="823" class="Symbol">(</a><a id="824" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="839" href="order-theory.top-elements-posets.html#674" class="Bound">X</a><a id="840" class="Symbol">)</a>

  <a id="845" href="order-theory.top-elements-posets.html#845" class="Function">is-top-element-Poset</a> <a id="866" class="Symbol">:</a> <a id="868" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="879" href="order-theory.top-elements-posets.html#674" class="Bound">X</a> <a id="881" class="Symbol">→</a> <a id="883" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="886" class="Symbol">(</a><a id="887" href="order-theory.top-elements-posets.html#658" class="Bound">l1</a> <a id="890" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="892" href="order-theory.top-elements-posets.html#661" class="Bound">l2</a><a id="894" class="Symbol">)</a>
  <a id="898" href="order-theory.top-elements-posets.html#845" class="Function">is-top-element-Poset</a> <a id="919" class="Symbol">=</a> <a id="921" href="order-theory.top-elements-preorders.html#813" class="Function">is-top-element-Preorder</a> <a id="945" class="Symbol">(</a><a id="946" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="961" href="order-theory.top-elements-posets.html#674" class="Bound">X</a><a id="962" class="Symbol">)</a>

  <a id="967" href="order-theory.top-elements-posets.html#967" class="Function">is-prop-is-top-element-Poset</a> <a id="996" class="Symbol">:</a>
    <a id="1002" class="Symbol">(</a><a id="1003" href="order-theory.top-elements-posets.html#1003" class="Bound">x</a> <a id="1005" class="Symbol">:</a> <a id="1007" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1018" href="order-theory.top-elements-posets.html#674" class="Bound">X</a><a id="1019" class="Symbol">)</a> <a id="1021" class="Symbol">→</a> <a id="1023" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1031" class="Symbol">(</a><a id="1032" href="order-theory.top-elements-posets.html#845" class="Function">is-top-element-Poset</a> <a id="1053" href="order-theory.top-elements-posets.html#1003" class="Bound">x</a><a id="1054" class="Symbol">)</a>
  <a id="1058" href="order-theory.top-elements-posets.html#967" class="Function">is-prop-is-top-element-Poset</a> <a id="1087" class="Symbol">=</a>
    <a id="1093" href="order-theory.top-elements-preorders.html#946" class="Function">is-prop-is-top-element-Preorder</a> <a id="1125" class="Symbol">(</a><a id="1126" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1141" href="order-theory.top-elements-posets.html#674" class="Bound">X</a><a id="1142" class="Symbol">)</a>

  <a id="1147" href="order-theory.top-elements-posets.html#1147" class="Function">has-top-element-Poset</a> <a id="1169" class="Symbol">:</a> <a id="1171" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1174" class="Symbol">(</a><a id="1175" href="order-theory.top-elements-posets.html#658" class="Bound">l1</a> <a id="1178" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1180" href="order-theory.top-elements-posets.html#661" class="Bound">l2</a><a id="1182" class="Symbol">)</a>
  <a id="1186" href="order-theory.top-elements-posets.html#1147" class="Function">has-top-element-Poset</a> <a id="1208" class="Symbol">=</a> <a id="1210" href="order-theory.top-elements-preorders.html#1140" class="Function">has-top-element-Preorder</a> <a id="1235" class="Symbol">(</a><a id="1236" href="order-theory.posets.html#1287" class="Function">preorder-Poset</a> <a id="1251" href="order-theory.top-elements-posets.html#674" class="Bound">X</a><a id="1252" class="Symbol">)</a>

  <a id="1257" href="order-theory.top-elements-posets.html#1257" class="Function">all-elements-equal-has-top-element-Poset</a> <a id="1298" class="Symbol">:</a>
    <a id="1304" href="foundation-core.propositions.html#2015" class="Function">all-elements-equal</a> <a id="1323" href="order-theory.top-elements-posets.html#1147" class="Function">has-top-element-Poset</a>
  <a id="1347" href="order-theory.top-elements-posets.html#1257" class="Function">all-elements-equal-has-top-element-Poset</a> <a id="1388" class="Symbol">(</a><a id="1389" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="1394" href="order-theory.top-elements-posets.html#1394" class="Bound">x</a> <a id="1396" href="order-theory.top-elements-posets.html#1396" class="Bound">H</a><a id="1397" class="Symbol">)</a> <a id="1399" class="Symbol">(</a><a id="1400" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="1405" href="order-theory.top-elements-posets.html#1405" class="Bound">y</a> <a id="1407" href="order-theory.top-elements-posets.html#1407" class="Bound">K</a><a id="1408" class="Symbol">)</a> <a id="1410" class="Symbol">=</a>
    <a id="1416" href="foundation-core.subtypes.html#3976" class="Function">eq-type-subtype</a>
      <a id="1438" class="Symbol">(</a> <a id="1440" href="order-theory.top-elements-posets.html#702" class="Function">is-top-element-prop-Poset</a><a id="1465" class="Symbol">)</a>
      <a id="1473" class="Symbol">(</a> <a id="1475" href="order-theory.posets.html#3131" class="Function">antisymmetric-leq-Poset</a> <a id="1499" href="order-theory.top-elements-posets.html#674" class="Bound">X</a> <a id="1501" href="order-theory.top-elements-posets.html#1394" class="Bound">x</a> <a id="1503" href="order-theory.top-elements-posets.html#1405" class="Bound">y</a> <a id="1505" class="Symbol">(</a><a id="1506" href="order-theory.top-elements-posets.html#1407" class="Bound">K</a> <a id="1508" href="order-theory.top-elements-posets.html#1394" class="Bound">x</a><a id="1509" class="Symbol">)</a> <a id="1511" class="Symbol">(</a><a id="1512" href="order-theory.top-elements-posets.html#1396" class="Bound">H</a> <a id="1514" href="order-theory.top-elements-posets.html#1405" class="Bound">y</a><a id="1515" class="Symbol">))</a>

  <a id="1521" href="order-theory.top-elements-posets.html#1521" class="Function">is-prop-has-top-element-Poset</a> <a id="1551" class="Symbol">:</a> <a id="1553" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1561" href="order-theory.top-elements-posets.html#1147" class="Function">has-top-element-Poset</a>
  <a id="1585" href="order-theory.top-elements-posets.html#1521" class="Function">is-prop-has-top-element-Poset</a> <a id="1615" class="Symbol">=</a>
    <a id="1621" href="foundation-core.propositions.html#2210" class="Function">is-prop-all-elements-equal</a> <a id="1648" href="order-theory.top-elements-posets.html#1257" class="Function">all-elements-equal-has-top-element-Poset</a>

  <a id="1692" href="order-theory.top-elements-posets.html#1692" class="Function">has-top-element-prop-Poset</a> <a id="1719" class="Symbol">:</a> <a id="1721" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1726" class="Symbol">(</a><a id="1727" href="order-theory.top-elements-posets.html#658" class="Bound">l1</a> <a id="1730" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1732" href="order-theory.top-elements-posets.html#661" class="Bound">l2</a><a id="1734" class="Symbol">)</a>
  <a id="1738" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1742" href="order-theory.top-elements-posets.html#1692" class="Function">has-top-element-prop-Poset</a> <a id="1769" class="Symbol">=</a> <a id="1771" href="order-theory.top-elements-posets.html#1147" class="Function">has-top-element-Poset</a>
  <a id="1795" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1799" href="order-theory.top-elements-posets.html#1692" class="Function">has-top-element-prop-Poset</a> <a id="1826" class="Symbol">=</a> <a id="1828" href="order-theory.top-elements-posets.html#1521" class="Function">is-prop-has-top-element-Poset</a>
</pre>
## External links

- [Maximal and minimal elements](https://en.wikipedia.org/wiki/Maximal_and_minimal_elements)
  at Wikipedia
- [maximal element](https://ncatlab.org/nlab/show/maximal+element) at $n$Lab
