# Lower sets in large posets

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="order-theory.lower-sets-large-posets.html" class="Module">order-theory.lower-sets-large-posets</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="order-theory.large-subposets.html" class="Module">order-theory.large-subposets</a>
</pre>
</details>

## Idea

A **lower set** or **downwards closed set** in a
[large poset](order-theory.large-posets.md) is a
[large subposet](order-theory.large-subposets.md) that is downwards closed,
i.e., that satisfies the condition that

```text
  ∀ (x y : P), (y ≤ x) → x ∈ S → y ∈ S.
```

## Definitions

### The predicate of being a lower set

<pre class="Agda"><a id="616" class="Keyword">module</a> <a id="623" href="order-theory.lower-sets-large-posets.html#623" class="Module">_</a>
  <a id="627" class="Symbol">{</a><a id="628" href="order-theory.lower-sets-large-posets.html#628" class="Bound">α</a> <a id="630" href="order-theory.lower-sets-large-posets.html#630" class="Bound">γ</a> <a id="632" class="Symbol">:</a> <a id="634" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="640" class="Symbol">→</a> <a id="642" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="647" class="Symbol">}</a> <a id="649" class="Symbol">{</a><a id="650" href="order-theory.lower-sets-large-posets.html#650" class="Bound">β</a> <a id="652" class="Symbol">:</a> <a id="654" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="660" class="Symbol">→</a> <a id="662" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="668" class="Symbol">→</a> <a id="670" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="675" class="Symbol">}</a>
  <a id="679" class="Symbol">(</a><a id="680" href="order-theory.lower-sets-large-posets.html#680" class="Bound">P</a> <a id="682" class="Symbol">:</a> <a id="684" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="696" href="order-theory.lower-sets-large-posets.html#628" class="Bound">α</a> <a id="698" href="order-theory.lower-sets-large-posets.html#650" class="Bound">β</a><a id="699" class="Symbol">)</a> <a id="701" class="Symbol">(</a><a id="702" href="order-theory.lower-sets-large-posets.html#702" class="Bound">S</a> <a id="704" class="Symbol">:</a> <a id="706" href="order-theory.large-subposets.html#1571" class="Record">Large-Subposet</a> <a id="721" href="order-theory.lower-sets-large-posets.html#630" class="Bound">γ</a> <a id="723" href="order-theory.lower-sets-large-posets.html#680" class="Bound">P</a><a id="724" class="Symbol">)</a>
  <a id="728" class="Keyword">where</a>

  <a id="737" href="order-theory.lower-sets-large-posets.html#737" class="Function">is-lower-set-Large-Subposet</a> <a id="765" class="Symbol">:</a> <a id="767" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="773" href="order-theory.lower-sets-large-posets.html#737" class="Function">is-lower-set-Large-Subposet</a> <a id="801" class="Symbol">=</a>
    <a id="807" class="Symbol">{</a><a id="808" href="order-theory.lower-sets-large-posets.html#808" class="Bound">l1</a> <a id="811" href="order-theory.lower-sets-large-posets.html#811" class="Bound">l2</a> <a id="814" class="Symbol">:</a> <a id="816" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="821" class="Symbol">}</a> <a id="823" class="Symbol">(</a><a id="824" href="order-theory.lower-sets-large-posets.html#824" class="Bound">x</a> <a id="826" class="Symbol">:</a> <a id="828" href="order-theory.large-posets.html#1534" class="Function">type-Large-Poset</a> <a id="845" href="order-theory.lower-sets-large-posets.html#680" class="Bound">P</a> <a id="847" href="order-theory.lower-sets-large-posets.html#808" class="Bound">l1</a><a id="849" class="Symbol">)</a> <a id="851" class="Symbol">(</a><a id="852" href="order-theory.lower-sets-large-posets.html#852" class="Bound">y</a> <a id="854" class="Symbol">:</a> <a id="856" href="order-theory.large-posets.html#1534" class="Function">type-Large-Poset</a> <a id="873" href="order-theory.lower-sets-large-posets.html#680" class="Bound">P</a> <a id="875" href="order-theory.lower-sets-large-posets.html#811" class="Bound">l2</a><a id="877" class="Symbol">)</a> <a id="879" class="Symbol">→</a>
    <a id="885" href="order-theory.large-posets.html#1798" class="Function">leq-Large-Poset</a> <a id="901" href="order-theory.lower-sets-large-posets.html#680" class="Bound">P</a> <a id="903" href="order-theory.lower-sets-large-posets.html#852" class="Bound">y</a> <a id="905" href="order-theory.lower-sets-large-posets.html#824" class="Bound">x</a> <a id="907" class="Symbol">→</a>
    <a id="913" href="order-theory.large-subposets.html#2251" class="Function">is-in-Large-Subposet</a> <a id="934" href="order-theory.lower-sets-large-posets.html#680" class="Bound">P</a> <a id="936" href="order-theory.lower-sets-large-posets.html#702" class="Bound">S</a> <a id="938" href="order-theory.lower-sets-large-posets.html#824" class="Bound">x</a> <a id="940" class="Symbol">→</a> <a id="942" href="order-theory.large-subposets.html#2251" class="Function">is-in-Large-Subposet</a> <a id="963" href="order-theory.lower-sets-large-posets.html#680" class="Bound">P</a> <a id="965" href="order-theory.lower-sets-large-posets.html#702" class="Bound">S</a> <a id="967" href="order-theory.lower-sets-large-posets.html#852" class="Bound">y</a>
</pre>
### Lower sets of a large poset

<pre class="Agda"><a id="1015" class="Keyword">module</a> <a id="1022" href="order-theory.lower-sets-large-posets.html#1022" class="Module">_</a>
  <a id="1026" class="Symbol">{</a><a id="1027" href="order-theory.lower-sets-large-posets.html#1027" class="Bound">α</a> <a id="1029" class="Symbol">:</a> <a id="1031" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1037" class="Symbol">→</a> <a id="1039" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1044" class="Symbol">}</a> <a id="1046" class="Symbol">{</a><a id="1047" href="order-theory.lower-sets-large-posets.html#1047" class="Bound">β</a> <a id="1049" class="Symbol">:</a> <a id="1051" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1057" class="Symbol">→</a> <a id="1059" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1065" class="Symbol">→</a> <a id="1067" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1072" class="Symbol">}</a> <a id="1074" class="Symbol">(</a><a id="1075" href="order-theory.lower-sets-large-posets.html#1075" class="Bound">γ</a> <a id="1077" class="Symbol">:</a> <a id="1079" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1085" class="Symbol">→</a> <a id="1087" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1092" class="Symbol">)</a>
  <a id="1096" class="Symbol">(</a><a id="1097" href="order-theory.lower-sets-large-posets.html#1097" class="Bound">P</a> <a id="1099" class="Symbol">:</a> <a id="1101" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1113" href="order-theory.lower-sets-large-posets.html#1027" class="Bound">α</a> <a id="1115" href="order-theory.lower-sets-large-posets.html#1047" class="Bound">β</a><a id="1116" class="Symbol">)</a>
  <a id="1120" class="Keyword">where</a>

  <a id="1129" class="Keyword">record</a>
    <a id="1140" href="order-theory.lower-sets-large-posets.html#1140" class="Record">lower-set-Large-Poset</a> <a id="1162" class="Symbol">:</a> <a id="1164" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
    <a id="1172" class="Keyword">where</a>
    <a id="1182" class="Keyword">field</a>
      <a id="1194" href="order-theory.lower-sets-large-posets.html#1194" class="Field">large-subposet-lower-set-Large-Poset</a> <a id="1231" class="Symbol">:</a>
        <a id="1241" href="order-theory.large-subposets.html#1571" class="Record">Large-Subposet</a> <a id="1256" href="order-theory.lower-sets-large-posets.html#1075" class="Bound">γ</a> <a id="1258" href="order-theory.lower-sets-large-posets.html#1097" class="Bound">P</a>
      <a id="1266" href="order-theory.lower-sets-large-posets.html#1266" class="Field">is-lower-set-lower-set-Large-Poset</a> <a id="1301" class="Symbol">:</a>
        <a id="1311" href="order-theory.lower-sets-large-posets.html#737" class="Function">is-lower-set-Large-Subposet</a> <a id="1339" href="order-theory.lower-sets-large-posets.html#1097" class="Bound">P</a> <a id="1341" href="order-theory.lower-sets-large-posets.html#1194" class="Field">large-subposet-lower-set-Large-Poset</a>

  <a id="1381" class="Keyword">open</a> <a id="1386" href="order-theory.lower-sets-large-posets.html#1140" class="Module">lower-set-Large-Poset</a> <a id="1408" class="Keyword">public</a>

<a id="1416" class="Keyword">module</a> <a id="1423" href="order-theory.lower-sets-large-posets.html#1423" class="Module">_</a>
  <a id="1427" class="Symbol">{</a><a id="1428" href="order-theory.lower-sets-large-posets.html#1428" class="Bound">α</a> <a id="1430" href="order-theory.lower-sets-large-posets.html#1430" class="Bound">γ</a> <a id="1432" class="Symbol">:</a> <a id="1434" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1440" class="Symbol">→</a> <a id="1442" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1447" class="Symbol">}</a> <a id="1449" class="Symbol">{</a><a id="1450" href="order-theory.lower-sets-large-posets.html#1450" class="Bound">β</a> <a id="1452" class="Symbol">:</a> <a id="1454" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1460" class="Symbol">→</a> <a id="1462" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1468" class="Symbol">→</a> <a id="1470" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1475" class="Symbol">}</a>
  <a id="1479" class="Symbol">(</a><a id="1480" href="order-theory.lower-sets-large-posets.html#1480" class="Bound">P</a> <a id="1482" class="Symbol">:</a> <a id="1484" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1496" href="order-theory.lower-sets-large-posets.html#1428" class="Bound">α</a> <a id="1498" href="order-theory.lower-sets-large-posets.html#1450" class="Bound">β</a><a id="1499" class="Symbol">)</a> <a id="1501" class="Symbol">(</a><a id="1502" href="order-theory.lower-sets-large-posets.html#1502" class="Bound">L</a> <a id="1504" class="Symbol">:</a> <a id="1506" href="order-theory.lower-sets-large-posets.html#1140" class="Record">lower-set-Large-Poset</a> <a id="1528" href="order-theory.lower-sets-large-posets.html#1430" class="Bound">γ</a> <a id="1530" href="order-theory.lower-sets-large-posets.html#1480" class="Bound">P</a><a id="1531" class="Symbol">)</a>
  <a id="1535" class="Keyword">where</a>

  <a id="1544" href="order-theory.lower-sets-large-posets.html#1544" class="Function">is-in-lower-set-Large-Poset</a> <a id="1572" class="Symbol">:</a>
    <a id="1578" class="Symbol">{</a><a id="1579" href="order-theory.lower-sets-large-posets.html#1579" class="Bound">l</a> <a id="1581" class="Symbol">:</a> <a id="1583" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1588" class="Symbol">}</a> <a id="1590" class="Symbol">(</a><a id="1591" href="order-theory.lower-sets-large-posets.html#1591" class="Bound">x</a> <a id="1593" class="Symbol">:</a> <a id="1595" href="order-theory.large-posets.html#1534" class="Function">type-Large-Poset</a> <a id="1612" href="order-theory.lower-sets-large-posets.html#1480" class="Bound">P</a> <a id="1614" href="order-theory.lower-sets-large-posets.html#1579" class="Bound">l</a><a id="1615" class="Symbol">)</a> <a id="1617" class="Symbol">→</a> <a id="1619" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1622" class="Symbol">(</a><a id="1623" href="order-theory.lower-sets-large-posets.html#1430" class="Bound">γ</a> <a id="1625" href="order-theory.lower-sets-large-posets.html#1579" class="Bound">l</a><a id="1626" class="Symbol">)</a>
  <a id="1630" href="order-theory.lower-sets-large-posets.html#1544" class="Function">is-in-lower-set-Large-Poset</a> <a id="1658" class="Symbol">=</a>
    <a id="1664" href="order-theory.large-subposets.html#2251" class="Function">is-in-Large-Subposet</a> <a id="1685" href="order-theory.lower-sets-large-posets.html#1480" class="Bound">P</a> <a id="1687" class="Symbol">(</a><a id="1688" href="order-theory.lower-sets-large-posets.html#1194" class="Field">large-subposet-lower-set-Large-Poset</a> <a id="1725" href="order-theory.lower-sets-large-posets.html#1502" class="Bound">L</a><a id="1726" class="Symbol">)</a>
</pre>
## See also

- [Principal lower sets](order-theory.principal-lower-sets-large-posets.md)
- [Upper sets](order-theory.upper-sets-large-posets.md)
