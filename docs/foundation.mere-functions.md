# Mere functions

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="foundation.mere-functions.html" class="Module">foundation.mere-functions</a> <a id="60" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="116" class="Keyword">open</a> <a id="121" class="Keyword">import</a> <a id="128" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="165" class="Keyword">open</a> <a id="170" class="Keyword">import</a> <a id="177" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

The type of
{{#concept "mere functions" Disambiguation="of types" Agda=mere-function}} from
`A` to `B` is the
[propositional truncation](foundation.propositional-truncations.md) of the type
of maps from `A` to `B`.

```text
  mere-function A B := ║(A → B)║₋₁
```

## Definitions

### Mere functions between types

<pre class="Agda"><a id="637" class="Keyword">module</a> <a id="644" href="foundation.mere-functions.html#644" class="Module">_</a>
  <a id="648" class="Symbol">{</a><a id="649" href="foundation.mere-functions.html#649" class="Bound">l1</a> <a id="652" href="foundation.mere-functions.html#652" class="Bound">l2</a> <a id="655" class="Symbol">:</a> <a id="657" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="662" class="Symbol">}</a> <a id="664" class="Symbol">(</a><a id="665" href="foundation.mere-functions.html#665" class="Bound">A</a> <a id="667" class="Symbol">:</a> <a id="669" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="672" href="foundation.mere-functions.html#649" class="Bound">l1</a><a id="674" class="Symbol">)</a> <a id="676" class="Symbol">(</a><a id="677" href="foundation.mere-functions.html#677" class="Bound">B</a> <a id="679" class="Symbol">:</a> <a id="681" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="684" href="foundation.mere-functions.html#652" class="Bound">l2</a><a id="686" class="Symbol">)</a>
  <a id="690" class="Keyword">where</a>

  <a id="699" href="foundation.mere-functions.html#699" class="Function">prop-mere-function</a> <a id="718" class="Symbol">:</a> <a id="720" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="725" class="Symbol">(</a><a id="726" href="foundation.mere-functions.html#649" class="Bound">l1</a> <a id="729" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="731" href="foundation.mere-functions.html#652" class="Bound">l2</a><a id="733" class="Symbol">)</a>
  <a id="737" href="foundation.mere-functions.html#699" class="Function">prop-mere-function</a> <a id="756" class="Symbol">=</a> <a id="758" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="769" class="Symbol">(</a><a id="770" href="foundation.mere-functions.html#665" class="Bound">A</a> <a id="772" class="Symbol">→</a> <a id="774" href="foundation.mere-functions.html#677" class="Bound">B</a><a id="775" class="Symbol">)</a>

  <a id="780" href="foundation.mere-functions.html#780" class="Function">mere-function</a> <a id="794" class="Symbol">:</a> <a id="796" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="799" class="Symbol">(</a><a id="800" href="foundation.mere-functions.html#649" class="Bound">l1</a> <a id="803" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="805" href="foundation.mere-functions.html#652" class="Bound">l2</a><a id="807" class="Symbol">)</a>
  <a id="811" href="foundation.mere-functions.html#780" class="Function">mere-function</a> <a id="825" class="Symbol">=</a> <a id="827" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="837" href="foundation.mere-functions.html#699" class="Function">prop-mere-function</a>

  <a id="859" href="foundation.mere-functions.html#859" class="Function">is-prop-mere-function</a> <a id="881" class="Symbol">:</a> <a id="883" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="891" href="foundation.mere-functions.html#780" class="Function">mere-function</a>
  <a id="907" href="foundation.mere-functions.html#859" class="Function">is-prop-mere-function</a> <a id="929" class="Symbol">=</a> <a id="931" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="949" href="foundation.mere-functions.html#699" class="Function">prop-mere-function</a>
</pre>
### The evaluation map on mere functions

If we have a mere function from `A` to `B` and `A` is inhabited, then `B` is
inhabited.

<pre class="Agda"><a id="1112" class="Keyword">module</a> <a id="1119" href="foundation.mere-functions.html#1119" class="Module">_</a>
  <a id="1123" class="Symbol">{</a><a id="1124" href="foundation.mere-functions.html#1124" class="Bound">l1</a> <a id="1127" href="foundation.mere-functions.html#1127" class="Bound">l2</a> <a id="1130" class="Symbol">:</a> <a id="1132" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1137" class="Symbol">}</a> <a id="1139" class="Symbol">(</a><a id="1140" href="foundation.mere-functions.html#1140" class="Bound">A</a> <a id="1142" class="Symbol">:</a> <a id="1144" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1147" href="foundation.mere-functions.html#1124" class="Bound">l1</a><a id="1149" class="Symbol">)</a> <a id="1151" class="Symbol">(</a><a id="1152" href="foundation.mere-functions.html#1152" class="Bound">B</a> <a id="1154" class="Symbol">:</a> <a id="1156" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1159" href="foundation.mere-functions.html#1127" class="Bound">l2</a><a id="1161" class="Symbol">)</a>
  <a id="1165" class="Keyword">where</a>

  <a id="1174" href="foundation.mere-functions.html#1174" class="Function">ev-mere-function&#39;</a> <a id="1192" class="Symbol">:</a> <a id="1194" class="Symbol">(</a><a id="1195" href="foundation.mere-functions.html#780" class="Function">mere-function</a> <a id="1209" href="foundation.mere-functions.html#1140" class="Bound">A</a> <a id="1211" href="foundation.mere-functions.html#1152" class="Bound">B</a><a id="1212" class="Symbol">)</a> <a id="1214" class="Symbol">→</a> <a id="1216" href="foundation.mere-functions.html#1140" class="Bound">A</a> <a id="1218" class="Symbol">→</a> <a id="1220" href="foundation.propositional-truncations.html#1662" class="Function Operator">║</a> <a id="1222" href="foundation.mere-functions.html#1152" class="Bound">B</a> <a id="1224" href="foundation.propositional-truncations.html#1662" class="Function Operator">║₋₁</a>
  <a id="1230" href="foundation.mere-functions.html#1174" class="Function">ev-mere-function&#39;</a> <a id="1248" href="foundation.mere-functions.html#1248" class="Bound">|f|</a> <a id="1252" href="foundation.mere-functions.html#1252" class="Bound">a</a> <a id="1254" class="Symbol">=</a>
    <a id="1260" href="foundation.propositional-truncations.html#4671" class="Function">rec-trunc-Prop</a> <a id="1275" class="Symbol">(</a><a id="1276" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="1287" href="foundation.mere-functions.html#1152" class="Bound">B</a><a id="1288" class="Symbol">)</a> <a id="1290" class="Symbol">(λ</a> <a id="1293" href="foundation.mere-functions.html#1293" class="Bound">f</a> <a id="1295" class="Symbol">→</a> <a id="1297" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="1313" class="Symbol">(</a><a id="1314" href="foundation.mere-functions.html#1293" class="Bound">f</a> <a id="1316" href="foundation.mere-functions.html#1252" class="Bound">a</a><a id="1317" class="Symbol">))</a> <a id="1320" href="foundation.mere-functions.html#1248" class="Bound">|f|</a>

  <a id="1327" href="foundation.mere-functions.html#1327" class="Function">ev-mere-function</a> <a id="1344" class="Symbol">:</a> <a id="1346" class="Symbol">(</a><a id="1347" href="foundation.mere-functions.html#780" class="Function">mere-function</a> <a id="1361" href="foundation.mere-functions.html#1140" class="Bound">A</a> <a id="1363" href="foundation.mere-functions.html#1152" class="Bound">B</a><a id="1364" class="Symbol">)</a> <a id="1366" class="Symbol">→</a> <a id="1368" href="foundation.propositional-truncations.html#1662" class="Function Operator">║</a> <a id="1370" href="foundation.mere-functions.html#1140" class="Bound">A</a> <a id="1372" href="foundation.propositional-truncations.html#1662" class="Function Operator">║₋₁</a> <a id="1376" class="Symbol">→</a> <a id="1378" href="foundation.propositional-truncations.html#1662" class="Function Operator">║</a> <a id="1380" href="foundation.mere-functions.html#1152" class="Bound">B</a> <a id="1382" href="foundation.propositional-truncations.html#1662" class="Function Operator">║₋₁</a>
  <a id="1388" href="foundation.mere-functions.html#1327" class="Function">ev-mere-function</a> <a id="1405" href="foundation.mere-functions.html#1405" class="Bound">|f|</a> <a id="1409" href="foundation.mere-functions.html#1409" class="Bound">|a|</a> <a id="1413" class="Symbol">=</a>
    <a id="1419" href="foundation.propositional-truncations.html#4671" class="Function">rec-trunc-Prop</a> <a id="1434" class="Symbol">(</a><a id="1435" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="1446" href="foundation.mere-functions.html#1152" class="Bound">B</a><a id="1447" class="Symbol">)</a> <a id="1449" class="Symbol">(</a><a id="1450" href="foundation.mere-functions.html#1174" class="Function">ev-mere-function&#39;</a> <a id="1468" href="foundation.mere-functions.html#1405" class="Bound">|f|</a><a id="1471" class="Symbol">)</a> <a id="1473" class="Symbol">(</a><a id="1474" href="foundation.mere-functions.html#1409" class="Bound">|a|</a><a id="1477" class="Symbol">)</a>
</pre>
### Mere functions form a reflexive relation

<pre class="Agda"><a id="1538" class="Keyword">module</a> <a id="1545" href="foundation.mere-functions.html#1545" class="Module">_</a>
  <a id="1549" class="Symbol">{</a><a id="1550" href="foundation.mere-functions.html#1550" class="Bound">l</a> <a id="1552" class="Symbol">:</a> <a id="1554" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1559" class="Symbol">}</a> <a id="1561" class="Symbol">(</a><a id="1562" href="foundation.mere-functions.html#1562" class="Bound">A</a> <a id="1564" class="Symbol">:</a> <a id="1566" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1569" href="foundation.mere-functions.html#1550" class="Bound">l</a><a id="1570" class="Symbol">)</a>
  <a id="1574" class="Keyword">where</a>

  <a id="1583" href="foundation.mere-functions.html#1583" class="Function">refl-mere-function</a> <a id="1602" class="Symbol">:</a> <a id="1604" href="foundation.mere-functions.html#780" class="Function">mere-function</a> <a id="1618" href="foundation.mere-functions.html#1562" class="Bound">A</a> <a id="1620" href="foundation.mere-functions.html#1562" class="Bound">A</a>
  <a id="1624" href="foundation.mere-functions.html#1583" class="Function">refl-mere-function</a> <a id="1643" class="Symbol">=</a> <a id="1645" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="1661" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>
### Mere functions form a transitive relation

<pre class="Agda"><a id="1724" class="Keyword">module</a> <a id="1731" href="foundation.mere-functions.html#1731" class="Module">_</a>
  <a id="1735" class="Symbol">{</a><a id="1736" href="foundation.mere-functions.html#1736" class="Bound">l1</a> <a id="1739" href="foundation.mere-functions.html#1739" class="Bound">l2</a> <a id="1742" href="foundation.mere-functions.html#1742" class="Bound">l3</a> <a id="1745" class="Symbol">:</a> <a id="1747" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1752" class="Symbol">}</a> <a id="1754" class="Symbol">{</a><a id="1755" href="foundation.mere-functions.html#1755" class="Bound">A</a> <a id="1757" class="Symbol">:</a> <a id="1759" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1762" href="foundation.mere-functions.html#1736" class="Bound">l1</a><a id="1764" class="Symbol">}</a> <a id="1766" class="Symbol">{</a><a id="1767" href="foundation.mere-functions.html#1767" class="Bound">B</a> <a id="1769" class="Symbol">:</a> <a id="1771" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1774" href="foundation.mere-functions.html#1739" class="Bound">l2</a><a id="1776" class="Symbol">}</a> <a id="1778" class="Symbol">{</a><a id="1779" href="foundation.mere-functions.html#1779" class="Bound">C</a> <a id="1781" class="Symbol">:</a> <a id="1783" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1786" href="foundation.mere-functions.html#1742" class="Bound">l3</a><a id="1788" class="Symbol">}</a>
  <a id="1792" class="Keyword">where</a>

  <a id="1801" href="foundation.mere-functions.html#1801" class="Function">transitive-mere-function</a> <a id="1826" class="Symbol">:</a>
    <a id="1832" href="foundation.mere-functions.html#780" class="Function">mere-function</a> <a id="1846" href="foundation.mere-functions.html#1767" class="Bound">B</a> <a id="1848" href="foundation.mere-functions.html#1779" class="Bound">C</a> <a id="1850" class="Symbol">→</a> <a id="1852" href="foundation.mere-functions.html#780" class="Function">mere-function</a> <a id="1866" href="foundation.mere-functions.html#1755" class="Bound">A</a> <a id="1868" href="foundation.mere-functions.html#1767" class="Bound">B</a> <a id="1870" class="Symbol">→</a> <a id="1872" href="foundation.mere-functions.html#780" class="Function">mere-function</a> <a id="1886" href="foundation.mere-functions.html#1755" class="Bound">A</a> <a id="1888" href="foundation.mere-functions.html#1779" class="Bound">C</a>
  <a id="1892" href="foundation.mere-functions.html#1801" class="Function">transitive-mere-function</a> <a id="1917" href="foundation.mere-functions.html#1917" class="Bound">|g|</a> <a id="1921" class="Symbol">=</a>
    <a id="1927" href="foundation.propositional-truncations.html#4671" class="Function">rec-trunc-Prop</a>
      <a id="1948" class="Symbol">(</a> <a id="1950" href="foundation.mere-functions.html#699" class="Function">prop-mere-function</a> <a id="1969" href="foundation.mere-functions.html#1755" class="Bound">A</a> <a id="1971" href="foundation.mere-functions.html#1779" class="Bound">C</a><a id="1972" class="Symbol">)</a>
      <a id="1980" class="Symbol">(</a> <a id="1982" class="Symbol">λ</a> <a id="1984" href="foundation.mere-functions.html#1984" class="Bound">f</a> <a id="1986" class="Symbol">→</a>
        <a id="1996" href="foundation.propositional-truncations.html#4671" class="Function">rec-trunc-Prop</a>
          <a id="2021" class="Symbol">(</a> <a id="2023" href="foundation.mere-functions.html#699" class="Function">prop-mere-function</a> <a id="2042" href="foundation.mere-functions.html#1755" class="Bound">A</a> <a id="2044" href="foundation.mere-functions.html#1779" class="Bound">C</a><a id="2045" class="Symbol">)</a>
          <a id="2057" class="Symbol">(</a> <a id="2059" class="Symbol">λ</a> <a id="2061" href="foundation.mere-functions.html#2061" class="Bound">g</a> <a id="2063" class="Symbol">→</a> <a id="2065" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="2081" class="Symbol">(</a><a id="2082" href="foundation.mere-functions.html#2061" class="Bound">g</a> <a id="2084" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2086" href="foundation.mere-functions.html#1984" class="Bound">f</a><a id="2087" class="Symbol">))</a>
          <a id="2100" class="Symbol">(</a> <a id="2102" href="foundation.mere-functions.html#1917" class="Bound">|g|</a><a id="2105" class="Symbol">))</a>
</pre>
## See also

- [Mere logical equivalences](foundation.mere-logical-equivalences.md)
