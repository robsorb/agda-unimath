# Semisimple commutative finite rings

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="finite-algebra.semisimple-commutative-finite-rings.html" class="Module">finite-algebra.semisimple-commutative-finite-rings</a> <a id="106" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="finite-algebra.commutative-finite-rings.html" class="Module">finite-algebra.commutative-finite-rings</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="finite-algebra.dependent-products-commutative-finite-rings.html" class="Module">finite-algebra.dependent-products-commutative-finite-rings</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="finite-algebra.finite-fields.html" class="Module">finite-algebra.finite-fields</a>
<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="finite-algebra.homomorphisms-commutative-finite-rings.html" class="Module">finite-algebra.homomorphisms-commutative-finite-rings</a>

<a id="447" class="Keyword">open</a> <a id="452" class="Keyword">import</a> <a id="459" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="491" class="Keyword">open</a> <a id="496" class="Keyword">import</a> <a id="503" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="579" class="Keyword">open</a> <a id="584" class="Keyword">import</a> <a id="591" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="726" class="Keyword">open</a> <a id="731" class="Keyword">import</a> <a id="738" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="775" class="Keyword">open</a> <a id="780" class="Keyword">import</a> <a id="787" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

A **semisimple commutative finite ring** is a commutative finite ring which is
merely equivalent to an iterated cartesian product of finite fields.

## Definitions

### Semisimple commutative finite rings

<pre class="Agda"><a id="is-semisimple-Finite-Commutative-Ring"></a><a id="1073" href="finite-algebra.semisimple-commutative-finite-rings.html#1073" class="Function">is-semisimple-Finite-Commutative-Ring</a> <a id="1111" class="Symbol">:</a>
  <a id="1115" class="Symbol">{</a><a id="1116" href="finite-algebra.semisimple-commutative-finite-rings.html#1116" class="Bound">l1</a> <a id="1119" class="Symbol">:</a> <a id="1121" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1126" class="Symbol">}</a> <a id="1128" class="Symbol">(</a><a id="1129" href="finite-algebra.semisimple-commutative-finite-rings.html#1129" class="Bound">l2</a> <a id="1132" class="Symbol">:</a> <a id="1134" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1139" class="Symbol">)</a> <a id="1141" class="Symbol">→</a> <a id="1143" href="finite-algebra.commutative-finite-rings.html#2193" class="Function">Finite-Commutative-Ring</a> <a id="1167" href="finite-algebra.semisimple-commutative-finite-rings.html#1116" class="Bound">l1</a> <a id="1170" class="Symbol">→</a>
  <a id="1174" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1177" class="Symbol">(</a><a id="1178" href="finite-algebra.semisimple-commutative-finite-rings.html#1116" class="Bound">l1</a> <a id="1181" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1183" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1188" href="finite-algebra.semisimple-commutative-finite-rings.html#1129" class="Bound">l2</a><a id="1190" class="Symbol">)</a>
<a id="1192" href="finite-algebra.semisimple-commutative-finite-rings.html#1073" class="Function">is-semisimple-Finite-Commutative-Ring</a> <a id="1230" href="finite-algebra.semisimple-commutative-finite-rings.html#1230" class="Bound">l2</a> <a id="1233" href="finite-algebra.semisimple-commutative-finite-rings.html#1233" class="Bound">R</a> <a id="1235" class="Symbol">=</a>
  <a id="1239" href="foundation.existential-quantification.html#4151" class="Function">exists</a>
    <a id="1250" class="Symbol">(</a> <a id="1252" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1253" class="Symbol">)</a>
    <a id="1259" class="Symbol">(</a> <a id="1261" class="Symbol">λ</a> <a id="1263" href="finite-algebra.semisimple-commutative-finite-rings.html#1263" class="Bound">n</a> <a id="1265" class="Symbol">→</a>
      <a id="1273" href="foundation.existential-quantification.html#4308" class="Function">∃</a> <a id="1275" class="Symbol">(</a> <a id="1277" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="1281" href="finite-algebra.semisimple-commutative-finite-rings.html#1263" class="Bound">n</a> <a id="1283" class="Symbol">→</a> <a id="1285" href="finite-algebra.finite-fields.html#1689" class="Function">Finite-Field</a> <a id="1298" href="finite-algebra.semisimple-commutative-finite-rings.html#1230" class="Bound">l2</a><a id="1300" class="Symbol">)</a>
        <a id="1310" class="Symbol">(</a> <a id="1312" class="Symbol">λ</a> <a id="1314" href="finite-algebra.semisimple-commutative-finite-rings.html#1314" class="Bound">A</a> <a id="1316" class="Symbol">→</a>
          <a id="1328" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a>
            <a id="1351" class="Symbol">(</a> <a id="1353" href="finite-algebra.homomorphisms-commutative-finite-rings.html#2462" class="Function">hom-Finite-Commutative-Ring</a>
              <a id="1395" class="Symbol">(</a> <a id="1397" href="finite-algebra.semisimple-commutative-finite-rings.html#1233" class="Bound">R</a><a id="1398" class="Symbol">)</a>
              <a id="1414" class="Symbol">(</a> <a id="1416" href="finite-algebra.dependent-products-commutative-finite-rings.html#8764" class="Function">Π-Finite-Commutative-Ring</a>
                <a id="1458" class="Symbol">(</a> <a id="1460" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="1464" href="finite-algebra.semisimple-commutative-finite-rings.html#1263" class="Bound">n</a> <a id="1466" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1468" href="univalent-combinatorics.finite-types.html#7616" class="Function">is-finite-Fin</a> <a id="1482" href="finite-algebra.semisimple-commutative-finite-rings.html#1263" class="Bound">n</a><a id="1483" class="Symbol">)</a>
                <a id="1501" class="Symbol">(</a> <a id="1503" href="finite-algebra.finite-fields.html#1891" class="Function">commutative-finite-ring-Finite-Field</a> <a id="1540" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1542" href="finite-algebra.semisimple-commutative-finite-rings.html#1314" class="Bound">A</a><a id="1543" class="Symbol">)))))</a>

<a id="Semisimple-Finite-Commutative-Ring"></a><a id="1550" href="finite-algebra.semisimple-commutative-finite-rings.html#1550" class="Function">Semisimple-Finite-Commutative-Ring</a> <a id="1585" class="Symbol">:</a>
  <a id="1589" class="Symbol">(</a><a id="1590" href="finite-algebra.semisimple-commutative-finite-rings.html#1590" class="Bound">l1</a> <a id="1593" href="finite-algebra.semisimple-commutative-finite-rings.html#1593" class="Bound">l2</a> <a id="1596" class="Symbol">:</a> <a id="1598" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1603" class="Symbol">)</a> <a id="1605" class="Symbol">→</a> <a id="1607" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1610" class="Symbol">(</a><a id="1611" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1616" href="finite-algebra.semisimple-commutative-finite-rings.html#1590" class="Bound">l1</a> <a id="1619" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1621" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1626" href="finite-algebra.semisimple-commutative-finite-rings.html#1593" class="Bound">l2</a><a id="1628" class="Symbol">)</a>
<a id="1630" href="finite-algebra.semisimple-commutative-finite-rings.html#1550" class="Function">Semisimple-Finite-Commutative-Ring</a> <a id="1665" href="finite-algebra.semisimple-commutative-finite-rings.html#1665" class="Bound">l1</a> <a id="1668" href="finite-algebra.semisimple-commutative-finite-rings.html#1668" class="Bound">l2</a> <a id="1671" class="Symbol">=</a>
  <a id="1675" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1677" class="Symbol">(</a><a id="1678" href="finite-algebra.commutative-finite-rings.html#2193" class="Function">Finite-Commutative-Ring</a> <a id="1702" href="finite-algebra.semisimple-commutative-finite-rings.html#1665" class="Bound">l1</a><a id="1704" class="Symbol">)</a> <a id="1706" class="Symbol">(</a><a id="1707" href="finite-algebra.semisimple-commutative-finite-rings.html#1073" class="Function">is-semisimple-Finite-Commutative-Ring</a> <a id="1745" href="finite-algebra.semisimple-commutative-finite-rings.html#1668" class="Bound">l2</a><a id="1747" class="Symbol">)</a>

<a id="1750" class="Keyword">module</a> <a id="1757" href="finite-algebra.semisimple-commutative-finite-rings.html#1757" class="Module">_</a>
  <a id="1761" class="Symbol">{</a><a id="1762" href="finite-algebra.semisimple-commutative-finite-rings.html#1762" class="Bound">l1</a> <a id="1765" href="finite-algebra.semisimple-commutative-finite-rings.html#1765" class="Bound">l2</a> <a id="1768" class="Symbol">:</a> <a id="1770" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1775" class="Symbol">}</a> <a id="1777" class="Symbol">(</a><a id="1778" href="finite-algebra.semisimple-commutative-finite-rings.html#1778" class="Bound">A</a> <a id="1780" class="Symbol">:</a> <a id="1782" href="finite-algebra.semisimple-commutative-finite-rings.html#1550" class="Function">Semisimple-Finite-Commutative-Ring</a> <a id="1817" href="finite-algebra.semisimple-commutative-finite-rings.html#1762" class="Bound">l1</a> <a id="1820" href="finite-algebra.semisimple-commutative-finite-rings.html#1765" class="Bound">l2</a><a id="1822" class="Symbol">)</a>
  <a id="1826" class="Keyword">where</a>

  <a id="1835" href="finite-algebra.semisimple-commutative-finite-rings.html#1835" class="Function">commutative-finite-ring-Semisimple-Finite-Commutative-Ring</a> <a id="1894" class="Symbol">:</a>
    <a id="1900" href="finite-algebra.commutative-finite-rings.html#2193" class="Function">Finite-Commutative-Ring</a> <a id="1924" href="finite-algebra.semisimple-commutative-finite-rings.html#1762" class="Bound">l1</a>
  <a id="1929" href="finite-algebra.semisimple-commutative-finite-rings.html#1835" class="Function">commutative-finite-ring-Semisimple-Finite-Commutative-Ring</a> <a id="1988" class="Symbol">=</a> <a id="1990" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1994" href="finite-algebra.semisimple-commutative-finite-rings.html#1778" class="Bound">A</a>
</pre>
## Properties

### The number of ways to equip a finite type with the structure of a semisimple commutative ring is finite

<pre class="Agda"><a id="2133" class="Keyword">module</a> <a id="2140" href="finite-algebra.semisimple-commutative-finite-rings.html#2140" class="Module">_</a>
  <a id="2144" class="Symbol">{</a><a id="2145" href="finite-algebra.semisimple-commutative-finite-rings.html#2145" class="Bound">l1</a> <a id="2148" class="Symbol">:</a> <a id="2150" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2155" class="Symbol">}</a>
  <a id="2159" class="Symbol">(</a><a id="2160" href="finite-algebra.semisimple-commutative-finite-rings.html#2160" class="Bound">l2</a> <a id="2163" class="Symbol">:</a> <a id="2165" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2170" class="Symbol">)</a>
  <a id="2174" class="Symbol">(</a><a id="2175" href="finite-algebra.semisimple-commutative-finite-rings.html#2175" class="Bound">X</a> <a id="2177" class="Symbol">:</a> <a id="2179" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="2191" href="finite-algebra.semisimple-commutative-finite-rings.html#2145" class="Bound">l1</a><a id="2193" class="Symbol">)</a>
  <a id="2197" class="Keyword">where</a>

  <a id="2206" href="finite-algebra.semisimple-commutative-finite-rings.html#2206" class="Function">structure-semisimple-commutative-ring-Finite-Type</a> <a id="2256" class="Symbol">:</a>
    <a id="2262" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2265" class="Symbol">(</a><a id="2266" href="finite-algebra.semisimple-commutative-finite-rings.html#2145" class="Bound">l1</a> <a id="2269" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2271" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2276" href="finite-algebra.semisimple-commutative-finite-rings.html#2160" class="Bound">l2</a><a id="2278" class="Symbol">)</a>
  <a id="2282" href="finite-algebra.semisimple-commutative-finite-rings.html#2206" class="Function">structure-semisimple-commutative-ring-Finite-Type</a> <a id="2332" class="Symbol">=</a>
    <a id="2338" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2340" class="Symbol">(</a> <a id="2342" href="finite-algebra.commutative-finite-rings.html#25520" class="Function">structure-commutative-ring-Finite-Type</a> <a id="2381" href="finite-algebra.semisimple-commutative-finite-rings.html#2175" class="Bound">X</a><a id="2382" class="Symbol">)</a>
      <a id="2390" class="Symbol">(</a> <a id="2392" class="Symbol">λ</a> <a id="2394" href="finite-algebra.semisimple-commutative-finite-rings.html#2394" class="Bound">r</a> <a id="2396" class="Symbol">→</a>
        <a id="2406" href="finite-algebra.semisimple-commutative-finite-rings.html#1073" class="Function">is-semisimple-Finite-Commutative-Ring</a>
          <a id="2454" class="Symbol">(</a> <a id="2456" href="finite-algebra.semisimple-commutative-finite-rings.html#2160" class="Bound">l2</a><a id="2458" class="Symbol">)</a>
          <a id="2470" class="Symbol">(</a> <a id="2472" href="finite-algebra.commutative-finite-rings.html#25750" class="Function">finite-commutative-ring-structure-commutative-ring-Finite-Type</a> <a id="2535" href="finite-algebra.semisimple-commutative-finite-rings.html#2175" class="Bound">X</a> <a id="2537" href="finite-algebra.semisimple-commutative-finite-rings.html#2394" class="Bound">r</a><a id="2538" class="Symbol">))</a>

  <a id="2544" href="finite-algebra.semisimple-commutative-finite-rings.html#2544" class="Function">finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-Finite-Type</a> <a id="2629" class="Symbol">:</a>
    <a id="2635" href="finite-algebra.semisimple-commutative-finite-rings.html#2206" class="Function">structure-semisimple-commutative-ring-Finite-Type</a> <a id="2685" class="Symbol">→</a>
    <a id="2691" href="finite-algebra.semisimple-commutative-finite-rings.html#1550" class="Function">Semisimple-Finite-Commutative-Ring</a> <a id="2726" href="finite-algebra.semisimple-commutative-finite-rings.html#2145" class="Bound">l1</a> <a id="2729" href="finite-algebra.semisimple-commutative-finite-rings.html#2160" class="Bound">l2</a>
  <a id="2734" href="finite-algebra.semisimple-commutative-finite-rings.html#2544" class="Function">finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-Finite-Type</a> <a id="2819" class="Symbol">=</a>
    <a id="2825" href="foundation-core.functoriality-dependent-pair-types.html#2021" class="Function">map-Σ-map-base</a>
      <a id="2846" class="Symbol">(</a> <a id="2848" href="finite-algebra.commutative-finite-rings.html#25750" class="Function">finite-commutative-ring-structure-commutative-ring-Finite-Type</a> <a id="2911" href="finite-algebra.semisimple-commutative-finite-rings.html#2175" class="Bound">X</a><a id="2912" class="Symbol">)</a>
      <a id="2920" class="Symbol">(</a> <a id="2922" href="finite-algebra.semisimple-commutative-finite-rings.html#1073" class="Function">is-semisimple-Finite-Commutative-Ring</a> <a id="2960" href="finite-algebra.semisimple-commutative-finite-rings.html#2160" class="Bound">l2</a><a id="2962" class="Symbol">)</a>
</pre>