# The groupoid of main classes of Latin squares

<pre class="Agda"><a id="58" class="Keyword">module</a> <a id="65" href="univalent-combinatorics.main-classes-of-latin-squares.html" class="Module">univalent-combinatorics.main-classes-of-latin-squares</a> <a id="119" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="foundation.1-types.html" class="Module">foundation.1-types</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="univalent-combinatorics.main-classes-of-latin-hypercubes.html" class="Module">univalent-combinatorics.main-classes-of-latin-hypercubes</a>
<a id="449" class="Keyword">open</a> <a id="454" class="Keyword">import</a> <a id="461" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
<a id="507" class="Keyword">open</a> <a id="512" class="Keyword">import</a> <a id="519" href="univalent-combinatorics.truncated-pi-finite-types.html" class="Module">univalent-combinatorics.truncated-pi-finite-types</a>
<a id="569" class="Keyword">open</a> <a id="574" class="Keyword">import</a> <a id="581" href="univalent-combinatorics.untruncated-pi-finite-types.html" class="Module">univalent-combinatorics.untruncated-pi-finite-types</a>
</pre>
</details>

## Idea

The [groupoid](foundation.1-types.md) of
{{#concept "main classes of latin squares" Agda=Main-Class-Latin-Squares}}
consists of [unordered triples](foundation.unordered-tuples.md) of
[inhabited](foundation.inhabited-types.md) types
[equipped](foundation.structure.md) with a ternary 1-1 correspondence.

## Definition

### Main classes of general latin squares

<pre class="Agda"><a id="Main-Class-Latin-Squares"></a><a id="1029" href="univalent-combinatorics.main-classes-of-latin-squares.html#1029" class="Function">Main-Class-Latin-Squares</a> <a id="1054" class="Symbol">:</a> <a id="1056" class="Symbol">(</a><a id="1057" href="univalent-combinatorics.main-classes-of-latin-squares.html#1057" class="Bound">l1</a> <a id="1060" href="univalent-combinatorics.main-classes-of-latin-squares.html#1060" class="Bound">l2</a> <a id="1063" class="Symbol">:</a> <a id="1065" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1070" class="Symbol">)</a> <a id="1072" class="Symbol">→</a> <a id="1074" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1077" class="Symbol">(</a><a id="1078" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1083" href="univalent-combinatorics.main-classes-of-latin-squares.html#1057" class="Bound">l1</a> <a id="1086" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1088" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1093" href="univalent-combinatorics.main-classes-of-latin-squares.html#1060" class="Bound">l2</a><a id="1095" class="Symbol">)</a>
<a id="1097" href="univalent-combinatorics.main-classes-of-latin-squares.html#1029" class="Function">Main-Class-Latin-Squares</a> <a id="1122" href="univalent-combinatorics.main-classes-of-latin-squares.html#1122" class="Bound">l1</a> <a id="1125" href="univalent-combinatorics.main-classes-of-latin-squares.html#1125" class="Bound">l2</a> <a id="1128" class="Symbol">=</a> <a id="1130" href="univalent-combinatorics.main-classes-of-latin-hypercubes.html#1161" class="Function">Main-Class-Latin-Hypercube</a> <a id="1157" href="univalent-combinatorics.main-classes-of-latin-squares.html#1122" class="Bound">l1</a> <a id="1160" href="univalent-combinatorics.main-classes-of-latin-squares.html#1125" class="Bound">l2</a> <a id="1163" class="Number">2</a>
</pre>
### Main classes of latin squares of fixed finite order

<pre class="Agda"><a id="Main-Class-Latin-Square-of-Order"></a><a id="1235" href="univalent-combinatorics.main-classes-of-latin-squares.html#1235" class="Function">Main-Class-Latin-Square-of-Order</a> <a id="1268" class="Symbol">:</a> <a id="1270" class="Symbol">(</a><a id="1271" href="univalent-combinatorics.main-classes-of-latin-squares.html#1271" class="Bound">m</a> <a id="1273" class="Symbol">:</a> <a id="1275" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1276" class="Symbol">)</a> <a id="1278" class="Symbol">→</a> <a id="1280" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1283" class="Symbol">(</a><a id="1284" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1289" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="1294" class="Symbol">)</a>
<a id="1296" href="univalent-combinatorics.main-classes-of-latin-squares.html#1235" class="Function">Main-Class-Latin-Square-of-Order</a> <a id="1329" href="univalent-combinatorics.main-classes-of-latin-squares.html#1329" class="Bound">m</a> <a id="1331" class="Symbol">=</a>
  <a id="1335" href="univalent-combinatorics.main-classes-of-latin-hypercubes.html#2197" class="Function">Main-Class-Latin-Hypercube-of-Order</a> <a id="1371" class="Number">2</a> <a id="1373" href="univalent-combinatorics.main-classes-of-latin-squares.html#1329" class="Bound">m</a>
</pre>
## Properties

### The groupoid of main classes of latin squares of fixed order is a groupoid

<pre class="Agda"><a id="is-1-type-Main-Class-Latin-Square-of-Order"></a><a id="1483" href="univalent-combinatorics.main-classes-of-latin-squares.html#1483" class="Function">is-1-type-Main-Class-Latin-Square-of-Order</a> <a id="1526" class="Symbol">:</a>
  <a id="1530" class="Symbol">(</a><a id="1531" href="univalent-combinatorics.main-classes-of-latin-squares.html#1531" class="Bound">m</a> <a id="1533" class="Symbol">:</a> <a id="1535" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1536" class="Symbol">)</a> <a id="1538" class="Symbol">→</a> <a id="1540" href="foundation-core.1-types.html#559" class="Function">is-1-type</a> <a id="1550" class="Symbol">(</a><a id="1551" href="univalent-combinatorics.main-classes-of-latin-squares.html#1235" class="Function">Main-Class-Latin-Square-of-Order</a> <a id="1584" href="univalent-combinatorics.main-classes-of-latin-squares.html#1531" class="Bound">m</a><a id="1585" class="Symbol">)</a>
<a id="1587" href="univalent-combinatorics.main-classes-of-latin-squares.html#1483" class="Function">is-1-type-Main-Class-Latin-Square-of-Order</a> <a id="1630" class="Symbol">=</a>
  <a id="1634" href="univalent-combinatorics.main-classes-of-latin-hypercubes.html#3548" class="Function">is-1-type-Main-Class-Latin-Hypercube-of-Order</a> <a id="1680" class="Number">2</a>
</pre>
### The groupoid of main classes of latin squares of fixed order is π₁-finite

<pre class="Agda"><a id="is-untruncated-π-finite-Main-Class-Latin-Square-of-Order"></a><a id="1774" href="univalent-combinatorics.main-classes-of-latin-squares.html#1774" class="Function">is-untruncated-π-finite-Main-Class-Latin-Square-of-Order</a> <a id="1831" class="Symbol">:</a>
  <a id="1835" class="Symbol">(</a><a id="1836" href="univalent-combinatorics.main-classes-of-latin-squares.html#1836" class="Bound">k</a> <a id="1838" href="univalent-combinatorics.main-classes-of-latin-squares.html#1838" class="Bound">m</a> <a id="1840" class="Symbol">:</a> <a id="1842" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1843" class="Symbol">)</a> <a id="1845" class="Symbol">→</a> <a id="1847" href="univalent-combinatorics.untruncated-pi-finite-types.html#3471" class="Function">is-untruncated-π-finite</a> <a id="1871" href="univalent-combinatorics.main-classes-of-latin-squares.html#1836" class="Bound">k</a> <a id="1873" class="Symbol">(</a><a id="1874" href="univalent-combinatorics.main-classes-of-latin-squares.html#1235" class="Function">Main-Class-Latin-Square-of-Order</a> <a id="1907" href="univalent-combinatorics.main-classes-of-latin-squares.html#1838" class="Bound">m</a><a id="1908" class="Symbol">)</a>
<a id="1910" href="univalent-combinatorics.main-classes-of-latin-squares.html#1774" class="Function">is-untruncated-π-finite-Main-Class-Latin-Square-of-Order</a> <a id="1967" href="univalent-combinatorics.main-classes-of-latin-squares.html#1967" class="Bound">k</a> <a id="1969" class="Symbol">=</a>
  <a id="1973" href="univalent-combinatorics.main-classes-of-latin-hypercubes.html#4169" class="Function">is-untruncated-π-finite-Main-Class-Latin-Hypercube-of-Order</a> <a id="2033" href="univalent-combinatorics.main-classes-of-latin-squares.html#1967" class="Bound">k</a> <a id="2035" class="Number">2</a>

<a id="is-truncated-π-finite-Main-Class-Latin-Square-of-Order"></a><a id="2038" href="univalent-combinatorics.main-classes-of-latin-squares.html#2038" class="Function">is-truncated-π-finite-Main-Class-Latin-Square-of-Order</a> <a id="2093" class="Symbol">:</a>
  <a id="2097" class="Symbol">(</a><a id="2098" href="univalent-combinatorics.main-classes-of-latin-squares.html#2098" class="Bound">m</a> <a id="2100" class="Symbol">:</a> <a id="2102" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2103" class="Symbol">)</a> <a id="2105" class="Symbol">→</a> <a id="2107" href="univalent-combinatorics.truncated-pi-finite-types.html#2701" class="Function">is-truncated-π-finite</a> <a id="2129" class="Number">1</a> <a id="2131" class="Symbol">(</a><a id="2132" href="univalent-combinatorics.main-classes-of-latin-squares.html#1235" class="Function">Main-Class-Latin-Square-of-Order</a> <a id="2165" href="univalent-combinatorics.main-classes-of-latin-squares.html#2098" class="Bound">m</a><a id="2166" class="Symbol">)</a>
<a id="2168" href="univalent-combinatorics.main-classes-of-latin-squares.html#2038" class="Function">is-truncated-π-finite-Main-Class-Latin-Square-of-Order</a> <a id="2223" class="Symbol">=</a>
  <a id="2227" href="univalent-combinatorics.main-classes-of-latin-hypercubes.html#7139" class="Function">is-truncated-π-finite-Main-Class-Latin-Hypercube-of-Order</a> <a id="2285" class="Number">2</a>
</pre>
### The sequence of the number of main classes of latin squares of finite order

The following sequence defines [A003090](https://oeis.org/A003090) in the OEIS.

<pre class="Agda"><a id="number-of-main-classes-of-Latin-squares-of-order"></a><a id="2462" href="univalent-combinatorics.main-classes-of-latin-squares.html#2462" class="Function">number-of-main-classes-of-Latin-squares-of-order</a> <a id="2511" class="Symbol">:</a> <a id="2513" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2515" class="Symbol">→</a> <a id="2517" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="2519" href="univalent-combinatorics.main-classes-of-latin-squares.html#2462" class="Function">number-of-main-classes-of-Latin-squares-of-order</a> <a id="2568" class="Symbol">=</a>
  <a id="2572" href="univalent-combinatorics.main-classes-of-latin-hypercubes.html#7612" class="Function">number-of-main-classes-of-Latin-hypercubes-of-order</a> <a id="2624" class="Number">2</a>

<a id="mere-equiv-number-of-main-classes-of-Latin-squares-of-order"></a><a id="2627" href="univalent-combinatorics.main-classes-of-latin-squares.html#2627" class="Function">mere-equiv-number-of-main-classes-of-Latin-squares-of-order</a> <a id="2687" class="Symbol">:</a>
  <a id="2691" class="Symbol">(</a><a id="2692" href="univalent-combinatorics.main-classes-of-latin-squares.html#2692" class="Bound">m</a> <a id="2694" class="Symbol">:</a> <a id="2696" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2697" class="Symbol">)</a> <a id="2699" class="Symbol">→</a>
  <a id="2703" href="foundation.mere-equivalences.html#960" class="Function">mere-equiv</a>
    <a id="2718" class="Symbol">(</a> <a id="2720" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="2724" class="Symbol">(</a><a id="2725" href="univalent-combinatorics.main-classes-of-latin-squares.html#2462" class="Function">number-of-main-classes-of-Latin-squares-of-order</a> <a id="2774" href="univalent-combinatorics.main-classes-of-latin-squares.html#2692" class="Bound">m</a><a id="2775" class="Symbol">))</a>
    <a id="2782" class="Symbol">(</a> <a id="2784" href="foundation.set-truncations.html#2028" class="Function">type-trunc-Set</a> <a id="2799" class="Symbol">(</a><a id="2800" href="univalent-combinatorics.main-classes-of-latin-squares.html#1235" class="Function">Main-Class-Latin-Square-of-Order</a> <a id="2833" href="univalent-combinatorics.main-classes-of-latin-squares.html#2692" class="Bound">m</a><a id="2834" class="Symbol">))</a>
<a id="2837" href="univalent-combinatorics.main-classes-of-latin-squares.html#2627" class="Function">mere-equiv-number-of-main-classes-of-Latin-squares-of-order</a> <a id="2897" class="Symbol">=</a>
  <a id="2901" href="univalent-combinatorics.main-classes-of-latin-hypercubes.html#7839" class="Function">mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-order</a> <a id="2964" class="Number">2</a>
</pre>