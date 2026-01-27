# Inequality of conatural numbers

<pre class="Agda"><a id="44" class="Symbol">{-#</a> <a id="48" class="Keyword">OPTIONS</a> <a id="56" class="Pragma">--guardedness</a> <a id="70" class="Symbol">#-}</a>

<a id="75" class="Keyword">module</a> <a id="82" href="elementary-number-theory.inequality-conatural-numbers.html" class="Module">elementary-number-theory.inequality-conatural-numbers</a> <a id="136" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="elementary-number-theory.conatural-numbers.html" class="Module">elementary-number-theory.conatural-numbers</a>

<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="307" class="Keyword">open</a> <a id="312" class="Keyword">import</a> <a id="319" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="433" class="Keyword">open</a> <a id="438" class="Keyword">import</a> <a id="445" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="516" class="Keyword">open</a> <a id="521" class="Keyword">import</a> <a id="528" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="551" class="Keyword">open</a> <a id="556" class="Keyword">import</a> <a id="563" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="589" class="Keyword">open</a> <a id="594" class="Keyword">import</a> <a id="601" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="642" class="Keyword">open</a> <a id="647" class="Keyword">import</a> <a id="654" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="680" class="Keyword">open</a> <a id="685" class="Keyword">import</a> <a id="692" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="709" class="Keyword">open</a> <a id="714" class="Keyword">import</a> <a id="721" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="741" class="Keyword">open</a> <a id="746" class="Keyword">import</a> <a id="753" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="777" class="Keyword">open</a> <a id="782" class="Keyword">import</a> <a id="789" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="810" class="Keyword">open</a> <a id="815" class="Keyword">import</a> <a id="822" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="850" class="Keyword">open</a> <a id="855" class="Keyword">import</a> <a id="862" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="882" class="Keyword">open</a> <a id="887" class="Keyword">import</a> <a id="894" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
</pre>
</details>

## Idea

The
{{#concept "inequality relation" Disambiguation="on conatural numbers" Agda=_≤-ℕ∞_}}
`≤` on the [conatural numbers](elementary-number-theory.conatural-numbers.md) is
the unique coinductively defined relation such that `0` is less than any
conatural number, and such that `m+1 ≤ n+1`
[if and only if](foundation.logical-equivalences.md) `m ≤ n`.

## Definitions

### Inequality on the conatural numbers

<pre class="Agda"><a id="1358" class="Keyword">record</a> <a id="leq-ℕ∞"></a><a id="1365" href="elementary-number-theory.inequality-conatural-numbers.html#1365" class="Record">leq-ℕ∞</a> <a id="1372" class="Symbol">(</a><a id="1373" href="elementary-number-theory.inequality-conatural-numbers.html#1373" class="Bound">x</a> <a id="1375" href="elementary-number-theory.inequality-conatural-numbers.html#1375" class="Bound">y</a> <a id="1377" class="Symbol">:</a> <a id="1379" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a><a id="1381" class="Symbol">)</a> <a id="1383" class="Symbol">:</a> <a id="1385" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1388" href="Agda.Primitive.html#915" class="Primitive">lzero</a>

<a id="leq-Maybe-ℕ∞"></a><a id="1395" href="elementary-number-theory.inequality-conatural-numbers.html#1395" class="Function">leq-Maybe-ℕ∞</a> <a id="1408" class="Symbol">:</a> <a id="1410" href="foundation.maybe.html#1591" class="Function">Maybe</a> <a id="1416" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a> <a id="1419" class="Symbol">→</a> <a id="1421" href="foundation.maybe.html#1591" class="Function">Maybe</a> <a id="1427" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a> <a id="1430" class="Symbol">→</a> <a id="1432" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1435" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1441" href="elementary-number-theory.inequality-conatural-numbers.html#1395" class="Function">leq-Maybe-ℕ∞</a> <a id="1454" class="Symbol">(</a><a id="1455" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="1459" href="elementary-number-theory.inequality-conatural-numbers.html#1459" class="Bound">x</a><a id="1460" class="Symbol">)</a> <a id="1462" class="Symbol">(</a><a id="1463" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="1467" href="elementary-number-theory.inequality-conatural-numbers.html#1467" class="Bound">y</a><a id="1468" class="Symbol">)</a> <a id="1470" class="Symbol">=</a> <a id="1472" href="elementary-number-theory.inequality-conatural-numbers.html#1365" class="Record">leq-ℕ∞</a> <a id="1479" href="elementary-number-theory.inequality-conatural-numbers.html#1459" class="Bound">x</a> <a id="1481" href="elementary-number-theory.inequality-conatural-numbers.html#1467" class="Bound">y</a>
<a id="1483" href="elementary-number-theory.inequality-conatural-numbers.html#1395" class="Function">leq-Maybe-ℕ∞</a> <a id="1496" class="Symbol">(</a><a id="1497" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="1501" href="elementary-number-theory.inequality-conatural-numbers.html#1501" class="Bound">x</a><a id="1502" class="Symbol">)</a> <a id="1504" class="Symbol">(</a><a id="1505" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="1509" href="elementary-number-theory.inequality-conatural-numbers.html#1509" class="Bound">y</a><a id="1510" class="Symbol">)</a> <a id="1512" class="Symbol">=</a> <a id="1514" href="foundation-core.empty-types.html#801" class="Datatype">empty</a>
<a id="1520" href="elementary-number-theory.inequality-conatural-numbers.html#1395" class="Function">leq-Maybe-ℕ∞</a> <a id="1533" class="Symbol">(</a><a id="1534" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="1538" href="elementary-number-theory.inequality-conatural-numbers.html#1538" class="Bound">x</a><a id="1539" class="Symbol">)</a> <a id="1541" href="elementary-number-theory.inequality-conatural-numbers.html#1541" class="Bound">y</a> <a id="1543" class="Symbol">=</a> <a id="1545" href="foundation.unit-type.html#950" class="Record">unit</a>

<a id="1551" class="Keyword">record</a> <a id="1558" href="elementary-number-theory.inequality-conatural-numbers.html#1365" class="Record">leq-ℕ∞</a> <a id="1565" href="elementary-number-theory.inequality-conatural-numbers.html#1565" class="Bound">x</a> <a id="1567" href="elementary-number-theory.inequality-conatural-numbers.html#1567" class="Bound">y</a> <a id="1569" class="Keyword">where</a>
  <a id="1577" class="Keyword">coinductive</a>
  <a id="1591" class="Keyword">constructor</a> <a id="cons-leq-ℕ∞"></a><a id="1603" href="elementary-number-theory.inequality-conatural-numbers.html#1603" class="CoinductiveConstructor">cons-leq-ℕ∞</a>
  <a id="1617" class="Keyword">field</a>
    <a id="leq-ℕ∞.decons-leq-ℕ∞"></a><a id="1627" href="elementary-number-theory.inequality-conatural-numbers.html#1627" class="Field">decons-leq-ℕ∞</a> <a id="1641" class="Symbol">:</a> <a id="1643" href="elementary-number-theory.inequality-conatural-numbers.html#1395" class="Function">leq-Maybe-ℕ∞</a> <a id="1656" class="Symbol">(</a><a id="1657" href="elementary-number-theory.conatural-numbers.html#1114" class="Field">decons-ℕ∞</a> <a id="1667" href="elementary-number-theory.inequality-conatural-numbers.html#1565" class="Bound">x</a><a id="1668" class="Symbol">)</a> <a id="1670" class="Symbol">(</a><a id="1671" href="elementary-number-theory.conatural-numbers.html#1114" class="Field">decons-ℕ∞</a> <a id="1681" href="elementary-number-theory.inequality-conatural-numbers.html#1567" class="Bound">y</a><a id="1682" class="Symbol">)</a>

<a id="1685" class="Keyword">infix</a> <a id="1691" class="Number">30</a> <a id="1694" href="elementary-number-theory.inequality-conatural-numbers.html#1701" class="Function Operator">_≤-ℕ∞_</a>
<a id="_≤-ℕ∞_"></a><a id="1701" href="elementary-number-theory.inequality-conatural-numbers.html#1701" class="Function Operator">_≤-ℕ∞_</a> <a id="1708" class="Symbol">=</a> <a id="1710" href="elementary-number-theory.inequality-conatural-numbers.html#1365" class="Record">leq-ℕ∞</a>
</pre>