# The zero conatural number

<pre class="Agda"><a id="38" class="Symbol">{-#</a> <a id="42" class="Keyword">OPTIONS</a> <a id="50" class="Pragma">--guardedness</a> <a id="64" class="Symbol">#-}</a>

<a id="69" class="Keyword">module</a> <a id="76" href="elementary-number-theory.zero-conatural-numbers.html" class="Module">elementary-number-theory.zero-conatural-numbers</a> <a id="124" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="elementary-number-theory.conatural-numbers.html" class="Module">elementary-number-theory.conatural-numbers</a>

<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="413" class="Keyword">open</a> <a id="418" class="Keyword">import</a> <a id="425" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="453" class="Keyword">open</a> <a id="458" class="Keyword">import</a> <a id="465" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="496" class="Keyword">open</a> <a id="501" class="Keyword">import</a> <a id="508" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A [conatural number](elementary-number-theory.conatural-numbers.md) `x` is
{{#concept "zero" Disambiguation="conatural number" Agda=is-zero-ℕ∞}} if it does
not have a predecessor.

## Definitions

### The predicate on conatural numbers of being zero

<pre class="Agda"><a id="is-zero-ℕ∞"></a><a id="822" href="elementary-number-theory.zero-conatural-numbers.html#822" class="Function">is-zero-ℕ∞</a> <a id="833" class="Symbol">:</a> <a id="835" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a> <a id="838" class="Symbol">→</a> <a id="840" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="843" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="849" href="elementary-number-theory.zero-conatural-numbers.html#822" class="Function">is-zero-ℕ∞</a> <a id="860" href="elementary-number-theory.zero-conatural-numbers.html#860" class="Bound">x</a> <a id="862" class="Symbol">=</a> <a id="864" href="foundation.maybe.html#2343" class="Function">is-exception-Maybe</a> <a id="883" class="Symbol">(</a><a id="884" href="elementary-number-theory.conatural-numbers.html#1114" class="Field">decons-ℕ∞</a> <a id="894" href="elementary-number-theory.zero-conatural-numbers.html#860" class="Bound">x</a><a id="895" class="Symbol">)</a>
</pre>
## Properties

### Zero is zero

<pre class="Agda"><a id="is-zero-zero-ℕ∞"></a><a id="943" href="elementary-number-theory.zero-conatural-numbers.html#943" class="Function">is-zero-zero-ℕ∞</a> <a id="959" class="Symbol">:</a> <a id="961" href="elementary-number-theory.zero-conatural-numbers.html#822" class="Function">is-zero-ℕ∞</a> <a id="972" href="elementary-number-theory.conatural-numbers.html#1211" class="Function">zero-ℕ∞</a>
<a id="980" href="elementary-number-theory.zero-conatural-numbers.html#943" class="Function">is-zero-zero-ℕ∞</a> <a id="996" class="Symbol">=</a> <a id="998" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### Successors are not zero

<pre class="Agda"><a id="is-not-zero-succ-ℕ∞"></a><a id="1045" href="elementary-number-theory.zero-conatural-numbers.html#1045" class="Function">is-not-zero-succ-ℕ∞</a> <a id="1065" class="Symbol">:</a> <a id="1067" class="Symbol">(</a><a id="1068" href="elementary-number-theory.zero-conatural-numbers.html#1068" class="Bound">x</a> <a id="1070" class="Symbol">:</a> <a id="1072" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a><a id="1074" class="Symbol">)</a> <a id="1076" class="Symbol">→</a> <a id="1078" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1080" class="Symbol">(</a><a id="1081" href="elementary-number-theory.zero-conatural-numbers.html#822" class="Function">is-zero-ℕ∞</a> <a id="1092" class="Symbol">(</a><a id="1093" href="elementary-number-theory.conatural-numbers.html#1457" class="Function">succ-ℕ∞</a> <a id="1101" href="elementary-number-theory.zero-conatural-numbers.html#1068" class="Bound">x</a><a id="1102" class="Symbol">))</a>
<a id="1105" href="elementary-number-theory.zero-conatural-numbers.html#1045" class="Function">is-not-zero-succ-ℕ∞</a> <a id="1125" href="elementary-number-theory.zero-conatural-numbers.html#1125" class="Bound">x</a> <a id="1127" class="Symbol">()</a>
</pre>
### The point at infinity is not zero

<pre class="Agda"><a id="is-not-zero-infinity-ℕ∞"></a><a id="1182" href="elementary-number-theory.zero-conatural-numbers.html#1182" class="Function">is-not-zero-infinity-ℕ∞</a> <a id="1206" class="Symbol">:</a> <a id="1208" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1210" class="Symbol">(</a><a id="1211" href="elementary-number-theory.zero-conatural-numbers.html#822" class="Function">is-zero-ℕ∞</a> <a id="1222" href="elementary-number-theory.conatural-numbers.html#1327" class="Function">infinity-ℕ∞</a><a id="1233" class="Symbol">)</a>
<a id="1235" href="elementary-number-theory.zero-conatural-numbers.html#1182" class="Function">is-not-zero-infinity-ℕ∞</a> <a id="1259" class="Symbol">=</a> <a id="1261" href="elementary-number-theory.zero-conatural-numbers.html#1045" class="Function">is-not-zero-succ-ℕ∞</a> <a id="1281" href="elementary-number-theory.conatural-numbers.html#1327" class="Function">infinity-ℕ∞</a>
</pre>
### Being zero is decidable

<pre class="Agda"><a id="is-decidable-is-zero-ℕ∞"></a><a id="1335" href="elementary-number-theory.zero-conatural-numbers.html#1335" class="Function">is-decidable-is-zero-ℕ∞</a> <a id="1359" class="Symbol">:</a> <a id="1361" class="Symbol">(</a><a id="1362" href="elementary-number-theory.zero-conatural-numbers.html#1362" class="Bound">x</a> <a id="1364" class="Symbol">:</a> <a id="1366" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a><a id="1368" class="Symbol">)</a> <a id="1370" class="Symbol">→</a> <a id="1372" href="foundation.decidable-types.html#1859" class="Function">is-decidable</a> <a id="1385" class="Symbol">(</a><a id="1386" href="elementary-number-theory.zero-conatural-numbers.html#822" class="Function">is-zero-ℕ∞</a> <a id="1397" href="elementary-number-theory.zero-conatural-numbers.html#1362" class="Bound">x</a><a id="1398" class="Symbol">)</a>
<a id="1400" href="elementary-number-theory.zero-conatural-numbers.html#1335" class="Function">is-decidable-is-zero-ℕ∞</a> <a id="1424" href="elementary-number-theory.zero-conatural-numbers.html#1424" class="Bound">x</a> <a id="1426" class="Keyword">with</a> <a id="1431" href="elementary-number-theory.conatural-numbers.html#1114" class="Field">decons-ℕ∞</a> <a id="1441" href="elementary-number-theory.zero-conatural-numbers.html#1424" class="Bound">x</a>
<a id="1443" href="elementary-number-theory.zero-conatural-numbers.html#1335" class="Function">is-decidable-is-zero-ℕ∞</a> <a id="1467" href="elementary-number-theory.zero-conatural-numbers.html#1467" class="Bound">x</a> <a id="1469" class="Symbol">|</a> <a id="1471" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="1475" href="elementary-number-theory.zero-conatural-numbers.html#1475" class="Bound">y</a> <a id="1477" class="Symbol">=</a> <a id="1479" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="1483" class="Symbol">(</a><a id="1484" href="elementary-number-theory.zero-conatural-numbers.html#1045" class="Function">is-not-zero-succ-ℕ∞</a> <a id="1504" href="elementary-number-theory.zero-conatural-numbers.html#1475" class="Bound">y</a><a id="1505" class="Symbol">)</a>
<a id="1507" href="elementary-number-theory.zero-conatural-numbers.html#1335" class="Function">is-decidable-is-zero-ℕ∞</a> <a id="1531" href="elementary-number-theory.zero-conatural-numbers.html#1531" class="Bound">x</a> <a id="1533" class="Symbol">|</a> <a id="1535" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="1539" href="elementary-number-theory.zero-conatural-numbers.html#1539" class="Bound">*</a> <a id="1541" class="Symbol">=</a> <a id="1543" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="1547" href="elementary-number-theory.zero-conatural-numbers.html#943" class="Function">is-zero-zero-ℕ∞</a>
</pre>
### Being zero is a property

<pre class="Agda"><a id="is-prop-is-zero-ℕ∞"></a><a id="1606" href="elementary-number-theory.zero-conatural-numbers.html#1606" class="Function">is-prop-is-zero-ℕ∞</a> <a id="1625" class="Symbol">:</a> <a id="1627" class="Symbol">(</a><a id="1628" href="elementary-number-theory.zero-conatural-numbers.html#1628" class="Bound">x</a> <a id="1630" class="Symbol">:</a> <a id="1632" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a><a id="1634" class="Symbol">)</a> <a id="1636" class="Symbol">→</a> <a id="1638" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1646" class="Symbol">(</a><a id="1647" href="elementary-number-theory.zero-conatural-numbers.html#822" class="Function">is-zero-ℕ∞</a> <a id="1658" href="elementary-number-theory.zero-conatural-numbers.html#1628" class="Bound">x</a><a id="1659" class="Symbol">)</a>
<a id="1661" href="elementary-number-theory.zero-conatural-numbers.html#1606" class="Function">is-prop-is-zero-ℕ∞</a> <a id="1680" class="Symbol">=</a> <a id="1682" href="foundation.maybe.html#2576" class="Function">is-prop-is-exception-Maybe</a> <a id="1709" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1711" href="elementary-number-theory.conatural-numbers.html#1114" class="Field">decons-ℕ∞</a>
</pre>
## See also

- [Positive conatural numbers](elementary-number-theory.positive-conatural-numbers.md)
- [Infinite conatural numbers](elementary-number-theory.infinite-conatural-numbers.md)
