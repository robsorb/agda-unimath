# Infinite conatural numbers

<pre class="Agda"><a id="39" class="Symbol">{-#</a> <a id="43" class="Keyword">OPTIONS</a> <a id="51" class="Pragma">--guardedness</a> <a id="65" class="Symbol">#-}</a>

<a id="70" class="Keyword">module</a> <a id="77" href="elementary-number-theory.infinite-conatural-numbers.html" class="Module">elementary-number-theory.infinite-conatural-numbers</a> <a id="129" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="elementary-number-theory.conatural-numbers.html" class="Module">elementary-number-theory.conatural-numbers</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="elementary-number-theory.equality-conatural-numbers.html" class="Module">elementary-number-theory.equality-conatural-numbers</a>

<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="403" class="Keyword">open</a> <a id="408" class="Keyword">import</a> <a id="415" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

A [conatural number](elementary-number-theory.conatural-numbers.md) `x` is
{{#concept "infinite" Disambiguation="conatural number" Agda=is-infinite-successor-condition-ℕ∞}}
if it is its own predecessor

```text
  decons-ℕ∞ x ＝ inl x
```

or, [equivalently](foundation-core.equivalences.md), if it is its own successor

```text
  x ＝ succ-ℕ∞ x.
```

## Definitions

### The predicate on conatural numbers of being infinite

<pre class="Agda"><a id="is-infinite-ℕ∞"></a><a id="943" href="elementary-number-theory.infinite-conatural-numbers.html#943" class="Function">is-infinite-ℕ∞</a> <a id="958" class="Symbol">:</a> <a id="960" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a> <a id="963" class="Symbol">→</a> <a id="965" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="968" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="974" href="elementary-number-theory.infinite-conatural-numbers.html#943" class="Function">is-infinite-ℕ∞</a> <a id="989" href="elementary-number-theory.infinite-conatural-numbers.html#989" class="Bound">x</a> <a id="991" class="Symbol">=</a> <a id="993" href="elementary-number-theory.conatural-numbers.html#1114" class="Field">decons-ℕ∞</a> <a id="1003" href="elementary-number-theory.infinite-conatural-numbers.html#989" class="Bound">x</a> <a id="1005" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1007" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="1011" href="elementary-number-theory.infinite-conatural-numbers.html#989" class="Bound">x</a>

<a id="is-infinite-successor-condition-ℕ∞"></a><a id="1014" href="elementary-number-theory.infinite-conatural-numbers.html#1014" class="Function">is-infinite-successor-condition-ℕ∞</a> <a id="1049" class="Symbol">:</a> <a id="1051" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a> <a id="1054" class="Symbol">→</a> <a id="1056" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1059" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1065" href="elementary-number-theory.infinite-conatural-numbers.html#1014" class="Function">is-infinite-successor-condition-ℕ∞</a> <a id="1100" href="elementary-number-theory.infinite-conatural-numbers.html#1100" class="Bound">x</a> <a id="1102" class="Symbol">=</a> <a id="1104" href="elementary-number-theory.infinite-conatural-numbers.html#1100" class="Bound">x</a> <a id="1106" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1108" href="elementary-number-theory.conatural-numbers.html#1457" class="Function">succ-ℕ∞</a> <a id="1116" href="elementary-number-theory.infinite-conatural-numbers.html#1100" class="Bound">x</a>
</pre>
## Properties

### The two definitions of being infinite agree

<pre class="Agda"><a id="is-infinite-is-infinite-successor-condition-ℕ∞"></a><a id="1195" href="elementary-number-theory.infinite-conatural-numbers.html#1195" class="Function">is-infinite-is-infinite-successor-condition-ℕ∞</a> <a id="1242" class="Symbol">:</a>
  <a id="1246" class="Symbol">{</a><a id="1247" href="elementary-number-theory.infinite-conatural-numbers.html#1247" class="Bound">x</a> <a id="1249" class="Symbol">:</a> <a id="1251" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a><a id="1253" class="Symbol">}</a> <a id="1255" class="Symbol">→</a> <a id="1257" href="elementary-number-theory.infinite-conatural-numbers.html#1014" class="Function">is-infinite-successor-condition-ℕ∞</a> <a id="1292" href="elementary-number-theory.infinite-conatural-numbers.html#1247" class="Bound">x</a> <a id="1294" class="Symbol">→</a> <a id="1296" href="elementary-number-theory.infinite-conatural-numbers.html#943" class="Function">is-infinite-ℕ∞</a> <a id="1311" href="elementary-number-theory.infinite-conatural-numbers.html#1247" class="Bound">x</a>
<a id="1313" href="elementary-number-theory.infinite-conatural-numbers.html#1195" class="Function">is-infinite-is-infinite-successor-condition-ℕ∞</a> <a id="1360" class="Symbol">=</a> <a id="1362" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="1365" href="elementary-number-theory.conatural-numbers.html#1114" class="Field">decons-ℕ∞</a>

<a id="is-infinite-successor-condition-is-infinite-ℕ∞"></a><a id="1376" href="elementary-number-theory.infinite-conatural-numbers.html#1376" class="Function">is-infinite-successor-condition-is-infinite-ℕ∞</a> <a id="1423" class="Symbol">:</a>
  <a id="1427" class="Symbol">{</a><a id="1428" href="elementary-number-theory.infinite-conatural-numbers.html#1428" class="Bound">x</a> <a id="1430" class="Symbol">:</a> <a id="1432" href="elementary-number-theory.conatural-numbers.html#1044" class="Record">ℕ∞</a><a id="1434" class="Symbol">}</a> <a id="1436" class="Symbol">→</a> <a id="1438" href="elementary-number-theory.infinite-conatural-numbers.html#943" class="Function">is-infinite-ℕ∞</a> <a id="1453" href="elementary-number-theory.infinite-conatural-numbers.html#1428" class="Bound">x</a> <a id="1455" class="Symbol">→</a> <a id="1457" href="elementary-number-theory.infinite-conatural-numbers.html#1014" class="Function">is-infinite-successor-condition-ℕ∞</a> <a id="1492" href="elementary-number-theory.infinite-conatural-numbers.html#1428" class="Bound">x</a>
<a id="1494" href="elementary-number-theory.infinite-conatural-numbers.html#1376" class="Function">is-infinite-successor-condition-is-infinite-ℕ∞</a> <a id="1541" class="Symbol">=</a> <a id="1543" href="elementary-number-theory.equality-conatural-numbers.html#5282" class="Function">is-injective-decons-ℕ∞</a>
</pre>
### The point at infinity is infinite

<pre class="Agda"><a id="is-infinite-infinity-ℕ∞"></a><a id="1618" href="elementary-number-theory.infinite-conatural-numbers.html#1618" class="Function">is-infinite-infinity-ℕ∞</a> <a id="1642" class="Symbol">:</a> <a id="1644" href="elementary-number-theory.infinite-conatural-numbers.html#943" class="Function">is-infinite-ℕ∞</a> <a id="1659" href="elementary-number-theory.conatural-numbers.html#1327" class="Function">infinity-ℕ∞</a>
<a id="1671" href="elementary-number-theory.infinite-conatural-numbers.html#1618" class="Function">is-infinite-infinity-ℕ∞</a> <a id="1695" class="Symbol">=</a> <a id="1697" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="is-infinite-successor-condition-infinity-ℕ∞"></a><a id="1703" href="elementary-number-theory.infinite-conatural-numbers.html#1703" class="Function">is-infinite-successor-condition-infinity-ℕ∞</a> <a id="1747" class="Symbol">:</a>
  <a id="1751" href="elementary-number-theory.infinite-conatural-numbers.html#1014" class="Function">is-infinite-successor-condition-ℕ∞</a> <a id="1786" href="elementary-number-theory.conatural-numbers.html#1327" class="Function">infinity-ℕ∞</a>
<a id="1798" href="elementary-number-theory.infinite-conatural-numbers.html#1703" class="Function">is-infinite-successor-condition-infinity-ℕ∞</a> <a id="1842" class="Symbol">=</a>
  <a id="1846" href="elementary-number-theory.infinite-conatural-numbers.html#1376" class="Function">is-infinite-successor-condition-is-infinite-ℕ∞</a> <a id="1893" href="elementary-number-theory.infinite-conatural-numbers.html#1618" class="Function">is-infinite-infinity-ℕ∞</a>
</pre>