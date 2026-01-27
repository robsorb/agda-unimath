# Taxicab numbers

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="elementary-number-theory.taxicab-numbers.html" class="Module">elementary-number-theory.taxicab-numbers</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="elementary-number-theory.cubes-natural-numbers.html" class="Module">elementary-number-theory.cubes-natural-numbers</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="elementary-number-theory.nonzero-natural-numbers.html" class="Module">elementary-number-theory.nonzero-natural-numbers</a>

<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="479" class="Keyword">open</a> <a id="484" class="Keyword">import</a> <a id="491" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="559" class="Keyword">open</a> <a id="564" class="Keyword">import</a> <a id="571" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="597" class="Keyword">open</a> <a id="602" class="Keyword">import</a> <a id="609" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The `n`-th
{{#concept "taxicab number" Agda=is-taxicab-number-ℕ WD="taxicab number" WDID=Q1462591}}
`taxicab n` is the smallest
[natural number](elementary-number-theory.natural-numbers.md) `x` such that `x`
is a [sum](elementary-number-theory.addition-natural-numbers.md) of two
[cubes](elementary-number-theory.cubes-natural-numbers.md) in `n`
[distinct](foundation.negated-equality.md) ways.

**Note:** The definition of taxicab numbers only considers sums of
[positive integers](elementary-number-theory.nonzero-natural-numbers.md). Note
that if `n` is a cube, i.e., if `n ＝ c³`, then the only solutions to the
equation

```text
  a³ + b³ = c³
```

have either `a ＝ 0` or `b ＝ 0` by
[Fermat's last theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem).
Therefore `n` can be written in at least two different ways as a sum of cubes of
positive natural numbers if and only if it can be written in at least two
different ways as a sum of cubes of arbitrary natural numbers. However, the
class of natural numbers that can be written in exactly one way as a sum of
cubes is different when we consider sums of cubes of positive natural numbers or
sums of cubes of arbitrary natural numbers.

## Definitions

### The type of decompositions of a natural number as a sum of cubes

<pre class="Agda"><a id="sum-of-cubes-decomposition-ℕ"></a><a id="2015" href="elementary-number-theory.taxicab-numbers.html#2015" class="Function">sum-of-cubes-decomposition-ℕ</a> <a id="2044" class="Symbol">:</a> <a id="2046" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2048" class="Symbol">→</a> <a id="2050" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2053" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2059" href="elementary-number-theory.taxicab-numbers.html#2015" class="Function">sum-of-cubes-decomposition-ℕ</a> <a id="2088" href="elementary-number-theory.taxicab-numbers.html#2088" class="Bound">x</a> <a id="2090" class="Symbol">=</a>
  <a id="2094" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2096" class="Symbol">(</a> <a id="2098" href="elementary-number-theory.nonzero-natural-numbers.html#1455" class="Function">nonzero-ℕ</a><a id="2107" class="Symbol">)</a>
    <a id="2113" class="Symbol">(</a> <a id="2115" class="Symbol">λ</a> <a id="2117" href="elementary-number-theory.taxicab-numbers.html#2117" class="Bound">y</a> <a id="2119" class="Symbol">→</a>
      <a id="2127" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2129" class="Symbol">(</a> <a id="2131" href="elementary-number-theory.nonzero-natural-numbers.html#1455" class="Function">nonzero-ℕ</a><a id="2140" class="Symbol">)</a>
        <a id="2150" class="Symbol">(</a> <a id="2152" class="Symbol">λ</a> <a id="2154" href="elementary-number-theory.taxicab-numbers.html#2154" class="Bound">z</a> <a id="2156" class="Symbol">→</a>
          <a id="2168" class="Symbol">(</a> <a id="2170" href="elementary-number-theory.inequality-natural-numbers.html#1276" class="Function">leq-ℕ</a> <a id="2176" class="Symbol">(</a><a id="2177" href="elementary-number-theory.nonzero-natural-numbers.html#1536" class="Function">nat-nonzero-ℕ</a> <a id="2191" href="elementary-number-theory.taxicab-numbers.html#2117" class="Bound">y</a><a id="2192" class="Symbol">)</a> <a id="2194" class="Symbol">(</a><a id="2195" href="elementary-number-theory.nonzero-natural-numbers.html#1536" class="Function">nat-nonzero-ℕ</a> <a id="2209" href="elementary-number-theory.taxicab-numbers.html#2154" class="Bound">z</a><a id="2210" class="Symbol">))</a> <a id="2213" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
          <a id="2225" class="Symbol">(</a> <a id="2227" href="elementary-number-theory.cubes-natural-numbers.html#812" class="Function">cube-ℕ</a> <a id="2234" class="Symbol">(</a><a id="2235" href="elementary-number-theory.nonzero-natural-numbers.html#1536" class="Function">nat-nonzero-ℕ</a> <a id="2249" href="elementary-number-theory.taxicab-numbers.html#2117" class="Bound">y</a><a id="2250" class="Symbol">)</a> <a id="2252" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="2255" href="elementary-number-theory.cubes-natural-numbers.html#812" class="Function">cube-ℕ</a> <a id="2262" class="Symbol">(</a><a id="2263" href="elementary-number-theory.nonzero-natural-numbers.html#1536" class="Function">nat-nonzero-ℕ</a> <a id="2277" href="elementary-number-theory.taxicab-numbers.html#2154" class="Bound">z</a><a id="2278" class="Symbol">)</a> <a id="2280" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2282" href="elementary-number-theory.taxicab-numbers.html#2088" class="Bound">x</a><a id="2283" class="Symbol">)))</a>
</pre>
### The predicate of being a sum of two cubes in exactly `n` distinct ways

A number `x` is a sum of cubes in `n` distinct ways if there is an equivalence

```text
  Fin n ≃ sum-of-cubes-decomposition-ℕ x
```

from the
[standard finite type](univalent-combinatorics.standard-finite-types.md) to the
type `sum-of-cubes-decomposition-ℕ x` of ways of writing `x` as a sum of cubes.

<pre class="Agda"><a id="is-sum-of-cubes-in-number-of-distinct-ways-ℕ"></a><a id="2680" href="elementary-number-theory.taxicab-numbers.html#2680" class="Function">is-sum-of-cubes-in-number-of-distinct-ways-ℕ</a> <a id="2725" class="Symbol">:</a> <a id="2727" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2729" class="Symbol">→</a> <a id="2731" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2733" class="Symbol">→</a> <a id="2735" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2738" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2744" href="elementary-number-theory.taxicab-numbers.html#2680" class="Function">is-sum-of-cubes-in-number-of-distinct-ways-ℕ</a> <a id="2789" href="elementary-number-theory.taxicab-numbers.html#2789" class="Bound">n</a> <a id="2791" href="elementary-number-theory.taxicab-numbers.html#2791" class="Bound">x</a> <a id="2793" class="Symbol">=</a>
  <a id="2797" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="2801" href="elementary-number-theory.taxicab-numbers.html#2789" class="Bound">n</a> <a id="2803" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2805" href="elementary-number-theory.taxicab-numbers.html#2015" class="Function">sum-of-cubes-decomposition-ℕ</a> <a id="2834" href="elementary-number-theory.taxicab-numbers.html#2791" class="Bound">x</a>
</pre>
### The predicate of being the `n`-th taxicab number

<pre class="Agda"><a id="is-taxicab-number-ℕ"></a><a id="2903" href="elementary-number-theory.taxicab-numbers.html#2903" class="Function">is-taxicab-number-ℕ</a> <a id="2923" class="Symbol">:</a> <a id="2925" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2927" class="Symbol">→</a> <a id="2929" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2931" class="Symbol">→</a> <a id="2933" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2936" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2942" href="elementary-number-theory.taxicab-numbers.html#2903" class="Function">is-taxicab-number-ℕ</a> <a id="2962" href="elementary-number-theory.taxicab-numbers.html#2962" class="Bound">n</a> <a id="2964" href="elementary-number-theory.taxicab-numbers.html#2964" class="Bound">x</a> <a id="2966" class="Symbol">=</a>
  <a id="2970" href="elementary-number-theory.taxicab-numbers.html#2680" class="Function">is-sum-of-cubes-in-number-of-distinct-ways-ℕ</a> <a id="3015" href="elementary-number-theory.taxicab-numbers.html#2962" class="Bound">n</a> <a id="3017" href="elementary-number-theory.taxicab-numbers.html#2964" class="Bound">x</a> <a id="3019" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
  <a id="3023" class="Symbol">((</a><a id="3025" href="elementary-number-theory.taxicab-numbers.html#3025" class="Bound">y</a> <a id="3027" class="Symbol">:</a> <a id="3029" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="3030" class="Symbol">)</a> <a id="3032" class="Symbol">→</a> <a id="3034" href="elementary-number-theory.taxicab-numbers.html#2680" class="Function">is-sum-of-cubes-in-number-of-distinct-ways-ℕ</a> <a id="3079" href="elementary-number-theory.taxicab-numbers.html#2962" class="Bound">n</a> <a id="3081" href="elementary-number-theory.taxicab-numbers.html#3025" class="Bound">y</a> <a id="3083" class="Symbol">→</a> <a id="3085" href="elementary-number-theory.inequality-natural-numbers.html#1276" class="Function">leq-ℕ</a> <a id="3091" href="elementary-number-theory.taxicab-numbers.html#2964" class="Bound">x</a> <a id="3093" href="elementary-number-theory.taxicab-numbers.html#3025" class="Bound">y</a><a id="3094" class="Symbol">)</a>
</pre>
## See also

- [The Hardy-Ramanujan number](elementary-number-theory.hardy-ramanujan-number.md)

## External links

- [Taxicab numbers](https://en.wikipedia.org/wiki/Taxicab_number) at Wikipedia
- [Taxicab numbers](https://oeis.org/A011541) in the OEIS.
