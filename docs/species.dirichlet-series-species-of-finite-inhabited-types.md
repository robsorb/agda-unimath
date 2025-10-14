# Dirichlet series of species of finite inhabited types

<pre class="Agda"><a id="66" class="Keyword">module</a> <a id="73" href="species.dirichlet-series-species-of-finite-inhabited-types.html" class="Module">species.dirichlet-series-species-of-finite-inhabited-types</a> <a id="132" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="species.species-of-finite-inhabited-types.html" class="Module">species.species-of-finite-inhabited-types</a>

<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="univalent-combinatorics.cycle-prime-decomposition-natural-numbers.html" class="Module">univalent-combinatorics.cycle-prime-decomposition-natural-numbers</a>
<a id="506" class="Keyword">open</a> <a id="511" class="Keyword">import</a> <a id="518" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="555" class="Keyword">open</a> <a id="560" class="Keyword">import</a> <a id="567" href="univalent-combinatorics.inhabited-finite-types.html" class="Module">univalent-combinatorics.inhabited-finite-types</a>
</pre>
</details>

## Idea

In classical mathematics, the _Dirichlet series_ of a
[species of finite inhabited types](species.species-of-finite-inhabited-types.md)
`T` is the formal series in `s`:

```text
  Σ (n : ℕ∖{0}) (|T({1,...,n})| n^(-s) / n!).
```

If `s` is a [negative integer](elementary-number-theory.negative-integers.md),
the categorified version of this formula is

```text
  Σ (F : Finite-Type∖{∅}), T(F) × (S → F).
```

We can generalize it to [species of types](species.species-of-types.md) as

```text
  Σ (X : UU) (T(X) × (S → X)).
```

The interesting case is when `s` is a positive number. The categorified version
of this formula then becomes

```text
  Σ ( n : ℕ∖{0}),
    ( Σ ( F : Type-With-Cardinality-ℕ n) ,
        ( T(F) × (S → cycle-prime-decomposition-ℕ n)).
```

We have picked the [concrete group](group-theory.concrete-groups.md)
`cycle-prime-decomposition-ℕ n` because it is closed under cartesian product and
also because its groupoid cardinality is `1/n`.

## Definition

<pre class="Agda"><a id="dirichlet-series-species-Inhabited-Finite-Type"></a><a id="1630" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1630" class="Function">dirichlet-series-species-Inhabited-Finite-Type</a> <a id="1677" class="Symbol">:</a>
  <a id="1681" class="Symbol">{</a><a id="1682" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1682" class="Bound">l1</a> <a id="1685" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1685" class="Bound">l2</a> <a id="1688" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1688" class="Bound">l3</a> <a id="1691" class="Symbol">:</a> <a id="1693" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1698" class="Symbol">}</a> <a id="1700" class="Symbol">→</a> <a id="1702" href="species.species-of-finite-inhabited-types.html#711" class="Function">species-Inhabited-Finite-Type</a> <a id="1732" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1682" class="Bound">l1</a> <a id="1735" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1685" class="Bound">l2</a> <a id="1738" class="Symbol">→</a> <a id="1740" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1743" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1688" class="Bound">l3</a> <a id="1746" class="Symbol">→</a>
  <a id="1750" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1753" class="Symbol">(</a><a id="1754" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1759" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1682" class="Bound">l1</a> <a id="1762" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1764" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1685" class="Bound">l2</a> <a id="1767" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1769" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1688" class="Bound">l3</a><a id="1771" class="Symbol">)</a>
<a id="1773" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1630" class="Function">dirichlet-series-species-Inhabited-Finite-Type</a> <a id="1820" class="Symbol">{</a><a id="1821" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1821" class="Bound">l1</a><a id="1823" class="Symbol">}</a> <a id="1825" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1825" class="Bound">T</a> <a id="1827" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1827" class="Bound">S</a> <a id="1829" class="Symbol">=</a>
  <a id="1833" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1835" class="Symbol">(</a> <a id="1837" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1838" class="Symbol">)</a>
    <a id="1844" class="Symbol">(</a> <a id="1846" class="Symbol">λ</a> <a id="1848" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1848" class="Bound">n</a> <a id="1850" class="Symbol">→</a>
      <a id="1858" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1860" class="Symbol">(</a> <a id="1862" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="1886" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1821" class="Bound">l1</a> <a id="1889" class="Symbol">(</a><a id="1890" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1897" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1848" class="Bound">n</a><a id="1898" class="Symbol">))</a>
        <a id="1909" class="Symbol">(</a> <a id="1911" class="Symbol">λ</a> <a id="1913" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1913" class="Bound">F</a> <a id="1915" class="Symbol">→</a>
          <a id="1927" class="Symbol">(</a> <a id="1929" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a>
            <a id="1958" class="Symbol">(</a> <a id="1960" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1825" class="Bound">T</a>
              <a id="1976" class="Symbol">(</a> <a id="1978" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="2007" class="Symbol">(</a><a id="2008" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2015" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1848" class="Bound">n</a><a id="2016" class="Symbol">)</a> <a id="2018" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1913" class="Bound">F</a> <a id="2020" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
                <a id="2038" href="univalent-combinatorics.inhabited-finite-types.html#5670" class="Function">is-finite-and-inhabited-type-Type-With-Cardinality-ℕ-succ-ℕ</a>
                  <a id="2116" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1848" class="Bound">n</a>
                  <a id="2136" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1913" class="Bound">F</a><a id="2137" class="Symbol">)))</a> <a id="2141" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
          <a id="2153" class="Symbol">(</a> <a id="2155" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1827" class="Bound">S</a> <a id="2157" class="Symbol">→</a> <a id="2159" href="univalent-combinatorics.cycle-prime-decomposition-natural-numbers.html#2102" class="Function">cycle-prime-decomposition-ℕ</a> <a id="2187" class="Symbol">(</a><a id="2188" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2195" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1848" class="Bound">n</a><a id="2196" class="Symbol">)</a> <a id="2198" class="Symbol">_)))</a>
</pre>