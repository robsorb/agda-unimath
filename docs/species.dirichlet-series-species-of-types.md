# Dirichlet series of species of types

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="species.dirichlet-series-species-of-types.html" class="Module">species.dirichlet-series-species-of-types</a> <a id="98" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

In classical mathematics, the _Dirichlet series_ of a
[species of finite inhabited types](species.species-of-finite-inhabited-types.md)
`T` is the formal series in `s`:

```text
  Σ (n : ℕ∖{0}), (|T({1,...,n})| n^(-s) / n!).
```

If `s` is a [negative integer](elementary-number-theory.negative-integers.md),
the categorified version of this formula is

```text
  Σ (F : Finite-Type∖{∅}), T(F) × (S → F).
```

We can generalize it to [species of types](species.species-of-types.md) as

```text
  Σ (X : UU), (T(X) × (S → X)).
```

The interesting case is when `s` is a positive number. The categorified version
of this formula then becomes

```text
  Σ ( n : ℕ∖{0}),
    ( Σ ( F : Type-With-Cardinality-ℕ n),
        ( T(F) × (S → cycle-prime-decomposition-ℕ n)).
```

We can generalize the two notions to
[species of types](species.species-of-types.md). Let `H : UU → UU` be a species
such that for every `X , Y : P` the following
[equivalence](foundation-core.equivalences.md) is satisfied
`H (X × Y) ≃ H X × H Y`. Then we can define the
{{#concept "`H`-Dirichlet series" Disambiguation="of species of types" Agda=dirichlet-series-species-types}}
of any species of types `T` by

```text
  Σ (X : P), (T(X) × (S → H(X))).
```

The condition on `H` ensure that all the usual properties of the Dirichlet
series are satisfied.

## Definition

<pre class="Agda"><a id="1697" class="Keyword">module</a> <a id="1704" href="species.dirichlet-series-species-of-types.html#1704" class="Module">_</a>
  <a id="1708" class="Symbol">{</a><a id="1709" href="species.dirichlet-series-species-of-types.html#1709" class="Bound">l1</a> <a id="1712" href="species.dirichlet-series-species-of-types.html#1712" class="Bound">l2</a> <a id="1715" href="species.dirichlet-series-species-of-types.html#1715" class="Bound">l3</a> <a id="1718" href="species.dirichlet-series-species-of-types.html#1718" class="Bound">l4</a> <a id="1721" class="Symbol">:</a> <a id="1723" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1728" class="Symbol">}</a>
  <a id="1732" class="Symbol">(</a><a id="1733" href="species.dirichlet-series-species-of-types.html#1733" class="Bound">H</a> <a id="1735" class="Symbol">:</a> <a id="1737" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1751" href="species.dirichlet-series-species-of-types.html#1709" class="Bound">l1</a> <a id="1754" href="species.dirichlet-series-species-of-types.html#1712" class="Bound">l2</a><a id="1756" class="Symbol">)</a>
  <a id="1760" class="Symbol">(</a><a id="1761" href="species.dirichlet-series-species-of-types.html#1761" class="Bound">C1</a> <a id="1764" class="Symbol">:</a> <a id="1766" href="species.species-of-types.html#694" class="Function">preserves-product-species-types</a> <a id="1798" href="species.dirichlet-series-species-of-types.html#1733" class="Bound">H</a><a id="1799" class="Symbol">)</a>
  <a id="1803" class="Symbol">(</a><a id="1804" href="species.dirichlet-series-species-of-types.html#1804" class="Bound">T</a> <a id="1806" class="Symbol">:</a> <a id="1808" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1822" href="species.dirichlet-series-species-of-types.html#1709" class="Bound">l1</a> <a id="1825" href="species.dirichlet-series-species-of-types.html#1715" class="Bound">l3</a><a id="1827" class="Symbol">)</a>
  <a id="1831" class="Symbol">(</a><a id="1832" href="species.dirichlet-series-species-of-types.html#1832" class="Bound">S</a> <a id="1834" class="Symbol">:</a> <a id="1836" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1839" href="species.dirichlet-series-species-of-types.html#1718" class="Bound">l4</a><a id="1841" class="Symbol">)</a>
  <a id="1845" class="Keyword">where</a>

  <a id="1854" href="species.dirichlet-series-species-of-types.html#1854" class="Function">dirichlet-series-species-types</a> <a id="1885" class="Symbol">:</a> <a id="1887" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1890" class="Symbol">(</a><a id="1891" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1896" href="species.dirichlet-series-species-of-types.html#1709" class="Bound">l1</a> <a id="1899" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1901" href="species.dirichlet-series-species-of-types.html#1712" class="Bound">l2</a> <a id="1904" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1906" href="species.dirichlet-series-species-of-types.html#1715" class="Bound">l3</a> <a id="1909" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1911" href="species.dirichlet-series-species-of-types.html#1718" class="Bound">l4</a><a id="1913" class="Symbol">)</a>
  <a id="1917" href="species.dirichlet-series-species-of-types.html#1854" class="Function">dirichlet-series-species-types</a> <a id="1948" class="Symbol">=</a> <a id="1950" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1952" class="Symbol">(</a><a id="1953" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1956" href="species.dirichlet-series-species-of-types.html#1709" class="Bound">l1</a><a id="1958" class="Symbol">)</a> <a id="1960" class="Symbol">(λ</a> <a id="1963" href="species.dirichlet-series-species-of-types.html#1963" class="Bound">X</a> <a id="1965" class="Symbol">→</a> <a id="1967" class="Symbol">(</a><a id="1968" href="species.dirichlet-series-species-of-types.html#1804" class="Bound">T</a> <a id="1970" href="species.dirichlet-series-species-of-types.html#1963" class="Bound">X</a><a id="1971" class="Symbol">)</a> <a id="1973" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1975" class="Symbol">(</a><a id="1976" href="species.dirichlet-series-species-of-types.html#1832" class="Bound">S</a> <a id="1978" class="Symbol">→</a> <a id="1980" href="species.dirichlet-series-species-of-types.html#1733" class="Bound">H</a> <a id="1982" class="Symbol">(</a><a id="1983" href="species.dirichlet-series-species-of-types.html#1963" class="Bound">X</a><a id="1984" class="Symbol">)))</a>
</pre>