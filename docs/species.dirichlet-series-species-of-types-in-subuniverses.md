# Dirichlet series of species of types in subuniverses

<pre class="Agda"><a id="65" class="Keyword">module</a> <a id="72" href="species.dirichlet-series-species-of-types-in-subuniverses.html" class="Module">species.dirichlet-series-species-of-types-in-subuniverses</a> <a id="130" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="species.species-of-types-in-subuniverses.html" class="Module">species.species-of-types-in-subuniverses</a>
</pre>
</details>

## Idea

In classical mathematics, the _Dirichlet series_ of a
[species of finite inhabited types](species.species-of-finite-inhabited-types.md)
`T` is the formal series in `s` :

```text
  Σ (n : ℕ∖{0}), (|T({1,...,n})| n^(-s) / n!)
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
[species of types in subuniverses](species.species-of-types-in-subuniverses.md).
Let `P` and `Q` two subuniverse such that `P` is closed under
[cartesian products](foundation.cartesian-product-types.md). Let `H : P → UU` be
a species such that for every `X , Y : P` the following
[equivalence](foundation-core.equivalences.md) is satisfied
`H (X × Y) ≃ H X × H Y`. Then we can define the
{{#concept "`H`-Dirichlet series" Disambiguation="of species of types in subuniverses" Agda=dirichlet-series-species-subuniverse}}
to any species of types in subuniverses `T` by

```text
  Σ (X : P), (T(X) × (S → H(X))).
```

The condition on `H` ensure that all the usual properties of the Dirichlet
series are satisfied.

## Definition

<pre class="Agda"><a id="1973" class="Keyword">module</a> <a id="1980" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1980" class="Module">_</a>
  <a id="1984" class="Symbol">{</a><a id="1985" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1985" class="Bound">l1</a> <a id="1988" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1988" class="Bound">l2</a> <a id="1991" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1991" class="Bound">l3</a> <a id="1994" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1994" class="Bound">l4</a> <a id="1997" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1997" class="Bound">l5</a> <a id="2000" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2000" class="Bound">l6</a> <a id="2003" class="Symbol">:</a> <a id="2005" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2010" class="Symbol">}</a>
  <a id="2014" class="Symbol">(</a><a id="2015" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2015" class="Bound">P</a> <a id="2017" class="Symbol">:</a> <a id="2019" href="foundation.subuniverses.html#1114" class="Function">subuniverse</a> <a id="2031" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1985" class="Bound">l1</a> <a id="2034" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1988" class="Bound">l2</a><a id="2036" class="Symbol">)</a>
  <a id="2040" class="Symbol">(</a><a id="2041" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2041" class="Bound">Q</a> <a id="2043" class="Symbol">:</a> <a id="2045" href="foundation.subuniverses.html#1114" class="Function">subuniverse</a> <a id="2057" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1991" class="Bound">l3</a> <a id="2060" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1994" class="Bound">l4</a><a id="2062" class="Symbol">)</a>
  <a id="2066" class="Symbol">(</a><a id="2067" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2067" class="Bound">C1</a> <a id="2070" class="Symbol">:</a> <a id="2072" href="foundation.cartesian-product-types.html#1140" class="Function">is-closed-under-products-subuniverse</a> <a id="2109" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2015" class="Bound">P</a><a id="2110" class="Symbol">)</a>
  <a id="2114" class="Symbol">(</a><a id="2115" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2115" class="Bound">H</a> <a id="2117" class="Symbol">:</a> <a id="2119" href="species.species-of-types-in-subuniverses.html#1018" class="Function">species-subuniverse-domain</a> <a id="2146" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1997" class="Bound">l5</a> <a id="2149" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2015" class="Bound">P</a><a id="2150" class="Symbol">)</a>
  <a id="2154" class="Symbol">(</a><a id="2155" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2155" class="Bound">C2</a> <a id="2158" class="Symbol">:</a> <a id="2160" href="species.species-of-types-in-subuniverses.html#1267" class="Function">preserves-product-species-subuniverse-domain</a> <a id="2205" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2015" class="Bound">P</a> <a id="2207" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2067" class="Bound">C1</a> <a id="2210" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2115" class="Bound">H</a><a id="2211" class="Symbol">)</a>
  <a id="2215" class="Symbol">(</a><a id="2216" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2216" class="Bound">T</a> <a id="2218" class="Symbol">:</a> <a id="2220" href="species.species-of-types-in-subuniverses.html#828" class="Function">species-subuniverse</a> <a id="2240" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2015" class="Bound">P</a> <a id="2242" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2041" class="Bound">Q</a><a id="2243" class="Symbol">)</a>
  <a id="2247" class="Symbol">(</a><a id="2248" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2248" class="Bound">S</a> <a id="2250" class="Symbol">:</a> <a id="2252" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2255" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2000" class="Bound">l6</a><a id="2257" class="Symbol">)</a>
  <a id="2261" class="Keyword">where</a>

  <a id="2270" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2270" class="Function">dirichlet-series-species-subuniverse</a> <a id="2307" class="Symbol">:</a> <a id="2309" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2312" class="Symbol">(</a><a id="2313" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2318" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1985" class="Bound">l1</a> <a id="2321" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2323" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1988" class="Bound">l2</a> <a id="2326" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2328" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1991" class="Bound">l3</a> <a id="2331" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2333" href="species.dirichlet-series-species-of-types-in-subuniverses.html#1997" class="Bound">l5</a> <a id="2336" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2338" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2000" class="Bound">l6</a><a id="2340" class="Symbol">)</a>
  <a id="2344" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2270" class="Function">dirichlet-series-species-subuniverse</a> <a id="2381" class="Symbol">=</a>
    <a id="2387" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2389" class="Symbol">(</a><a id="2390" href="foundation.subuniverses.html#1440" class="Function">type-subuniverse</a> <a id="2407" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2015" class="Bound">P</a><a id="2408" class="Symbol">)</a> <a id="2410" class="Symbol">(λ</a> <a id="2413" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2413" class="Bound">X</a> <a id="2415" class="Symbol">→</a> <a id="2417" href="foundation.subuniverses.html#1720" class="Function">inclusion-subuniverse</a> <a id="2439" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2041" class="Bound">Q</a> <a id="2441" class="Symbol">(</a><a id="2442" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2216" class="Bound">T</a> <a id="2444" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2413" class="Bound">X</a><a id="2445" class="Symbol">)</a> <a id="2447" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="2449" class="Symbol">(</a><a id="2450" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2248" class="Bound">S</a> <a id="2452" class="Symbol">→</a> <a id="2454" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2115" class="Bound">H</a> <a id="2456" class="Symbol">(</a><a id="2457" href="species.dirichlet-series-species-of-types-in-subuniverses.html#2413" class="Bound">X</a><a id="2458" class="Symbol">)))</a>
</pre>