# Indexed W-types

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="trees.indexed-w-types.html" class="Module">trees.indexed-w-types</a> <a id="57" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="113" class="Keyword">open</a> <a id="118" class="Keyword">import</a> <a id="125" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The concept of _indexed W-types_ is a generalization of ordinary
[W-types](trees.w-types.md) using a dependently typed variant of
[polynomial endofunctors](trees.polynomial-endofunctors.md). The main idea is
that indexed W-types are initial
[algebras](trees.algebras-polynomial-endofunctors.md) for the polynomial
endofunctor

```text
  (X : I → UU) ↦ (λ (j : I) → Σ (a : A j), Π (i : I), B i j a → X i),
```

where `B : (i j : I) → A j → 𝒰` is a type family. In other words, given the data

```text
  A : I → 𝒰
  B : (i j : I) → A j → 𝒰
```

of an indexed container we obtain for each `j : I` a multivariable polynomial

```text
  Σ (a : A j), Π (i : I), B i j a → X i
```

Since the functorial operation

```text
  (X : I → UU) ↦ (λ (j : I) → Σ (a : A j), Π (i : I), B i j a → X i),
```

takes an `I`-indexed family of inputs and returns an `I`-indexed family of
outputs, it is endofunctorial, meaning that it can be iterated and we can
consider initial algebras for this endofunctor.

We will formally define the {{#concept "indexed W-type" Agda=indexed-𝕎}}
associated to the data of an indexed container as the inductive type generated
by

```text
  tree-indexed-𝕎 :
    (x : A j) (α : (i : I) (y : B i j x) → indexed-𝕎 i) → indexed-𝕎 j.
```

**Note.** In the usual definition of indexed container, the type family `B` is
directly given as a type family over `A`

```text
  B : (i : I) → A i → 𝒰,
```

and furthermore there is a reindexing function

```text
  j : (i : I) (a : A i) → B i a → I.
```

The pair `(B , j)` of such a type family and a reindexing function is via
[type duality](foundation.type-duality.md) equivalent to a single type family

```text
  (j i : I) → A i → 𝒰.
```

## Definitions

### The indexed W-type associated to an indexed container

<pre class="Agda"><a id="1954" class="Keyword">data</a>
  <a id="indexed-𝕎"></a><a id="1961" href="trees.indexed-w-types.html#1961" class="Datatype">indexed-𝕎</a>
    <a id="1975" class="Symbol">{</a><a id="1976" href="trees.indexed-w-types.html#1976" class="Bound">l1</a> <a id="1979" href="trees.indexed-w-types.html#1979" class="Bound">l2</a> <a id="1982" href="trees.indexed-w-types.html#1982" class="Bound">l3</a> <a id="1985" class="Symbol">:</a> <a id="1987" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1992" class="Symbol">}</a> <a id="1994" class="Symbol">(</a><a id="1995" href="trees.indexed-w-types.html#1995" class="Bound">I</a> <a id="1997" class="Symbol">:</a> <a id="1999" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2002" href="trees.indexed-w-types.html#1976" class="Bound">l1</a><a id="2004" class="Symbol">)</a> <a id="2006" class="Symbol">(</a><a id="2007" href="trees.indexed-w-types.html#2007" class="Bound">A</a> <a id="2009" class="Symbol">:</a> <a id="2011" href="trees.indexed-w-types.html#1995" class="Bound">I</a> <a id="2013" class="Symbol">→</a> <a id="2015" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2018" href="trees.indexed-w-types.html#1979" class="Bound">l2</a><a id="2020" class="Symbol">)</a>
    <a id="2026" class="Symbol">(</a><a id="2027" href="trees.indexed-w-types.html#2027" class="Bound">B</a> <a id="2029" class="Symbol">:</a> <a id="2031" class="Symbol">(</a><a id="2032" href="trees.indexed-w-types.html#2032" class="Bound">i</a> <a id="2034" href="trees.indexed-w-types.html#2034" class="Bound">j</a> <a id="2036" class="Symbol">:</a> <a id="2038" href="trees.indexed-w-types.html#1995" class="Bound">I</a><a id="2039" class="Symbol">)</a> <a id="2041" class="Symbol">→</a> <a id="2043" href="trees.indexed-w-types.html#2007" class="Bound">A</a> <a id="2045" href="trees.indexed-w-types.html#2034" class="Bound">j</a> <a id="2047" class="Symbol">→</a> <a id="2049" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2052" href="trees.indexed-w-types.html#1982" class="Bound">l3</a><a id="2054" class="Symbol">)</a> <a id="2056" class="Symbol">(</a><a id="2057" href="trees.indexed-w-types.html#2057" class="Bound">j</a> <a id="2059" class="Symbol">:</a> <a id="2061" href="trees.indexed-w-types.html#1995" class="Bound">I</a><a id="2062" class="Symbol">)</a> <a id="2064" class="Symbol">:</a>
    <a id="2070" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2073" class="Symbol">(</a><a id="2074" href="trees.indexed-w-types.html#1976" class="Bound">l1</a> <a id="2077" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2079" href="trees.indexed-w-types.html#1979" class="Bound">l2</a> <a id="2082" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2084" href="trees.indexed-w-types.html#1982" class="Bound">l3</a><a id="2086" class="Symbol">)</a>
    <a id="2092" class="Keyword">where</a>
  <a id="indexed-𝕎.tree-indexed-𝕎"></a><a id="2100" href="trees.indexed-w-types.html#2100" class="InductiveConstructor">tree-indexed-𝕎</a> <a id="2115" class="Symbol">:</a>
    <a id="2121" class="Symbol">(</a><a id="2122" href="trees.indexed-w-types.html#2122" class="Bound">x</a> <a id="2124" class="Symbol">:</a> <a id="2126" href="trees.indexed-w-types.html#2007" class="Bound">A</a> <a id="2128" href="trees.indexed-w-types.html#2057" class="Bound">j</a><a id="2129" class="Symbol">)</a> <a id="2131" class="Symbol">(</a><a id="2132" href="trees.indexed-w-types.html#2132" class="Bound">α</a> <a id="2134" class="Symbol">:</a> <a id="2136" class="Symbol">(</a><a id="2137" href="trees.indexed-w-types.html#2137" class="Bound">i</a> <a id="2139" class="Symbol">:</a> <a id="2141" href="trees.indexed-w-types.html#1995" class="Bound">I</a><a id="2142" class="Symbol">)</a> <a id="2144" class="Symbol">(</a><a id="2145" href="trees.indexed-w-types.html#2145" class="Bound">y</a> <a id="2147" class="Symbol">:</a> <a id="2149" href="trees.indexed-w-types.html#2027" class="Bound">B</a> <a id="2151" href="trees.indexed-w-types.html#2137" class="Bound">i</a> <a id="2153" href="trees.indexed-w-types.html#2057" class="Bound">j</a> <a id="2155" href="trees.indexed-w-types.html#2122" class="Bound">x</a><a id="2156" class="Symbol">)</a> <a id="2158" class="Symbol">→</a> <a id="2160" href="trees.indexed-w-types.html#1961" class="Datatype">indexed-𝕎</a> <a id="2170" href="trees.indexed-w-types.html#1995" class="Bound">I</a> <a id="2172" href="trees.indexed-w-types.html#2007" class="Bound">A</a> <a id="2174" href="trees.indexed-w-types.html#2027" class="Bound">B</a> <a id="2176" href="trees.indexed-w-types.html#2137" class="Bound">i</a><a id="2177" class="Symbol">)</a> <a id="2179" class="Symbol">→</a>
    <a id="2185" href="trees.indexed-w-types.html#1961" class="Datatype">indexed-𝕎</a> <a id="2195" href="trees.indexed-w-types.html#1995" class="Bound">I</a> <a id="2197" href="trees.indexed-w-types.html#2007" class="Bound">A</a> <a id="2199" href="trees.indexed-w-types.html#2027" class="Bound">B</a> <a id="2201" href="trees.indexed-w-types.html#2057" class="Bound">j</a>
</pre>