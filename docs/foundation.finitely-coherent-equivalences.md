# Finitely coherent equivalences

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="foundation.finitely-coherent-equivalences.html" class="Module">foundation.finitely-coherent-equivalences</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The condition of being a
{{#concept "finitely coherent equivalence" Agda=is-finitely-coherent-equivalence}}
is introduced by induction on the
[natural numbers](elementary-number-theory.natural-numbers.md). In the base
case, we say that any map `f : A → B` is a
{{#concept "`0`-coherent equivalence" Agda=is-finitely-coherent-equivalence}}.
Recursively, we say that a map `f : A → B` is an
{{#concept "`n + 1`-coherent equivalence" Agda=is-finitely-coherent-equivalence}}
if it comes equipped with a map `g : B → A` and a family of maps

```text
  r x y : (f x ＝ y) → (x ＝ g y)
```

indexed by `x : A` and `y : B`, such that each `r x y` is an `n`-coherent
equivalence.

By the equivalence of [retracting homotopies](foundation-core.retractions.md)
and
[transposition operations of identifications](foundation.transposition-identifications-along-retractions.md)
it therefore follows that a `1`-coherent equivalence is equivalently described
as a map equipped with a retraction. A `2`-coherent equivalence is a map
`f : A → B` equipped with `g : B → A` and for each `x : A` and `y : B` a map
`r x y : (f x ＝ y) → (x ＝ g y)`, equipped with

```text
  s x y : (x ＝ g y) → (f x ＝ y)
```

and for each `p : f x ＝ y` and `q : x ＝ g y` a map

```text
  t p q : (r x y p ＝ q) → (p ＝ s x y q).
```

This data is equivalent to the data of a
[coherently invertible map](foundation-core.coherently-invertible-maps.md)

```text
  r : (x : A) → g (f x) ＝ x
  s : (y : B) → f (g y) ＝ y
  t : (x : A) → ap f (r x) ＝ s (f x).
```

The condition of being an `n`-coherent equivalence is a
[proposition](foundation-core.propositions.md) for each `n ≥ 2`, and this
proposition is equivalent to being an equivalence.

## Definitions

### The predicate of being an `n`-coherent equivalence

<pre class="Agda"><a id="2113" class="Keyword">data</a>
  <a id="is-finitely-coherent-equivalence"></a><a id="2120" href="foundation.finitely-coherent-equivalences.html#2120" class="Datatype">is-finitely-coherent-equivalence</a>
    <a id="2157" class="Symbol">{</a><a id="2158" href="foundation.finitely-coherent-equivalences.html#2158" class="Bound">l1</a> <a id="2161" href="foundation.finitely-coherent-equivalences.html#2161" class="Bound">l2</a> <a id="2164" class="Symbol">:</a> <a id="2166" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2171" class="Symbol">}</a> <a id="2173" class="Symbol">{</a><a id="2174" href="foundation.finitely-coherent-equivalences.html#2174" class="Bound">A</a> <a id="2176" class="Symbol">:</a> <a id="2178" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2181" href="foundation.finitely-coherent-equivalences.html#2158" class="Bound">l1</a><a id="2183" class="Symbol">}</a> <a id="2185" class="Symbol">{</a><a id="2186" href="foundation.finitely-coherent-equivalences.html#2186" class="Bound">B</a> <a id="2188" class="Symbol">:</a> <a id="2190" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2193" href="foundation.finitely-coherent-equivalences.html#2161" class="Bound">l2</a><a id="2195" class="Symbol">}</a> <a id="2197" class="Symbol">:</a>
    <a id="2203" class="Symbol">(</a><a id="2204" href="foundation.finitely-coherent-equivalences.html#2204" class="Bound">n</a> <a id="2206" class="Symbol">:</a> <a id="2208" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2209" class="Symbol">)</a> <a id="2211" class="Symbol">(</a><a id="2212" href="foundation.finitely-coherent-equivalences.html#2212" class="Bound">f</a> <a id="2214" class="Symbol">:</a> <a id="2216" href="foundation.finitely-coherent-equivalences.html#2174" class="Bound">A</a> <a id="2218" class="Symbol">→</a> <a id="2220" href="foundation.finitely-coherent-equivalences.html#2186" class="Bound">B</a><a id="2221" class="Symbol">)</a> <a id="2223" class="Symbol">→</a> <a id="2225" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2228" class="Symbol">(</a><a id="2229" href="foundation.finitely-coherent-equivalences.html#2158" class="Bound">l1</a> <a id="2232" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2234" href="foundation.finitely-coherent-equivalences.html#2161" class="Bound">l2</a><a id="2236" class="Symbol">)</a>
  <a id="2240" class="Keyword">where</a>
  <a id="is-finitely-coherent-equivalence.is-zero-coherent-equivalence"></a><a id="2248" href="foundation.finitely-coherent-equivalences.html#2248" class="InductiveConstructor">is-zero-coherent-equivalence</a> <a id="2277" class="Symbol">:</a>
    <a id="2283" class="Symbol">(</a><a id="2284" href="foundation.finitely-coherent-equivalences.html#2284" class="Bound">f</a> <a id="2286" class="Symbol">:</a> <a id="2288" href="foundation.finitely-coherent-equivalences.html#2174" class="Bound">A</a> <a id="2290" class="Symbol">→</a> <a id="2292" href="foundation.finitely-coherent-equivalences.html#2186" class="Bound">B</a><a id="2293" class="Symbol">)</a> <a id="2295" class="Symbol">→</a> <a id="2297" href="foundation.finitely-coherent-equivalences.html#2120" class="Datatype">is-finitely-coherent-equivalence</a> <a id="2330" class="Number">0</a> <a id="2332" href="foundation.finitely-coherent-equivalences.html#2284" class="Bound">f</a>
  <a id="is-finitely-coherent-equivalence.is-succ-coherent-equivalence"></a><a id="2336" href="foundation.finitely-coherent-equivalences.html#2336" class="InductiveConstructor">is-succ-coherent-equivalence</a> <a id="2365" class="Symbol">:</a>
    <a id="2371" class="Symbol">(</a><a id="2372" href="foundation.finitely-coherent-equivalences.html#2372" class="Bound">n</a> <a id="2374" class="Symbol">:</a> <a id="2376" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2377" class="Symbol">)</a>
    <a id="2383" class="Symbol">(</a><a id="2384" href="foundation.finitely-coherent-equivalences.html#2384" class="Bound">f</a> <a id="2386" class="Symbol">:</a> <a id="2388" href="foundation.finitely-coherent-equivalences.html#2174" class="Bound">A</a> <a id="2390" class="Symbol">→</a> <a id="2392" href="foundation.finitely-coherent-equivalences.html#2186" class="Bound">B</a><a id="2393" class="Symbol">)</a> <a id="2395" class="Symbol">(</a><a id="2396" href="foundation.finitely-coherent-equivalences.html#2396" class="Bound">g</a> <a id="2398" class="Symbol">:</a> <a id="2400" href="foundation.finitely-coherent-equivalences.html#2186" class="Bound">B</a> <a id="2402" class="Symbol">→</a> <a id="2404" href="foundation.finitely-coherent-equivalences.html#2174" class="Bound">A</a><a id="2405" class="Symbol">)</a> <a id="2407" class="Symbol">(</a><a id="2408" href="foundation.finitely-coherent-equivalences.html#2408" class="Bound">H</a> <a id="2410" class="Symbol">:</a> <a id="2412" class="Symbol">(</a><a id="2413" href="foundation.finitely-coherent-equivalences.html#2413" class="Bound">x</a> <a id="2415" class="Symbol">:</a> <a id="2417" href="foundation.finitely-coherent-equivalences.html#2174" class="Bound">A</a><a id="2418" class="Symbol">)</a> <a id="2420" class="Symbol">(</a><a id="2421" href="foundation.finitely-coherent-equivalences.html#2421" class="Bound">y</a> <a id="2423" class="Symbol">:</a> <a id="2425" href="foundation.finitely-coherent-equivalences.html#2186" class="Bound">B</a><a id="2426" class="Symbol">)</a> <a id="2428" class="Symbol">→</a> <a id="2430" class="Symbol">(</a><a id="2431" href="foundation.finitely-coherent-equivalences.html#2384" class="Bound">f</a> <a id="2433" href="foundation.finitely-coherent-equivalences.html#2413" class="Bound">x</a> <a id="2435" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2437" href="foundation.finitely-coherent-equivalences.html#2421" class="Bound">y</a><a id="2438" class="Symbol">)</a> <a id="2440" class="Symbol">→</a> <a id="2442" class="Symbol">(</a><a id="2443" href="foundation.finitely-coherent-equivalences.html#2413" class="Bound">x</a> <a id="2445" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2447" href="foundation.finitely-coherent-equivalences.html#2396" class="Bound">g</a> <a id="2449" href="foundation.finitely-coherent-equivalences.html#2421" class="Bound">y</a><a id="2450" class="Symbol">))</a> <a id="2453" class="Symbol">→</a>
    <a id="2459" class="Symbol">((</a><a id="2461" href="foundation.finitely-coherent-equivalences.html#2461" class="Bound">x</a> <a id="2463" class="Symbol">:</a> <a id="2465" href="foundation.finitely-coherent-equivalences.html#2174" class="Bound">A</a><a id="2466" class="Symbol">)</a> <a id="2468" class="Symbol">(</a><a id="2469" href="foundation.finitely-coherent-equivalences.html#2469" class="Bound">y</a> <a id="2471" class="Symbol">:</a> <a id="2473" href="foundation.finitely-coherent-equivalences.html#2186" class="Bound">B</a><a id="2474" class="Symbol">)</a> <a id="2476" class="Symbol">→</a> <a id="2478" href="foundation.finitely-coherent-equivalences.html#2120" class="Datatype">is-finitely-coherent-equivalence</a> <a id="2511" href="foundation.finitely-coherent-equivalences.html#2372" class="Bound">n</a> <a id="2513" class="Symbol">(</a><a id="2514" href="foundation.finitely-coherent-equivalences.html#2408" class="Bound">H</a> <a id="2516" href="foundation.finitely-coherent-equivalences.html#2461" class="Bound">x</a> <a id="2518" href="foundation.finitely-coherent-equivalences.html#2469" class="Bound">y</a><a id="2519" class="Symbol">))</a> <a id="2522" class="Symbol">→</a>
    <a id="2528" href="foundation.finitely-coherent-equivalences.html#2120" class="Datatype">is-finitely-coherent-equivalence</a> <a id="2561" class="Symbol">(</a><a id="2562" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2569" href="foundation.finitely-coherent-equivalences.html#2372" class="Bound">n</a><a id="2570" class="Symbol">)</a> <a id="2572" href="foundation.finitely-coherent-equivalences.html#2384" class="Bound">f</a>
</pre>