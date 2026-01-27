# Finitely coherently invertible maps

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="foundation.finitely-coherently-invertible-maps.html" class="Module">foundation.finitely-coherently-invertible-maps</a> <a id="102" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

We introduce the concept of being a
{{#concept "finitely coherently invertible map" Agda=is-finitely-coherently-invertible}}
by induction on the
[natural numbers](elementary-number-theory.natural-numbers.md). In the base
case, we say that a map `f : A → B` is a
{{#concept "`0`-coherently invertible map" Agda=is-finitely-coherently-invertible}}
if it comes equipped with a map `g : B → A`. Recursively, we say that a map
`f : A → B` is an
{{#concept "`n + 1`-coherently invertible map" Agda=is-finitely-coherently-invertible}}
if it comes equipped with map `g : B → A` and a family of maps

```text
  r x y : (f x ＝ y) → (x ＝ g y)
```

indexed by `x : A` and `y : B`, such that each `r x y` is `n`-coherently
invertible.

A `1`-coherently invertible map `f : A → B` is therefore equivalently described
as a map equipped with an inverse `g : B → A` which is simultaneously a
[retraction](foundation-core.retractions.md) and a
[section](foundation-core.sections.md) of `f`. In other words, a `1`-coherently
invertible map is just an [invertible map](foundation-core.invertible-maps.md).

A `2`-coherently invertible map `f : A → B` comes equipped with `g : B → A` and
for each `x : A` and `y : B` two maps

```text
  r : (f x ＝ y) → (x ＝ g y)
  s : (x ＝ g y) → (f x ＝ y)
```

and for each `p : f x ＝ y` and `q : x ＝ g y` a map

```text
  t p q : (r p ＝ q) → (p ＝ s q)
  u p q : (p ＝ s q) → (r p ＝ q).
```

This data is equivalent to the data of

```text
  r : (x : A) → g (f x) ＝ x
  s : (y : B) → f (g y) ＝ y
  t : (x : A) → ap f (r x) ＝ s (f x)
  u : (y : B) → ap g (s y) ＝ r (f y).
```

The condition of being a `n`-coherently invertible map is not a
[proposition](foundation-core.propositions.md) for any `n`. In fact, for `n ≥ 1`
the type of all `n`-coherently invertible maps in a universe `𝒰` is equivalent
to the type of maps `sphere (n + 1) → 𝒰` of `n + 1`-spheres in the universe `𝒰`.

## Definitions

### The predicate of being an `n`-coherently invertible map

<pre class="Agda"><a id="2328" class="Keyword">data</a>
  <a id="is-finitely-coherently-invertible"></a><a id="2335" href="foundation.finitely-coherently-invertible-maps.html#2335" class="Datatype">is-finitely-coherently-invertible</a>
    <a id="2373" class="Symbol">{</a><a id="2374" href="foundation.finitely-coherently-invertible-maps.html#2374" class="Bound">l1</a> <a id="2377" href="foundation.finitely-coherently-invertible-maps.html#2377" class="Bound">l2</a> <a id="2380" class="Symbol">:</a> <a id="2382" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2387" class="Symbol">}</a> <a id="2389" class="Symbol">{</a><a id="2390" href="foundation.finitely-coherently-invertible-maps.html#2390" class="Bound">A</a> <a id="2392" class="Symbol">:</a> <a id="2394" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2397" href="foundation.finitely-coherently-invertible-maps.html#2374" class="Bound">l1</a><a id="2399" class="Symbol">}</a> <a id="2401" class="Symbol">{</a><a id="2402" href="foundation.finitely-coherently-invertible-maps.html#2402" class="Bound">B</a> <a id="2404" class="Symbol">:</a> <a id="2406" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2409" href="foundation.finitely-coherently-invertible-maps.html#2377" class="Bound">l2</a><a id="2411" class="Symbol">}</a> <a id="2413" class="Symbol">:</a>
    <a id="2419" class="Symbol">(</a><a id="2420" href="foundation.finitely-coherently-invertible-maps.html#2420" class="Bound">n</a> <a id="2422" class="Symbol">:</a> <a id="2424" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2425" class="Symbol">)</a> <a id="2427" class="Symbol">(</a><a id="2428" href="foundation.finitely-coherently-invertible-maps.html#2428" class="Bound">f</a> <a id="2430" class="Symbol">:</a> <a id="2432" href="foundation.finitely-coherently-invertible-maps.html#2390" class="Bound">A</a> <a id="2434" class="Symbol">→</a> <a id="2436" href="foundation.finitely-coherently-invertible-maps.html#2402" class="Bound">B</a><a id="2437" class="Symbol">)</a> <a id="2439" class="Symbol">→</a> <a id="2441" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2444" class="Symbol">(</a><a id="2445" href="foundation.finitely-coherently-invertible-maps.html#2374" class="Bound">l1</a> <a id="2448" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2450" href="foundation.finitely-coherently-invertible-maps.html#2377" class="Bound">l2</a><a id="2452" class="Symbol">)</a>
  <a id="2456" class="Keyword">where</a>
  <a id="is-finitely-coherently-invertible.is-zero-coherently-invertible"></a><a id="2464" href="foundation.finitely-coherently-invertible-maps.html#2464" class="InductiveConstructor">is-zero-coherently-invertible</a> <a id="2494" class="Symbol">:</a>
    <a id="2500" class="Symbol">(</a><a id="2501" href="foundation.finitely-coherently-invertible-maps.html#2501" class="Bound">f</a> <a id="2503" class="Symbol">:</a> <a id="2505" href="foundation.finitely-coherently-invertible-maps.html#2390" class="Bound">A</a> <a id="2507" class="Symbol">→</a> <a id="2509" href="foundation.finitely-coherently-invertible-maps.html#2402" class="Bound">B</a><a id="2510" class="Symbol">)</a> <a id="2512" class="Symbol">→</a> <a id="2514" class="Symbol">(</a><a id="2515" href="foundation.finitely-coherently-invertible-maps.html#2402" class="Bound">B</a> <a id="2517" class="Symbol">→</a> <a id="2519" href="foundation.finitely-coherently-invertible-maps.html#2390" class="Bound">A</a><a id="2520" class="Symbol">)</a> <a id="2522" class="Symbol">→</a> <a id="2524" href="foundation.finitely-coherently-invertible-maps.html#2335" class="Datatype">is-finitely-coherently-invertible</a> <a id="2558" class="Number">0</a> <a id="2560" href="foundation.finitely-coherently-invertible-maps.html#2501" class="Bound">f</a>
  <a id="is-finitely-coherently-invertible.is-succ-coherently-invertible"></a><a id="2564" href="foundation.finitely-coherently-invertible-maps.html#2564" class="InductiveConstructor">is-succ-coherently-invertible</a> <a id="2594" class="Symbol">:</a>
    <a id="2600" class="Symbol">(</a><a id="2601" href="foundation.finitely-coherently-invertible-maps.html#2601" class="Bound">n</a> <a id="2603" class="Symbol">:</a> <a id="2605" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2606" class="Symbol">)</a>
    <a id="2612" class="Symbol">(</a><a id="2613" href="foundation.finitely-coherently-invertible-maps.html#2613" class="Bound">f</a> <a id="2615" class="Symbol">:</a> <a id="2617" href="foundation.finitely-coherently-invertible-maps.html#2390" class="Bound">A</a> <a id="2619" class="Symbol">→</a> <a id="2621" href="foundation.finitely-coherently-invertible-maps.html#2402" class="Bound">B</a><a id="2622" class="Symbol">)</a> <a id="2624" class="Symbol">(</a><a id="2625" href="foundation.finitely-coherently-invertible-maps.html#2625" class="Bound">g</a> <a id="2627" class="Symbol">:</a> <a id="2629" href="foundation.finitely-coherently-invertible-maps.html#2402" class="Bound">B</a> <a id="2631" class="Symbol">→</a> <a id="2633" href="foundation.finitely-coherently-invertible-maps.html#2390" class="Bound">A</a><a id="2634" class="Symbol">)</a> <a id="2636" class="Symbol">(</a><a id="2637" href="foundation.finitely-coherently-invertible-maps.html#2637" class="Bound">H</a> <a id="2639" class="Symbol">:</a> <a id="2641" class="Symbol">(</a><a id="2642" href="foundation.finitely-coherently-invertible-maps.html#2642" class="Bound">x</a> <a id="2644" class="Symbol">:</a> <a id="2646" href="foundation.finitely-coherently-invertible-maps.html#2390" class="Bound">A</a><a id="2647" class="Symbol">)</a> <a id="2649" class="Symbol">(</a><a id="2650" href="foundation.finitely-coherently-invertible-maps.html#2650" class="Bound">y</a> <a id="2652" class="Symbol">:</a> <a id="2654" href="foundation.finitely-coherently-invertible-maps.html#2402" class="Bound">B</a><a id="2655" class="Symbol">)</a> <a id="2657" class="Symbol">→</a> <a id="2659" class="Symbol">(</a><a id="2660" href="foundation.finitely-coherently-invertible-maps.html#2613" class="Bound">f</a> <a id="2662" href="foundation.finitely-coherently-invertible-maps.html#2642" class="Bound">x</a> <a id="2664" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2666" href="foundation.finitely-coherently-invertible-maps.html#2650" class="Bound">y</a><a id="2667" class="Symbol">)</a> <a id="2669" class="Symbol">→</a> <a id="2671" class="Symbol">(</a><a id="2672" href="foundation.finitely-coherently-invertible-maps.html#2642" class="Bound">x</a> <a id="2674" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2676" href="foundation.finitely-coherently-invertible-maps.html#2625" class="Bound">g</a> <a id="2678" href="foundation.finitely-coherently-invertible-maps.html#2650" class="Bound">y</a><a id="2679" class="Symbol">))</a> <a id="2682" class="Symbol">→</a>
    <a id="2688" class="Symbol">((</a><a id="2690" href="foundation.finitely-coherently-invertible-maps.html#2690" class="Bound">x</a> <a id="2692" class="Symbol">:</a> <a id="2694" href="foundation.finitely-coherently-invertible-maps.html#2390" class="Bound">A</a><a id="2695" class="Symbol">)</a> <a id="2697" class="Symbol">(</a><a id="2698" href="foundation.finitely-coherently-invertible-maps.html#2698" class="Bound">y</a> <a id="2700" class="Symbol">:</a> <a id="2702" href="foundation.finitely-coherently-invertible-maps.html#2402" class="Bound">B</a><a id="2703" class="Symbol">)</a> <a id="2705" class="Symbol">→</a> <a id="2707" href="foundation.finitely-coherently-invertible-maps.html#2335" class="Datatype">is-finitely-coherently-invertible</a> <a id="2741" href="foundation.finitely-coherently-invertible-maps.html#2601" class="Bound">n</a> <a id="2743" class="Symbol">(</a><a id="2744" href="foundation.finitely-coherently-invertible-maps.html#2637" class="Bound">H</a> <a id="2746" href="foundation.finitely-coherently-invertible-maps.html#2690" class="Bound">x</a> <a id="2748" href="foundation.finitely-coherently-invertible-maps.html#2698" class="Bound">y</a><a id="2749" class="Symbol">))</a> <a id="2752" class="Symbol">→</a>
    <a id="2758" href="foundation.finitely-coherently-invertible-maps.html#2335" class="Datatype">is-finitely-coherently-invertible</a> <a id="2792" class="Symbol">(</a><a id="2793" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2800" href="foundation.finitely-coherently-invertible-maps.html#2601" class="Bound">n</a><a id="2801" class="Symbol">)</a> <a id="2803" href="foundation.finitely-coherently-invertible-maps.html#2613" class="Bound">f</a>
</pre>