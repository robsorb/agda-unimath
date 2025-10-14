# Homotopy groups

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="synthetic-homotopy-theory.homotopy-groups.html" class="Module">synthetic-homotopy-theory.homotopy-groups</a> <a id="77" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="133" class="Keyword">open</a> <a id="138" class="Keyword">import</a> <a id="145" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.connected-components.html" class="Module">foundation.connected-components</a>
<a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="342" class="Keyword">open</a> <a id="347" class="Keyword">import</a> <a id="354" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="458" class="Keyword">open</a> <a id="463" class="Keyword">import</a> <a id="470" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="499" class="Keyword">open</a> <a id="504" class="Keyword">import</a> <a id="511" href="group-theory.homotopy-automorphism-groups.html" class="Module">group-theory.homotopy-automorphism-groups</a>

<a id="554" class="Keyword">open</a> <a id="559" class="Keyword">import</a> <a id="566" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="598" class="Keyword">open</a> <a id="603" class="Keyword">import</a> <a id="610" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a>
</pre>
</details>

## Idea

The {{#concept "(abstract) homotopy groups" Disambiguation="of a pointed type"}}
of a [pointed type](structured-types.pointed-types.md) `A` are a
[sequence](lists.sequences.md) `i ↦ πᵢ A` of [sets](foundation.sets.md) where

- `π₀ A` is the set of
  [connected components](foundation.connected-components.md) of `A`, and
- `πᵢ₊₁ A` is the set `πᵢ ΩA` equipped with the
  [group structure](group-theory.groups.md) obtained from the
  [loop space](synthetic-homotopy-theory.loop-spaces.md).

For `i ≥ 2`, the `i`-th homotopy group `πᵢ A` of `A` is
[abelian](group-theory.abelian-groups.md) by the
[Eckmann-Hilton argument](synthetic-homotopy-theory.eckmann-hilton-argument.md).

Alternatively, we can define the
{{#concept "concrete homotopy groups" Disambiguation="of a pointed type" Agda=concrete-homotopy-group}}
of a pointed type `A` to be the sequence `ℕ → Concrete-Group`, given by

```text
  i ↦ concrete-group-Pointed-Type (iterated-loop-space i A)
```

However, note that there is an
[Obi-wan error](https://www.urbandictionary.com/define.php?term=Obi-wan+error)
in this definition: The `0`-th concrete homotopy group corresponds to the first
abstract homotopy group.

## Definitions

### The underlying sets of the homotopy groups

<pre class="Agda"><a id="1931" class="Keyword">module</a> <a id="1938" href="synthetic-homotopy-theory.homotopy-groups.html#1938" class="Module">_</a>
  <a id="1942" class="Symbol">{</a><a id="1943" href="synthetic-homotopy-theory.homotopy-groups.html#1943" class="Bound">l</a> <a id="1945" class="Symbol">:</a> <a id="1947" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1952" class="Symbol">}</a> <a id="1954" class="Symbol">(</a><a id="1955" href="synthetic-homotopy-theory.homotopy-groups.html#1955" class="Bound">n</a> <a id="1957" class="Symbol">:</a> <a id="1959" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1960" class="Symbol">)</a> <a id="1962" class="Symbol">(</a><a id="1963" href="synthetic-homotopy-theory.homotopy-groups.html#1963" class="Bound">A</a> <a id="1965" class="Symbol">:</a> <a id="1967" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1980" href="synthetic-homotopy-theory.homotopy-groups.html#1943" class="Bound">l</a><a id="1981" class="Symbol">)</a>
  <a id="1985" class="Keyword">where</a>

  <a id="1994" href="synthetic-homotopy-theory.homotopy-groups.html#1994" class="Function">set-homotopy-group</a> <a id="2013" class="Symbol">:</a> <a id="2015" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="2019" href="synthetic-homotopy-theory.homotopy-groups.html#1943" class="Bound">l</a>
  <a id="2023" href="synthetic-homotopy-theory.homotopy-groups.html#1994" class="Function">set-homotopy-group</a> <a id="2042" class="Symbol">=</a> <a id="2044" href="foundation.set-truncations.html#1963" class="Function">trunc-Set</a> <a id="2054" class="Symbol">(</a><a id="2055" href="synthetic-homotopy-theory.iterated-loop-spaces.html#940" class="Function">type-iterated-loop-space</a> <a id="2080" href="synthetic-homotopy-theory.homotopy-groups.html#1955" class="Bound">n</a> <a id="2082" href="synthetic-homotopy-theory.homotopy-groups.html#1963" class="Bound">A</a><a id="2083" class="Symbol">)</a>

  <a id="2088" href="synthetic-homotopy-theory.homotopy-groups.html#2088" class="Function">type-homotopy-group</a> <a id="2108" class="Symbol">:</a> <a id="2110" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2113" href="synthetic-homotopy-theory.homotopy-groups.html#1943" class="Bound">l</a>
  <a id="2117" href="synthetic-homotopy-theory.homotopy-groups.html#2088" class="Function">type-homotopy-group</a> <a id="2137" class="Symbol">=</a> <a id="2139" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="2148" href="synthetic-homotopy-theory.homotopy-groups.html#1994" class="Function">set-homotopy-group</a>

  <a id="2170" href="synthetic-homotopy-theory.homotopy-groups.html#2170" class="Function">is-set-type-homotopy-group</a> <a id="2197" class="Symbol">:</a> <a id="2199" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="2206" href="synthetic-homotopy-theory.homotopy-groups.html#2088" class="Function">type-homotopy-group</a>
  <a id="2228" href="synthetic-homotopy-theory.homotopy-groups.html#2170" class="Function">is-set-type-homotopy-group</a> <a id="2255" class="Symbol">=</a> <a id="2257" href="foundation-core.sets.html#1076" class="Function">is-set-type-Set</a> <a id="2273" href="synthetic-homotopy-theory.homotopy-groups.html#1994" class="Function">set-homotopy-group</a>

  <a id="2295" href="synthetic-homotopy-theory.homotopy-groups.html#2295" class="Function">point-homotopy-group</a> <a id="2316" class="Symbol">:</a> <a id="2318" href="synthetic-homotopy-theory.homotopy-groups.html#2088" class="Function">type-homotopy-group</a>
  <a id="2340" href="synthetic-homotopy-theory.homotopy-groups.html#2295" class="Function">point-homotopy-group</a> <a id="2361" class="Symbol">=</a> <a id="2363" href="foundation.set-truncations.html#2227" class="Function">unit-trunc-Set</a> <a id="2378" class="Symbol">(</a><a id="2379" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1073" class="Function">point-iterated-loop-space</a> <a id="2405" href="synthetic-homotopy-theory.homotopy-groups.html#1955" class="Bound">n</a> <a id="2407" href="synthetic-homotopy-theory.homotopy-groups.html#1963" class="Bound">A</a><a id="2408" class="Symbol">)</a>

  <a id="2413" href="synthetic-homotopy-theory.homotopy-groups.html#2413" class="Function">pointed-type-homotopy-group</a> <a id="2441" class="Symbol">:</a> <a id="2443" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2456" href="synthetic-homotopy-theory.homotopy-groups.html#1943" class="Bound">l</a>
  <a id="2460" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2464" href="synthetic-homotopy-theory.homotopy-groups.html#2413" class="Function">pointed-type-homotopy-group</a> <a id="2492" class="Symbol">=</a> <a id="2494" href="synthetic-homotopy-theory.homotopy-groups.html#2088" class="Function">type-homotopy-group</a>
  <a id="2516" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2520" href="synthetic-homotopy-theory.homotopy-groups.html#2413" class="Function">pointed-type-homotopy-group</a> <a id="2548" class="Symbol">=</a> <a id="2550" href="synthetic-homotopy-theory.homotopy-groups.html#2295" class="Function">point-homotopy-group</a>
</pre>
### The concrete homotopy groups

<pre class="Agda"><a id="2618" class="Keyword">module</a> <a id="2625" href="synthetic-homotopy-theory.homotopy-groups.html#2625" class="Module">_</a>
  <a id="2629" class="Symbol">{</a><a id="2630" href="synthetic-homotopy-theory.homotopy-groups.html#2630" class="Bound">l</a> <a id="2632" class="Symbol">:</a> <a id="2634" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2639" class="Symbol">}</a> <a id="2641" class="Symbol">(</a><a id="2642" href="synthetic-homotopy-theory.homotopy-groups.html#2642" class="Bound">n</a> <a id="2644" class="Symbol">:</a> <a id="2646" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2647" class="Symbol">)</a> <a id="2649" class="Symbol">(</a><a id="2650" href="synthetic-homotopy-theory.homotopy-groups.html#2650" class="Bound">A</a> <a id="2652" class="Symbol">:</a> <a id="2654" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2667" href="synthetic-homotopy-theory.homotopy-groups.html#2630" class="Bound">l</a><a id="2668" class="Symbol">)</a>
  <a id="2672" class="Keyword">where</a>

  <a id="2681" href="synthetic-homotopy-theory.homotopy-groups.html#2681" class="Function">concrete-homotopy-group</a> <a id="2705" class="Symbol">:</a> <a id="2707" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="2722" href="synthetic-homotopy-theory.homotopy-groups.html#2630" class="Bound">l</a>
  <a id="2726" href="synthetic-homotopy-theory.homotopy-groups.html#2681" class="Function">concrete-homotopy-group</a> <a id="2750" class="Symbol">=</a>
    <a id="2756" href="group-theory.homotopy-automorphism-groups.html#1509" class="Function">concrete-group-Pointed-Type</a> <a id="2784" class="Symbol">(</a><a id="2785" href="synthetic-homotopy-theory.iterated-loop-spaces.html#841" class="Function">iterated-loop-space</a> <a id="2805" href="synthetic-homotopy-theory.homotopy-groups.html#2642" class="Bound">n</a> <a id="2807" href="synthetic-homotopy-theory.homotopy-groups.html#2650" class="Bound">A</a><a id="2808" class="Symbol">)</a>
</pre>