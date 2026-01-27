# Cyclic types

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="structured-types.cyclic-types.html" class="Module">structured-types.cyclic-types</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="155" class="Keyword">open</a> <a id="160" class="Keyword">import</a> <a id="167" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.iterating-automorphisms.html" class="Module">foundation.iterating-automorphisms</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="331" class="Keyword">open</a> <a id="336" class="Keyword">import</a> <a id="343" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="398" class="Keyword">open</a> <a id="403" class="Keyword">import</a> <a id="410" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="438" class="Keyword">open</a> <a id="443" class="Keyword">import</a> <a id="450" href="structured-types.sets-equipped-with-automorphisms.html" class="Module">structured-types.sets-equipped-with-automorphisms</a>
</pre>
</details>

## Idea

A **cyclic set** consists of a [set](foundation.sets.md) `A` equipped with an
[automorphism](foundation.automorphisms.md) `e : A ≃ A` which is _cyclic_ in the
sense that its underlying set is [inhabited](foundation.inhabited-types.md) and
the map

```text
  k ↦ eᵏ x
```

is [surjective](foundation.surjective-maps.md) for every `x : A`. There are
several equivalent ways of stating the concept of cyclic sets. Two further
equivalent ways are:

- A cyclic set is a
  [connected set bundle](synthetic-homotopy-theory.connected-set-bundles-circle.md)
  over the [circle](synthetic-homotopy-theory.circle.md).
- A cyclic set is a set equipped with a
  [transitive](group-theory.transitive-group-actions.md) `ℤ`-action.
- A cyclic set is a set which is a [`C`-torsor](group-theory.torsors.md) for
  some [cyclic group](group-theory.cyclic-groups.md) `C`.

Note that the [empty set](foundation.empty-types.md) equipped with the identity
automorphism is not considered to be a cyclic set, for reasons similar to those
of not considering empty group actions to be transitive.

## Definition

### The predicate of being a cyclic set

<pre class="Agda"><a id="1660" class="Keyword">module</a> <a id="1667" href="structured-types.cyclic-types.html#1667" class="Module">_</a>
  <a id="1671" class="Symbol">{</a><a id="1672" href="structured-types.cyclic-types.html#1672" class="Bound">l</a> <a id="1674" class="Symbol">:</a> <a id="1676" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1681" class="Symbol">}</a> <a id="1683" class="Symbol">(</a><a id="1684" href="structured-types.cyclic-types.html#1684" class="Bound">X</a> <a id="1686" class="Symbol">:</a> <a id="1688" href="structured-types.sets-equipped-with-automorphisms.html#632" class="Function">Set-With-Automorphism</a> <a id="1710" href="structured-types.cyclic-types.html#1672" class="Bound">l</a><a id="1711" class="Symbol">)</a>
  <a id="1715" class="Keyword">where</a>

  <a id="1724" href="structured-types.cyclic-types.html#1724" class="Function">is-cyclic-prop-Set-With-Automorphism</a> <a id="1761" class="Symbol">:</a> <a id="1763" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1768" href="structured-types.cyclic-types.html#1672" class="Bound">l</a>
  <a id="1772" href="structured-types.cyclic-types.html#1724" class="Function">is-cyclic-prop-Set-With-Automorphism</a> <a id="1809" class="Symbol">=</a>
    <a id="1815" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="1834" class="Symbol">(</a> <a id="1836" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="1847" class="Symbol">(</a><a id="1848" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a> <a id="1875" href="structured-types.cyclic-types.html#1684" class="Bound">X</a><a id="1876" class="Symbol">))</a>
      <a id="1885" class="Symbol">(</a> <a id="1887" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
        <a id="1902" class="Symbol">(</a> <a id="1904" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a> <a id="1931" href="structured-types.cyclic-types.html#1684" class="Bound">X</a><a id="1932" class="Symbol">)</a>
        <a id="1942" class="Symbol">(</a> <a id="1944" class="Symbol">λ</a> <a id="1946" href="structured-types.cyclic-types.html#1946" class="Bound">x</a> <a id="1948" class="Symbol">→</a>
          <a id="1960" href="foundation.surjective-maps.html#2370" class="Function">is-surjective-Prop</a>
            <a id="1991" class="Symbol">(</a> <a id="1993" class="Symbol">λ</a> <a id="1995" href="structured-types.cyclic-types.html#1995" class="Bound">k</a> <a id="1997" class="Symbol">→</a>
              <a id="2013" href="foundation.iterating-automorphisms.html#3053" class="Function">map-iterate-automorphism-ℤ</a> <a id="2040" href="structured-types.cyclic-types.html#1995" class="Bound">k</a> <a id="2042" class="Symbol">(</a><a id="2043" href="structured-types.sets-equipped-with-automorphisms.html#1129" class="Function">aut-Set-With-Automorphism</a> <a id="2069" href="structured-types.cyclic-types.html#1684" class="Bound">X</a><a id="2070" class="Symbol">)</a> <a id="2072" href="structured-types.cyclic-types.html#1946" class="Bound">x</a><a id="2073" class="Symbol">)))</a>

  <a id="2080" href="structured-types.cyclic-types.html#2080" class="Function">is-cyclic-Set-With-Automorphism</a> <a id="2112" class="Symbol">:</a> <a id="2114" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2117" href="structured-types.cyclic-types.html#1672" class="Bound">l</a>
  <a id="2121" href="structured-types.cyclic-types.html#2080" class="Function">is-cyclic-Set-With-Automorphism</a> <a id="2153" class="Symbol">=</a>
    <a id="2159" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2169" href="structured-types.cyclic-types.html#1724" class="Function">is-cyclic-prop-Set-With-Automorphism</a>
</pre>
### Cyclic sets

<pre class="Agda"><a id="Cyclic-Set"></a><a id="2236" href="structured-types.cyclic-types.html#2236" class="Function">Cyclic-Set</a> <a id="2247" class="Symbol">:</a>
  <a id="2251" class="Symbol">(</a><a id="2252" href="structured-types.cyclic-types.html#2252" class="Bound">l</a> <a id="2254" class="Symbol">:</a> <a id="2256" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2261" class="Symbol">)</a> <a id="2263" class="Symbol">→</a> <a id="2265" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2268" class="Symbol">(</a><a id="2269" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2274" href="structured-types.cyclic-types.html#2252" class="Bound">l</a><a id="2275" class="Symbol">)</a>
<a id="2277" href="structured-types.cyclic-types.html#2236" class="Function">Cyclic-Set</a> <a id="2288" href="structured-types.cyclic-types.html#2288" class="Bound">l</a> <a id="2290" class="Symbol">=</a>
  <a id="2294" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2296" class="Symbol">(</a><a id="2297" href="structured-types.sets-equipped-with-automorphisms.html#632" class="Function">Set-With-Automorphism</a> <a id="2319" href="structured-types.cyclic-types.html#2288" class="Bound">l</a><a id="2320" class="Symbol">)</a> <a id="2322" class="Symbol">(λ</a> <a id="2325" href="structured-types.cyclic-types.html#2325" class="Bound">X</a> <a id="2327" class="Symbol">→</a> <a id="2329" href="structured-types.cyclic-types.html#2080" class="Function">is-cyclic-Set-With-Automorphism</a> <a id="2361" href="structured-types.cyclic-types.html#2325" class="Bound">X</a><a id="2362" class="Symbol">)</a>

<a id="2365" class="Keyword">module</a> <a id="2372" href="structured-types.cyclic-types.html#2372" class="Module">_</a>
  <a id="2376" class="Symbol">{</a><a id="2377" href="structured-types.cyclic-types.html#2377" class="Bound">l</a> <a id="2379" class="Symbol">:</a> <a id="2381" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2386" class="Symbol">}</a> <a id="2388" class="Symbol">(</a><a id="2389" href="structured-types.cyclic-types.html#2389" class="Bound">X</a> <a id="2391" class="Symbol">:</a> <a id="2393" href="structured-types.cyclic-types.html#2236" class="Function">Cyclic-Set</a> <a id="2404" href="structured-types.cyclic-types.html#2377" class="Bound">l</a><a id="2405" class="Symbol">)</a>
  <a id="2409" class="Keyword">where</a>

  <a id="2418" href="structured-types.cyclic-types.html#2418" class="Function">set-with-automorphism-Cyclic-Set</a> <a id="2451" class="Symbol">:</a> <a id="2453" href="structured-types.sets-equipped-with-automorphisms.html#632" class="Function">Set-With-Automorphism</a> <a id="2475" href="structured-types.cyclic-types.html#2377" class="Bound">l</a>
  <a id="2479" href="structured-types.cyclic-types.html#2418" class="Function">set-with-automorphism-Cyclic-Set</a> <a id="2512" class="Symbol">=</a> <a id="2514" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2518" href="structured-types.cyclic-types.html#2389" class="Bound">X</a>

  <a id="2523" href="structured-types.cyclic-types.html#2523" class="Function">set-Cyclic-Set</a> <a id="2538" class="Symbol">:</a> <a id="2540" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="2544" href="structured-types.cyclic-types.html#2377" class="Bound">l</a>
  <a id="2548" href="structured-types.cyclic-types.html#2523" class="Function">set-Cyclic-Set</a> <a id="2563" class="Symbol">=</a> <a id="2565" href="structured-types.sets-equipped-with-automorphisms.html#800" class="Function">set-Set-With-Automorphism</a> <a id="2591" href="structured-types.cyclic-types.html#2418" class="Function">set-with-automorphism-Cyclic-Set</a>

  <a id="2627" href="structured-types.cyclic-types.html#2627" class="Function">type-Cyclic-Set</a> <a id="2643" class="Symbol">:</a> <a id="2645" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2648" href="structured-types.cyclic-types.html#2377" class="Bound">l</a>
  <a id="2652" href="structured-types.cyclic-types.html#2627" class="Function">type-Cyclic-Set</a> <a id="2668" class="Symbol">=</a> <a id="2670" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a> <a id="2697" href="structured-types.cyclic-types.html#2418" class="Function">set-with-automorphism-Cyclic-Set</a>

  <a id="2733" href="structured-types.cyclic-types.html#2733" class="Function">is-set-type-Cyclic-Set</a> <a id="2756" class="Symbol">:</a> <a id="2758" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="2765" href="structured-types.cyclic-types.html#2627" class="Function">type-Cyclic-Set</a>
  <a id="2783" href="structured-types.cyclic-types.html#2733" class="Function">is-set-type-Cyclic-Set</a> <a id="2806" class="Symbol">=</a>
    <a id="2812" href="structured-types.sets-equipped-with-automorphisms.html#976" class="Function">is-set-type-Set-With-Automorphism</a> <a id="2846" href="structured-types.cyclic-types.html#2418" class="Function">set-with-automorphism-Cyclic-Set</a>

  <a id="2882" href="structured-types.cyclic-types.html#2882" class="Function">aut-Cyclic-Set</a> <a id="2897" class="Symbol">:</a> <a id="2899" href="foundation.automorphisms.html#538" class="Function">Aut</a> <a id="2903" href="structured-types.cyclic-types.html#2627" class="Function">type-Cyclic-Set</a>
  <a id="2921" href="structured-types.cyclic-types.html#2882" class="Function">aut-Cyclic-Set</a> <a id="2936" class="Symbol">=</a> <a id="2938" href="structured-types.sets-equipped-with-automorphisms.html#1129" class="Function">aut-Set-With-Automorphism</a> <a id="2964" href="structured-types.cyclic-types.html#2418" class="Function">set-with-automorphism-Cyclic-Set</a>

  <a id="3000" href="structured-types.cyclic-types.html#3000" class="Function">map-Cyclic-Set</a> <a id="3015" class="Symbol">:</a> <a id="3017" href="structured-types.cyclic-types.html#2627" class="Function">type-Cyclic-Set</a> <a id="3033" class="Symbol">→</a> <a id="3035" href="structured-types.cyclic-types.html#2627" class="Function">type-Cyclic-Set</a>
  <a id="3053" href="structured-types.cyclic-types.html#3000" class="Function">map-Cyclic-Set</a> <a id="3068" class="Symbol">=</a> <a id="3070" href="structured-types.sets-equipped-with-automorphisms.html#1227" class="Function">map-Set-With-Automorphism</a> <a id="3096" href="structured-types.cyclic-types.html#2418" class="Function">set-with-automorphism-Cyclic-Set</a>
</pre>
## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
