# Baire space

<pre class="Agda"><a id="24" class="Keyword">module</a> <a id="31" href="set-theory.baire-space.html" class="Module">set-theory.baire-space</a> <a id="54" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="110" class="Keyword">open</a> <a id="115" class="Keyword">import</a> <a id="122" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a>
<a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a>
<a id="466" class="Keyword">open</a> <a id="471" class="Keyword">import</a> <a id="478" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="498" class="Keyword">open</a> <a id="503" class="Keyword">import</a> <a id="510" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="547" class="Keyword">open</a> <a id="552" class="Keyword">import</a> <a id="559" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="575" class="Keyword">open</a> <a id="580" class="Keyword">import</a> <a id="587" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="615" class="Keyword">open</a> <a id="620" class="Keyword">import</a> <a id="627" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
<a id="655" class="Keyword">open</a> <a id="660" class="Keyword">import</a> <a id="667" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="698" class="Keyword">open</a> <a id="703" class="Keyword">import</a> <a id="710" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>

<a id="740" class="Keyword">open</a> <a id="745" class="Keyword">import</a> <a id="752" href="set-theory.cantors-diagonal-argument.html" class="Module">set-theory.cantors-diagonal-argument</a>
<a id="789" class="Keyword">open</a> <a id="794" class="Keyword">import</a> <a id="801" href="set-theory.countable-sets.html" class="Module">set-theory.countable-sets</a>
<a id="827" class="Keyword">open</a> <a id="832" class="Keyword">import</a> <a id="839" href="set-theory.uncountable-sets.html" class="Module">set-theory.uncountable-sets</a>
</pre>
</details>

## Idea

The
{{#concept "Baire space" Disambiguation="as a type" Agda=baire-space WD="Baire space" WDID=Q803936}}
is the [set](foundation-core.sets.md) of
[functions](foundation-core.function-types.md) `ℕ → ℕ`. In other words, it is
the set of infinite [sequences](lists.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md).

## Definition

<pre class="Agda"><a id="baire-space"></a><a id="1260" href="set-theory.baire-space.html#1260" class="Function">baire-space</a> <a id="1272" class="Symbol">:</a> <a id="1274" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1277" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1283" href="set-theory.baire-space.html#1260" class="Function">baire-space</a> <a id="1295" class="Symbol">=</a> <a id="1297" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1299" class="Symbol">→</a> <a id="1301" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
</pre>
## Properties

### The Baire space is a set

<pre class="Agda"><a id="is-set-baire-space"></a><a id="1361" href="set-theory.baire-space.html#1361" class="Function">is-set-baire-space</a> <a id="1380" class="Symbol">:</a> <a id="1382" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="1389" href="set-theory.baire-space.html#1260" class="Function">baire-space</a>
<a id="1401" href="set-theory.baire-space.html#1361" class="Function">is-set-baire-space</a> <a id="1420" class="Symbol">=</a> <a id="1422" href="foundation.sets.html#3922" class="Function">is-set-function-type</a> <a id="1443" href="elementary-number-theory.equality-natural-numbers.html#1885" class="Function">is-set-ℕ</a>

<a id="baire-space-Set"></a><a id="1453" href="set-theory.baire-space.html#1453" class="Function">baire-space-Set</a> <a id="1469" class="Symbol">:</a> <a id="1471" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1475" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1481" href="set-theory.baire-space.html#1453" class="Function">baire-space-Set</a> <a id="1497" class="Symbol">=</a> <a id="1499" class="Symbol">(</a><a id="1500" href="set-theory.baire-space.html#1260" class="Function">baire-space</a> <a id="1512" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1514" href="set-theory.baire-space.html#1361" class="Function">is-set-baire-space</a><a id="1532" class="Symbol">)</a>
</pre>
### The Baire space is uncountable

We give two proofs. The first proof uses that the successor function on the
natural numbers has no fixed points and applies
[Lawvere's fixed point theorem](foundation.lawveres-fixed-point-theorem.md). The
second proof uses that equality on the natural numbers is
[decidable](foundation.decidable-types.md), and applies
[Cantor's diagonal argument](set-theory.cantors-diagonal-argument.md).

<pre class="Agda"><a id="1974" class="Keyword">abstract</a>
  <a id="is-uncountable-baire-space"></a><a id="1985" href="set-theory.baire-space.html#1985" class="Function">is-uncountable-baire-space</a> <a id="2012" class="Symbol">:</a> <a id="2014" href="set-theory.uncountable-sets.html#821" class="Function">is-uncountable</a> <a id="2029" href="set-theory.baire-space.html#1453" class="Function">baire-space-Set</a>
  <a id="2047" href="set-theory.baire-space.html#1985" class="Function">is-uncountable-baire-space</a> <a id="2074" href="set-theory.baire-space.html#2074" class="Bound">P</a> <a id="2076" class="Symbol">=</a>
    <a id="2082" href="foundation.propositional-truncations.html#6198" class="Function">apply-universal-property-trunc-Prop</a>
      <a id="2124" class="Symbol">(</a> <a id="2126" href="set-theory.countable-sets.html#4293" class="Function">is-directly-countable-is-countable</a> <a id="2161" href="set-theory.baire-space.html#1453" class="Function">baire-space-Set</a> <a id="2177" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2184" href="set-theory.baire-space.html#2074" class="Bound">P</a><a id="2185" class="Symbol">)</a>
      <a id="2193" class="Symbol">(</a> <a id="2195" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a><a id="2205" class="Symbol">)</a>
      <a id="2213" class="Symbol">(</a> <a id="2215" class="Symbol">λ</a> <a id="2217" href="set-theory.baire-space.html#2217" class="Bound">H</a> <a id="2219" class="Symbol">→</a>
        <a id="2229" href="foundation.propositional-truncations.html#6198" class="Function">apply-universal-property-trunc-Prop</a>
          <a id="2275" class="Symbol">(</a> <a id="2277" href="foundation.lawveres-fixed-point-theorem.html#903" class="Function">fixed-point-theorem-Lawvere</a> <a id="2305" class="Symbol">(</a><a id="2306" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2310" href="set-theory.baire-space.html#2217" class="Bound">H</a><a id="2311" class="Symbol">)</a> <a id="2313" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a><a id="2319" class="Symbol">)</a>
          <a id="2331" class="Symbol">(</a> <a id="2333" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a><a id="2343" class="Symbol">)</a>
          <a id="2355" class="Symbol">(</a> <a id="2357" class="Symbol">λ</a> <a id="2359" href="set-theory.baire-space.html#2359" class="Bound">F</a> <a id="2361" class="Symbol">→</a>
            <a id="2375" href="foundation.negation.html#1348" class="Function">reductio-ad-absurdum</a> <a id="2396" class="Symbol">(</a><a id="2397" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2401" href="set-theory.baire-space.html#2359" class="Bound">F</a><a id="2402" class="Symbol">)</a> <a id="2404" class="Symbol">(</a><a id="2405" href="elementary-number-theory.natural-numbers.html#2961" class="Function">has-no-fixed-points-succ-ℕ</a> <a id="2432" class="Symbol">(</a><a id="2433" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2437" href="set-theory.baire-space.html#2359" class="Bound">F</a><a id="2438" class="Symbol">))))</a>

<a id="2444" class="Keyword">abstract</a>
  <a id="is-uncountable-baire-space&#39;"></a><a id="2455" href="set-theory.baire-space.html#2455" class="Function">is-uncountable-baire-space&#39;</a> <a id="2483" class="Symbol">:</a> <a id="2485" href="set-theory.uncountable-sets.html#821" class="Function">is-uncountable</a> <a id="2500" href="set-theory.baire-space.html#1453" class="Function">baire-space-Set</a>
  <a id="2518" href="set-theory.baire-space.html#2455" class="Function">is-uncountable-baire-space&#39;</a> <a id="2546" class="Symbol">=</a>
    <a id="2552" href="set-theory.cantors-diagonal-argument.html#6015" class="Function">is-uncountable-sequence-discrete-type-diagonal-argument-Cantor</a>
      <a id="2621" class="Symbol">(</a> <a id="2623" href="elementary-number-theory.equality-natural-numbers.html#3018" class="Function">ℕ-Discrete-Type</a><a id="2638" class="Symbol">)</a>
      <a id="2646" class="Symbol">(</a> <a id="2648" class="Number">0</a><a id="2649" class="Symbol">)</a>
      <a id="2657" class="Symbol">(</a> <a id="2659" class="Number">1</a><a id="2660" class="Symbol">)</a>
      <a id="2668" class="Symbol">(</a> <a id="2670" href="elementary-number-theory.natural-numbers.html#3087" class="Function">is-nonzero-one-ℕ</a> <a id="2687" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2689" href="foundation-core.identity-types.html#6358" class="Function">inv</a><a id="2692" class="Symbol">)</a>
</pre>
## External links

- [Baire space (set theory)](<https://en.wikipedia.org/wiki/Baire_space_(set_theory)>)
  at Wikipedia
- [Baire space of sequences](https://ncatlab.org/nlab/show/Baire+space+of+sequences)
  at $n$Lab
