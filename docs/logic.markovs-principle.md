# Markov's principle

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="logic.markovs-principle.html" class="Module">logic.markovs-principle</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="413" class="Keyword">open</a> <a id="418" class="Keyword">import</a> <a id="425" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="484" class="Keyword">open</a> <a id="489" class="Keyword">import</a> <a id="496" href="foundation.universal-quantification.html" class="Module">foundation.universal-quantification</a>
<a id="532" class="Keyword">open</a> <a id="537" class="Keyword">import</a> <a id="544" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="572" class="Keyword">open</a> <a id="577" class="Keyword">import</a> <a id="584" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="615" class="Keyword">open</a> <a id="620" class="Keyword">import</a> <a id="627" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="656" class="Keyword">open</a> <a id="661" class="Keyword">import</a> <a id="668" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>

<a id="690" class="Keyword">open</a> <a id="695" class="Keyword">import</a> <a id="702" href="logic.markovian-types.html" class="Module">logic.markovian-types</a>

<a id="725" class="Keyword">open</a> <a id="730" class="Keyword">import</a> <a id="737" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

{{#concept "Markov's principle" WDID=Q3922074 WD="Markov's principle" Agda=Markov's-Principle}}
asserts that if a [decidable subtype](foundation.decidable-subtypes.md) `𝒫` of
the [natural numbers](elementary-number-theory.natural-numbers.md) `ℕ` is not
[full](foundation.full-subtypes.md), then
[there is](foundation.existential-quantification.md) a natural number `n` that
is not in `𝒫`.

Markov's principle is an example of a _constructive taboo_. It is a consequence
of the [law of excluded middle](foundation.law-of-excluded-middle.md) that is
not provable generally in constructive mathematics.

## Definitions

### Markov's principle

<pre class="Agda"><a id="Markov&#39;s-Principle"></a><a id="1458" href="logic.markovs-principle.html#1458" class="Function">Markov&#39;s-Principle</a> <a id="1477" class="Symbol">:</a> <a id="1479" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1482" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1488" href="logic.markovs-principle.html#1458" class="Function">Markov&#39;s-Principle</a> <a id="1507" class="Symbol">=</a> <a id="1509" href="logic.markovian-types.html#965" class="Function">is-markovian</a> <a id="1522" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
</pre>
## Properties

### Markov's principle is constructively valid for upwards closed subtypes

**Proof.** Assume given an ascending chain of decidable propositions `Pᵢ ⇒ Pᵢ₊₁`
indexed by the natural numbers `ℕ`. This gives a decidable subtype `𝒫` of `ℕ`
given by `i ∈ 𝒫` iff `Pᵢ` is true. Observe that if `i ∈ 𝒫` then every `j ≥ i` is
also in `𝒫`, and there must exist a least such `i ∈ 𝒫`. Therefore,
`𝒫 = Σ (m ∈ ℕ) (m ≥ k)` for some `k`. So, if `¬ (∀ᵢ Pᵢ)` it is necessarily the
case that `¬ P₀`.

<pre class="Agda"><a id="markovs-principle-upwards-closed-structure"></a><a id="2033" href="logic.markovs-principle.html#2033" class="Function">markovs-principle-upwards-closed-structure</a> <a id="2076" class="Symbol">:</a>
  <a id="2080" class="Symbol">{</a><a id="2081" href="logic.markovs-principle.html#2081" class="Bound">l</a> <a id="2083" class="Symbol">:</a> <a id="2085" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2090" class="Symbol">}</a> <a id="2092" class="Symbol">(</a><a id="2093" href="logic.markovs-principle.html#2093" class="Bound">P</a> <a id="2095" class="Symbol">:</a> <a id="2097" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2099" class="Symbol">→</a> <a id="2101" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2104" href="logic.markovs-principle.html#2081" class="Bound">l</a><a id="2105" class="Symbol">)</a>
  <a id="2109" class="Symbol">(</a><a id="2110" href="logic.markovs-principle.html#2110" class="Bound">H</a> <a id="2112" class="Symbol">:</a> <a id="2114" class="Symbol">(</a><a id="2115" href="logic.markovs-principle.html#2115" class="Bound">n</a> <a id="2117" class="Symbol">:</a> <a id="2119" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2120" class="Symbol">)</a> <a id="2122" class="Symbol">→</a> <a id="2124" href="logic.markovs-principle.html#2093" class="Bound">P</a> <a id="2126" href="logic.markovs-principle.html#2115" class="Bound">n</a> <a id="2128" class="Symbol">→</a> <a id="2130" href="logic.markovs-principle.html#2093" class="Bound">P</a> <a id="2132" class="Symbol">(</a><a id="2133" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2140" href="logic.markovs-principle.html#2115" class="Bound">n</a><a id="2141" class="Symbol">))</a> <a id="2144" class="Symbol">→</a> <a id="2146" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2148" class="Symbol">((</a><a id="2150" href="logic.markovs-principle.html#2150" class="Bound">n</a> <a id="2152" class="Symbol">:</a> <a id="2154" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2155" class="Symbol">)</a> <a id="2157" class="Symbol">→</a> <a id="2159" href="logic.markovs-principle.html#2093" class="Bound">P</a> <a id="2161" href="logic.markovs-principle.html#2150" class="Bound">n</a><a id="2162" class="Symbol">)</a> <a id="2164" class="Symbol">→</a> <a id="2166" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2168" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2170" class="Symbol">(</a><a id="2171" href="foundation-core.negation.html#595" class="Function Operator">¬_</a> <a id="2174" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2176" href="logic.markovs-principle.html#2093" class="Bound">P</a><a id="2177" class="Symbol">)</a>
<a id="2179" href="logic.markovs-principle.html#2033" class="Function">markovs-principle-upwards-closed-structure</a> <a id="2222" href="logic.markovs-principle.html#2222" class="Bound">P</a> <a id="2224" href="logic.markovs-principle.html#2224" class="Bound">H</a> <a id="2226" href="logic.markovs-principle.html#2226" class="Bound">q</a> <a id="2228" class="Symbol">=</a> <a id="2230" class="Symbol">(</a><a id="2231" class="Number">0</a> <a id="2233" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2235" class="Symbol">λ</a> <a id="2237" href="logic.markovs-principle.html#2237" class="Bound">x</a> <a id="2239" class="Symbol">→</a> <a id="2241" href="logic.markovs-principle.html#2226" class="Bound">q</a> <a id="2243" class="Symbol">(</a><a id="2244" href="elementary-number-theory.natural-numbers.html#2052" class="Function">ind-ℕ</a> <a id="2250" href="logic.markovs-principle.html#2237" class="Bound">x</a> <a id="2252" href="logic.markovs-principle.html#2224" class="Bound">H</a><a id="2253" class="Symbol">))</a>
</pre>
## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)

## External links

- [`Taboos.MarkovsPrinciple`](https://martinescardo.github.io/TypeTopology/Taboos.MarkovsPrinciple.html)
  at TypeTopology
- [limited principle of omniscience](https://ncatlab.org/nlab/show/limited+principle+of+omniscience)
  at $n$Lab
