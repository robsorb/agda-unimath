# The principle of omniscience

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation.principle-of-omniscience.html" class="Module">foundation.principle-of-omniscience</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="foundation-core.decidable-propositions.html" class="Module">foundation-core.decidable-propositions</a>
<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A type `X` is said to satisfy the
{{#concept "principle of omniscience" Disambiguation="type" Agda=is-omniscient}}
if every [decidable subtype](foundation.decidable-subtypes.md) of `X` is either
[inhabited](foundation.inhabited-types.md) or
[empty](foundation-core.empty-types.md).

## Definition

<pre class="Agda"><a id="is-omniscient-Prop"></a><a id="695" href="foundation.principle-of-omniscience.html#695" class="Function">is-omniscient-Prop</a> <a id="714" class="Symbol">:</a> <a id="716" class="Symbol">{</a><a id="717" href="foundation.principle-of-omniscience.html#717" class="Bound">l</a> <a id="719" class="Symbol">:</a> <a id="721" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="726" class="Symbol">}</a> <a id="728" class="Symbol">→</a> <a id="730" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="733" href="foundation.principle-of-omniscience.html#717" class="Bound">l</a> <a id="735" class="Symbol">→</a> <a id="737" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="742" class="Symbol">(</a><a id="743" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="748" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="754" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="756" href="foundation.principle-of-omniscience.html#717" class="Bound">l</a><a id="757" class="Symbol">)</a>
<a id="759" href="foundation.principle-of-omniscience.html#695" class="Function">is-omniscient-Prop</a> <a id="778" href="foundation.principle-of-omniscience.html#778" class="Bound">X</a> <a id="780" class="Symbol">=</a>
  <a id="784" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
    <a id="795" class="Symbol">(</a> <a id="797" href="foundation.decidable-subtypes.html#2727" class="Function">decidable-subtype</a> <a id="815" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="821" href="foundation.principle-of-omniscience.html#778" class="Bound">X</a><a id="822" class="Symbol">)</a>
    <a id="828" class="Symbol">(</a> <a id="830" class="Symbol">λ</a> <a id="832" href="foundation.principle-of-omniscience.html#832" class="Bound">P</a> <a id="834" class="Symbol">→</a> <a id="836" href="foundation-core.decidable-propositions.html#1342" class="Function">is-decidable-Prop</a> <a id="854" class="Symbol">(</a><a id="855" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="866" class="Symbol">(</a><a id="867" href="foundation.decidable-subtypes.html#3903" class="Function">type-decidable-subtype</a> <a id="890" href="foundation.principle-of-omniscience.html#832" class="Bound">P</a><a id="891" class="Symbol">)))</a>

<a id="is-omniscient"></a><a id="896" href="foundation.principle-of-omniscience.html#896" class="Function">is-omniscient</a> <a id="910" class="Symbol">:</a> <a id="912" class="Symbol">{</a><a id="913" href="foundation.principle-of-omniscience.html#913" class="Bound">l</a> <a id="915" class="Symbol">:</a> <a id="917" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="922" class="Symbol">}</a> <a id="924" class="Symbol">→</a> <a id="926" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="929" href="foundation.principle-of-omniscience.html#913" class="Bound">l</a> <a id="931" class="Symbol">→</a> <a id="933" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="936" class="Symbol">(</a><a id="937" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="942" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="948" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="950" href="foundation.principle-of-omniscience.html#913" class="Bound">l</a><a id="951" class="Symbol">)</a>
<a id="953" href="foundation.principle-of-omniscience.html#896" class="Function">is-omniscient</a> <a id="967" href="foundation.principle-of-omniscience.html#967" class="Bound">X</a> <a id="969" class="Symbol">=</a> <a id="971" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="981" class="Symbol">(</a><a id="982" href="foundation.principle-of-omniscience.html#695" class="Function">is-omniscient-Prop</a> <a id="1001" href="foundation.principle-of-omniscience.html#967" class="Bound">X</a><a id="1002" class="Symbol">)</a>
</pre>
## See also

- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)
