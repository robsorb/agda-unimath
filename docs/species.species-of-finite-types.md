# Species of finite types

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="species.species-of-finite-types.html" class="Module">species.species-of-finite-types</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="species.species-of-types-in-subuniverses.html" class="Module">species.species-of-types-in-subuniverses</a>

<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

A {{#concept "species of finite types" Agda=finite-species}} is a map from the
[subuniverse](foundation.global-subuniverses.md) of
[finite types](univalent-combinatorics.finite-types.md) to itself.

## Definition

<pre class="Agda"><a id="finite-species"></a><a id="522" href="species.species-of-finite-types.html#522" class="Function">finite-species</a> <a id="537" class="Symbol">:</a> <a id="539" class="Symbol">(</a><a id="540" href="species.species-of-finite-types.html#540" class="Bound">l1</a> <a id="543" href="species.species-of-finite-types.html#543" class="Bound">l2</a> <a id="546" class="Symbol">:</a> <a id="548" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="553" class="Symbol">)</a> <a id="555" class="Symbol">→</a> <a id="557" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="560" class="Symbol">(</a><a id="561" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="566" href="species.species-of-finite-types.html#540" class="Bound">l1</a> <a id="569" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="571" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="576" href="species.species-of-finite-types.html#543" class="Bound">l2</a><a id="578" class="Symbol">)</a>
<a id="580" href="species.species-of-finite-types.html#522" class="Function">finite-species</a> <a id="595" href="species.species-of-finite-types.html#595" class="Bound">l1</a> <a id="598" href="species.species-of-finite-types.html#598" class="Bound">l2</a> <a id="601" class="Symbol">=</a>
  <a id="605" href="species.species-of-types-in-subuniverses.html#828" class="Function">species-subuniverse</a> <a id="625" class="Symbol">(</a><a id="626" href="univalent-combinatorics.finite-types.html#2201" class="Function">is-finite-Prop</a> <a id="641" class="Symbol">{</a><a id="642" href="species.species-of-finite-types.html#595" class="Bound">l1</a><a id="644" class="Symbol">})</a> <a id="647" class="Symbol">(</a><a id="648" href="univalent-combinatorics.finite-types.html#2201" class="Function">is-finite-Prop</a> <a id="663" class="Symbol">{</a><a id="664" href="species.species-of-finite-types.html#598" class="Bound">l2</a><a id="666" class="Symbol">})</a>
</pre>