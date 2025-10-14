# Species of finite inhabited types

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="species.species-of-finite-inhabited-types.html" class="Module">species.species-of-finite-inhabited-types</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="species.species-of-types-in-subuniverses.html" class="Module">species.species-of-types-in-subuniverses</a>

<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="univalent-combinatorics.inhabited-finite-types.html" class="Module">univalent-combinatorics.inhabited-finite-types</a>
</pre>
</details>

## Idea

A
{{#concept "species of finite inhabited types" Agda=species-Inhabited-Finite-Type}}
is a map from the [subuniverse](foundation.global-subuniverses.md) of
[finite inhabited types](univalent-combinatorics.inhabited-finite-types.md) to
the universe of [finite types](univalent-combinatorics.finite-types.md).

## Definition

<pre class="Agda"><a id="species-Inhabited-Finite-Type"></a><a id="711" href="species.species-of-finite-inhabited-types.html#711" class="Function">species-Inhabited-Finite-Type</a> <a id="741" class="Symbol">:</a> <a id="743" class="Symbol">(</a><a id="744" href="species.species-of-finite-inhabited-types.html#744" class="Bound">l1</a> <a id="747" href="species.species-of-finite-inhabited-types.html#747" class="Bound">l2</a> <a id="750" class="Symbol">:</a> <a id="752" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="757" class="Symbol">)</a> <a id="759" class="Symbol">→</a> <a id="761" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="764" class="Symbol">(</a><a id="765" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="770" href="species.species-of-finite-inhabited-types.html#744" class="Bound">l1</a> <a id="773" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="775" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="780" href="species.species-of-finite-inhabited-types.html#747" class="Bound">l2</a><a id="782" class="Symbol">)</a>
<a id="784" href="species.species-of-finite-inhabited-types.html#711" class="Function">species-Inhabited-Finite-Type</a> <a id="814" href="species.species-of-finite-inhabited-types.html#814" class="Bound">l1</a> <a id="817" href="species.species-of-finite-inhabited-types.html#817" class="Bound">l2</a> <a id="820" class="Symbol">=</a>
  <a id="824" href="species.species-of-types-in-subuniverses.html#828" class="Function">species-subuniverse</a> <a id="844" class="Symbol">(</a><a id="845" href="univalent-combinatorics.inhabited-finite-types.html#2421" class="Function">is-finite-and-inhabited-Prop</a> <a id="874" class="Symbol">{</a><a id="875" href="species.species-of-finite-inhabited-types.html#814" class="Bound">l1</a><a id="877" class="Symbol">})</a> <a id="880" class="Symbol">(</a><a id="881" href="univalent-combinatorics.finite-types.html#2201" class="Function">is-finite-Prop</a> <a id="896" class="Symbol">{</a><a id="897" href="species.species-of-finite-inhabited-types.html#817" class="Bound">l2</a><a id="899" class="Symbol">})</a>
</pre>