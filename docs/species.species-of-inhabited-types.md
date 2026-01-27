# Species of inhabited types

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="species.species-of-inhabited-types.html" class="Module">species.species-of-inhabited-types</a> <a id="81" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="species.species-of-types-in-subuniverses.html" class="Module">species.species-of-types-in-subuniverses</a>
</pre>
</details>

## Idea

A {{#concept "species of inhabited types" Agda=species-inhabited-types}} is a
map from the [subuniverse](foundation.global-subuniverses.md) of
[inhabited types](foundation.inhabited-types.md) to the universe of all types.

## Definition

<pre class="Agda"><a id="species-inhabited-types"></a><a id="574" href="species.species-of-inhabited-types.html#574" class="Function">species-inhabited-types</a> <a id="598" class="Symbol">:</a> <a id="600" class="Symbol">(</a><a id="601" href="species.species-of-inhabited-types.html#601" class="Bound">l1</a> <a id="604" href="species.species-of-inhabited-types.html#604" class="Bound">l2</a> <a id="607" class="Symbol">:</a> <a id="609" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="614" class="Symbol">)</a> <a id="616" class="Symbol">→</a> <a id="618" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="621" class="Symbol">(</a><a id="622" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="627" href="species.species-of-inhabited-types.html#601" class="Bound">l1</a> <a id="630" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="632" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="637" href="species.species-of-inhabited-types.html#604" class="Bound">l2</a><a id="639" class="Symbol">)</a>
<a id="641" href="species.species-of-inhabited-types.html#574" class="Function">species-inhabited-types</a> <a id="665" href="species.species-of-inhabited-types.html#665" class="Bound">l1</a> <a id="668" href="species.species-of-inhabited-types.html#668" class="Bound">l2</a> <a id="671" class="Symbol">=</a>
  <a id="675" href="species.species-of-types-in-subuniverses.html#828" class="Function">species-subuniverse</a> <a id="695" class="Symbol">(</a><a id="696" href="foundation.inhabited-types.html#1261" class="Function">is-inhabited-Prop</a> <a id="714" class="Symbol">{</a><a id="715" href="species.species-of-inhabited-types.html#665" class="Bound">l1</a><a id="717" class="Symbol">})</a> <a id="720" class="Symbol">(λ</a> <a id="723" class="Symbol">(</a><a id="724" href="species.species-of-inhabited-types.html#724" class="Bound">X</a> <a id="726" class="Symbol">:</a> <a id="728" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="731" href="species.species-of-inhabited-types.html#668" class="Bound">l2</a><a id="733" class="Symbol">)</a> <a id="735" class="Symbol">→</a> <a id="737" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a><a id="746" class="Symbol">)</a>
</pre>