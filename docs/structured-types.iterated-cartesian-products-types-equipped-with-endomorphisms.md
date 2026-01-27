# Iterated cartesian products of types equipped with endomorphisms

<pre class="Agda"><a id="77" class="Keyword">module</a>
  <a id="86" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html" class="Module">structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms</a>
  <a id="167" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="lists.lists.html" class="Module">lists.lists</a>

<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html" class="Module">structured-types.cartesian-products-types-equipped-with-endomorphisms</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="structured-types.types-equipped-with-endomorphisms.html" class="Module">structured-types.types-equipped-with-endomorphisms</a>
</pre>
</details>

## Idea

From a list of a types equipped with endomorphisms, we define its iterated
cartesian product recursively via the cartesian product of types equipped with
endomorphism.

## Definitions

<pre class="Agda"><a id="iterated-product-list-Type-With-Endomorphism"></a><a id="652" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#652" class="Function">iterated-product-list-Type-With-Endomorphism</a> <a id="697" class="Symbol">:</a>
  <a id="701" class="Symbol">{</a><a id="702" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#702" class="Bound">l</a> <a id="704" class="Symbol">:</a> <a id="706" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="711" class="Symbol">}</a> <a id="713" class="Symbol">→</a> <a id="715" href="lists.lists.html#1328" class="Datatype">list</a> <a id="720" class="Symbol">(</a><a id="721" href="structured-types.types-equipped-with-endomorphisms.html#530" class="Function">Type-With-Endomorphism</a> <a id="744" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#702" class="Bound">l</a><a id="745" class="Symbol">)</a> <a id="747" class="Symbol">→</a> <a id="749" href="structured-types.types-equipped-with-endomorphisms.html#530" class="Function">Type-With-Endomorphism</a> <a id="772" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#702" class="Bound">l</a>
<a id="774" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#652" class="Function">iterated-product-list-Type-With-Endomorphism</a> <a id="819" href="lists.lists.html#1371" class="InductiveConstructor">nil</a> <a id="823" class="Symbol">=</a>
  <a id="827" href="structured-types.types-equipped-with-endomorphisms.html#978" class="Function">trivial-Type-With-Endomorphism</a>
<a id="858" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#652" class="Function">iterated-product-list-Type-With-Endomorphism</a> <a id="903" class="Symbol">(</a><a id="904" href="lists.lists.html#1386" class="InductiveConstructor">cons</a> <a id="909" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#909" class="Bound">A</a> <a id="911" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#911" class="Bound">L</a><a id="912" class="Symbol">)</a> <a id="914" class="Symbol">=</a>
  <a id="918" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#1238" class="Function">product-Type-With-Endomorphism</a> <a id="949" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#909" class="Bound">A</a>
    <a id="955" class="Symbol">(</a> <a id="957" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#652" class="Function">iterated-product-list-Type-With-Endomorphism</a> <a id="1002" href="structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms.html#911" class="Bound">L</a><a id="1003" class="Symbol">)</a>
</pre>