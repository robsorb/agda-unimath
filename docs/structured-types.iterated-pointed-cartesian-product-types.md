# Iterated cartesian products of pointed types

<pre class="Agda"><a id="57" class="Keyword">module</a> <a id="64" href="structured-types.iterated-pointed-cartesian-product-types.html" class="Module">structured-types.iterated-pointed-cartesian-product-types</a> <a id="122" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="lists.lists.html" class="Module">lists.lists</a>

<a id="320" class="Keyword">open</a> <a id="325" class="Keyword">import</a> <a id="332" href="structured-types.pointed-cartesian-product-types.html" class="Module">structured-types.pointed-cartesian-product-types</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

Given a list of pointed types `l` we define recursively the iterated pointed
cartesian product of `l`.

## Definition

<pre class="Agda"><a id="iterated-product-Pointed-Type"></a><a id="577" href="structured-types.iterated-pointed-cartesian-product-types.html#577" class="Function">iterated-product-Pointed-Type</a> <a id="607" class="Symbol">:</a>
  <a id="611" class="Symbol">{</a><a id="612" href="structured-types.iterated-pointed-cartesian-product-types.html#612" class="Bound">l</a> <a id="614" class="Symbol">:</a> <a id="616" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="621" class="Symbol">}</a> <a id="623" class="Symbol">→</a> <a id="625" class="Symbol">(</a><a id="626" href="structured-types.iterated-pointed-cartesian-product-types.html#626" class="Bound">L</a> <a id="628" class="Symbol">:</a> <a id="630" href="lists.lists.html#1328" class="Datatype">list</a> <a id="635" class="Symbol">(</a><a id="636" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="649" href="structured-types.iterated-pointed-cartesian-product-types.html#612" class="Bound">l</a><a id="650" class="Symbol">))</a> <a id="653" class="Symbol">→</a> <a id="655" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="668" href="structured-types.iterated-pointed-cartesian-product-types.html#612" class="Bound">l</a>
<a id="670" href="structured-types.iterated-pointed-cartesian-product-types.html#577" class="Function">iterated-product-Pointed-Type</a> <a id="700" href="lists.lists.html#1371" class="InductiveConstructor">nil</a> <a id="704" class="Symbol">=</a> <a id="706" href="foundation.unit-type.html#1545" class="Function">raise-unit</a> <a id="717" class="Symbol">_</a> <a id="719" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="721" href="foundation.unit-type.html#1606" class="Function">raise-star</a>
<a id="732" href="structured-types.iterated-pointed-cartesian-product-types.html#577" class="Function">iterated-product-Pointed-Type</a> <a id="762" class="Symbol">(</a><a id="763" href="lists.lists.html#1386" class="InductiveConstructor">cons</a> <a id="768" href="structured-types.iterated-pointed-cartesian-product-types.html#768" class="Bound">x</a> <a id="770" href="structured-types.iterated-pointed-cartesian-product-types.html#770" class="Bound">L</a><a id="771" class="Symbol">)</a> <a id="773" class="Symbol">=</a>
  <a id="777" href="structured-types.iterated-pointed-cartesian-product-types.html#768" class="Bound">x</a> <a id="779" href="structured-types.pointed-cartesian-product-types.html#1064" class="Function Operator">×∗</a> <a id="782" class="Symbol">(</a><a id="783" href="structured-types.iterated-pointed-cartesian-product-types.html#577" class="Function">iterated-product-Pointed-Type</a> <a id="813" href="structured-types.iterated-pointed-cartesian-product-types.html#770" class="Bound">L</a><a id="814" class="Symbol">)</a>
</pre>