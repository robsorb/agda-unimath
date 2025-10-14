# The plus-principle

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="synthetic-homotopy-theory.plus-principle.html" class="Module">synthetic-homotopy-theory.plus-principle</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="synthetic-homotopy-theory.acyclic-types.html" class="Module">synthetic-homotopy-theory.acyclic-types</a>
</pre>
</details>

## Idea

The **plus-principle** asserts that any
[acyclic](synthetic-homotopy-theory.acyclic-types.md)
[1-connected type](foundation.connected-types.md) is
[contractible](foundation.contractible-types.md).

## Definition

<pre class="Agda"><a id="plus-principle"></a><a id="596" href="synthetic-homotopy-theory.plus-principle.html#596" class="Function">plus-principle</a> <a id="611" class="Symbol">:</a> <a id="613" class="Symbol">(</a><a id="614" href="synthetic-homotopy-theory.plus-principle.html#614" class="Bound">l</a> <a id="616" class="Symbol">:</a> <a id="618" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="623" class="Symbol">)</a> <a id="625" class="Symbol">→</a> <a id="627" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="630" class="Symbol">(</a><a id="631" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="636" href="synthetic-homotopy-theory.plus-principle.html#614" class="Bound">l</a><a id="637" class="Symbol">)</a>
<a id="639" href="synthetic-homotopy-theory.plus-principle.html#596" class="Function">plus-principle</a> <a id="654" href="synthetic-homotopy-theory.plus-principle.html#654" class="Bound">l</a> <a id="656" class="Symbol">=</a>
  <a id="660" class="Symbol">(</a><a id="661" href="synthetic-homotopy-theory.plus-principle.html#661" class="Bound">A</a> <a id="663" class="Symbol">:</a> <a id="665" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="668" href="synthetic-homotopy-theory.plus-principle.html#654" class="Bound">l</a><a id="669" class="Symbol">)</a> <a id="671" class="Symbol">→</a> <a id="673" href="synthetic-homotopy-theory.acyclic-types.html#787" class="Function">is-acyclic</a> <a id="684" href="synthetic-homotopy-theory.plus-principle.html#661" class="Bound">A</a> <a id="686" class="Symbol">→</a> <a id="688" href="foundation.connected-types.html#1379" class="Function">is-connected</a> <a id="701" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a> <a id="707" href="synthetic-homotopy-theory.plus-principle.html#661" class="Bound">A</a> <a id="709" class="Symbol">→</a> <a id="711" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="720" href="synthetic-homotopy-theory.plus-principle.html#661" class="Bound">A</a>
</pre>