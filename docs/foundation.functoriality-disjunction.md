# Functoriality of disjunction

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation.functoriality-disjunction.html" class="Module">foundation.functoriality-disjunction</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="267" class="Keyword">open</a> <a id="272" class="Keyword">import</a> <a id="279" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Any two implications `f : A ⇒ B` and `g : C ⇒ D` induce an implication
`map-disjunction f g : (A ∨ B) ⇒ (C ∨ D)`.

## Definitions

### The functorial action of disjunction

<pre class="Agda"><a id="575" class="Keyword">module</a> <a id="582" href="foundation.functoriality-disjunction.html#582" class="Module">_</a>
  <a id="586" class="Symbol">{</a><a id="587" href="foundation.functoriality-disjunction.html#587" class="Bound">l1</a> <a id="590" href="foundation.functoriality-disjunction.html#590" class="Bound">l2</a> <a id="593" href="foundation.functoriality-disjunction.html#593" class="Bound">l3</a> <a id="596" href="foundation.functoriality-disjunction.html#596" class="Bound">l4</a> <a id="599" class="Symbol">:</a> <a id="601" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="606" class="Symbol">}</a> <a id="608" class="Symbol">{</a><a id="609" href="foundation.functoriality-disjunction.html#609" class="Bound">A</a> <a id="611" class="Symbol">:</a> <a id="613" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="616" href="foundation.functoriality-disjunction.html#587" class="Bound">l1</a><a id="618" class="Symbol">}</a> <a id="620" class="Symbol">{</a><a id="621" href="foundation.functoriality-disjunction.html#621" class="Bound">B</a> <a id="623" class="Symbol">:</a> <a id="625" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="628" href="foundation.functoriality-disjunction.html#590" class="Bound">l2</a><a id="630" class="Symbol">}</a> <a id="632" class="Symbol">{</a><a id="633" href="foundation.functoriality-disjunction.html#633" class="Bound">C</a> <a id="635" class="Symbol">:</a> <a id="637" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="640" href="foundation.functoriality-disjunction.html#593" class="Bound">l3</a><a id="642" class="Symbol">}</a> <a id="644" class="Symbol">{</a><a id="645" href="foundation.functoriality-disjunction.html#645" class="Bound">D</a> <a id="647" class="Symbol">:</a> <a id="649" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="652" href="foundation.functoriality-disjunction.html#596" class="Bound">l4</a><a id="654" class="Symbol">}</a>
  <a id="658" class="Symbol">(</a><a id="659" href="foundation.functoriality-disjunction.html#659" class="Bound">f</a> <a id="661" class="Symbol">:</a> <a id="663" href="foundation.functoriality-disjunction.html#609" class="Bound">A</a> <a id="665" class="Symbol">→</a> <a id="667" href="foundation.functoriality-disjunction.html#621" class="Bound">B</a><a id="668" class="Symbol">)</a> <a id="670" class="Symbol">(</a><a id="671" href="foundation.functoriality-disjunction.html#671" class="Bound">g</a> <a id="673" class="Symbol">:</a> <a id="675" href="foundation.functoriality-disjunction.html#633" class="Bound">C</a> <a id="677" class="Symbol">→</a> <a id="679" href="foundation.functoriality-disjunction.html#645" class="Bound">D</a><a id="680" class="Symbol">)</a>
  <a id="684" class="Keyword">where</a>

  <a id="693" href="foundation.functoriality-disjunction.html#693" class="Function">map-disjunction</a> <a id="709" class="Symbol">:</a> <a id="711" href="foundation.disjunction.html#3159" class="Function">disjunction-type</a> <a id="728" href="foundation.functoriality-disjunction.html#609" class="Bound">A</a> <a id="730" href="foundation.functoriality-disjunction.html#633" class="Bound">C</a> <a id="732" class="Symbol">→</a> <a id="734" href="foundation.disjunction.html#3159" class="Function">disjunction-type</a> <a id="751" href="foundation.functoriality-disjunction.html#621" class="Bound">B</a> <a id="753" href="foundation.functoriality-disjunction.html#645" class="Bound">D</a>
  <a id="757" href="foundation.functoriality-disjunction.html#693" class="Function">map-disjunction</a> <a id="773" class="Symbol">=</a> <a id="775" href="foundation.functoriality-propositional-truncation.html#1256" class="Function">map-trunc-Prop</a> <a id="790" class="Symbol">(</a><a id="791" href="foundation.functoriality-coproduct-types.html#2021" class="Function">map-coproduct</a> <a id="805" href="foundation.functoriality-disjunction.html#659" class="Bound">f</a> <a id="807" href="foundation.functoriality-disjunction.html#671" class="Bound">g</a><a id="808" class="Symbol">)</a>
</pre>