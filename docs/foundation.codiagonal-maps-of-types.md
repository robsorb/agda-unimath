# Codiagonal maps of types

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="foundation.codiagonal-maps-of-types.html" class="Module">foundation.codiagonal-maps-of-types</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation-core.coproduct-types.html" class="Module">foundation-core.coproduct-types</a>
</pre>
</details>

## Idea

The codiagonal map `∇ : A + A → A` of `A` is the map that projects `A + A` onto
`A`.

## Definitions

<pre class="Agda"><a id="356" class="Keyword">module</a> <a id="363" href="foundation.codiagonal-maps-of-types.html#363" class="Module">_</a>
  <a id="367" class="Symbol">{</a> <a id="369" href="foundation.codiagonal-maps-of-types.html#369" class="Bound">l1</a> <a id="372" class="Symbol">:</a> <a id="374" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="379" class="Symbol">}</a> <a id="381" class="Symbol">(</a><a id="382" href="foundation.codiagonal-maps-of-types.html#382" class="Bound">A</a> <a id="384" class="Symbol">:</a> <a id="386" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="389" href="foundation.codiagonal-maps-of-types.html#369" class="Bound">l1</a><a id="391" class="Symbol">)</a>
  <a id="395" class="Keyword">where</a>

  <a id="404" href="foundation.codiagonal-maps-of-types.html#404" class="Function">codiagonal</a> <a id="415" class="Symbol">:</a> <a id="417" href="foundation.codiagonal-maps-of-types.html#382" class="Bound">A</a> <a id="419" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="421" href="foundation.codiagonal-maps-of-types.html#382" class="Bound">A</a> <a id="423" class="Symbol">→</a> <a id="425" href="foundation.codiagonal-maps-of-types.html#382" class="Bound">A</a>
  <a id="429" href="foundation.codiagonal-maps-of-types.html#404" class="Function">codiagonal</a> <a id="440" class="Symbol">(</a><a id="441" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="445" href="foundation.codiagonal-maps-of-types.html#445" class="Bound">a</a><a id="446" class="Symbol">)</a> <a id="448" class="Symbol">=</a> <a id="450" href="foundation.codiagonal-maps-of-types.html#445" class="Bound">a</a>
  <a id="454" href="foundation.codiagonal-maps-of-types.html#404" class="Function">codiagonal</a> <a id="465" class="Symbol">(</a><a id="466" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="470" href="foundation.codiagonal-maps-of-types.html#470" class="Bound">a</a><a id="471" class="Symbol">)</a> <a id="473" class="Symbol">=</a> <a id="475" href="foundation.codiagonal-maps-of-types.html#470" class="Bound">a</a>
</pre>