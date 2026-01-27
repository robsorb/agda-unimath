# Derivatives of species

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="species.derivatives-species-of-types.html" class="Module">species.derivatives-species-of-types</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

When we think of a [species of types](species.species-of-types.md) as the
coefficients of a formal power series, the
{{#concept "derivative" Disambiguation="of species of types" Agda=derivative-species-types}}
of a species of types is the species of types representing the derivative of
that formal power series.

## Definition

<pre class="Agda"><a id="derivative-species-types"></a><a id="647" href="species.derivatives-species-of-types.html#647" class="Function">derivative-species-types</a> <a id="672" class="Symbol">:</a>
  <a id="676" class="Symbol">{</a><a id="677" href="species.derivatives-species-of-types.html#677" class="Bound">l1</a> <a id="680" href="species.derivatives-species-of-types.html#680" class="Bound">l2</a> <a id="683" class="Symbol">:</a> <a id="685" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="690" class="Symbol">}</a> <a id="692" class="Symbol">→</a> <a id="694" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="708" href="species.derivatives-species-of-types.html#677" class="Bound">l1</a> <a id="711" href="species.derivatives-species-of-types.html#680" class="Bound">l2</a> <a id="714" class="Symbol">→</a> <a id="716" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="730" href="species.derivatives-species-of-types.html#677" class="Bound">l1</a> <a id="733" href="species.derivatives-species-of-types.html#680" class="Bound">l2</a>
<a id="736" href="species.derivatives-species-of-types.html#647" class="Function">derivative-species-types</a> <a id="761" href="species.derivatives-species-of-types.html#761" class="Bound">F</a> <a id="763" href="species.derivatives-species-of-types.html#763" class="Bound">X</a> <a id="765" class="Symbol">=</a> <a id="767" href="species.derivatives-species-of-types.html#761" class="Bound">F</a> <a id="769" class="Symbol">(</a><a id="770" href="species.derivatives-species-of-types.html#763" class="Bound">X</a> <a id="772" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="774" href="foundation.unit-type.html#950" class="Record">unit</a><a id="778" class="Symbol">)</a>
</pre>