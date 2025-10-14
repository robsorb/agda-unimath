# Impredicative universes

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation.impredicative-universes.html" class="Module">foundation.impredicative-universes</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation-core.small-types.html" class="Module">foundation-core.small-types</a>
</pre>
</details>

## Idea

A universe `𝒰` is {{#concept "impredicative"}} if the type of
[propositions](foundation-core.propositions.md) in `𝒰` is `𝒰`-small.

## Definition

<pre class="Agda"><a id="is-impredicative-UU"></a><a id="436" href="foundation.impredicative-universes.html#436" class="Function">is-impredicative-UU</a> <a id="456" class="Symbol">:</a> <a id="458" class="Symbol">(</a><a id="459" href="foundation.impredicative-universes.html#459" class="Bound">l</a> <a id="461" class="Symbol">:</a> <a id="463" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="468" class="Symbol">)</a> <a id="470" class="Symbol">→</a> <a id="472" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="475" class="Symbol">(</a><a id="476" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="481" href="foundation.impredicative-universes.html#459" class="Bound">l</a><a id="482" class="Symbol">)</a>
<a id="484" href="foundation.impredicative-universes.html#436" class="Function">is-impredicative-UU</a> <a id="504" href="foundation.impredicative-universes.html#504" class="Bound">l</a> <a id="506" class="Symbol">=</a> <a id="508" href="foundation-core.small-types.html#1494" class="Function">is-small</a> <a id="517" href="foundation.impredicative-universes.html#504" class="Bound">l</a> <a id="519" class="Symbol">(</a><a id="520" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="525" href="foundation.impredicative-universes.html#504" class="Bound">l</a><a id="526" class="Symbol">)</a>
</pre>
## See also

- [Impredicative encodings of the logical operations](foundation.impredicative-encodings.md)
