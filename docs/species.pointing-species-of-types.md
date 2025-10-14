# Pointing of species of types

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="species.pointing-species-of-types.html" class="Module">species.pointing-species-of-types</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

A
{{#concept "pointing" Disambiguation="of species of types" Agda=pointing-species-types}}
of a [species of types](species.species-of-types.md) `F` is the species of types
`F∗` given by `F∗ X := X × F X`. In other words, it is the species of points and
`F`-[structures](foundation.structure.md).

## Definition

<pre class="Agda"><a id="pointing-species-types"></a><a id="608" href="species.pointing-species-of-types.html#608" class="Function">pointing-species-types</a> <a id="631" class="Symbol">:</a>
  <a id="635" class="Symbol">{</a><a id="636" href="species.pointing-species-of-types.html#636" class="Bound">l1</a> <a id="639" href="species.pointing-species-of-types.html#639" class="Bound">l2</a> <a id="642" class="Symbol">:</a> <a id="644" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="649" class="Symbol">}</a> <a id="651" class="Symbol">→</a> <a id="653" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="667" href="species.pointing-species-of-types.html#636" class="Bound">l1</a> <a id="670" href="species.pointing-species-of-types.html#639" class="Bound">l2</a> <a id="673" class="Symbol">→</a> <a id="675" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="689" href="species.pointing-species-of-types.html#636" class="Bound">l1</a> <a id="692" class="Symbol">(</a><a id="693" href="species.pointing-species-of-types.html#636" class="Bound">l1</a> <a id="696" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="698" href="species.pointing-species-of-types.html#639" class="Bound">l2</a><a id="700" class="Symbol">)</a>
<a id="702" href="species.pointing-species-of-types.html#608" class="Function">pointing-species-types</a> <a id="725" href="species.pointing-species-of-types.html#725" class="Bound">F</a> <a id="727" href="species.pointing-species-of-types.html#727" class="Bound">X</a> <a id="729" class="Symbol">=</a> <a id="731" href="species.pointing-species-of-types.html#727" class="Bound">X</a> <a id="733" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="735" href="species.pointing-species-of-types.html#725" class="Bound">F</a> <a id="737" href="species.pointing-species-of-types.html#727" class="Bound">X</a>
</pre>