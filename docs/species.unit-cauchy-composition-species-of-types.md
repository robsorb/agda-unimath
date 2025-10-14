# The unit of Cauchy composition of species of types

<pre class="Agda"><a id="63" class="Keyword">module</a> <a id="70" href="species.unit-cauchy-composition-species-of-types.html" class="Module">species.unit-cauchy-composition-species-of-types</a> <a id="119" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

The
{{#concept "unit" Disambiguation="of Cauchy composition of species of types" Agda=unit-species-types}}
of [Cauchy composition](species.cauchy-composition-species-of-types.md) of
[species of types](species.species-of-types.md) is the species

```text
  X ↦ is-contr X.
```

## Definition

<pre class="Agda"><a id="unit-species-types"></a><a id="620" href="species.unit-cauchy-composition-species-of-types.html#620" class="Function">unit-species-types</a> <a id="639" class="Symbol">:</a> <a id="641" class="Symbol">{</a><a id="642" href="species.unit-cauchy-composition-species-of-types.html#642" class="Bound">l1</a> <a id="645" class="Symbol">:</a> <a id="647" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="652" class="Symbol">}</a> <a id="654" class="Symbol">→</a> <a id="656" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="670" href="species.unit-cauchy-composition-species-of-types.html#642" class="Bound">l1</a> <a id="673" href="species.unit-cauchy-composition-species-of-types.html#642" class="Bound">l1</a>
<a id="676" href="species.unit-cauchy-composition-species-of-types.html#620" class="Function">unit-species-types</a> <a id="695" class="Symbol">=</a> <a id="697" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a>
</pre>