# Cartesian exponents of species of types

<pre class="Agda"><a id="52" class="Keyword">module</a> <a id="59" href="species.cartesian-exponents-species-of-types.html" class="Module">species.cartesian-exponents-species-of-types</a> <a id="104" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

The
{{#concept "Cartesian exponent" Disambiguation="of species of types" Agda=function-species-types}}
of two [species of types](species.species-of-types.md) `F` and `G` is the
pointwise exponent of `F` and `G`.

Note that we call such exponents _cartesian_ to disambiguate from other notions
of exponents, such as
[Cauchy exponentials](species.cauchy-exponentials-species-of-types.md).

## Definitions

### Cartesian exponents of species of types

<pre class="Agda"><a id="function-species-types"></a><a id="720" href="species.cartesian-exponents-species-of-types.html#720" class="Function">function-species-types</a> <a id="743" class="Symbol">:</a>
  <a id="747" class="Symbol">{</a><a id="748" href="species.cartesian-exponents-species-of-types.html#748" class="Bound">l1</a> <a id="751" href="species.cartesian-exponents-species-of-types.html#751" class="Bound">l2</a> <a id="754" href="species.cartesian-exponents-species-of-types.html#754" class="Bound">l3</a> <a id="757" class="Symbol">:</a> <a id="759" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="764" class="Symbol">}</a> <a id="766" class="Symbol">→</a>
  <a id="770" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="784" href="species.cartesian-exponents-species-of-types.html#748" class="Bound">l1</a> <a id="787" href="species.cartesian-exponents-species-of-types.html#751" class="Bound">l2</a> <a id="790" class="Symbol">→</a> <a id="792" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="806" href="species.cartesian-exponents-species-of-types.html#748" class="Bound">l1</a> <a id="809" href="species.cartesian-exponents-species-of-types.html#754" class="Bound">l3</a> <a id="812" class="Symbol">→</a> <a id="814" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="828" href="species.cartesian-exponents-species-of-types.html#748" class="Bound">l1</a> <a id="831" class="Symbol">(</a><a id="832" href="species.cartesian-exponents-species-of-types.html#751" class="Bound">l2</a> <a id="835" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="837" href="species.cartesian-exponents-species-of-types.html#754" class="Bound">l3</a><a id="839" class="Symbol">)</a>
<a id="841" href="species.cartesian-exponents-species-of-types.html#720" class="Function">function-species-types</a> <a id="864" href="species.cartesian-exponents-species-of-types.html#864" class="Bound">F</a> <a id="866" href="species.cartesian-exponents-species-of-types.html#866" class="Bound">G</a> <a id="868" href="species.cartesian-exponents-species-of-types.html#868" class="Bound">X</a> <a id="870" class="Symbol">=</a> <a id="872" class="Symbol">(</a><a id="873" href="species.cartesian-exponents-species-of-types.html#864" class="Bound">F</a> <a id="875" href="species.cartesian-exponents-species-of-types.html#868" class="Bound">X</a> <a id="877" class="Symbol">→</a> <a id="879" href="species.cartesian-exponents-species-of-types.html#866" class="Bound">G</a> <a id="881" href="species.cartesian-exponents-species-of-types.html#868" class="Bound">X</a><a id="882" class="Symbol">)</a>
</pre>