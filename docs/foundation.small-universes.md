# Small universes

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="foundation.small-universes.html" class="Module">foundation.small-universes</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="foundation-core.small-types.html" class="Module">foundation-core.small-types</a>
</pre>
</details>

## Idea

A [universe](foundation.universe-levels.md) `𝒰` is said to be
{{#concept "small" Disambiguation="universe of types" Agda=is-small-universe}}
with respect to `𝒱` if `𝒰` is a `𝒱`-[small](foundation-core.small-types.md) type
and each `X : 𝒰` is a `𝒱`-small type.

<pre class="Agda"><a id="is-small-universe"></a><a id="545" href="foundation.small-universes.html#545" class="Function">is-small-universe</a> <a id="563" class="Symbol">:</a>
  <a id="567" class="Symbol">(</a><a id="568" href="foundation.small-universes.html#568" class="Bound">l</a> <a id="570" href="foundation.small-universes.html#570" class="Bound">l1</a> <a id="573" class="Symbol">:</a> <a id="575" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="580" class="Symbol">)</a> <a id="582" class="Symbol">→</a> <a id="584" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="587" class="Symbol">(</a><a id="588" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="593" href="foundation.small-universes.html#570" class="Bound">l1</a> <a id="596" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="598" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="603" href="foundation.small-universes.html#568" class="Bound">l</a><a id="604" class="Symbol">)</a>
<a id="606" href="foundation.small-universes.html#545" class="Function">is-small-universe</a> <a id="624" href="foundation.small-universes.html#624" class="Bound">l</a> <a id="626" href="foundation.small-universes.html#626" class="Bound">l1</a> <a id="629" class="Symbol">=</a> <a id="631" href="foundation-core.small-types.html#1494" class="Function">is-small</a> <a id="640" href="foundation.small-universes.html#624" class="Bound">l</a> <a id="642" class="Symbol">(</a><a id="643" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="646" href="foundation.small-universes.html#626" class="Bound">l1</a><a id="648" class="Symbol">)</a> <a id="650" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="652" class="Symbol">((</a><a id="654" href="foundation.small-universes.html#654" class="Bound">X</a> <a id="656" class="Symbol">:</a> <a id="658" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="661" href="foundation.small-universes.html#626" class="Bound">l1</a><a id="663" class="Symbol">)</a> <a id="665" class="Symbol">→</a> <a id="667" href="foundation-core.small-types.html#1494" class="Function">is-small</a> <a id="676" href="foundation.small-universes.html#624" class="Bound">l</a> <a id="678" href="foundation.small-universes.html#654" class="Bound">X</a><a id="679" class="Symbol">)</a>
</pre>