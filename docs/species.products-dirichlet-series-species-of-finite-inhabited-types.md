# Products of Dirichlet series of species of finite inhabited types

<pre class="Agda"><a id="78" class="Keyword">module</a> <a id="85" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html" class="Module">species.products-dirichlet-series-species-of-finite-inhabited-types</a> <a id="153" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="species.dirichlet-series-species-of-finite-inhabited-types.html" class="Module">species.dirichlet-series-species-of-finite-inhabited-types</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="species.species-of-finite-inhabited-types.html" class="Module">species.species-of-finite-inhabited-types</a>
</pre>
</details>

## Idea

The
{{#concept "product" Disambiguation="of Caucy series of species of finite inhabited types" Agda=product-dirichlet-series-species-Inhabited-Finite-Type}}
of two
[Dirichlet series](species.dirichlet-series-species-of-finite-inhabited-types.md)
of
[species of types in subuniverses](species.species-of-finite-inhabited-types.md)
is just the pointwise [product](foundation.cartesian-product-types.md).

## Definition

<pre class="Agda"><a id="product-dirichlet-series-species-Inhabited-Finite-Type"></a><a id="873" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#873" class="Function">product-dirichlet-series-species-Inhabited-Finite-Type</a> <a id="928" class="Symbol">:</a>
  <a id="932" class="Symbol">{</a><a id="933" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#933" class="Bound">l1</a> <a id="936" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#936" class="Bound">l2</a> <a id="939" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#939" class="Bound">l3</a> <a id="942" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#942" class="Bound">l4</a> <a id="945" class="Symbol">:</a> <a id="947" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="952" class="Symbol">}</a> <a id="954" class="Symbol">→</a> <a id="956" href="species.species-of-finite-inhabited-types.html#711" class="Function">species-Inhabited-Finite-Type</a> <a id="986" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#933" class="Bound">l1</a> <a id="989" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#936" class="Bound">l2</a> <a id="992" class="Symbol">→</a>
  <a id="996" href="species.species-of-finite-inhabited-types.html#711" class="Function">species-Inhabited-Finite-Type</a> <a id="1026" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#933" class="Bound">l1</a> <a id="1029" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#939" class="Bound">l3</a> <a id="1032" class="Symbol">→</a>
  <a id="1036" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1039" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#942" class="Bound">l4</a> <a id="1042" class="Symbol">→</a> <a id="1044" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1047" class="Symbol">(</a><a id="1048" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1053" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#933" class="Bound">l1</a> <a id="1056" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1058" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#936" class="Bound">l2</a> <a id="1061" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1063" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#939" class="Bound">l3</a> <a id="1066" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1068" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#942" class="Bound">l4</a><a id="1070" class="Symbol">)</a>
<a id="1072" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#873" class="Function">product-dirichlet-series-species-Inhabited-Finite-Type</a> <a id="1127" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#1127" class="Bound">S</a> <a id="1129" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#1129" class="Bound">T</a> <a id="1131" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#1131" class="Bound">X</a> <a id="1133" class="Symbol">=</a>
  <a id="1137" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1630" class="Function">dirichlet-series-species-Inhabited-Finite-Type</a> <a id="1184" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#1127" class="Bound">S</a> <a id="1186" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#1131" class="Bound">X</a> <a id="1188" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
  <a id="1192" href="species.dirichlet-series-species-of-finite-inhabited-types.html#1630" class="Function">dirichlet-series-species-Inhabited-Finite-Type</a> <a id="1239" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#1129" class="Bound">T</a> <a id="1241" href="species.products-dirichlet-series-species-of-finite-inhabited-types.html#1131" class="Bound">X</a>
</pre>