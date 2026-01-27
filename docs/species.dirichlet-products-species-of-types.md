# Dirichlet products of species of types

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="species.dirichlet-products-species-of-types.html" class="Module">species.dirichlet-products-species-of-types</a> <a id="102" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.product-decompositions.html" class="Module">foundation.product-decompositions</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

The
{{#concept "Dirichlet product" Disambiguation="of species of types" Agda=dirichlet-product-species-types}}
of two [species of types](species.species-of-types.md) `S` and `T` on `X` is
defined as

```text
  Σ (k : UU) (Σ (k' : UU) (Σ (e : k × k' ≃ X) S(k) × T(k'))).
```

## Definition

<pre class="Agda"><a id="696" class="Keyword">module</a> <a id="703" href="species.dirichlet-products-species-of-types.html#703" class="Module">_</a>
  <a id="707" class="Symbol">{</a><a id="708" href="species.dirichlet-products-species-of-types.html#708" class="Bound">l1</a> <a id="711" href="species.dirichlet-products-species-of-types.html#711" class="Bound">l2</a> <a id="714" href="species.dirichlet-products-species-of-types.html#714" class="Bound">l3</a> <a id="717" class="Symbol">:</a> <a id="719" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="724" class="Symbol">}</a>
  <a id="728" class="Symbol">(</a><a id="729" href="species.dirichlet-products-species-of-types.html#729" class="Bound">S</a> <a id="731" class="Symbol">:</a> <a id="733" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="747" href="species.dirichlet-products-species-of-types.html#708" class="Bound">l1</a> <a id="750" href="species.dirichlet-products-species-of-types.html#711" class="Bound">l2</a><a id="752" class="Symbol">)</a>
  <a id="756" class="Symbol">(</a><a id="757" href="species.dirichlet-products-species-of-types.html#757" class="Bound">T</a> <a id="759" class="Symbol">:</a> <a id="761" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="775" href="species.dirichlet-products-species-of-types.html#708" class="Bound">l1</a> <a id="778" href="species.dirichlet-products-species-of-types.html#714" class="Bound">l3</a><a id="780" class="Symbol">)</a>
  <a id="784" class="Keyword">where</a>

  <a id="793" href="species.dirichlet-products-species-of-types.html#793" class="Function">dirichlet-product-species-types</a> <a id="825" class="Symbol">:</a> <a id="827" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="841" href="species.dirichlet-products-species-of-types.html#708" class="Bound">l1</a> <a id="844" class="Symbol">(</a><a id="845" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="850" href="species.dirichlet-products-species-of-types.html#708" class="Bound">l1</a> <a id="853" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="855" href="species.dirichlet-products-species-of-types.html#711" class="Bound">l2</a> <a id="858" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="860" href="species.dirichlet-products-species-of-types.html#714" class="Bound">l3</a><a id="862" class="Symbol">)</a>
  <a id="866" href="species.dirichlet-products-species-of-types.html#793" class="Function">dirichlet-product-species-types</a> <a id="898" href="species.dirichlet-products-species-of-types.html#898" class="Bound">X</a> <a id="900" class="Symbol">=</a>
    <a id="906" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="908" class="Symbol">(</a> <a id="910" href="foundation.product-decompositions.html#447" class="Function">binary-product-Decomposition</a> <a id="939" href="species.dirichlet-products-species-of-types.html#708" class="Bound">l1</a> <a id="942" href="species.dirichlet-products-species-of-types.html#708" class="Bound">l1</a> <a id="945" href="species.dirichlet-products-species-of-types.html#898" class="Bound">X</a><a id="946" class="Symbol">)</a>
      <a id="954" class="Symbol">(</a> <a id="956" class="Symbol">λ</a> <a id="958" href="species.dirichlet-products-species-of-types.html#958" class="Bound">d</a> <a id="960" class="Symbol">→</a>
        <a id="970" href="species.dirichlet-products-species-of-types.html#729" class="Bound">S</a> <a id="972" class="Symbol">(</a><a id="973" href="foundation.product-decompositions.html#690" class="Function">left-summand-binary-product-Decomposition</a> <a id="1015" href="species.dirichlet-products-species-of-types.html#958" class="Bound">d</a><a id="1016" class="Symbol">)</a> <a id="1018" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
        <a id="1028" href="species.dirichlet-products-species-of-types.html#757" class="Bound">T</a> <a id="1030" class="Symbol">(</a><a id="1031" href="foundation.product-decompositions.html#795" class="Function">right-summand-binary-product-Decomposition</a> <a id="1074" href="species.dirichlet-products-species-of-types.html#958" class="Bound">d</a><a id="1075" class="Symbol">))</a>
</pre>