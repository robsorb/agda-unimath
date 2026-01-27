# Cauchy products of species of types

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="species.cauchy-products-species-of-types.html" class="Module">species.cauchy-products-species-of-types</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.coproduct-decompositions.html" class="Module">foundation.coproduct-decompositions</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="331" class="Keyword">open</a> <a id="336" class="Keyword">import</a> <a id="343" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

The
{{#concept "Cauchy product" Disambiguation="of species of types" Agda=cauchy-product-species-types}}
of two [species of types](species.species-of-types.md) `S` and `T` on `X` is
defined as

```text
  Σ (k : UU) (Σ (k' : UU) (Σ (e : k + k' ≃ X) S(k) × T(k'))).
```

## Definition

<pre class="Agda"><a id="686" class="Keyword">module</a> <a id="693" href="species.cauchy-products-species-of-types.html#693" class="Module">_</a>
  <a id="697" class="Symbol">{</a><a id="698" href="species.cauchy-products-species-of-types.html#698" class="Bound">l1</a> <a id="701" href="species.cauchy-products-species-of-types.html#701" class="Bound">l2</a> <a id="704" href="species.cauchy-products-species-of-types.html#704" class="Bound">l3</a> <a id="707" class="Symbol">:</a> <a id="709" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="714" class="Symbol">}</a>
  <a id="718" class="Symbol">(</a><a id="719" href="species.cauchy-products-species-of-types.html#719" class="Bound">S</a> <a id="721" class="Symbol">:</a> <a id="723" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="737" href="species.cauchy-products-species-of-types.html#698" class="Bound">l1</a> <a id="740" href="species.cauchy-products-species-of-types.html#701" class="Bound">l2</a><a id="742" class="Symbol">)</a>
  <a id="746" class="Symbol">(</a><a id="747" href="species.cauchy-products-species-of-types.html#747" class="Bound">T</a> <a id="749" class="Symbol">:</a> <a id="751" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="765" href="species.cauchy-products-species-of-types.html#698" class="Bound">l1</a> <a id="768" href="species.cauchy-products-species-of-types.html#704" class="Bound">l3</a><a id="770" class="Symbol">)</a>
  <a id="774" class="Keyword">where</a>

  <a id="783" href="species.cauchy-products-species-of-types.html#783" class="Function">cauchy-product-species-types</a> <a id="812" class="Symbol">:</a> <a id="814" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="828" href="species.cauchy-products-species-of-types.html#698" class="Bound">l1</a> <a id="831" class="Symbol">(</a><a id="832" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="837" href="species.cauchy-products-species-of-types.html#698" class="Bound">l1</a> <a id="840" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="842" href="species.cauchy-products-species-of-types.html#701" class="Bound">l2</a> <a id="845" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="847" href="species.cauchy-products-species-of-types.html#704" class="Bound">l3</a><a id="849" class="Symbol">)</a>
  <a id="853" href="species.cauchy-products-species-of-types.html#783" class="Function">cauchy-product-species-types</a> <a id="882" href="species.cauchy-products-species-of-types.html#882" class="Bound">X</a> <a id="884" class="Symbol">=</a>
    <a id="890" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="892" class="Symbol">(</a> <a id="894" href="foundation.coproduct-decompositions.html#1803" class="Function">binary-coproduct-Decomposition</a> <a id="925" href="species.cauchy-products-species-of-types.html#698" class="Bound">l1</a> <a id="928" href="species.cauchy-products-species-of-types.html#698" class="Bound">l1</a> <a id="931" href="species.cauchy-products-species-of-types.html#882" class="Bound">X</a><a id="932" class="Symbol">)</a>
      <a id="940" class="Symbol">(</a> <a id="942" class="Symbol">λ</a> <a id="944" href="species.cauchy-products-species-of-types.html#944" class="Bound">d</a> <a id="946" class="Symbol">→</a>
        <a id="956" href="species.cauchy-products-species-of-types.html#719" class="Bound">S</a> <a id="958" class="Symbol">(</a><a id="959" href="foundation.coproduct-decompositions.html#2058" class="Function">left-summand-binary-coproduct-Decomposition</a> <a id="1003" href="species.cauchy-products-species-of-types.html#944" class="Bound">d</a><a id="1004" class="Symbol">)</a> <a id="1006" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
        <a id="1016" href="species.cauchy-products-species-of-types.html#747" class="Bound">T</a> <a id="1018" class="Symbol">(</a><a id="1019" href="foundation.coproduct-decompositions.html#2167" class="Function">right-summand-binary-coproduct-Decomposition</a> <a id="1064" href="species.cauchy-products-species-of-types.html#944" class="Bound">d</a><a id="1065" class="Symbol">))</a>
</pre>