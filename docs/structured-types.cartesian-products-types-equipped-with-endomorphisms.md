# Cartesian products of types equipped with endomorphisms

<pre class="Agda"><a id="68" class="Keyword">module</a> <a id="75" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html" class="Module">structured-types.cartesian-products-types-equipped-with-endomorphisms</a> <a id="145" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="structured-types.types-equipped-with-endomorphisms.html" class="Module">structured-types.types-equipped-with-endomorphisms</a>
</pre>
</details>

## Idea

The **cartesian product** of two
[types equipped with an endomorphism](structured-types.types-equipped-with-endomorphisms.md)
`(A , f)` and `(B , g)` is defined as `(A × B , f × g)`

## Definitions

<pre class="Agda"><a id="689" class="Keyword">module</a> <a id="696" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#696" class="Module">_</a>
  <a id="700" class="Symbol">{</a><a id="701" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#701" class="Bound">l1</a> <a id="704" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#704" class="Bound">l2</a> <a id="707" class="Symbol">:</a> <a id="709" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="714" class="Symbol">}</a>
  <a id="718" class="Symbol">(</a><a id="719" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#719" class="Bound">A</a> <a id="721" class="Symbol">:</a> <a id="723" href="structured-types.types-equipped-with-endomorphisms.html#530" class="Function">Type-With-Endomorphism</a> <a id="746" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#701" class="Bound">l1</a><a id="748" class="Symbol">)</a> <a id="750" class="Symbol">(</a><a id="751" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#751" class="Bound">B</a> <a id="753" class="Symbol">:</a> <a id="755" href="structured-types.types-equipped-with-endomorphisms.html#530" class="Function">Type-With-Endomorphism</a> <a id="778" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#704" class="Bound">l2</a><a id="780" class="Symbol">)</a>
  <a id="784" class="Keyword">where</a>

  <a id="793" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#793" class="Function">type-product-Type-With-Endomorphism</a> <a id="829" class="Symbol">:</a> <a id="831" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="834" class="Symbol">(</a><a id="835" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#701" class="Bound">l1</a> <a id="838" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="840" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#704" class="Bound">l2</a><a id="842" class="Symbol">)</a>
  <a id="846" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#793" class="Function">type-product-Type-With-Endomorphism</a> <a id="882" class="Symbol">=</a>
    <a id="888" href="structured-types.types-equipped-with-endomorphisms.html#688" class="Function">type-Type-With-Endomorphism</a> <a id="916" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#719" class="Bound">A</a> <a id="918" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="920" href="structured-types.types-equipped-with-endomorphisms.html#688" class="Function">type-Type-With-Endomorphism</a> <a id="948" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#751" class="Bound">B</a>

  <a id="953" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#953" class="Function">endomorphism-product-Type-With-Endomorphism</a> <a id="997" class="Symbol">:</a>
    <a id="1003" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#793" class="Function">type-product-Type-With-Endomorphism</a> <a id="1039" class="Symbol">→</a> <a id="1041" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#793" class="Function">type-product-Type-With-Endomorphism</a>
  <a id="1079" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#953" class="Function">endomorphism-product-Type-With-Endomorphism</a> <a id="1123" class="Symbol">=</a>
    <a id="1129" href="foundation.functoriality-cartesian-product-types.html#1644" class="Function">map-product</a>
      <a id="1147" class="Symbol">(</a> <a id="1149" href="structured-types.types-equipped-with-endomorphisms.html#764" class="Function">endomorphism-Type-With-Endomorphism</a> <a id="1185" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#719" class="Bound">A</a><a id="1186" class="Symbol">)</a>
      <a id="1194" class="Symbol">(</a> <a id="1196" href="structured-types.types-equipped-with-endomorphisms.html#764" class="Function">endomorphism-Type-With-Endomorphism</a> <a id="1232" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#751" class="Bound">B</a><a id="1233" class="Symbol">)</a>

  <a id="1238" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#1238" class="Function">product-Type-With-Endomorphism</a> <a id="1269" class="Symbol">:</a>
    <a id="1275" href="structured-types.types-equipped-with-endomorphisms.html#530" class="Function">Type-With-Endomorphism</a> <a id="1298" class="Symbol">(</a><a id="1299" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#701" class="Bound">l1</a> <a id="1302" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1304" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#704" class="Bound">l2</a><a id="1306" class="Symbol">)</a>
  <a id="1310" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1314" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#1238" class="Function">product-Type-With-Endomorphism</a> <a id="1345" class="Symbol">=</a>
    <a id="1351" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#793" class="Function">type-product-Type-With-Endomorphism</a>
  <a id="1389" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1393" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#1238" class="Function">product-Type-With-Endomorphism</a> <a id="1424" class="Symbol">=</a>
    <a id="1430" href="structured-types.cartesian-products-types-equipped-with-endomorphisms.html#953" class="Function">endomorphism-product-Type-With-Endomorphism</a>
</pre>