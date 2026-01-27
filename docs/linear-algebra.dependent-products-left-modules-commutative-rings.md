# Dependent products of left modules over commutative rings

<pre class="Agda"><a id="70" class="Keyword">module</a> <a id="77" href="linear-algebra.dependent-products-left-modules-commutative-rings.html" class="Module">linear-algebra.dependent-products-left-modules-commutative-rings</a> <a id="142" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="commutative-algebra.commutative-rings.html" class="Module">commutative-algebra.commutative-rings</a>

<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="linear-algebra.dependent-products-left-modules-rings.html" class="Module">linear-algebra.dependent-products-left-modules-rings</a>
<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="linear-algebra.left-modules-commutative-rings.html" class="Module">linear-algebra.left-modules-commutative-rings</a>
</pre>
</details>

## Idea

Given a [commutative ring](commutative-algebra.commutative-rings.md) `R` and a
family of [left modules](linear-algebra.left-modules-commutative-rings.md) `Mᵢ`
over `R` indexed by `i : I`, the dependent product `Π (i : I) Mᵢ` is a left
module over `R`.

## Definition

<pre class="Agda"><a id="761" class="Keyword">module</a> <a id="768" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#768" class="Module">_</a>
  <a id="772" class="Symbol">{</a><a id="773" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#773" class="Bound">l1</a> <a id="776" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#776" class="Bound">l2</a> <a id="779" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#779" class="Bound">l3</a> <a id="782" class="Symbol">:</a> <a id="784" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="789" class="Symbol">}</a> <a id="791" class="Symbol">(</a><a id="792" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#792" class="Bound">R</a> <a id="794" class="Symbol">:</a> <a id="796" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="813" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#773" class="Bound">l1</a><a id="815" class="Symbol">)</a> <a id="817" class="Symbol">(</a><a id="818" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#818" class="Bound">I</a> <a id="820" class="Symbol">:</a> <a id="822" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="825" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#776" class="Bound">l2</a><a id="827" class="Symbol">)</a>
  <a id="831" class="Symbol">(</a><a id="832" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#832" class="Bound">M</a> <a id="834" class="Symbol">:</a> <a id="836" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#818" class="Bound">I</a> <a id="838" class="Symbol">→</a> <a id="840" href="linear-algebra.left-modules-commutative-rings.html#806" class="Function">left-module-Commutative-Ring</a> <a id="869" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#779" class="Bound">l3</a> <a id="872" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#792" class="Bound">R</a><a id="873" class="Symbol">)</a>
  <a id="877" class="Keyword">where</a>

  <a id="886" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#886" class="Function">Π-left-module-Commutative-Ring</a> <a id="917" class="Symbol">:</a> <a id="919" href="linear-algebra.left-modules-commutative-rings.html#806" class="Function">left-module-Commutative-Ring</a> <a id="948" class="Symbol">(</a><a id="949" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#776" class="Bound">l2</a> <a id="952" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="954" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#779" class="Bound">l3</a><a id="956" class="Symbol">)</a> <a id="958" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#792" class="Bound">R</a>
  <a id="962" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#886" class="Function">Π-left-module-Commutative-Ring</a> <a id="993" class="Symbol">=</a>
    <a id="999" href="linear-algebra.dependent-products-left-modules-rings.html#2857" class="Function">Π-left-module-Ring</a> <a id="1018" class="Symbol">(</a><a id="1019" href="commutative-algebra.commutative-rings.html#2260" class="Function">ring-Commutative-Ring</a> <a id="1041" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#792" class="Bound">R</a><a id="1042" class="Symbol">)</a> <a id="1044" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#818" class="Bound">I</a> <a id="1046" href="linear-algebra.dependent-products-left-modules-commutative-rings.html#832" class="Bound">M</a>
</pre>