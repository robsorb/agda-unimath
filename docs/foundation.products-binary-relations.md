# Products of binary relations

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation.products-binary-relations.html" class="Module">foundation.products-binary-relations</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

Given two relations `R` and `S`, their product is given by
`(R × S) (a , b) (a' , b')` iff `R a a'` and `S b b'`.

## Definition

### The product of two relations

<pre class="Agda"><a id="556" class="Keyword">module</a> <a id="563" href="foundation.products-binary-relations.html#563" class="Module">_</a>
  <a id="567" class="Symbol">{</a><a id="568" href="foundation.products-binary-relations.html#568" class="Bound">l1</a> <a id="571" href="foundation.products-binary-relations.html#571" class="Bound">l2</a> <a id="574" href="foundation.products-binary-relations.html#574" class="Bound">l3</a> <a id="577" href="foundation.products-binary-relations.html#577" class="Bound">l4</a> <a id="580" class="Symbol">:</a> <a id="582" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="587" class="Symbol">}</a>
  <a id="591" class="Symbol">{</a><a id="592" href="foundation.products-binary-relations.html#592" class="Bound">A</a> <a id="594" class="Symbol">:</a> <a id="596" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="599" href="foundation.products-binary-relations.html#568" class="Bound">l1</a><a id="601" class="Symbol">}</a> <a id="603" class="Symbol">(</a><a id="604" href="foundation.products-binary-relations.html#604" class="Bound">R</a> <a id="606" class="Symbol">:</a> <a id="608" href="foundation.binary-relations.html#1511" class="Function">Relation-Prop</a> <a id="622" href="foundation.products-binary-relations.html#571" class="Bound">l2</a> <a id="625" href="foundation.products-binary-relations.html#592" class="Bound">A</a><a id="626" class="Symbol">)</a>
  <a id="630" class="Symbol">{</a><a id="631" href="foundation.products-binary-relations.html#631" class="Bound">B</a> <a id="633" class="Symbol">:</a> <a id="635" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="638" href="foundation.products-binary-relations.html#574" class="Bound">l3</a><a id="640" class="Symbol">}</a> <a id="642" class="Symbol">(</a><a id="643" href="foundation.products-binary-relations.html#643" class="Bound">S</a> <a id="645" class="Symbol">:</a> <a id="647" href="foundation.binary-relations.html#1511" class="Function">Relation-Prop</a> <a id="661" href="foundation.products-binary-relations.html#577" class="Bound">l4</a> <a id="664" href="foundation.products-binary-relations.html#631" class="Bound">B</a><a id="665" class="Symbol">)</a>
  <a id="669" class="Keyword">where</a>

  <a id="678" href="foundation.products-binary-relations.html#678" class="Function">product-Relation-Prop</a> <a id="700" class="Symbol">:</a>
    <a id="706" href="foundation.binary-relations.html#1511" class="Function">Relation-Prop</a> <a id="720" class="Symbol">(</a><a id="721" href="foundation.products-binary-relations.html#571" class="Bound">l2</a> <a id="724" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="726" href="foundation.products-binary-relations.html#577" class="Bound">l4</a><a id="728" class="Symbol">)</a> <a id="730" class="Symbol">(</a><a id="731" href="foundation.products-binary-relations.html#592" class="Bound">A</a> <a id="733" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="735" href="foundation.products-binary-relations.html#631" class="Bound">B</a><a id="736" class="Symbol">)</a>
  <a id="740" href="foundation.products-binary-relations.html#678" class="Function">product-Relation-Prop</a> <a id="762" class="Symbol">(</a><a id="763" href="foundation.products-binary-relations.html#763" class="Bound">a</a> <a id="765" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="767" href="foundation.products-binary-relations.html#767" class="Bound">b</a><a id="768" class="Symbol">)</a> <a id="770" class="Symbol">(</a><a id="771" href="foundation.products-binary-relations.html#771" class="Bound">a&#39;</a> <a id="774" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="776" href="foundation.products-binary-relations.html#776" class="Bound">b&#39;</a><a id="778" class="Symbol">)</a> <a id="780" class="Symbol">=</a>
    <a id="786" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="805" class="Symbol">(</a> <a id="807" href="foundation.products-binary-relations.html#604" class="Bound">R</a> <a id="809" href="foundation.products-binary-relations.html#763" class="Bound">a</a> <a id="811" href="foundation.products-binary-relations.html#771" class="Bound">a&#39;</a><a id="813" class="Symbol">)</a>
      <a id="821" class="Symbol">(</a> <a id="823" href="foundation.products-binary-relations.html#643" class="Bound">S</a> <a id="825" href="foundation.products-binary-relations.html#767" class="Bound">b</a> <a id="827" href="foundation.products-binary-relations.html#776" class="Bound">b&#39;</a><a id="829" class="Symbol">)</a>
</pre>