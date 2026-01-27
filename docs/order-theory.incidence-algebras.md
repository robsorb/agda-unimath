# Incidence algebras

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="order-theory.incidence-algebras.html" class="Module">order-theory.incidence-algebras</a> <a id="70" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="126" class="Keyword">open</a> <a id="131" class="Keyword">import</a> <a id="138" href="commutative-algebra.commutative-rings.html" class="Module">commutative-algebra.commutative-rings</a>

<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>

<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="order-theory.interval-subposets.html" class="Module">order-theory.interval-subposets</a>
<a id="397" class="Keyword">open</a> <a id="402" class="Keyword">import</a> <a id="409" href="order-theory.locally-finite-posets.html" class="Module">order-theory.locally-finite-posets</a>
<a id="444" class="Keyword">open</a> <a id="449" class="Keyword">import</a> <a id="456" href="order-theory.posets.html" class="Module">order-theory.posets</a>
</pre>
</details>

## Idea

For a [locally finite poset](order-theory.locally-finite-posets.md) `P` and
[commutative ring](commutative-algebra.commutative-rings.md) `R`, there is a
canonical `R`-associative algebra whose underlying `R`-module are the set-maps
from the nonempty [intervals](order-theory.interval-subposets.md) of `P` to `R`
(which we constructify as the inhabited intervals), and whose multiplication is
given by a "convolution" of maps. This is the **incidence algebra** of `P` over
`R`.

## Definition

<pre class="Agda"><a id="1003" class="Keyword">module</a> <a id="1010" href="order-theory.incidence-algebras.html#1010" class="Module">_</a>
  <a id="1014" class="Symbol">{</a><a id="1015" href="order-theory.incidence-algebras.html#1015" class="Bound">l1</a> <a id="1018" href="order-theory.incidence-algebras.html#1018" class="Bound">l2</a> <a id="1021" href="order-theory.incidence-algebras.html#1021" class="Bound">l3</a> <a id="1024" class="Symbol">:</a> <a id="1026" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1031" class="Symbol">}</a> <a id="1033" class="Symbol">(</a><a id="1034" href="order-theory.incidence-algebras.html#1034" class="Bound">P</a> <a id="1036" class="Symbol">:</a> <a id="1038" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1044" href="order-theory.incidence-algebras.html#1015" class="Bound">l1</a> <a id="1047" href="order-theory.incidence-algebras.html#1018" class="Bound">l2</a><a id="1049" class="Symbol">)</a> <a id="1051" class="Symbol">(</a><a id="1052" href="order-theory.incidence-algebras.html#1052" class="Bound">loc-fin</a> <a id="1060" class="Symbol">:</a> <a id="1062" href="order-theory.locally-finite-posets.html#879" class="Function">is-locally-finite-Poset</a> <a id="1086" href="order-theory.incidence-algebras.html#1034" class="Bound">P</a><a id="1087" class="Symbol">)</a>
  <a id="1091" class="Symbol">(</a><a id="1092" href="order-theory.incidence-algebras.html#1092" class="Bound">x</a> <a id="1094" href="order-theory.incidence-algebras.html#1094" class="Bound">y</a> <a id="1096" class="Symbol">:</a> <a id="1098" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1109" href="order-theory.incidence-algebras.html#1034" class="Bound">P</a><a id="1110" class="Symbol">)</a> <a id="1112" class="Symbol">(</a><a id="1113" href="order-theory.incidence-algebras.html#1113" class="Bound">R</a> <a id="1115" class="Symbol">:</a> <a id="1117" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="1134" href="order-theory.incidence-algebras.html#1021" class="Bound">l3</a><a id="1136" class="Symbol">)</a>
  <a id="1140" class="Keyword">where</a>

  <a id="1149" href="order-theory.incidence-algebras.html#1149" class="Function">interval-map</a> <a id="1162" class="Symbol">:</a> <a id="1164" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1167" class="Symbol">(</a><a id="1168" href="order-theory.incidence-algebras.html#1015" class="Bound">l1</a> <a id="1171" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1173" href="order-theory.incidence-algebras.html#1018" class="Bound">l2</a> <a id="1176" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1178" href="order-theory.incidence-algebras.html#1021" class="Bound">l3</a><a id="1180" class="Symbol">)</a>
  <a id="1184" href="order-theory.incidence-algebras.html#1149" class="Function">interval-map</a> <a id="1197" class="Symbol">=</a> <a id="1199" href="order-theory.interval-subposets.html#1343" class="Function">inhabited-interval</a> <a id="1218" href="order-theory.incidence-algebras.html#1034" class="Bound">P</a> <a id="1220" class="Symbol">→</a> <a id="1222" href="commutative-algebra.commutative-rings.html#2498" class="Function">type-Commutative-Ring</a> <a id="1244" href="order-theory.incidence-algebras.html#1113" class="Bound">R</a>
</pre>
WIP: complete this definition after _R-modules_ have been defined. Defining
convolution of maps would be aided as well with a lemma on 'unordered' addition
in abelian groups over finite sets.
