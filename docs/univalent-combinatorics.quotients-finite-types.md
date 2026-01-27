# Quotients of finite types

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="univalent-combinatorics.quotients-finite-types.html" class="Module">univalent-combinatorics.quotients-finite-types</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="univalent-combinatorics.decidable-equivalence-relations.html" class="Module">univalent-combinatorics.decidable-equivalence-relations</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="univalent-combinatorics.decidable-subtypes.html" class="Module">univalent-combinatorics.decidable-subtypes</a>
<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="404" class="Keyword">open</a> <a id="409" class="Keyword">import</a> <a id="416" href="univalent-combinatorics.image-of-maps.html" class="Module">univalent-combinatorics.image-of-maps</a>
</pre>
</details>

## Idea

The quotient of a [finite type](univalent-combinatorics.finite-types.md) by a
[decidable equivalence relation](foundation.decidable-equivalence-relations.md)
is again a finite type. In this file we set up some infrastructure for such
quotients.

## Definition

<pre class="Agda"><a id="749" class="Keyword">module</a> <a id="756" href="univalent-combinatorics.quotients-finite-types.html#756" class="Module">_</a>
  <a id="760" class="Symbol">{</a><a id="761" href="univalent-combinatorics.quotients-finite-types.html#761" class="Bound">l1</a> <a id="764" href="univalent-combinatorics.quotients-finite-types.html#764" class="Bound">l2</a> <a id="767" class="Symbol">:</a> <a id="769" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="774" class="Symbol">}</a> <a id="776" class="Symbol">(</a><a id="777" href="univalent-combinatorics.quotients-finite-types.html#777" class="Bound">X</a> <a id="779" class="Symbol">:</a> <a id="781" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="793" href="univalent-combinatorics.quotients-finite-types.html#761" class="Bound">l1</a><a id="795" class="Symbol">)</a>
  <a id="799" class="Symbol">(</a><a id="800" href="univalent-combinatorics.quotients-finite-types.html#800" class="Bound">R</a> <a id="802" class="Symbol">:</a> <a id="804" href="univalent-combinatorics.decidable-equivalence-relations.html#1795" class="Function">type-Decidable-Equivalence-Relation-Finite-Type</a> <a id="852" href="univalent-combinatorics.quotients-finite-types.html#764" class="Bound">l2</a> <a id="855" href="univalent-combinatorics.quotients-finite-types.html#777" class="Bound">X</a><a id="856" class="Symbol">)</a>
  <a id="860" class="Keyword">where</a>

  <a id="869" href="univalent-combinatorics.quotients-finite-types.html#869" class="Function">equivalence-class-Decidable-Equivalence-Relation-Finite-Type</a> <a id="930" class="Symbol">:</a>
    <a id="936" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="939" class="Symbol">(</a><a id="940" href="univalent-combinatorics.quotients-finite-types.html#761" class="Bound">l1</a> <a id="943" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="945" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="950" href="univalent-combinatorics.quotients-finite-types.html#764" class="Bound">l2</a><a id="952" class="Symbol">)</a>
  <a id="956" href="univalent-combinatorics.quotients-finite-types.html#869" class="Function">equivalence-class-Decidable-Equivalence-Relation-Finite-Type</a> <a id="1017" class="Symbol">=</a>
    <a id="1023" href="foundation.images.html#1761" class="Function">im</a> <a id="1026" class="Symbol">(</a><a id="1027" href="univalent-combinatorics.decidable-equivalence-relations.html#2147" class="Function">decidable-relation-Decidable-Equivalence-Relation-Finite-Type</a> <a id="1089" href="univalent-combinatorics.quotients-finite-types.html#777" class="Bound">X</a> <a id="1091" href="univalent-combinatorics.quotients-finite-types.html#800" class="Bound">R</a><a id="1092" class="Symbol">)</a>

  <a id="1097" href="univalent-combinatorics.quotients-finite-types.html#1097" class="Function">is-finite-equivalence-class-Decidable-Equivalence-Relation-Finite-Type&#39;</a> <a id="1169" class="Symbol">:</a>
    <a id="1175" href="univalent-combinatorics.finite-types.html#2289" class="Function">is-finite</a> <a id="1185" href="univalent-combinatorics.quotients-finite-types.html#869" class="Function">equivalence-class-Decidable-Equivalence-Relation-Finite-Type</a>
  <a id="1248" href="univalent-combinatorics.quotients-finite-types.html#1097" class="Function">is-finite-equivalence-class-Decidable-Equivalence-Relation-Finite-Type&#39;</a> <a id="1320" class="Symbol">=</a>
    <a id="1326" href="univalent-combinatorics.image-of-maps.html#1082" class="Function">is-finite-im</a>
      <a id="1345" class="Symbol">(</a> <a id="1347" href="univalent-combinatorics.finite-types.html#2854" class="Function">is-finite-type-Finite-Type</a> <a id="1374" href="univalent-combinatorics.quotients-finite-types.html#777" class="Bound">X</a><a id="1375" class="Symbol">)</a>
      <a id="1383" class="Symbol">(</a> <a id="1385" href="univalent-combinatorics.decidable-subtypes.html#4275" class="Function">has-decidable-equality-Subset-Finite-Type</a> <a id="1427" href="univalent-combinatorics.quotients-finite-types.html#777" class="Bound">X</a><a id="1428" class="Symbol">)</a>

  <a id="1433" href="univalent-combinatorics.quotients-finite-types.html#1433" class="Function">quotient-Finite-Type</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1468" class="Symbol">(</a><a id="1469" href="univalent-combinatorics.quotients-finite-types.html#761" class="Bound">l1</a> <a id="1472" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1474" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1479" href="univalent-combinatorics.quotients-finite-types.html#764" class="Bound">l2</a><a id="1481" class="Symbol">)</a>
  <a id="1485" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1489" href="univalent-combinatorics.quotients-finite-types.html#1433" class="Function">quotient-Finite-Type</a> <a id="1510" class="Symbol">=</a>
    <a id="1516" href="univalent-combinatorics.quotients-finite-types.html#869" class="Function">equivalence-class-Decidable-Equivalence-Relation-Finite-Type</a>
  <a id="1579" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1583" href="univalent-combinatorics.quotients-finite-types.html#1433" class="Function">quotient-Finite-Type</a> <a id="1604" class="Symbol">=</a>
    <a id="1610" href="univalent-combinatorics.quotients-finite-types.html#1097" class="Function">is-finite-equivalence-class-Decidable-Equivalence-Relation-Finite-Type&#39;</a>
</pre>