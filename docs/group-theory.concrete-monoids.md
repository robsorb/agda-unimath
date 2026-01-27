# Concrete monoids

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="group-theory.concrete-monoids.html" class="Module">group-theory.concrete-monoids</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="category-theory.categories.html" class="Module">category-theory.categories</a>

<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.0-connected-types.html" class="Module">foundation.0-connected-types</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="334" class="Keyword">open</a> <a id="339" class="Keyword">import</a> <a id="346" href="group-theory.cores-monoids.html" class="Module">group-theory.cores-monoids</a>
<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
<a id="406" class="Keyword">open</a> <a id="411" class="Keyword">import</a> <a id="418" href="group-theory.torsors.html" class="Module">group-theory.torsors</a>
</pre>
</details>

## Idea

A **concrete monoid**, or **univalent monoid**, is the homotopy type theoretic
analog of [monoids](group-theory.monoids.md). We define it as a
[category](category-theory.categories.md) whose type of objects is
[pointed](structured-types.pointed-types.md) and
[connected](foundation.0-connected-types.md).

## Definition

<pre class="Agda"><a id="is-concrete-monoid-Category"></a><a id="794" href="group-theory.concrete-monoids.html#794" class="Function">is-concrete-monoid-Category</a> <a id="822" class="Symbol">:</a> <a id="824" class="Symbol">{</a><a id="825" href="group-theory.concrete-monoids.html#825" class="Bound">l1</a> <a id="828" href="group-theory.concrete-monoids.html#828" class="Bound">l2</a> <a id="831" class="Symbol">:</a> <a id="833" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="838" class="Symbol">}</a> <a id="840" class="Symbol">→</a> <a id="842" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="851" href="group-theory.concrete-monoids.html#825" class="Bound">l1</a> <a id="854" href="group-theory.concrete-monoids.html#828" class="Bound">l2</a> <a id="857" class="Symbol">→</a> <a id="859" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="862" href="group-theory.concrete-monoids.html#825" class="Bound">l1</a>
<a id="865" href="group-theory.concrete-monoids.html#794" class="Function">is-concrete-monoid-Category</a> <a id="893" href="group-theory.concrete-monoids.html#893" class="Bound">C</a> <a id="895" class="Symbol">=</a> <a id="897" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="910" href="group-theory.concrete-monoids.html#893" class="Bound">C</a> <a id="912" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="914" href="foundation.0-connected-types.html#1548" class="Function">is-0-connected</a> <a id="929" class="Symbol">(</a><a id="930" href="category-theory.categories.html#2542" class="Function">obj-Category</a> <a id="943" href="group-theory.concrete-monoids.html#893" class="Bound">C</a><a id="944" class="Symbol">)</a>

<a id="Concrete-Monoid"></a><a id="947" href="group-theory.concrete-monoids.html#947" class="Function">Concrete-Monoid</a> <a id="963" class="Symbol">:</a> <a id="965" class="Symbol">(</a><a id="966" href="group-theory.concrete-monoids.html#966" class="Bound">l1</a> <a id="969" href="group-theory.concrete-monoids.html#969" class="Bound">l2</a> <a id="972" class="Symbol">:</a> <a id="974" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="979" class="Symbol">)</a> <a id="981" class="Symbol">→</a> <a id="983" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="986" class="Symbol">(</a><a id="987" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="992" href="group-theory.concrete-monoids.html#966" class="Bound">l1</a> <a id="995" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="997" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1002" href="group-theory.concrete-monoids.html#969" class="Bound">l2</a><a id="1004" class="Symbol">)</a>
<a id="1006" href="group-theory.concrete-monoids.html#947" class="Function">Concrete-Monoid</a> <a id="1022" href="group-theory.concrete-monoids.html#1022" class="Bound">l1</a> <a id="1025" href="group-theory.concrete-monoids.html#1025" class="Bound">l2</a> <a id="1028" class="Symbol">=</a> <a id="1030" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1032" class="Symbol">(</a><a id="1033" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1042" href="group-theory.concrete-monoids.html#1022" class="Bound">l1</a> <a id="1045" href="group-theory.concrete-monoids.html#1025" class="Bound">l2</a><a id="1047" class="Symbol">)</a> <a id="1049" class="Symbol">(</a><a id="1050" href="group-theory.concrete-monoids.html#794" class="Function">is-concrete-monoid-Category</a><a id="1077" class="Symbol">)</a>

<a id="1080" class="Keyword">module</a> <a id="1087" href="group-theory.concrete-monoids.html#1087" class="Module">_</a>
  <a id="1091" class="Symbol">{</a><a id="1092" href="group-theory.concrete-monoids.html#1092" class="Bound">l1</a> <a id="1095" href="group-theory.concrete-monoids.html#1095" class="Bound">l2</a> <a id="1098" class="Symbol">:</a> <a id="1100" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1105" class="Symbol">}</a> <a id="1107" class="Symbol">(</a><a id="1108" href="group-theory.concrete-monoids.html#1108" class="Bound">M</a> <a id="1110" class="Symbol">:</a> <a id="1112" href="group-theory.concrete-monoids.html#947" class="Function">Concrete-Monoid</a> <a id="1128" href="group-theory.concrete-monoids.html#1092" class="Bound">l1</a> <a id="1131" href="group-theory.concrete-monoids.html#1095" class="Bound">l2</a><a id="1133" class="Symbol">)</a>
  <a id="1137" class="Keyword">where</a>

  <a id="1146" href="group-theory.concrete-monoids.html#1146" class="Function">category-Concrete-Monoid</a> <a id="1171" class="Symbol">:</a> <a id="1173" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="1182" href="group-theory.concrete-monoids.html#1092" class="Bound">l1</a> <a id="1185" href="group-theory.concrete-monoids.html#1095" class="Bound">l2</a>
  <a id="1190" href="group-theory.concrete-monoids.html#1146" class="Function">category-Concrete-Monoid</a> <a id="1215" class="Symbol">=</a> <a id="1217" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1221" href="group-theory.concrete-monoids.html#1108" class="Bound">M</a>

  <a id="1226" href="group-theory.concrete-monoids.html#1226" class="Function">is-concrete-monoid-category-Concrete-Monoid</a> <a id="1270" class="Symbol">:</a>
    <a id="1276" href="group-theory.concrete-monoids.html#794" class="Function">is-concrete-monoid-Category</a> <a id="1304" href="group-theory.concrete-monoids.html#1146" class="Function">category-Concrete-Monoid</a>
  <a id="1331" href="group-theory.concrete-monoids.html#1226" class="Function">is-concrete-monoid-category-Concrete-Monoid</a> <a id="1375" class="Symbol">=</a> <a id="1377" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1381" href="group-theory.concrete-monoids.html#1108" class="Bound">M</a>
</pre>
## Properties

### Concrete monoids from monoids

Given a monoid, we can define its associated concrete monoid. The type of
objects is the [classifying type](group-theory.concrete-groups.md) of the
[core](group-theory.cores-monoids.md) of the monoid. Moreover, we must take care
in how we define the family of homomorphisms. They cannot simply be the constant
family, as [transporting along](foundation.transport-along-identifications.md)
an [invertible element](group-theory.invertible-elements-monoids.md) should
correspond to multiplying by the element in the family.

<pre class="Agda"><a id="1968" class="Keyword">module</a> <a id="1975" href="group-theory.concrete-monoids.html#1975" class="Module">_</a>
  <a id="1979" class="Symbol">{</a><a id="1980" href="group-theory.concrete-monoids.html#1980" class="Bound">l</a> <a id="1982" class="Symbol">:</a> <a id="1984" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1989" class="Symbol">}</a> <a id="1991" class="Symbol">(</a><a id="1992" href="group-theory.concrete-monoids.html#1992" class="Bound">M</a> <a id="1994" class="Symbol">:</a> <a id="1996" href="group-theory.monoids.html#835" class="Function">Monoid</a> <a id="2003" href="group-theory.concrete-monoids.html#1980" class="Bound">l</a><a id="2004" class="Symbol">)</a>
  <a id="2008" class="Keyword">where</a>

  <a id="2017" href="group-theory.concrete-monoids.html#2017" class="Function">obj-concrete-monoid-Monoid</a> <a id="2044" class="Symbol">:</a> <a id="2046" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2049" class="Symbol">(</a><a id="2050" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2055" href="group-theory.concrete-monoids.html#1980" class="Bound">l</a><a id="2056" class="Symbol">)</a>
  <a id="2060" href="group-theory.concrete-monoids.html#2017" class="Function">obj-concrete-monoid-Monoid</a> <a id="2087" class="Symbol">=</a> <a id="2089" href="group-theory.torsors.html#18937" class="Function">classifying-type-Group</a> <a id="2112" class="Symbol">(</a><a id="2113" href="group-theory.cores-monoids.html#4162" class="Function">core-Monoid</a> <a id="2125" href="group-theory.concrete-monoids.html#1992" class="Bound">M</a><a id="2126" class="Symbol">)</a>
</pre>
The remainder of the construction remains to be written down. We note that this
is precisely the Rezk completion of the one object precategory associated to a
monoid.
