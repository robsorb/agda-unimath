# The category of algebras of theories

<pre class="Agda"><a id="49" class="Symbol">{-#</a> <a id="53" class="Keyword">OPTIONS</a> <a id="61" class="Pragma">--lossy-unification</a> <a id="81" class="Symbol">#-}</a>

<a id="86" class="Keyword">module</a> <a id="93" href="universal-algebra.category-of-algebras-of-theories.html" class="Module">universal-algebra.category-of-algebras-of-theories</a> <a id="144" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="category-theory.isomorphisms-in-large-precategories.html" class="Module">category-theory.isomorphisms-in-large-precategories</a>
<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>

<a id="358" class="Keyword">open</a> <a id="363" class="Keyword">import</a> <a id="370" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="402" class="Keyword">open</a> <a id="407" class="Keyword">import</a> <a id="414" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="430" class="Keyword">open</a> <a id="435" class="Keyword">import</a> <a id="442" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="480" class="Keyword">open</a> <a id="485" class="Keyword">import</a> <a id="492" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="520" class="Keyword">open</a> <a id="525" class="Keyword">import</a> <a id="532" href="foundation-core.equality-dependent-pair-types.html" class="Module">foundation-core.equality-dependent-pair-types</a>
<a id="578" class="Keyword">open</a> <a id="583" class="Keyword">import</a> <a id="590" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="619" class="Keyword">open</a> <a id="624" class="Keyword">import</a> <a id="631" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="662" class="Keyword">open</a> <a id="667" class="Keyword">import</a> <a id="674" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>

<a id="706" class="Keyword">open</a> <a id="711" class="Keyword">import</a> <a id="718" href="universal-algebra.algebraic-theories.html" class="Module">universal-algebra.algebraic-theories</a>
<a id="755" class="Keyword">open</a> <a id="760" class="Keyword">import</a> <a id="767" href="universal-algebra.algebras-of-theories.html" class="Module">universal-algebra.algebras-of-theories</a>
<a id="806" class="Keyword">open</a> <a id="811" class="Keyword">import</a> <a id="818" href="universal-algebra.homomorphisms-of-algebras.html" class="Module">universal-algebra.homomorphisms-of-algebras</a>
<a id="862" class="Keyword">open</a> <a id="867" class="Keyword">import</a> <a id="874" href="universal-algebra.isomorphisms-of-algebras.html" class="Module">universal-algebra.isomorphisms-of-algebras</a>
<a id="917" class="Keyword">open</a> <a id="922" class="Keyword">import</a> <a id="929" href="universal-algebra.models-of-signatures.html" class="Module">universal-algebra.models-of-signatures</a>
<a id="968" class="Keyword">open</a> <a id="973" class="Keyword">import</a> <a id="980" href="universal-algebra.precategory-of-algebras-of-theories.html" class="Module">universal-algebra.precategory-of-algebras-of-theories</a>
<a id="1034" class="Keyword">open</a> <a id="1039" class="Keyword">import</a> <a id="1046" href="universal-algebra.signatures.html" class="Module">universal-algebra.signatures</a>
</pre>
</details>

## Idea

The
[precategory of algebras of a theory](universal-algebra.precategory-of-algebras-of-theories.md)
is a [category](category-theory.large-categories.md).

## Definition

<pre class="Agda"><a id="1279" class="Keyword">module</a> <a id="1286" href="universal-algebra.category-of-algebras-of-theories.html#1286" class="Module">_</a>
  <a id="1290" class="Symbol">{</a><a id="1291" href="universal-algebra.category-of-algebras-of-theories.html#1291" class="Bound">l1</a> <a id="1294" href="universal-algebra.category-of-algebras-of-theories.html#1294" class="Bound">l2</a> <a id="1297" class="Symbol">:</a> <a id="1299" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1304" class="Symbol">}</a> <a id="1306" class="Symbol">(</a><a id="1307" href="universal-algebra.category-of-algebras-of-theories.html#1307" class="Bound">σ</a> <a id="1309" class="Symbol">:</a> <a id="1311" href="universal-algebra.signatures.html#506" class="Function">signature</a> <a id="1321" href="universal-algebra.category-of-algebras-of-theories.html#1291" class="Bound">l1</a><a id="1323" class="Symbol">)</a> <a id="1325" class="Symbol">(</a><a id="1326" href="universal-algebra.category-of-algebras-of-theories.html#1326" class="Bound">T</a> <a id="1328" class="Symbol">:</a> <a id="1330" href="universal-algebra.algebraic-theories.html#730" class="Function">Theory</a> <a id="1337" href="universal-algebra.category-of-algebras-of-theories.html#1307" class="Bound">σ</a> <a id="1339" href="universal-algebra.category-of-algebras-of-theories.html#1294" class="Bound">l2</a><a id="1341" class="Symbol">)</a>
  <a id="1345" class="Keyword">where</a>

  <a id="1354" href="universal-algebra.category-of-algebras-of-theories.html#1354" class="Function">is-large-category-Algebra-Large-Precategory</a> <a id="1398" class="Symbol">:</a>
    <a id="1404" href="category-theory.large-categories.html#1350" class="Function">is-large-category-Large-Precategory</a> <a id="1440" class="Symbol">(</a><a id="1441" href="universal-algebra.precategory-of-algebras-of-theories.html#1092" class="Function">Algebra-Large-Precategory</a> <a id="1467" href="universal-algebra.category-of-algebras-of-theories.html#1307" class="Bound">σ</a> <a id="1469" href="universal-algebra.category-of-algebras-of-theories.html#1326" class="Bound">T</a><a id="1470" class="Symbol">)</a>
  <a id="1474" href="universal-algebra.category-of-algebras-of-theories.html#1354" class="Function">is-large-category-Algebra-Large-Precategory</a> <a id="1518" class="Symbol">=</a> <a id="1520" href="universal-algebra.isomorphisms-of-algebras.html#8907" class="Function">is-equiv-iso-eq-Algebra</a> <a id="1544" href="universal-algebra.category-of-algebras-of-theories.html#1307" class="Bound">σ</a> <a id="1546" href="universal-algebra.category-of-algebras-of-theories.html#1326" class="Bound">T</a>

  <a id="1551" href="universal-algebra.category-of-algebras-of-theories.html#1551" class="Function">Algebra-Large-Category</a> <a id="1574" class="Symbol">:</a>
    <a id="1580" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="1595" class="Symbol">(λ</a> <a id="1598" href="universal-algebra.category-of-algebras-of-theories.html#1598" class="Bound">l</a> <a id="1600" class="Symbol">→</a> <a id="1602" href="universal-algebra.category-of-algebras-of-theories.html#1291" class="Bound">l1</a> <a id="1605" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1607" href="universal-algebra.category-of-algebras-of-theories.html#1294" class="Bound">l2</a> <a id="1610" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1612" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1617" href="universal-algebra.category-of-algebras-of-theories.html#1598" class="Bound">l</a><a id="1618" class="Symbol">)</a> <a id="1620" class="Symbol">(λ</a> <a id="1623" href="universal-algebra.category-of-algebras-of-theories.html#1623" class="Bound">l3</a> <a id="1626" class="Symbol">→</a> <a id="1628" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a> <a id="1632" class="Symbol">(</a><a id="1633" href="universal-algebra.category-of-algebras-of-theories.html#1291" class="Bound">l1</a> <a id="1636" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1638" href="universal-algebra.category-of-algebras-of-theories.html#1623" class="Bound">l3</a><a id="1640" class="Symbol">))</a>
  <a id="1645" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a> <a id="1678" href="universal-algebra.category-of-algebras-of-theories.html#1551" class="Function">Algebra-Large-Category</a> <a id="1701" class="Symbol">=</a>
    <a id="1707" href="universal-algebra.precategory-of-algebras-of-theories.html#1092" class="Function">Algebra-Large-Precategory</a> <a id="1733" href="universal-algebra.category-of-algebras-of-theories.html#1307" class="Bound">σ</a> <a id="1735" href="universal-algebra.category-of-algebras-of-theories.html#1326" class="Bound">T</a>
  <a id="1739" href="category-theory.large-categories.html#1868" class="Field">is-large-category-Large-Category</a> <a id="1772" href="universal-algebra.category-of-algebras-of-theories.html#1551" class="Function">Algebra-Large-Category</a> <a id="1795" class="Symbol">=</a>
    <a id="1801" href="universal-algebra.category-of-algebras-of-theories.html#1354" class="Function">is-large-category-Algebra-Large-Precategory</a>
</pre>