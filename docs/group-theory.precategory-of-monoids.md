# The precategory of monoids

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="group-theory.precategory-of-monoids.html" class="Module">group-theory.precategory-of-monoids</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="category-theory.large-subprecategories.html" class="Module">category-theory.large-subprecategories</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="group-theory.homomorphisms-monoids.html" class="Module">group-theory.homomorphisms-monoids</a>
<a id="411" class="Keyword">open</a> <a id="416" class="Keyword">import</a> <a id="423" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
<a id="444" class="Keyword">open</a> <a id="449" class="Keyword">import</a> <a id="456" href="group-theory.precategory-of-semigroups.html" class="Module">group-theory.precategory-of-semigroups</a>
</pre>
</details>

## Idea

The {{#concept "precategory of monoids" Agda=Monoid-Large-Precategory}} consists
of [monoids](group-theory.monoids.md) and
[homomorphisms of monoids](group-theory.homomorphisms-monoids.md).

## Definitions

### The precategory of monoids as a subprecategory of the precategory of semigroups

<pre class="Agda"><a id="Monoid-Large-Subprecategory"></a><a id="821" href="group-theory.precategory-of-monoids.html#821" class="Function">Monoid-Large-Subprecategory</a> <a id="849" class="Symbol">:</a>
  <a id="853" href="category-theory.large-subprecategories.html#1016" class="Record">Large-Subprecategory</a> <a id="874" class="Symbol">(λ</a> <a id="877" href="group-theory.precategory-of-monoids.html#877" class="Bound">l</a> <a id="879" class="Symbol">→</a> <a id="881" href="group-theory.precategory-of-monoids.html#877" class="Bound">l</a><a id="882" class="Symbol">)</a> <a id="884" class="Symbol">(λ</a> <a id="887" href="group-theory.precategory-of-monoids.html#887" class="Bound">l1</a> <a id="890" href="group-theory.precategory-of-monoids.html#890" class="Bound">l2</a> <a id="893" class="Symbol">→</a> <a id="895" href="group-theory.precategory-of-monoids.html#890" class="Bound">l2</a><a id="897" class="Symbol">)</a> <a id="899" href="group-theory.precategory-of-semigroups.html#469" class="Function">Semigroup-Large-Precategory</a>
<a id="927" href="group-theory.precategory-of-monoids.html#821" class="Function">Monoid-Large-Subprecategory</a> <a id="955" class="Symbol">=</a>
  <a id="959" class="Symbol">λ</a> <a id="961" class="Keyword">where</a>
    <a id="971" class="Symbol">.</a><a id="972" href="category-theory.large-subprecategories.html#1199" class="Field">subtype-obj-Large-Subprecategory</a> <a id="1005" href="group-theory.precategory-of-monoids.html#1005" class="Bound">l</a> <a id="1007" class="Symbol">→</a>
      <a id="1015" href="group-theory.monoids.html#4036" class="Function">is-unital-prop-Semigroup</a> <a id="1040" class="Symbol">{</a><a id="1041" href="group-theory.precategory-of-monoids.html#1005" class="Bound">l</a><a id="1042" class="Symbol">}</a>
    <a id="1048" class="Symbol">.</a><a id="1049" href="category-theory.large-subprecategories.html#1638" class="Field">subtype-hom-Large-Subprecategory</a> <a id="1082" href="group-theory.precategory-of-monoids.html#1082" class="Bound">G</a> <a id="1084" href="group-theory.precategory-of-monoids.html#1084" class="Bound">H</a> <a id="1086" href="group-theory.precategory-of-monoids.html#1086" class="Bound">is-unital-G</a> <a id="1098" href="group-theory.precategory-of-monoids.html#1098" class="Bound">is-unital-H</a> <a id="1110" class="Symbol">→</a>
      <a id="1118" href="group-theory.homomorphisms-monoids.html#1942" class="Function">preserves-unit-hom-prop-Semigroup</a> <a id="1152" class="Symbol">(</a><a id="1153" href="group-theory.precategory-of-monoids.html#1082" class="Bound">G</a> <a id="1155" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1157" href="group-theory.precategory-of-monoids.html#1086" class="Bound">is-unital-G</a><a id="1168" class="Symbol">)</a> <a id="1170" class="Symbol">(</a><a id="1171" href="group-theory.precategory-of-monoids.html#1084" class="Bound">H</a> <a id="1173" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1175" href="group-theory.precategory-of-monoids.html#1098" class="Bound">is-unital-H</a><a id="1186" class="Symbol">)</a>
    <a id="1192" class="Symbol">.</a><a id="1193" href="category-theory.large-subprecategories.html#2327" class="Field">contains-id-Large-Subprecategory</a> <a id="1226" href="group-theory.precategory-of-monoids.html#1226" class="Bound">G</a> <a id="1228" href="group-theory.precategory-of-monoids.html#1228" class="Bound">is-unital-G</a> <a id="1240" class="Symbol">→</a>
      <a id="1248" href="group-theory.homomorphisms-monoids.html#3297" class="Function">preserves-unit-id-hom-Monoid</a> <a id="1277" class="Symbol">(</a><a id="1278" href="group-theory.precategory-of-monoids.html#1226" class="Bound">G</a> <a id="1280" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1282" href="group-theory.precategory-of-monoids.html#1228" class="Bound">is-unital-G</a><a id="1293" class="Symbol">)</a>
    <a id="1299" class="Symbol">.</a><a id="1300" href="category-theory.large-subprecategories.html#2546" class="Field">is-closed-under-composition-Large-Subprecategory</a>
      <a id="1355" href="group-theory.precategory-of-monoids.html#1355" class="Bound">G</a> <a id="1357" href="group-theory.precategory-of-monoids.html#1357" class="Bound">H</a> <a id="1359" href="group-theory.precategory-of-monoids.html#1359" class="Bound">K</a> <a id="1361" href="group-theory.precategory-of-monoids.html#1361" class="Bound">g</a> <a id="1363" href="group-theory.precategory-of-monoids.html#1363" class="Bound">f</a> <a id="1365" href="group-theory.precategory-of-monoids.html#1365" class="Bound">is-unital-G</a> <a id="1377" href="group-theory.precategory-of-monoids.html#1377" class="Bound">is-unital-H</a> <a id="1389" href="group-theory.precategory-of-monoids.html#1389" class="Bound">is-unital-K</a> <a id="1401" href="group-theory.precategory-of-monoids.html#1401" class="Bound">unit-g</a> <a id="1408" href="group-theory.precategory-of-monoids.html#1408" class="Bound">unit-f</a> <a id="1415" class="Symbol">→</a>
      <a id="1423" href="group-theory.homomorphisms-monoids.html#3800" class="Function">preserves-unit-comp-hom-Monoid</a>
        <a id="1462" class="Symbol">(</a> <a id="1464" href="group-theory.precategory-of-monoids.html#1355" class="Bound">G</a> <a id="1466" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1468" href="group-theory.precategory-of-monoids.html#1365" class="Bound">is-unital-G</a><a id="1479" class="Symbol">)</a>
        <a id="1489" class="Symbol">(</a> <a id="1491" href="group-theory.precategory-of-monoids.html#1357" class="Bound">H</a> <a id="1493" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1495" href="group-theory.precategory-of-monoids.html#1377" class="Bound">is-unital-H</a><a id="1506" class="Symbol">)</a>
        <a id="1516" class="Symbol">(</a> <a id="1518" href="group-theory.precategory-of-monoids.html#1359" class="Bound">K</a> <a id="1520" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1522" href="group-theory.precategory-of-monoids.html#1389" class="Bound">is-unital-K</a><a id="1533" class="Symbol">)</a>
        <a id="1543" class="Symbol">(</a> <a id="1545" href="group-theory.precategory-of-monoids.html#1361" class="Bound">g</a> <a id="1547" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1549" href="group-theory.precategory-of-monoids.html#1401" class="Bound">unit-g</a><a id="1555" class="Symbol">)</a>
        <a id="1565" class="Symbol">(</a> <a id="1567" href="group-theory.precategory-of-monoids.html#1363" class="Bound">f</a> <a id="1569" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1571" href="group-theory.precategory-of-monoids.html#1408" class="Bound">unit-f</a><a id="1577" class="Symbol">)</a>
</pre>
### The large precategory of monoids

<pre class="Agda"><a id="Monoid-Large-Precategory"></a><a id="1630" href="group-theory.precategory-of-monoids.html#1630" class="Function">Monoid-Large-Precategory</a> <a id="1655" class="Symbol">:</a> <a id="1657" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="1675" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1680" class="Symbol">(</a><a id="1681" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1684" class="Symbol">)</a>
<a id="1686" href="group-theory.precategory-of-monoids.html#1630" class="Function">Monoid-Large-Precategory</a> <a id="1711" class="Symbol">=</a>
  <a id="1715" href="category-theory.large-subprecategories.html#7203" class="Function">large-precategory-Large-Subprecategory</a> <a id="1754" href="group-theory.precategory-of-monoids.html#821" class="Function">Monoid-Large-Subprecategory</a>
</pre>
### The precategory of small monoids

<pre class="Agda"><a id="Monoid-Precategory"></a><a id="1833" href="group-theory.precategory-of-monoids.html#1833" class="Function">Monoid-Precategory</a> <a id="1852" class="Symbol">:</a> <a id="1854" class="Symbol">(</a><a id="1855" href="group-theory.precategory-of-monoids.html#1855" class="Bound">l</a> <a id="1857" class="Symbol">:</a> <a id="1859" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1864" class="Symbol">)</a> <a id="1866" class="Symbol">→</a> <a id="1868" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1880" class="Symbol">(</a><a id="1881" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1886" href="group-theory.precategory-of-monoids.html#1855" class="Bound">l</a><a id="1887" class="Symbol">)</a> <a id="1889" href="group-theory.precategory-of-monoids.html#1855" class="Bound">l</a>
<a id="1891" href="group-theory.precategory-of-monoids.html#1833" class="Function">Monoid-Precategory</a> <a id="1910" class="Symbol">=</a> <a id="1912" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1942" href="group-theory.precategory-of-monoids.html#1630" class="Function">Monoid-Large-Precategory</a>
</pre>