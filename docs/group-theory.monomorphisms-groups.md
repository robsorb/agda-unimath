# Monomorphisms in the category of groups

<pre class="Agda"><a id="52" class="Keyword">module</a> <a id="59" href="group-theory.monomorphisms-groups.html" class="Module">group-theory.monomorphisms-groups</a> <a id="93" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="category-theory.monomorphisms-in-large-precategories.html" class="Module">category-theory.monomorphisms-in-large-precategories</a>

<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="group-theory.isomorphisms-groups.html" class="Module">group-theory.isomorphisms-groups</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="group-theory.precategory-of-groups.html" class="Module">group-theory.precategory-of-groups</a>
</pre>
</details>

## Idea

A [group homomorphism](group-theory.homomorphisms-groups.md) `f : x → y` is a
**monomorphism** if whenever we have two group homomorphisms `g h : w → x` such
that `f ∘ g = f ∘ h`, then in fact `g = h`. The way to state this in Homotopy
Type Theory is to say that postcomposition by `f` is an
[embedding](foundation-core.embeddings.md).

## Definition

<pre class="Agda"><a id="847" class="Keyword">module</a> <a id="854" href="group-theory.monomorphisms-groups.html#854" class="Module">_</a>
  <a id="858" class="Symbol">{</a><a id="859" href="group-theory.monomorphisms-groups.html#859" class="Bound">l1</a> <a id="862" href="group-theory.monomorphisms-groups.html#862" class="Bound">l2</a> <a id="865" class="Symbol">:</a> <a id="867" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="872" class="Symbol">}</a> <a id="874" class="Symbol">(</a><a id="875" href="group-theory.monomorphisms-groups.html#875" class="Bound">l3</a> <a id="878" class="Symbol">:</a> <a id="880" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="885" class="Symbol">)</a> <a id="887" class="Symbol">(</a><a id="888" href="group-theory.monomorphisms-groups.html#888" class="Bound">G</a> <a id="890" class="Symbol">:</a> <a id="892" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="898" href="group-theory.monomorphisms-groups.html#859" class="Bound">l1</a><a id="900" class="Symbol">)</a>
  <a id="904" class="Symbol">(</a><a id="905" href="group-theory.monomorphisms-groups.html#905" class="Bound">H</a> <a id="907" class="Symbol">:</a> <a id="909" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="915" href="group-theory.monomorphisms-groups.html#862" class="Bound">l2</a><a id="917" class="Symbol">)</a> <a id="919" class="Symbol">(</a><a id="920" href="group-theory.monomorphisms-groups.html#920" class="Bound">f</a> <a id="922" class="Symbol">:</a> <a id="924" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="934" href="group-theory.monomorphisms-groups.html#888" class="Bound">G</a> <a id="936" href="group-theory.monomorphisms-groups.html#905" class="Bound">H</a><a id="937" class="Symbol">)</a>
  <a id="941" class="Keyword">where</a>

  <a id="950" href="group-theory.monomorphisms-groups.html#950" class="Function">is-mono-prop-hom-Group</a> <a id="973" class="Symbol">:</a> <a id="975" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="980" class="Symbol">(</a><a id="981" href="group-theory.monomorphisms-groups.html#859" class="Bound">l1</a> <a id="984" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="986" href="group-theory.monomorphisms-groups.html#862" class="Bound">l2</a> <a id="989" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="991" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="996" href="group-theory.monomorphisms-groups.html#875" class="Bound">l3</a><a id="998" class="Symbol">)</a>
  <a id="1002" href="group-theory.monomorphisms-groups.html#950" class="Function">is-mono-prop-hom-Group</a> <a id="1025" class="Symbol">=</a>
    <a id="1031" href="category-theory.monomorphisms-in-large-precategories.html#945" class="Function">is-mono-prop-Large-Precategory</a> <a id="1062" href="group-theory.precategory-of-groups.html#743" class="Function">Group-Large-Precategory</a> <a id="1086" href="group-theory.monomorphisms-groups.html#875" class="Bound">l3</a> <a id="1089" href="group-theory.monomorphisms-groups.html#888" class="Bound">G</a> <a id="1091" href="group-theory.monomorphisms-groups.html#905" class="Bound">H</a> <a id="1093" href="group-theory.monomorphisms-groups.html#920" class="Bound">f</a>

  <a id="1098" href="group-theory.monomorphisms-groups.html#1098" class="Function">is-mono-hom-Group</a> <a id="1116" class="Symbol">:</a> <a id="1118" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1121" class="Symbol">(</a><a id="1122" href="group-theory.monomorphisms-groups.html#859" class="Bound">l1</a> <a id="1125" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1127" href="group-theory.monomorphisms-groups.html#862" class="Bound">l2</a> <a id="1130" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1132" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1137" href="group-theory.monomorphisms-groups.html#875" class="Bound">l3</a><a id="1139" class="Symbol">)</a>
  <a id="1143" href="group-theory.monomorphisms-groups.html#1098" class="Function">is-mono-hom-Group</a> <a id="1161" class="Symbol">=</a> <a id="1163" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1173" href="group-theory.monomorphisms-groups.html#950" class="Function">is-mono-prop-hom-Group</a>

  <a id="1199" href="group-theory.monomorphisms-groups.html#1199" class="Function">is-prop-is-mono-hom-Group</a> <a id="1225" class="Symbol">:</a> <a id="1227" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1235" href="group-theory.monomorphisms-groups.html#1098" class="Function">is-mono-hom-Group</a>
  <a id="1255" href="group-theory.monomorphisms-groups.html#1199" class="Function">is-prop-is-mono-hom-Group</a> <a id="1281" class="Symbol">=</a> <a id="1283" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1301" href="group-theory.monomorphisms-groups.html#950" class="Function">is-mono-prop-hom-Group</a>
</pre>
## Properties

### Isomorphisms are monomorphisms

<pre class="Agda"><a id="1388" class="Keyword">module</a> <a id="1395" href="group-theory.monomorphisms-groups.html#1395" class="Module">_</a>
  <a id="1399" class="Symbol">{</a><a id="1400" href="group-theory.monomorphisms-groups.html#1400" class="Bound">l1</a> <a id="1403" href="group-theory.monomorphisms-groups.html#1403" class="Bound">l2</a> <a id="1406" class="Symbol">:</a> <a id="1408" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1413" class="Symbol">}</a> <a id="1415" class="Symbol">(</a><a id="1416" href="group-theory.monomorphisms-groups.html#1416" class="Bound">l3</a> <a id="1419" class="Symbol">:</a> <a id="1421" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1426" class="Symbol">)</a> <a id="1428" class="Symbol">(</a><a id="1429" href="group-theory.monomorphisms-groups.html#1429" class="Bound">G</a> <a id="1431" class="Symbol">:</a> <a id="1433" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1439" href="group-theory.monomorphisms-groups.html#1400" class="Bound">l1</a><a id="1441" class="Symbol">)</a>
  <a id="1445" class="Symbol">(</a><a id="1446" href="group-theory.monomorphisms-groups.html#1446" class="Bound">H</a> <a id="1448" class="Symbol">:</a> <a id="1450" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1456" href="group-theory.monomorphisms-groups.html#1403" class="Bound">l2</a><a id="1458" class="Symbol">)</a> <a id="1460" class="Symbol">(</a><a id="1461" href="group-theory.monomorphisms-groups.html#1461" class="Bound">f</a> <a id="1463" class="Symbol">:</a> <a id="1465" href="group-theory.isomorphisms-groups.html#3368" class="Function">iso-Group</a> <a id="1475" href="group-theory.monomorphisms-groups.html#1429" class="Bound">G</a> <a id="1477" href="group-theory.monomorphisms-groups.html#1446" class="Bound">H</a><a id="1478" class="Symbol">)</a>
  <a id="1482" class="Keyword">where</a>

  <a id="1491" href="group-theory.monomorphisms-groups.html#1491" class="Function">is-mono-iso-Group</a> <a id="1509" class="Symbol">:</a> <a id="1511" href="group-theory.monomorphisms-groups.html#1098" class="Function">is-mono-hom-Group</a> <a id="1529" href="group-theory.monomorphisms-groups.html#1416" class="Bound">l3</a> <a id="1532" href="group-theory.monomorphisms-groups.html#1429" class="Bound">G</a> <a id="1534" href="group-theory.monomorphisms-groups.html#1446" class="Bound">H</a> <a id="1536" class="Symbol">(</a><a id="1537" href="group-theory.isomorphisms-groups.html#3464" class="Function">hom-iso-Group</a> <a id="1551" href="group-theory.monomorphisms-groups.html#1429" class="Bound">G</a> <a id="1553" href="group-theory.monomorphisms-groups.html#1446" class="Bound">H</a> <a id="1555" href="group-theory.monomorphisms-groups.html#1461" class="Bound">f</a><a id="1556" class="Symbol">)</a>
  <a id="1560" href="group-theory.monomorphisms-groups.html#1491" class="Function">is-mono-iso-Group</a> <a id="1578" class="Symbol">=</a>
    <a id="1584" href="category-theory.monomorphisms-in-large-precategories.html#1753" class="Function">is-mono-iso-Large-Precategory</a> <a id="1614" href="group-theory.precategory-of-groups.html#743" class="Function">Group-Large-Precategory</a> <a id="1638" href="group-theory.monomorphisms-groups.html#1416" class="Bound">l3</a> <a id="1641" href="group-theory.monomorphisms-groups.html#1429" class="Bound">G</a> <a id="1643" href="group-theory.monomorphisms-groups.html#1446" class="Bound">H</a> <a id="1645" href="group-theory.monomorphisms-groups.html#1461" class="Bound">f</a>
</pre>