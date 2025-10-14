# Rigid objects in a precategory

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="category-theory.rigid-objects-precategories.html" class="Module">category-theory.rigid-objects-precategories</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="category-theory.isomorphisms-in-precategories.html" class="Module">category-theory.isomorphisms-in-precategories</a>
<a id="208" class="Keyword">open</a> <a id="213" class="Keyword">import</a> <a id="220" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A **rigid object** in a [precategory](category-theory.precategories.md) is an
object whose [automorphism group](group-theory.automorphism-groups.md) is
[trivial](group-theory.trivial-groups.md).

## Definitions

### The predicate of being rigid

<pre class="Agda"><a id="692" class="Keyword">module</a> <a id="699" href="category-theory.rigid-objects-precategories.html#699" class="Module">_</a>
  <a id="703" class="Symbol">{</a><a id="704" href="category-theory.rigid-objects-precategories.html#704" class="Bound">l1</a> <a id="707" href="category-theory.rigid-objects-precategories.html#707" class="Bound">l2</a> <a id="710" class="Symbol">:</a> <a id="712" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="717" class="Symbol">}</a> <a id="719" class="Symbol">(</a><a id="720" href="category-theory.rigid-objects-precategories.html#720" class="Bound">C</a> <a id="722" class="Symbol">:</a> <a id="724" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="736" href="category-theory.rigid-objects-precategories.html#704" class="Bound">l1</a> <a id="739" href="category-theory.rigid-objects-precategories.html#707" class="Bound">l2</a><a id="741" class="Symbol">)</a> <a id="743" class="Symbol">(</a><a id="744" href="category-theory.rigid-objects-precategories.html#744" class="Bound">x</a> <a id="746" class="Symbol">:</a> <a id="748" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="764" href="category-theory.rigid-objects-precategories.html#720" class="Bound">C</a><a id="765" class="Symbol">)</a>
  <a id="769" class="Keyword">where</a>

  <a id="778" href="category-theory.rigid-objects-precategories.html#778" class="Function">is-rigid-obj-prop-Precategory</a> <a id="808" class="Symbol">:</a> <a id="810" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="815" href="category-theory.rigid-objects-precategories.html#707" class="Bound">l2</a>
  <a id="820" href="category-theory.rigid-objects-precategories.html#778" class="Function">is-rigid-obj-prop-Precategory</a> <a id="850" class="Symbol">=</a> <a id="852" href="foundation.contractible-types.html#1057" class="Function">is-contr-Prop</a> <a id="866" class="Symbol">(</a><a id="867" href="category-theory.isomorphisms-in-precategories.html#2238" class="Function">iso-Precategory</a> <a id="883" href="category-theory.rigid-objects-precategories.html#720" class="Bound">C</a> <a id="885" href="category-theory.rigid-objects-precategories.html#744" class="Bound">x</a> <a id="887" href="category-theory.rigid-objects-precategories.html#744" class="Bound">x</a><a id="888" class="Symbol">)</a>

  <a id="893" href="category-theory.rigid-objects-precategories.html#893" class="Function">is-rigid-obj-Precategory</a> <a id="918" class="Symbol">:</a> <a id="920" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="923" href="category-theory.rigid-objects-precategories.html#707" class="Bound">l2</a>
  <a id="928" href="category-theory.rigid-objects-precategories.html#893" class="Function">is-rigid-obj-Precategory</a> <a id="953" class="Symbol">=</a> <a id="955" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="965" href="category-theory.rigid-objects-precategories.html#778" class="Function">is-rigid-obj-prop-Precategory</a>

  <a id="998" href="category-theory.rigid-objects-precategories.html#998" class="Function">is-prop-is-rigid-obj-Precategory</a> <a id="1031" class="Symbol">:</a> <a id="1033" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1041" href="category-theory.rigid-objects-precategories.html#893" class="Function">is-rigid-obj-Precategory</a>
  <a id="1068" href="category-theory.rigid-objects-precategories.html#998" class="Function">is-prop-is-rigid-obj-Precategory</a> <a id="1101" class="Symbol">=</a>
    <a id="1107" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1125" href="category-theory.rigid-objects-precategories.html#778" class="Function">is-rigid-obj-prop-Precategory</a>
</pre>
### The type of rigid objects in a precategory

<pre class="Agda"><a id="rigid-obj-Precategory"></a><a id="1216" href="category-theory.rigid-objects-precategories.html#1216" class="Function">rigid-obj-Precategory</a> <a id="1238" class="Symbol">:</a> <a id="1240" class="Symbol">{</a><a id="1241" href="category-theory.rigid-objects-precategories.html#1241" class="Bound">l1</a> <a id="1244" href="category-theory.rigid-objects-precategories.html#1244" class="Bound">l2</a> <a id="1247" class="Symbol">:</a> <a id="1249" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1254" class="Symbol">}</a> <a id="1256" class="Symbol">(</a><a id="1257" href="category-theory.rigid-objects-precategories.html#1257" class="Bound">C</a> <a id="1259" class="Symbol">:</a> <a id="1261" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1273" href="category-theory.rigid-objects-precategories.html#1241" class="Bound">l1</a> <a id="1276" href="category-theory.rigid-objects-precategories.html#1244" class="Bound">l2</a><a id="1278" class="Symbol">)</a> <a id="1280" class="Symbol">→</a> <a id="1282" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1285" class="Symbol">(</a><a id="1286" href="category-theory.rigid-objects-precategories.html#1241" class="Bound">l1</a> <a id="1289" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1291" href="category-theory.rigid-objects-precategories.html#1244" class="Bound">l2</a><a id="1293" class="Symbol">)</a>
<a id="1295" href="category-theory.rigid-objects-precategories.html#1216" class="Function">rigid-obj-Precategory</a> <a id="1317" href="category-theory.rigid-objects-precategories.html#1317" class="Bound">C</a> <a id="1319" class="Symbol">=</a> <a id="1321" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1323" class="Symbol">(</a><a id="1324" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="1340" href="category-theory.rigid-objects-precategories.html#1317" class="Bound">C</a><a id="1341" class="Symbol">)</a> <a id="1343" class="Symbol">(</a><a id="1344" href="category-theory.rigid-objects-precategories.html#893" class="Function">is-rigid-obj-Precategory</a> <a id="1369" href="category-theory.rigid-objects-precategories.html#1317" class="Bound">C</a><a id="1370" class="Symbol">)</a>

<a id="1373" class="Keyword">module</a> <a id="1380" href="category-theory.rigid-objects-precategories.html#1380" class="Module">_</a>
  <a id="1384" class="Symbol">{</a><a id="1385" href="category-theory.rigid-objects-precategories.html#1385" class="Bound">l1</a> <a id="1388" href="category-theory.rigid-objects-precategories.html#1388" class="Bound">l2</a> <a id="1391" class="Symbol">:</a> <a id="1393" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1398" class="Symbol">}</a> <a id="1400" class="Symbol">(</a><a id="1401" href="category-theory.rigid-objects-precategories.html#1401" class="Bound">C</a> <a id="1403" class="Symbol">:</a> <a id="1405" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1417" href="category-theory.rigid-objects-precategories.html#1385" class="Bound">l1</a> <a id="1420" href="category-theory.rigid-objects-precategories.html#1388" class="Bound">l2</a><a id="1422" class="Symbol">)</a>
  <a id="1426" class="Keyword">where</a>

  <a id="1435" href="category-theory.rigid-objects-precategories.html#1435" class="Function">obj-rigid-obj-Precategory</a> <a id="1461" class="Symbol">:</a> <a id="1463" href="category-theory.rigid-objects-precategories.html#1216" class="Function">rigid-obj-Precategory</a> <a id="1485" href="category-theory.rigid-objects-precategories.html#1401" class="Bound">C</a> <a id="1487" class="Symbol">→</a> <a id="1489" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="1505" href="category-theory.rigid-objects-precategories.html#1401" class="Bound">C</a>
  <a id="1509" href="category-theory.rigid-objects-precategories.html#1435" class="Function">obj-rigid-obj-Precategory</a> <a id="1535" class="Symbol">=</a> <a id="1537" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="1544" href="category-theory.rigid-objects-precategories.html#1544" class="Function">is-rigid-rigid-obj-Precategory</a> <a id="1575" class="Symbol">:</a>
    <a id="1581" class="Symbol">(</a><a id="1582" href="category-theory.rigid-objects-precategories.html#1582" class="Bound">x</a> <a id="1584" class="Symbol">:</a> <a id="1586" href="category-theory.rigid-objects-precategories.html#1216" class="Function">rigid-obj-Precategory</a> <a id="1608" href="category-theory.rigid-objects-precategories.html#1401" class="Bound">C</a><a id="1609" class="Symbol">)</a> <a id="1611" class="Symbol">→</a>
    <a id="1617" href="category-theory.rigid-objects-precategories.html#893" class="Function">is-rigid-obj-Precategory</a> <a id="1642" href="category-theory.rigid-objects-precategories.html#1401" class="Bound">C</a> <a id="1644" class="Symbol">(</a><a id="1645" href="category-theory.rigid-objects-precategories.html#1435" class="Function">obj-rigid-obj-Precategory</a> <a id="1671" href="category-theory.rigid-objects-precategories.html#1582" class="Bound">x</a><a id="1672" class="Symbol">)</a>
  <a id="1676" href="category-theory.rigid-objects-precategories.html#1544" class="Function">is-rigid-rigid-obj-Precategory</a> <a id="1707" class="Symbol">=</a> <a id="1709" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>
## External links

- [rigid object](https://ncatlab.org/nlab/show/rigid+object) at $n$Lab
