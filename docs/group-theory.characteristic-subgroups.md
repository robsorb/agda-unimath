# Characteristic subgroups

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="group-theory.characteristic-subgroups.html" class="Module">group-theory.characteristic-subgroups</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="group-theory.images-of-group-homomorphisms.html" class="Module">group-theory.images-of-group-homomorphisms</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="group-theory.isomorphisms-groups.html" class="Module">group-theory.isomorphisms-groups</a>
<a id="346" class="Keyword">open</a> <a id="351" class="Keyword">import</a> <a id="358" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
</pre>
</details>

## Idea

A **characteristic subgroup** of a [group](group-theory.groups.md) `G` is a
[subgroup](group-theory.subgroups.md) `H` of `G` such that `f H ⊆ H` for every
[isomorphism](group-theory.isomorphisms-groups.md) `f : G ≅ G`. The seemingly
stronger condition, which asserts that `f H ＝ H` for every isomorphism
`f : G ≅ G` is equivalent.

Note that any characteristic subgroup is
[normal](group-theory.normal-subgroups.md), since the condition of being
characteristic implies that `conjugation x H ＝ H`.

We also note that every subgroup which is defined for all groups, such as the
commutator subgroup, is automatically characteristic as a consequence of the
[univalence axiom](foundation.univalence.md), and therefore also normal.

## Definition

### The predicate of being a characteristic subgroup

<pre class="Agda"><a id="1211" class="Keyword">module</a> <a id="1218" href="group-theory.characteristic-subgroups.html#1218" class="Module">_</a>
  <a id="1222" class="Symbol">{</a><a id="1223" href="group-theory.characteristic-subgroups.html#1223" class="Bound">l1</a> <a id="1226" href="group-theory.characteristic-subgroups.html#1226" class="Bound">l2</a> <a id="1229" class="Symbol">:</a> <a id="1231" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1236" class="Symbol">}</a> <a id="1238" class="Symbol">(</a><a id="1239" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a> <a id="1241" class="Symbol">:</a> <a id="1243" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1249" href="group-theory.characteristic-subgroups.html#1223" class="Bound">l1</a><a id="1251" class="Symbol">)</a> <a id="1253" class="Symbol">(</a><a id="1254" href="group-theory.characteristic-subgroups.html#1254" class="Bound">H</a> <a id="1256" class="Symbol">:</a> <a id="1258" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="1267" href="group-theory.characteristic-subgroups.html#1226" class="Bound">l2</a> <a id="1270" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a><a id="1271" class="Symbol">)</a>
  <a id="1275" class="Keyword">where</a>

  <a id="1284" href="group-theory.characteristic-subgroups.html#1284" class="Function">is-characteristic-prop-Subgroup</a> <a id="1316" class="Symbol">:</a> <a id="1318" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1323" class="Symbol">(</a><a id="1324" href="group-theory.characteristic-subgroups.html#1223" class="Bound">l1</a> <a id="1327" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1329" href="group-theory.characteristic-subgroups.html#1226" class="Bound">l2</a><a id="1331" class="Symbol">)</a>
  <a id="1335" href="group-theory.characteristic-subgroups.html#1284" class="Function">is-characteristic-prop-Subgroup</a> <a id="1367" class="Symbol">=</a>
    <a id="1373" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1386" class="Symbol">(</a> <a id="1388" href="group-theory.isomorphisms-groups.html#3368" class="Function">iso-Group</a> <a id="1398" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a> <a id="1400" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a><a id="1401" class="Symbol">)</a>
      <a id="1409" class="Symbol">(</a> <a id="1411" class="Symbol">λ</a> <a id="1413" href="group-theory.characteristic-subgroups.html#1413" class="Bound">f</a> <a id="1415" class="Symbol">→</a>
        <a id="1425" href="group-theory.subgroups.html#13729" class="Function">leq-prop-Subgroup</a> <a id="1443" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a>
          <a id="1455" class="Symbol">(</a> <a id="1457" href="group-theory.images-of-group-homomorphisms.html#6950" class="Function">im-hom-Subgroup</a> <a id="1473" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a> <a id="1475" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a> <a id="1477" class="Symbol">(</a><a id="1478" href="group-theory.isomorphisms-groups.html#3464" class="Function">hom-iso-Group</a> <a id="1492" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a> <a id="1494" href="group-theory.characteristic-subgroups.html#1239" class="Bound">G</a> <a id="1496" href="group-theory.characteristic-subgroups.html#1413" class="Bound">f</a><a id="1497" class="Symbol">)</a> <a id="1499" href="group-theory.characteristic-subgroups.html#1254" class="Bound">H</a><a id="1500" class="Symbol">)</a>
          <a id="1512" class="Symbol">(</a> <a id="1514" href="group-theory.characteristic-subgroups.html#1254" class="Bound">H</a><a id="1515" class="Symbol">))</a>
</pre>
### The stronger predicate of being a characteristic subgroup

<pre class="Agda"><a id="1594" class="Keyword">module</a> <a id="1601" href="group-theory.characteristic-subgroups.html#1601" class="Module">_</a>
  <a id="1605" class="Symbol">{</a><a id="1606" href="group-theory.characteristic-subgroups.html#1606" class="Bound">l1</a> <a id="1609" href="group-theory.characteristic-subgroups.html#1609" class="Bound">l2</a> <a id="1612" class="Symbol">:</a> <a id="1614" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1619" class="Symbol">}</a> <a id="1621" class="Symbol">(</a><a id="1622" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a> <a id="1624" class="Symbol">:</a> <a id="1626" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1632" href="group-theory.characteristic-subgroups.html#1606" class="Bound">l1</a><a id="1634" class="Symbol">)</a> <a id="1636" class="Symbol">(</a><a id="1637" href="group-theory.characteristic-subgroups.html#1637" class="Bound">H</a> <a id="1639" class="Symbol">:</a> <a id="1641" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="1650" href="group-theory.characteristic-subgroups.html#1609" class="Bound">l2</a> <a id="1653" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a><a id="1654" class="Symbol">)</a>
  <a id="1658" class="Keyword">where</a>

  <a id="1667" href="group-theory.characteristic-subgroups.html#1667" class="Function">is-characteristic-prop-Subgroup&#39;</a> <a id="1700" class="Symbol">:</a> <a id="1702" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1707" class="Symbol">(</a><a id="1708" href="group-theory.characteristic-subgroups.html#1606" class="Bound">l1</a> <a id="1711" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1713" href="group-theory.characteristic-subgroups.html#1609" class="Bound">l2</a><a id="1715" class="Symbol">)</a>
  <a id="1719" href="group-theory.characteristic-subgroups.html#1667" class="Function">is-characteristic-prop-Subgroup&#39;</a> <a id="1752" class="Symbol">=</a>
    <a id="1758" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1771" class="Symbol">(</a> <a id="1773" href="group-theory.isomorphisms-groups.html#3368" class="Function">iso-Group</a> <a id="1783" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a> <a id="1785" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a><a id="1786" class="Symbol">)</a>
      <a id="1794" class="Symbol">(</a> <a id="1796" class="Symbol">λ</a> <a id="1798" href="group-theory.characteristic-subgroups.html#1798" class="Bound">f</a> <a id="1800" class="Symbol">→</a>
        <a id="1810" href="group-theory.subgroups.html#12419" class="Function">has-same-elements-prop-Subgroup</a> <a id="1842" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a>
          <a id="1854" class="Symbol">(</a> <a id="1856" href="group-theory.images-of-group-homomorphisms.html#6950" class="Function">im-hom-Subgroup</a> <a id="1872" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a> <a id="1874" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a> <a id="1876" class="Symbol">(</a><a id="1877" href="group-theory.isomorphisms-groups.html#3464" class="Function">hom-iso-Group</a> <a id="1891" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a> <a id="1893" href="group-theory.characteristic-subgroups.html#1622" class="Bound">G</a> <a id="1895" href="group-theory.characteristic-subgroups.html#1798" class="Bound">f</a><a id="1896" class="Symbol">)</a> <a id="1898" href="group-theory.characteristic-subgroups.html#1637" class="Bound">H</a><a id="1899" class="Symbol">)</a>
          <a id="1911" class="Symbol">(</a> <a id="1913" href="group-theory.characteristic-subgroups.html#1637" class="Bound">H</a><a id="1914" class="Symbol">))</a>
</pre>
## See also

- [Characteristic subgroup](https://groupprops.subwiki.org/wiki/Characteristic_subgroup)
  at Groupprops
- [Characteristic subgroup](https://www.wikidata.org/entity/Q747027) at Wikidata
- [Characteristic subgroup](https://en.wikipedia.org/wiki/Characteristic_subgroup)
  at Wikipedia
