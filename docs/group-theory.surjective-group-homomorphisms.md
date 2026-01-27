# Surjective group homomorphisms

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="group-theory.surjective-group-homomorphisms.html" class="Module">group-theory.surjective-group-homomorphisms</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="group-theory.full-subgroups.html" class="Module">group-theory.full-subgroups</a>
<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="group-theory.images-of-group-homomorphisms.html" class="Module">group-theory.images-of-group-homomorphisms</a>
<a id="438" class="Keyword">open</a> <a id="443" class="Keyword">import</a> <a id="450" href="group-theory.surjective-semigroup-homomorphisms.html" class="Module">group-theory.surjective-semigroup-homomorphisms</a>
</pre>
</details>

A [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` is said
to be **surjective** if its underlying map is
[surjective](foundation.surjective-maps.md).

## Definition

### Surjective group homomorphisms

<pre class="Agda"><a id="747" class="Keyword">module</a> <a id="754" href="group-theory.surjective-group-homomorphisms.html#754" class="Module">_</a>
  <a id="758" class="Symbol">{</a><a id="759" href="group-theory.surjective-group-homomorphisms.html#759" class="Bound">l1</a> <a id="762" href="group-theory.surjective-group-homomorphisms.html#762" class="Bound">l2</a> <a id="765" class="Symbol">:</a> <a id="767" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="772" class="Symbol">}</a> <a id="774" class="Symbol">(</a><a id="775" href="group-theory.surjective-group-homomorphisms.html#775" class="Bound">G</a> <a id="777" class="Symbol">:</a> <a id="779" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="785" href="group-theory.surjective-group-homomorphisms.html#759" class="Bound">l1</a><a id="787" class="Symbol">)</a> <a id="789" class="Symbol">(</a><a id="790" href="group-theory.surjective-group-homomorphisms.html#790" class="Bound">H</a> <a id="792" class="Symbol">:</a> <a id="794" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="800" href="group-theory.surjective-group-homomorphisms.html#762" class="Bound">l2</a><a id="802" class="Symbol">)</a> <a id="804" class="Symbol">(</a><a id="805" href="group-theory.surjective-group-homomorphisms.html#805" class="Bound">f</a> <a id="807" class="Symbol">:</a> <a id="809" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="819" href="group-theory.surjective-group-homomorphisms.html#775" class="Bound">G</a> <a id="821" href="group-theory.surjective-group-homomorphisms.html#790" class="Bound">H</a><a id="822" class="Symbol">)</a>
  <a id="826" class="Keyword">where</a>

  <a id="835" href="group-theory.surjective-group-homomorphisms.html#835" class="Function">is-surjective-prop-hom-Group</a> <a id="864" class="Symbol">:</a> <a id="866" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="871" class="Symbol">(</a><a id="872" href="group-theory.surjective-group-homomorphisms.html#759" class="Bound">l1</a> <a id="875" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="877" href="group-theory.surjective-group-homomorphisms.html#762" class="Bound">l2</a><a id="879" class="Symbol">)</a>
  <a id="883" href="group-theory.surjective-group-homomorphisms.html#835" class="Function">is-surjective-prop-hom-Group</a> <a id="912" class="Symbol">=</a>
    <a id="918" href="group-theory.surjective-semigroup-homomorphisms.html#823" class="Function">is-surjective-prop-hom-Semigroup</a>
      <a id="957" class="Symbol">(</a> <a id="959" href="group-theory.groups.html#2476" class="Function">semigroup-Group</a> <a id="975" href="group-theory.surjective-group-homomorphisms.html#775" class="Bound">G</a><a id="976" class="Symbol">)</a>
      <a id="984" class="Symbol">(</a> <a id="986" href="group-theory.groups.html#2476" class="Function">semigroup-Group</a> <a id="1002" href="group-theory.surjective-group-homomorphisms.html#790" class="Bound">H</a><a id="1003" class="Symbol">)</a>
      <a id="1011" class="Symbol">(</a> <a id="1013" href="group-theory.surjective-group-homomorphisms.html#805" class="Bound">f</a><a id="1014" class="Symbol">)</a>

  <a id="1019" href="group-theory.surjective-group-homomorphisms.html#1019" class="Function">is-surjective-hom-Group</a> <a id="1043" class="Symbol">:</a> <a id="1045" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1048" class="Symbol">(</a><a id="1049" href="group-theory.surjective-group-homomorphisms.html#759" class="Bound">l1</a> <a id="1052" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1054" href="group-theory.surjective-group-homomorphisms.html#762" class="Bound">l2</a><a id="1056" class="Symbol">)</a>
  <a id="1060" href="group-theory.surjective-group-homomorphisms.html#1019" class="Function">is-surjective-hom-Group</a> <a id="1084" class="Symbol">=</a>
    <a id="1090" href="group-theory.surjective-semigroup-homomorphisms.html#962" class="Function">is-surjective-hom-Semigroup</a>
      <a id="1124" class="Symbol">(</a> <a id="1126" href="group-theory.groups.html#2476" class="Function">semigroup-Group</a> <a id="1142" href="group-theory.surjective-group-homomorphisms.html#775" class="Bound">G</a><a id="1143" class="Symbol">)</a>
      <a id="1151" class="Symbol">(</a> <a id="1153" href="group-theory.groups.html#2476" class="Function">semigroup-Group</a> <a id="1169" href="group-theory.surjective-group-homomorphisms.html#790" class="Bound">H</a><a id="1170" class="Symbol">)</a>
      <a id="1178" class="Symbol">(</a> <a id="1180" href="group-theory.surjective-group-homomorphisms.html#805" class="Bound">f</a><a id="1181" class="Symbol">)</a>

  <a id="1186" href="group-theory.surjective-group-homomorphisms.html#1186" class="Function">is-prop-is-surjective-hom-Group</a> <a id="1218" class="Symbol">:</a> <a id="1220" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1228" href="group-theory.surjective-group-homomorphisms.html#1019" class="Function">is-surjective-hom-Group</a>
  <a id="1254" href="group-theory.surjective-group-homomorphisms.html#1186" class="Function">is-prop-is-surjective-hom-Group</a> <a id="1286" class="Symbol">=</a>
    <a id="1292" href="group-theory.surjective-semigroup-homomorphisms.html#1083" class="Function">is-prop-is-surjective-hom-Semigroup</a>
      <a id="1334" class="Symbol">(</a> <a id="1336" href="group-theory.groups.html#2476" class="Function">semigroup-Group</a> <a id="1352" href="group-theory.surjective-group-homomorphisms.html#775" class="Bound">G</a><a id="1353" class="Symbol">)</a>
      <a id="1361" class="Symbol">(</a> <a id="1363" href="group-theory.groups.html#2476" class="Function">semigroup-Group</a> <a id="1379" href="group-theory.surjective-group-homomorphisms.html#790" class="Bound">H</a><a id="1380" class="Symbol">)</a>
      <a id="1388" class="Symbol">(</a> <a id="1390" href="group-theory.surjective-group-homomorphisms.html#805" class="Bound">f</a><a id="1391" class="Symbol">)</a>
</pre>
## Properties

### A group homomorphism is surjective if and only if its image is the full subgroup

<pre class="Agda"><a id="1507" class="Keyword">module</a> <a id="1514" href="group-theory.surjective-group-homomorphisms.html#1514" class="Module">_</a>
  <a id="1518" class="Symbol">{</a><a id="1519" href="group-theory.surjective-group-homomorphisms.html#1519" class="Bound">l1</a> <a id="1522" href="group-theory.surjective-group-homomorphisms.html#1522" class="Bound">l2</a> <a id="1525" class="Symbol">:</a> <a id="1527" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1532" class="Symbol">}</a> <a id="1534" class="Symbol">(</a><a id="1535" href="group-theory.surjective-group-homomorphisms.html#1535" class="Bound">G</a> <a id="1537" class="Symbol">:</a> <a id="1539" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1545" href="group-theory.surjective-group-homomorphisms.html#1519" class="Bound">l1</a><a id="1547" class="Symbol">)</a> <a id="1549" class="Symbol">(</a><a id="1550" href="group-theory.surjective-group-homomorphisms.html#1550" class="Bound">H</a> <a id="1552" class="Symbol">:</a> <a id="1554" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1560" href="group-theory.surjective-group-homomorphisms.html#1522" class="Bound">l2</a><a id="1562" class="Symbol">)</a> <a id="1564" class="Symbol">(</a><a id="1565" href="group-theory.surjective-group-homomorphisms.html#1565" class="Bound">f</a> <a id="1567" class="Symbol">:</a> <a id="1569" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="1579" href="group-theory.surjective-group-homomorphisms.html#1535" class="Bound">G</a> <a id="1581" href="group-theory.surjective-group-homomorphisms.html#1550" class="Bound">H</a><a id="1582" class="Symbol">)</a>
  <a id="1586" class="Keyword">where</a>

  <a id="1595" href="group-theory.surjective-group-homomorphisms.html#1595" class="Function">is-surjective-is-full-subgroup-image-hom-Group</a> <a id="1642" class="Symbol">:</a>
    <a id="1648" href="group-theory.full-subgroups.html#1068" class="Function">is-full-Subgroup</a> <a id="1665" href="group-theory.surjective-group-homomorphisms.html#1550" class="Bound">H</a> <a id="1667" class="Symbol">(</a><a id="1668" href="group-theory.images-of-group-homomorphisms.html#4505" class="Function">image-hom-Group</a> <a id="1684" href="group-theory.surjective-group-homomorphisms.html#1535" class="Bound">G</a> <a id="1686" href="group-theory.surjective-group-homomorphisms.html#1550" class="Bound">H</a> <a id="1688" href="group-theory.surjective-group-homomorphisms.html#1565" class="Bound">f</a><a id="1689" class="Symbol">)</a> <a id="1691" class="Symbol">→</a>
    <a id="1697" href="group-theory.surjective-group-homomorphisms.html#1019" class="Function">is-surjective-hom-Group</a> <a id="1721" href="group-theory.surjective-group-homomorphisms.html#1535" class="Bound">G</a> <a id="1723" href="group-theory.surjective-group-homomorphisms.html#1550" class="Bound">H</a> <a id="1725" href="group-theory.surjective-group-homomorphisms.html#1565" class="Bound">f</a>
  <a id="1729" href="group-theory.surjective-group-homomorphisms.html#1595" class="Function">is-surjective-is-full-subgroup-image-hom-Group</a> <a id="1776" href="group-theory.surjective-group-homomorphisms.html#1776" class="Bound">u</a> <a id="1778" class="Symbol">=</a> <a id="1780" href="group-theory.surjective-group-homomorphisms.html#1776" class="Bound">u</a>

  <a id="1785" href="group-theory.surjective-group-homomorphisms.html#1785" class="Function">is-full-subgroup-image-is-surjective-hom-Group</a> <a id="1832" class="Symbol">:</a>
    <a id="1838" href="group-theory.surjective-group-homomorphisms.html#1019" class="Function">is-surjective-hom-Group</a> <a id="1862" href="group-theory.surjective-group-homomorphisms.html#1535" class="Bound">G</a> <a id="1864" href="group-theory.surjective-group-homomorphisms.html#1550" class="Bound">H</a> <a id="1866" href="group-theory.surjective-group-homomorphisms.html#1565" class="Bound">f</a> <a id="1868" class="Symbol">→</a>
    <a id="1874" href="group-theory.full-subgroups.html#1068" class="Function">is-full-Subgroup</a> <a id="1891" href="group-theory.surjective-group-homomorphisms.html#1550" class="Bound">H</a> <a id="1893" class="Symbol">(</a><a id="1894" href="group-theory.images-of-group-homomorphisms.html#4505" class="Function">image-hom-Group</a> <a id="1910" href="group-theory.surjective-group-homomorphisms.html#1535" class="Bound">G</a> <a id="1912" href="group-theory.surjective-group-homomorphisms.html#1550" class="Bound">H</a> <a id="1914" href="group-theory.surjective-group-homomorphisms.html#1565" class="Bound">f</a><a id="1915" class="Symbol">)</a>
  <a id="1919" href="group-theory.surjective-group-homomorphisms.html#1785" class="Function">is-full-subgroup-image-is-surjective-hom-Group</a> <a id="1966" href="group-theory.surjective-group-homomorphisms.html#1966" class="Bound">u</a> <a id="1968" class="Symbol">=</a> <a id="1970" href="group-theory.surjective-group-homomorphisms.html#1966" class="Bound">u</a>
</pre>