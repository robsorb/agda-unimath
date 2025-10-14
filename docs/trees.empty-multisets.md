# Empty multisets

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="trees.empty-multisets.html" class="Module">trees.empty-multisets</a> <a id="57" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="113" class="Keyword">open</a> <a id="118" class="Keyword">import</a> <a id="125" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="306" class="Keyword">open</a> <a id="311" class="Keyword">import</a> <a id="318" href="trees.elementhood-relation-w-types.html" class="Module">trees.elementhood-relation-w-types</a>
<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="trees.multisets.html" class="Module">trees.multisets</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="trees.w-types.html" class="Module">trees.w-types</a>
</pre>
</details>

## Idea

A [multiset](trees.multisets.md) is said to be **empty** if it has no
[elements](trees.elementhood-relation-w-types.md).

## Definition

### The predicate of being an empty multiset

<pre class="Agda"><a id="624" class="Keyword">module</a> <a id="631" href="trees.empty-multisets.html#631" class="Module">_</a>
  <a id="635" class="Symbol">{</a><a id="636" href="trees.empty-multisets.html#636" class="Bound">l</a> <a id="638" class="Symbol">:</a> <a id="640" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="645" class="Symbol">}</a>
  <a id="649" class="Keyword">where</a>

  <a id="658" href="trees.empty-multisets.html#658" class="Function">is-empty-𝕍</a> <a id="669" class="Symbol">:</a> <a id="671" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="673" href="trees.empty-multisets.html#636" class="Bound">l</a> <a id="675" class="Symbol">→</a> <a id="677" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="680" href="trees.empty-multisets.html#636" class="Bound">l</a>
  <a id="684" href="trees.empty-multisets.html#658" class="Function">is-empty-𝕍</a> <a id="695" class="Symbol">(</a><a id="696" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="703" href="trees.empty-multisets.html#703" class="Bound">X</a> <a id="705" href="trees.empty-multisets.html#705" class="Bound">Y</a><a id="706" class="Symbol">)</a> <a id="708" class="Symbol">=</a> <a id="710" href="foundation-core.empty-types.html#972" class="Function">is-empty</a> <a id="719" href="trees.empty-multisets.html#703" class="Bound">X</a>

  <a id="724" href="trees.empty-multisets.html#724" class="Function">is-property-is-empty-𝕍</a> <a id="747" class="Symbol">:</a> <a id="749" class="Symbol">(</a><a id="750" href="trees.empty-multisets.html#750" class="Bound">X</a> <a id="752" class="Symbol">:</a> <a id="754" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="756" href="trees.empty-multisets.html#636" class="Bound">l</a><a id="757" class="Symbol">)</a> <a id="759" class="Symbol">→</a> <a id="761" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="769" class="Symbol">(</a><a id="770" href="trees.empty-multisets.html#658" class="Function">is-empty-𝕍</a> <a id="781" href="trees.empty-multisets.html#750" class="Bound">X</a><a id="782" class="Symbol">)</a>
  <a id="786" href="trees.empty-multisets.html#724" class="Function">is-property-is-empty-𝕍</a> <a id="809" class="Symbol">(</a><a id="810" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="817" href="trees.empty-multisets.html#817" class="Bound">X</a> <a id="819" href="trees.empty-multisets.html#819" class="Bound">Y</a><a id="820" class="Symbol">)</a> <a id="822" class="Symbol">=</a> <a id="824" href="foundation.empty-types.html#2605" class="Function">is-property-is-empty</a>

  <a id="848" href="trees.empty-multisets.html#848" class="Function">is-empty-prop-𝕍</a> <a id="864" class="Symbol">:</a> <a id="866" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="868" href="trees.empty-multisets.html#636" class="Bound">l</a> <a id="870" class="Symbol">→</a> <a id="872" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="877" href="trees.empty-multisets.html#636" class="Bound">l</a>
  <a id="881" href="trees.empty-multisets.html#848" class="Function">is-empty-prop-𝕍</a> <a id="897" href="trees.empty-multisets.html#897" class="Bound">X</a> <a id="899" class="Symbol">=</a> <a id="901" href="trees.empty-multisets.html#658" class="Function">is-empty-𝕍</a> <a id="912" href="trees.empty-multisets.html#897" class="Bound">X</a> <a id="914" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="916" href="trees.empty-multisets.html#724" class="Function">is-property-is-empty-𝕍</a> <a id="939" href="trees.empty-multisets.html#897" class="Bound">X</a>
</pre>
### The predicate of being a multiset with no elements

However, note that this predicate returns a type of universe level `lsuc l`.

<pre class="Agda"><a id="1088" class="Keyword">module</a> <a id="1095" href="trees.empty-multisets.html#1095" class="Module">_</a>
  <a id="1099" class="Symbol">{</a><a id="1100" href="trees.empty-multisets.html#1100" class="Bound">l</a> <a id="1102" class="Symbol">:</a> <a id="1104" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1109" class="Symbol">}</a>
  <a id="1113" class="Keyword">where</a>

  <a id="1122" href="trees.empty-multisets.html#1122" class="Function">has-no-elements-𝕍</a> <a id="1140" class="Symbol">:</a> <a id="1142" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="1144" href="trees.empty-multisets.html#1100" class="Bound">l</a> <a id="1146" class="Symbol">→</a> <a id="1148" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1151" class="Symbol">(</a><a id="1152" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1157" href="trees.empty-multisets.html#1100" class="Bound">l</a><a id="1158" class="Symbol">)</a>
  <a id="1162" href="trees.empty-multisets.html#1122" class="Function">has-no-elements-𝕍</a> <a id="1180" href="trees.empty-multisets.html#1180" class="Bound">X</a> <a id="1182" class="Symbol">=</a> <a id="1184" class="Symbol">(</a><a id="1185" href="trees.empty-multisets.html#1185" class="Bound">Y</a> <a id="1187" class="Symbol">:</a> <a id="1189" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="1191" href="trees.empty-multisets.html#1100" class="Bound">l</a><a id="1192" class="Symbol">)</a> <a id="1194" class="Symbol">→</a> <a id="1196" href="trees.empty-multisets.html#1185" class="Bound">Y</a> <a id="1198" href="trees.elementhood-relation-w-types.html#814" class="Function Operator">∉-𝕎</a> <a id="1202" href="trees.empty-multisets.html#1180" class="Bound">X</a>
</pre>
## Properties

### A multiset `X` is empty if and only if it has no elements

<pre class="Agda"><a id="1295" class="Keyword">module</a> <a id="1302" href="trees.empty-multisets.html#1302" class="Module">_</a>
  <a id="1306" class="Symbol">{</a><a id="1307" href="trees.empty-multisets.html#1307" class="Bound">l</a> <a id="1309" class="Symbol">:</a> <a id="1311" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1316" class="Symbol">}</a>
  <a id="1320" class="Keyword">where</a>

  <a id="1329" href="trees.empty-multisets.html#1329" class="Function">is-empty-has-no-elements-𝕍</a> <a id="1356" class="Symbol">:</a>
    <a id="1362" class="Symbol">(</a><a id="1363" href="trees.empty-multisets.html#1363" class="Bound">X</a> <a id="1365" class="Symbol">:</a> <a id="1367" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="1369" href="trees.empty-multisets.html#1307" class="Bound">l</a><a id="1370" class="Symbol">)</a> <a id="1372" class="Symbol">→</a> <a id="1374" href="trees.empty-multisets.html#1122" class="Function">has-no-elements-𝕍</a> <a id="1392" href="trees.empty-multisets.html#1363" class="Bound">X</a> <a id="1394" class="Symbol">→</a> <a id="1396" href="trees.empty-multisets.html#658" class="Function">is-empty-𝕍</a> <a id="1407" href="trees.empty-multisets.html#1363" class="Bound">X</a>
  <a id="1411" href="trees.empty-multisets.html#1329" class="Function">is-empty-has-no-elements-𝕍</a> <a id="1438" class="Symbol">(</a><a id="1439" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1446" href="trees.empty-multisets.html#1446" class="Bound">X</a> <a id="1448" href="trees.empty-multisets.html#1448" class="Bound">Y</a><a id="1449" class="Symbol">)</a> <a id="1451" href="trees.empty-multisets.html#1451" class="Bound">H</a> <a id="1453" href="trees.empty-multisets.html#1453" class="Bound">x</a> <a id="1455" class="Symbol">=</a> <a id="1457" href="trees.empty-multisets.html#1451" class="Bound">H</a> <a id="1459" class="Symbol">(</a><a id="1460" href="trees.empty-multisets.html#1448" class="Bound">Y</a> <a id="1462" href="trees.empty-multisets.html#1453" class="Bound">x</a><a id="1463" class="Symbol">)</a> <a id="1465" class="Symbol">(</a><a id="1466" href="trees.empty-multisets.html#1453" class="Bound">x</a> <a id="1468" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1470" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1474" class="Symbol">)</a>

  <a id="1479" href="trees.empty-multisets.html#1479" class="Function">has-no-elements-is-empty-𝕍</a> <a id="1506" class="Symbol">:</a>
    <a id="1512" class="Symbol">(</a><a id="1513" href="trees.empty-multisets.html#1513" class="Bound">X</a> <a id="1515" class="Symbol">:</a> <a id="1517" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="1519" href="trees.empty-multisets.html#1307" class="Bound">l</a><a id="1520" class="Symbol">)</a> <a id="1522" class="Symbol">→</a> <a id="1524" href="trees.empty-multisets.html#658" class="Function">is-empty-𝕍</a> <a id="1535" href="trees.empty-multisets.html#1513" class="Bound">X</a> <a id="1537" class="Symbol">→</a> <a id="1539" href="trees.empty-multisets.html#1122" class="Function">has-no-elements-𝕍</a> <a id="1557" href="trees.empty-multisets.html#1513" class="Bound">X</a>
  <a id="1561" href="trees.empty-multisets.html#1479" class="Function">has-no-elements-is-empty-𝕍</a> <a id="1588" class="Symbol">(</a><a id="1589" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1596" href="trees.empty-multisets.html#1596" class="Bound">X</a> <a id="1598" href="trees.empty-multisets.html#1598" class="Bound">Y</a><a id="1599" class="Symbol">)</a> <a id="1601" href="trees.empty-multisets.html#1601" class="Bound">H</a> <a id="1603" class="DottedPattern Symbol">._</a> <a id="1606" class="Symbol">(</a><a id="1607" href="trees.empty-multisets.html#1607" class="Bound">x</a> <a id="1609" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1611" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1615" class="Symbol">)</a> <a id="1617" class="Symbol">=</a> <a id="1619" href="trees.empty-multisets.html#1601" class="Bound">H</a> <a id="1621" href="trees.empty-multisets.html#1607" class="Bound">x</a>
</pre>