# Fixity

<pre class="Agda"><a id="19" class="Keyword">module</a> <a id="26" href="reflection.fixity.html" class="Module">reflection.fixity</a> <a id="44" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="100" class="Keyword">open</a> <a id="105" class="Keyword">import</a> <a id="112" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a>

<a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="234" class="Keyword">open</a> <a id="239" class="Keyword">import</a> <a id="246" href="primitives.floats.html" class="Module">primitives.floats</a>

<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="reflection.names.html" class="Module">reflection.names</a>
</pre>
</details>

## Idea

The fixity of a quoted name is given by

- An associativity, i.e. it is left-associative, right-associative or neither.
- A precedence, i.e. it is unrelated (it has no precedence) or it is related and
  has a float precedence.

## Definition

<pre class="Agda"><a id="571" class="Keyword">data</a> <a id="Associativity-Agda"></a><a id="576" href="reflection.fixity.html#576" class="Datatype">Associativity-Agda</a> <a id="595" class="Symbol">:</a> <a id="597" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="600" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="606" class="Keyword">where</a>
  <a id="Associativity-Agda.left-Associativity-Agda"></a><a id="614" href="reflection.fixity.html#614" class="InductiveConstructor">left-Associativity-Agda</a> <a id="638" class="Symbol">:</a> <a id="640" href="reflection.fixity.html#576" class="Datatype">Associativity-Agda</a>
  <a id="Associativity-Agda.right-Associativity-Agda"></a><a id="661" href="reflection.fixity.html#661" class="InductiveConstructor">right-Associativity-Agda</a> <a id="686" class="Symbol">:</a> <a id="688" href="reflection.fixity.html#576" class="Datatype">Associativity-Agda</a>
  <a id="Associativity-Agda.none-Associativity-Agda"></a><a id="709" href="reflection.fixity.html#709" class="InductiveConstructor">none-Associativity-Agda</a> <a id="733" class="Symbol">:</a> <a id="735" href="reflection.fixity.html#576" class="Datatype">Associativity-Agda</a>

<a id="755" class="Keyword">data</a> <a id="Precedence-Agda"></a><a id="760" href="reflection.fixity.html#760" class="Datatype">Precedence-Agda</a> <a id="776" class="Symbol">:</a> <a id="778" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="781" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="787" class="Keyword">where</a>
  <a id="Precedence-Agda.related-Precedence-Agda"></a><a id="795" href="reflection.fixity.html#795" class="InductiveConstructor">related-Precedence-Agda</a> <a id="819" class="Symbol">:</a> <a id="821" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="827" class="Symbol">→</a> <a id="829" href="reflection.fixity.html#760" class="Datatype">Precedence-Agda</a>
  <a id="Precedence-Agda.unrelated-Precedence-Agda"></a><a id="847" href="reflection.fixity.html#847" class="InductiveConstructor">unrelated-Precedence-Agda</a> <a id="873" class="Symbol">:</a> <a id="875" href="reflection.fixity.html#760" class="Datatype">Precedence-Agda</a>

<a id="892" class="Keyword">data</a> <a id="Fixity-Agda"></a><a id="897" href="reflection.fixity.html#897" class="Datatype">Fixity-Agda</a> <a id="909" class="Symbol">:</a> <a id="911" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="914" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="920" class="Keyword">where</a>
  <a id="Fixity-Agda.cons-Fixity-Agda"></a><a id="928" href="reflection.fixity.html#928" class="InductiveConstructor">cons-Fixity-Agda</a> <a id="945" class="Symbol">:</a> <a id="947" href="reflection.fixity.html#576" class="Datatype">Associativity-Agda</a> <a id="966" class="Symbol">→</a> <a id="968" href="reflection.fixity.html#760" class="Datatype">Precedence-Agda</a> <a id="984" class="Symbol">→</a> <a id="986" href="reflection.fixity.html#897" class="Datatype">Fixity-Agda</a>

<a id="999" class="Symbol">{-#</a> <a id="1003" class="Keyword">BUILTIN</a> <a id="1011" class="Keyword">ASSOC</a> <a id="1017" href="reflection.fixity.html#576" class="Datatype">Associativity-Agda</a> <a id="1036" class="Symbol">#-}</a>
<a id="1040" class="Symbol">{-#</a> <a id="1044" class="Keyword">BUILTIN</a> <a id="1052" class="Keyword">ASSOCLEFT</a> <a id="1062" href="reflection.fixity.html#614" class="InductiveConstructor">left-Associativity-Agda</a> <a id="1086" class="Symbol">#-}</a>
<a id="1090" class="Symbol">{-#</a> <a id="1094" class="Keyword">BUILTIN</a> <a id="1102" class="Keyword">ASSOCRIGHT</a> <a id="1113" href="reflection.fixity.html#661" class="InductiveConstructor">right-Associativity-Agda</a> <a id="1138" class="Symbol">#-}</a>
<a id="1142" class="Symbol">{-#</a> <a id="1146" class="Keyword">BUILTIN</a> <a id="1154" class="Keyword">ASSOCNON</a> <a id="1163" href="reflection.fixity.html#709" class="InductiveConstructor">none-Associativity-Agda</a> <a id="1187" class="Symbol">#-}</a>

<a id="1192" class="Symbol">{-#</a> <a id="1196" class="Keyword">BUILTIN</a> <a id="1204" class="Keyword">PRECEDENCE</a> <a id="1215" href="reflection.fixity.html#760" class="Datatype">Precedence-Agda</a> <a id="1231" class="Symbol">#-}</a>
<a id="1235" class="Symbol">{-#</a> <a id="1239" class="Keyword">BUILTIN</a> <a id="1247" class="Keyword">PRECRELATED</a> <a id="1259" href="reflection.fixity.html#795" class="InductiveConstructor">related-Precedence-Agda</a> <a id="1283" class="Symbol">#-}</a>
<a id="1287" class="Symbol">{-#</a> <a id="1291" class="Keyword">BUILTIN</a> <a id="1299" class="Keyword">PRECUNRELATED</a> <a id="1313" href="reflection.fixity.html#847" class="InductiveConstructor">unrelated-Precedence-Agda</a> <a id="1339" class="Symbol">#-}</a>

<a id="1344" class="Symbol">{-#</a> <a id="1348" class="Keyword">BUILTIN</a> <a id="1356" class="Keyword">FIXITY</a> <a id="1363" href="reflection.fixity.html#897" class="Datatype">Fixity-Agda</a> <a id="1375" class="Symbol">#-}</a>
<a id="1379" class="Symbol">{-#</a> <a id="1383" class="Keyword">BUILTIN</a> <a id="1391" class="Keyword">FIXITYFIXITY</a> <a id="1404" href="reflection.fixity.html#928" class="InductiveConstructor">cons-Fixity-Agda</a> <a id="1421" class="Symbol">#-}</a>

<a id="1426" class="Keyword">primitive</a>
  <a id="primQNameFixity"></a><a id="1438" href="reflection.fixity.html#1438" class="Primitive">primQNameFixity</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="1466" class="Symbol">→</a> <a id="1468" href="reflection.fixity.html#897" class="Datatype">Fixity-Agda</a>
</pre>
## Examples

<pre class="Agda"><a id="1506" href="reflection.fixity.html#1506" class="Function">_</a> <a id="1508" class="Symbol">:</a>
  <a id="1512" href="reflection.fixity.html#1438" class="Primitive">primQNameFixity</a> <a id="1528" class="Symbol">(</a><a id="1529" class="Keyword">quote</a> <a id="1535" href="elementary-number-theory.addition-integers.html#1312" class="Function">add-ℤ</a><a id="1540" class="Symbol">)</a> <a id="1542" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
  <a id="1546" href="reflection.fixity.html#928" class="InductiveConstructor">cons-Fixity-Agda</a> <a id="1563" href="reflection.fixity.html#709" class="InductiveConstructor">none-Associativity-Agda</a> <a id="1587" href="reflection.fixity.html#847" class="InductiveConstructor">unrelated-Precedence-Agda</a>
<a id="1613" class="Symbol">_</a> <a id="1615" class="Symbol">=</a> <a id="1617" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="1623" href="reflection.fixity.html#1623" class="Function">_</a> <a id="1625" class="Symbol">:</a>
  <a id="1629" href="reflection.fixity.html#1438" class="Primitive">primQNameFixity</a> <a id="1645" class="Symbol">(</a><a id="1646" class="Keyword">quote</a> <a id="1652" class="Symbol">(</a><a id="1653" href="elementary-number-theory.addition-integers.html#1604" class="Function Operator">_+ℤ_</a><a id="1657" class="Symbol">))</a> <a id="1660" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
  <a id="1664" href="reflection.fixity.html#928" class="InductiveConstructor">cons-Fixity-Agda</a> <a id="1681" href="reflection.fixity.html#614" class="InductiveConstructor">left-Associativity-Agda</a> <a id="1705" class="Symbol">(</a><a id="1706" href="reflection.fixity.html#795" class="InductiveConstructor">related-Precedence-Agda</a> <a id="1730" class="Number">35.0</a><a id="1734" class="Symbol">)</a>
<a id="1736" class="Symbol">_</a> <a id="1738" class="Symbol">=</a> <a id="1740" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>