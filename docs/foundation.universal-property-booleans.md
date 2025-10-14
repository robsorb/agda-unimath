# The universal property of booleans

<pre class="Agda"><a id="47" class="Keyword">module</a> <a id="54" href="foundation.universal-property-booleans.html" class="Module">foundation.universal-property-booleans</a> <a id="93" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.equality-cartesian-product-types.html" class="Module">foundation.equality-cartesian-product-types</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="420" class="Keyword">open</a> <a id="425" class="Keyword">import</a> <a id="432" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="461" class="Keyword">open</a> <a id="466" class="Keyword">import</a> <a id="473" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="504" class="Keyword">open</a> <a id="509" class="Keyword">import</a> <a id="516" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="543" class="Keyword">open</a> <a id="548" class="Keyword">import</a> <a id="555" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

<pre class="Agda"><a id="ev-true-false"></a><a id="611" href="foundation.universal-property-booleans.html#611" class="Function">ev-true-false</a> <a id="625" class="Symbol">:</a>
  <a id="629" class="Symbol">{</a><a id="630" href="foundation.universal-property-booleans.html#630" class="Bound">l</a> <a id="632" class="Symbol">:</a> <a id="634" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="639" class="Symbol">}</a> <a id="641" class="Symbol">(</a><a id="642" href="foundation.universal-property-booleans.html#642" class="Bound">A</a> <a id="644" class="Symbol">:</a> <a id="646" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="649" href="foundation.universal-property-booleans.html#630" class="Bound">l</a><a id="650" class="Symbol">)</a> <a id="652" class="Symbol">→</a> <a id="654" class="Symbol">(</a><a id="655" href="foundation.universal-property-booleans.html#655" class="Bound">f</a> <a id="657" class="Symbol">:</a> <a id="659" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="664" class="Symbol">→</a> <a id="666" href="foundation.universal-property-booleans.html#642" class="Bound">A</a><a id="667" class="Symbol">)</a> <a id="669" class="Symbol">→</a> <a id="671" href="foundation.universal-property-booleans.html#642" class="Bound">A</a> <a id="673" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="675" href="foundation.universal-property-booleans.html#642" class="Bound">A</a>
<a id="677" href="foundation.universal-property-booleans.html#611" class="Function">ev-true-false</a> <a id="691" href="foundation.universal-property-booleans.html#691" class="Bound">A</a> <a id="693" href="foundation.universal-property-booleans.html#693" class="Bound">f</a> <a id="695" class="Symbol">=</a> <a id="697" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="702" class="Symbol">(</a><a id="703" href="foundation.universal-property-booleans.html#693" class="Bound">f</a> <a id="705" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a><a id="709" class="Symbol">)</a> <a id="711" class="Symbol">(</a><a id="712" href="foundation.universal-property-booleans.html#693" class="Bound">f</a> <a id="714" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a><a id="719" class="Symbol">)</a>

<a id="map-universal-property-bool"></a><a id="722" href="foundation.universal-property-booleans.html#722" class="Function">map-universal-property-bool</a> <a id="750" class="Symbol">:</a>
  <a id="754" class="Symbol">{</a><a id="755" href="foundation.universal-property-booleans.html#755" class="Bound">l</a> <a id="757" class="Symbol">:</a> <a id="759" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="764" class="Symbol">}</a> <a id="766" class="Symbol">{</a><a id="767" href="foundation.universal-property-booleans.html#767" class="Bound">A</a> <a id="769" class="Symbol">:</a> <a id="771" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="774" href="foundation.universal-property-booleans.html#755" class="Bound">l</a><a id="775" class="Symbol">}</a> <a id="777" class="Symbol">→</a>
  <a id="781" href="foundation.universal-property-booleans.html#767" class="Bound">A</a> <a id="783" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="785" href="foundation.universal-property-booleans.html#767" class="Bound">A</a> <a id="787" class="Symbol">→</a> <a id="789" class="Symbol">(</a><a id="790" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="795" class="Symbol">→</a> <a id="797" href="foundation.universal-property-booleans.html#767" class="Bound">A</a><a id="798" class="Symbol">)</a>
<a id="800" href="foundation.universal-property-booleans.html#722" class="Function">map-universal-property-bool</a> <a id="828" class="Symbol">(</a><a id="829" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="834" href="foundation.universal-property-booleans.html#834" class="Bound">x</a> <a id="836" href="foundation.universal-property-booleans.html#836" class="Bound">y</a><a id="837" class="Symbol">)</a> <a id="839" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a> <a id="844" class="Symbol">=</a> <a id="846" href="foundation.universal-property-booleans.html#834" class="Bound">x</a>
<a id="848" href="foundation.universal-property-booleans.html#722" class="Function">map-universal-property-bool</a> <a id="876" class="Symbol">(</a><a id="877" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="882" href="foundation.universal-property-booleans.html#882" class="Bound">x</a> <a id="884" href="foundation.universal-property-booleans.html#884" class="Bound">y</a><a id="885" class="Symbol">)</a> <a id="887" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="893" class="Symbol">=</a> <a id="895" href="foundation.universal-property-booleans.html#884" class="Bound">y</a>

<a id="898" class="Keyword">abstract</a>
  <a id="is-section-map-universal-property-bool"></a><a id="909" href="foundation.universal-property-booleans.html#909" class="Function">is-section-map-universal-property-bool</a> <a id="948" class="Symbol">:</a>
    <a id="954" class="Symbol">{</a><a id="955" href="foundation.universal-property-booleans.html#955" class="Bound">l</a> <a id="957" class="Symbol">:</a> <a id="959" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="964" class="Symbol">}</a> <a id="966" class="Symbol">{</a><a id="967" href="foundation.universal-property-booleans.html#967" class="Bound">A</a> <a id="969" class="Symbol">:</a> <a id="971" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="974" href="foundation.universal-property-booleans.html#955" class="Bound">l</a><a id="975" class="Symbol">}</a> <a id="977" class="Symbol">→</a>
    <a id="983" class="Symbol">((</a><a id="985" href="foundation.universal-property-booleans.html#611" class="Function">ev-true-false</a> <a id="999" href="foundation.universal-property-booleans.html#967" class="Bound">A</a><a id="1000" class="Symbol">)</a> <a id="1002" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1004" href="foundation.universal-property-booleans.html#722" class="Function">map-universal-property-bool</a><a id="1031" class="Symbol">)</a> <a id="1033" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1035" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="1040" href="foundation.universal-property-booleans.html#909" class="Function">is-section-map-universal-property-bool</a> <a id="1079" class="Symbol">(</a><a id="1080" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="1085" href="foundation.universal-property-booleans.html#1085" class="Bound">x</a> <a id="1087" href="foundation.universal-property-booleans.html#1087" class="Bound">y</a><a id="1088" class="Symbol">)</a> <a id="1090" class="Symbol">=</a> <a id="1092" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="1098" class="Keyword">abstract</a>
  <a id="is-retraction-map-universal-property-bool&#39;"></a><a id="1109" href="foundation.universal-property-booleans.html#1109" class="Function">is-retraction-map-universal-property-bool&#39;</a> <a id="1152" class="Symbol">:</a>
    <a id="1158" class="Symbol">{</a><a id="1159" href="foundation.universal-property-booleans.html#1159" class="Bound">l</a> <a id="1161" class="Symbol">:</a> <a id="1163" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1168" class="Symbol">}</a> <a id="1170" class="Symbol">{</a><a id="1171" href="foundation.universal-property-booleans.html#1171" class="Bound">A</a> <a id="1173" class="Symbol">:</a> <a id="1175" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1178" href="foundation.universal-property-booleans.html#1159" class="Bound">l</a><a id="1179" class="Symbol">}</a> <a id="1181" class="Symbol">(</a><a id="1182" href="foundation.universal-property-booleans.html#1182" class="Bound">f</a> <a id="1184" class="Symbol">:</a> <a id="1186" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="1191" class="Symbol">→</a> <a id="1193" href="foundation.universal-property-booleans.html#1171" class="Bound">A</a><a id="1194" class="Symbol">)</a> <a id="1196" class="Symbol">→</a>
    <a id="1202" class="Symbol">(</a><a id="1203" href="foundation.universal-property-booleans.html#722" class="Function">map-universal-property-bool</a> <a id="1231" class="Symbol">(</a><a id="1232" href="foundation.universal-property-booleans.html#611" class="Function">ev-true-false</a> <a id="1246" href="foundation.universal-property-booleans.html#1171" class="Bound">A</a> <a id="1248" href="foundation.universal-property-booleans.html#1182" class="Bound">f</a><a id="1249" class="Symbol">))</a> <a id="1252" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1254" href="foundation.universal-property-booleans.html#1182" class="Bound">f</a>
  <a id="1258" href="foundation.universal-property-booleans.html#1109" class="Function">is-retraction-map-universal-property-bool&#39;</a> <a id="1301" href="foundation.universal-property-booleans.html#1301" class="Bound">f</a> <a id="1303" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a> <a id="1308" class="Symbol">=</a> <a id="1310" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
  <a id="1317" href="foundation.universal-property-booleans.html#1109" class="Function">is-retraction-map-universal-property-bool&#39;</a> <a id="1360" href="foundation.universal-property-booleans.html#1360" class="Bound">f</a> <a id="1362" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="1368" class="Symbol">=</a> <a id="1370" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="1376" class="Keyword">abstract</a>
  <a id="is-retraction-map-universal-property-bool"></a><a id="1387" href="foundation.universal-property-booleans.html#1387" class="Function">is-retraction-map-universal-property-bool</a> <a id="1429" class="Symbol">:</a>
    <a id="1435" class="Symbol">{</a><a id="1436" href="foundation.universal-property-booleans.html#1436" class="Bound">l</a> <a id="1438" class="Symbol">:</a> <a id="1440" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1445" class="Symbol">}</a> <a id="1447" class="Symbol">{</a><a id="1448" href="foundation.universal-property-booleans.html#1448" class="Bound">A</a> <a id="1450" class="Symbol">:</a> <a id="1452" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1455" href="foundation.universal-property-booleans.html#1436" class="Bound">l</a><a id="1456" class="Symbol">}</a> <a id="1458" class="Symbol">→</a>
    <a id="1464" class="Symbol">(</a><a id="1465" href="foundation.universal-property-booleans.html#722" class="Function">map-universal-property-bool</a> <a id="1493" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1495" class="Symbol">(</a><a id="1496" href="foundation.universal-property-booleans.html#611" class="Function">ev-true-false</a> <a id="1510" href="foundation.universal-property-booleans.html#1448" class="Bound">A</a><a id="1511" class="Symbol">))</a> <a id="1514" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1516" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="1521" href="foundation.universal-property-booleans.html#1387" class="Function">is-retraction-map-universal-property-bool</a> <a id="1563" href="foundation.universal-property-booleans.html#1563" class="Bound">f</a> <a id="1565" class="Symbol">=</a>
    <a id="1571" href="foundation.function-extensionality.html#3905" class="Postulate">eq-htpy</a> <a id="1579" class="Symbol">(</a><a id="1580" href="foundation.universal-property-booleans.html#1109" class="Function">is-retraction-map-universal-property-bool&#39;</a> <a id="1623" href="foundation.universal-property-booleans.html#1563" class="Bound">f</a><a id="1624" class="Symbol">)</a>

<a id="1627" class="Keyword">abstract</a>
  <a id="universal-property-bool"></a><a id="1638" href="foundation.universal-property-booleans.html#1638" class="Function">universal-property-bool</a> <a id="1662" class="Symbol">:</a>
    <a id="1668" class="Symbol">{</a><a id="1669" href="foundation.universal-property-booleans.html#1669" class="Bound">l</a> <a id="1671" class="Symbol">:</a> <a id="1673" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1678" class="Symbol">}</a> <a id="1680" class="Symbol">(</a><a id="1681" href="foundation.universal-property-booleans.html#1681" class="Bound">A</a> <a id="1683" class="Symbol">:</a> <a id="1685" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1688" href="foundation.universal-property-booleans.html#1669" class="Bound">l</a><a id="1689" class="Symbol">)</a> <a id="1691" class="Symbol">→</a>
    <a id="1697" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1706" class="Symbol">(λ</a> <a id="1709" class="Symbol">(</a><a id="1710" href="foundation.universal-property-booleans.html#1710" class="Bound">f</a> <a id="1712" class="Symbol">:</a> <a id="1714" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="1719" class="Symbol">→</a> <a id="1721" href="foundation.universal-property-booleans.html#1681" class="Bound">A</a><a id="1722" class="Symbol">)</a> <a id="1724" class="Symbol">→</a> <a id="1726" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="1731" class="Symbol">(</a><a id="1732" href="foundation.universal-property-booleans.html#1710" class="Bound">f</a> <a id="1734" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a><a id="1738" class="Symbol">)</a> <a id="1740" class="Symbol">(</a><a id="1741" href="foundation.universal-property-booleans.html#1710" class="Bound">f</a> <a id="1743" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a><a id="1748" class="Symbol">))</a>
  <a id="1753" href="foundation.universal-property-booleans.html#1638" class="Function">universal-property-bool</a> <a id="1777" href="foundation.universal-property-booleans.html#1777" class="Bound">A</a> <a id="1779" class="Symbol">=</a>
    <a id="1785" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
      <a id="1814" href="foundation.universal-property-booleans.html#722" class="Function">map-universal-property-bool</a>
      <a id="1848" href="foundation.universal-property-booleans.html#909" class="Function">is-section-map-universal-property-bool</a>
      <a id="1893" href="foundation.universal-property-booleans.html#1387" class="Function">is-retraction-map-universal-property-bool</a>

<a id="ev-true"></a><a id="1936" href="foundation.universal-property-booleans.html#1936" class="Function">ev-true</a> <a id="1944" class="Symbol">:</a>
  <a id="1948" class="Symbol">{</a><a id="1949" href="foundation.universal-property-booleans.html#1949" class="Bound">l</a> <a id="1951" class="Symbol">:</a> <a id="1953" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1958" class="Symbol">}</a> <a id="1960" class="Symbol">{</a><a id="1961" href="foundation.universal-property-booleans.html#1961" class="Bound">A</a> <a id="1963" class="Symbol">:</a> <a id="1965" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1968" href="foundation.universal-property-booleans.html#1949" class="Bound">l</a><a id="1969" class="Symbol">}</a> <a id="1971" class="Symbol">→</a> <a id="1973" class="Symbol">(</a><a id="1974" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="1979" class="Symbol">→</a> <a id="1981" href="foundation.universal-property-booleans.html#1961" class="Bound">A</a><a id="1982" class="Symbol">)</a> <a id="1984" class="Symbol">→</a> <a id="1986" href="foundation.universal-property-booleans.html#1961" class="Bound">A</a>
<a id="1988" href="foundation.universal-property-booleans.html#1936" class="Function">ev-true</a> <a id="1996" href="foundation.universal-property-booleans.html#1996" class="Bound">f</a> <a id="1998" class="Symbol">=</a> <a id="2000" href="foundation.universal-property-booleans.html#1996" class="Bound">f</a> <a id="2002" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a>

<a id="triangle-ev-true"></a><a id="2008" href="foundation.universal-property-booleans.html#2008" class="Function">triangle-ev-true</a> <a id="2025" class="Symbol">:</a>
  <a id="2029" class="Symbol">{</a><a id="2030" href="foundation.universal-property-booleans.html#2030" class="Bound">l</a> <a id="2032" class="Symbol">:</a> <a id="2034" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2039" class="Symbol">}</a> <a id="2041" class="Symbol">(</a><a id="2042" href="foundation.universal-property-booleans.html#2042" class="Bound">A</a> <a id="2044" class="Symbol">:</a> <a id="2046" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2049" href="foundation.universal-property-booleans.html#2030" class="Bound">l</a><a id="2050" class="Symbol">)</a> <a id="2052" class="Symbol">→</a>
  <a id="2056" href="foundation.universal-property-booleans.html#1936" class="Function">ev-true</a> <a id="2064" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="2066" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2070" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2072" href="foundation.universal-property-booleans.html#611" class="Function">ev-true-false</a> <a id="2086" href="foundation.universal-property-booleans.html#2042" class="Bound">A</a>
<a id="2088" href="foundation.universal-property-booleans.html#2008" class="Function">triangle-ev-true</a> <a id="2105" href="foundation.universal-property-booleans.html#2105" class="Bound">A</a> <a id="2107" class="Symbol">=</a> <a id="2109" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>

<a id="2120" class="Comment">{-
aut-bool-bool :
  bool → (bool ≃ bool)
aut-bool-bool true = id-equiv
aut-bool-bool false = equiv-neg-𝟚

bool-aut-bool :
  (bool ≃ bool) → bool
bool-aut-bool e = map-equiv e true

decide-true-false :
  (b : bool) → coproduct (b ＝ true) (b ＝ false)
decide-true-false true = inl refl
decide-true-false false = inr refl

eq-false :
  (b : bool) → (b ≠ true) → (b ＝ false)
eq-false true p = ind-empty (p refl)
eq-false false p = refl

eq-true :
  (b : bool) → b ≠ false → b ＝ true
eq-true true p = refl
eq-true false p = ind-empty (p refl)

Eq-𝟚-eq : (x y : bool) → x ＝ y → Eq-𝟚 x y
Eq-𝟚-eq x .x refl = reflexive-Eq-𝟚 x

eq-false-equiv&#39; :
  (e : bool ≃ bool) → map-equiv e true ＝ true →
  is-decidable (map-equiv e false ＝ false) → map-equiv e false ＝ false
eq-false-equiv&#39; e p (inl q) = q
eq-false-equiv&#39; e p (inr x) =
  ind-empty
    ( Eq-𝟚-eq true false
      ( ap pr1
        ( eq-is-contr&#39;
          ( is-contr-map-is-equiv (is-equiv-map-equiv e) true)
          ( pair true p)
          ( pair false (eq-true (map-equiv e false) x)))))
-}</a>
</pre>