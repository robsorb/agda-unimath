# Floats

<pre class="Agda"><a id="19" class="Keyword">module</a> <a id="26" href="primitives.floats.html" class="Module">primitives.floats</a> <a id="44" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="100" class="Keyword">open</a> <a id="105" class="Keyword">import</a> <a id="112" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="primitives.machine-integers.html" class="Module">primitives.machine-integers</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="primitives.strings.html" class="Module">primitives.strings</a>
</pre>
</details>

## Idea

The `Float` type represents IEEE754 floats. Agda provides primitive functions to
manipulate them. Floats can be written as usual, using dots as separators, e.g.
`3.14`.

## Definitions

<pre class="Agda"><a id="546" class="Keyword">postulate</a>
  <a id="Float"></a><a id="558" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="564" class="Symbol">:</a> <a id="566" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="569" href="Agda.Primitive.html#915" class="Primitive">lzero</a>

<a id="576" class="Symbol">{-#</a> <a id="580" class="Keyword">BUILTIN</a> <a id="588" class="Keyword">FLOAT</a> <a id="594" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="600" class="Symbol">#-}</a>

<a id="605" class="Keyword">primitive</a>
  <a id="617" class="Comment">-- Relations</a>
  <a id="primFloatInequality"></a><a id="632" href="primitives.floats.html#632" class="Primitive">primFloatInequality</a> <a id="652" class="Symbol">:</a> <a id="654" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="660" class="Symbol">→</a> <a id="662" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="668" class="Symbol">→</a> <a id="670" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primFloatEquality"></a><a id="677" href="primitives.floats.html#677" class="Primitive">primFloatEquality</a> <a id="695" class="Symbol">:</a> <a id="697" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="703" class="Symbol">→</a> <a id="705" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="711" class="Symbol">→</a> <a id="713" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primFloatLess"></a><a id="720" href="primitives.floats.html#720" class="Primitive">primFloatLess</a> <a id="734" class="Symbol">:</a> <a id="736" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="742" class="Symbol">→</a> <a id="744" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="750" class="Symbol">→</a> <a id="752" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primFloatIsInfinite"></a><a id="759" href="primitives.floats.html#759" class="Primitive">primFloatIsInfinite</a> <a id="779" class="Symbol">:</a> <a id="781" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="787" class="Symbol">→</a> <a id="789" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primFloatIsNaN"></a><a id="796" href="primitives.floats.html#796" class="Primitive">primFloatIsNaN</a> <a id="811" class="Symbol">:</a> <a id="813" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="819" class="Symbol">→</a> <a id="821" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primFloatIsNegativeZero"></a><a id="828" href="primitives.floats.html#828" class="Primitive">primFloatIsNegativeZero</a> <a id="852" class="Symbol">:</a> <a id="854" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="860" class="Symbol">→</a> <a id="862" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primFloatIsSafeInteger"></a><a id="869" href="primitives.floats.html#869" class="Primitive">primFloatIsSafeInteger</a> <a id="892" class="Symbol">:</a> <a id="894" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="900" class="Symbol">→</a> <a id="902" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="909" class="Comment">-- Conversions</a>
  <a id="primFloatToWord64"></a><a id="926" href="primitives.floats.html#926" class="Primitive">primFloatToWord64</a> <a id="944" class="Symbol">:</a> <a id="946" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="952" class="Symbol">→</a> <a id="954" href="foundation.maybe.html#2157" class="Datatype">Maybe&#39;</a> <a id="961" href="primitives.machine-integers.html#419" class="Postulate">Word64</a>
  <a id="primNatToFloat"></a><a id="970" href="primitives.floats.html#970" class="Primitive">primNatToFloat</a> <a id="985" class="Symbol">:</a> <a id="987" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="989" class="Symbol">→</a> <a id="991" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="999" class="Comment">-- primIntToFloat             : Int → Float</a>
  <a id="1045" class="Comment">-- primFloatRound             : Float → Maybe&#39; Int</a>
  <a id="1098" class="Comment">-- primFloatFloor             : Float → Maybe&#39; Int</a>
  <a id="1151" class="Comment">-- primFloatCeiling           : Float → Maybe&#39; Int</a>
  <a id="1204" class="Comment">-- primFloatToRatio           : Float → (Σ Int λ _ → Int)</a>
  <a id="1264" class="Comment">-- primRatioToFloat           : Int → Int → Float</a>
  <a id="1316" class="Comment">-- primFloatDecode            : Float → Maybe&#39; (Σ Int λ _ → Int)</a>
  <a id="1383" class="Comment">-- primFloatEncode            : Int → Int → Maybe&#39; Float</a>
  <a id="primShowFloat"></a><a id="1442" href="primitives.floats.html#1442" class="Primitive">primShowFloat</a> <a id="1456" class="Symbol">:</a> <a id="1458" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1464" class="Symbol">→</a> <a id="1466" href="primitives.strings.html#581" class="Postulate">String</a>
  <a id="1475" class="Comment">-- Operations</a>
  <a id="primFloatPlus"></a><a id="1491" href="primitives.floats.html#1491" class="Primitive">primFloatPlus</a> <a id="1505" class="Symbol">:</a> <a id="1507" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1513" class="Symbol">→</a> <a id="1515" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1521" class="Symbol">→</a> <a id="1523" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatMinus"></a><a id="1531" href="primitives.floats.html#1531" class="Primitive">primFloatMinus</a> <a id="1546" class="Symbol">:</a> <a id="1548" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1554" class="Symbol">→</a> <a id="1556" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1562" class="Symbol">→</a> <a id="1564" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatTimes"></a><a id="1572" href="primitives.floats.html#1572" class="Primitive">primFloatTimes</a> <a id="1587" class="Symbol">:</a> <a id="1589" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1595" class="Symbol">→</a> <a id="1597" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1603" class="Symbol">→</a> <a id="1605" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatDiv"></a><a id="1613" href="primitives.floats.html#1613" class="Primitive">primFloatDiv</a> <a id="1626" class="Symbol">:</a> <a id="1628" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1634" class="Symbol">→</a> <a id="1636" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1642" class="Symbol">→</a> <a id="1644" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatPow"></a><a id="1652" href="primitives.floats.html#1652" class="Primitive">primFloatPow</a> <a id="1665" class="Symbol">:</a> <a id="1667" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1673" class="Symbol">→</a> <a id="1675" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1681" class="Symbol">→</a> <a id="1683" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatNegate"></a><a id="1691" href="primitives.floats.html#1691" class="Primitive">primFloatNegate</a> <a id="1707" class="Symbol">:</a> <a id="1709" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1715" class="Symbol">→</a> <a id="1717" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatSqrt"></a><a id="1725" href="primitives.floats.html#1725" class="Primitive">primFloatSqrt</a> <a id="1739" class="Symbol">:</a> <a id="1741" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1747" class="Symbol">→</a> <a id="1749" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatExp"></a><a id="1757" href="primitives.floats.html#1757" class="Primitive">primFloatExp</a> <a id="1770" class="Symbol">:</a> <a id="1772" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1778" class="Symbol">→</a> <a id="1780" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatLog"></a><a id="1788" href="primitives.floats.html#1788" class="Primitive">primFloatLog</a> <a id="1801" class="Symbol">:</a> <a id="1803" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1809" class="Symbol">→</a> <a id="1811" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatSin"></a><a id="1819" href="primitives.floats.html#1819" class="Primitive">primFloatSin</a> <a id="1832" class="Symbol">:</a> <a id="1834" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1840" class="Symbol">→</a> <a id="1842" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatCos"></a><a id="1850" href="primitives.floats.html#1850" class="Primitive">primFloatCos</a> <a id="1863" class="Symbol">:</a> <a id="1865" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1871" class="Symbol">→</a> <a id="1873" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatTan"></a><a id="1881" href="primitives.floats.html#1881" class="Primitive">primFloatTan</a> <a id="1894" class="Symbol">:</a> <a id="1896" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1902" class="Symbol">→</a> <a id="1904" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatASin"></a><a id="1912" href="primitives.floats.html#1912" class="Primitive">primFloatASin</a> <a id="1926" class="Symbol">:</a> <a id="1928" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1934" class="Symbol">→</a> <a id="1936" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatACos"></a><a id="1944" href="primitives.floats.html#1944" class="Primitive">primFloatACos</a> <a id="1958" class="Symbol">:</a> <a id="1960" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1966" class="Symbol">→</a> <a id="1968" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatATan"></a><a id="1976" href="primitives.floats.html#1976" class="Primitive">primFloatATan</a> <a id="1990" class="Symbol">:</a> <a id="1992" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="1998" class="Symbol">→</a> <a id="2000" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatATan2"></a><a id="2008" href="primitives.floats.html#2008" class="Primitive">primFloatATan2</a> <a id="2023" class="Symbol">:</a> <a id="2025" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="2031" class="Symbol">→</a> <a id="2033" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="2039" class="Symbol">→</a> <a id="2041" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatSinh"></a><a id="2049" href="primitives.floats.html#2049" class="Primitive">primFloatSinh</a> <a id="2063" class="Symbol">:</a> <a id="2065" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="2071" class="Symbol">→</a> <a id="2073" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatCosh"></a><a id="2081" href="primitives.floats.html#2081" class="Primitive">primFloatCosh</a> <a id="2095" class="Symbol">:</a> <a id="2097" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="2103" class="Symbol">→</a> <a id="2105" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatTanh"></a><a id="2113" href="primitives.floats.html#2113" class="Primitive">primFloatTanh</a> <a id="2127" class="Symbol">:</a> <a id="2129" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="2135" class="Symbol">→</a> <a id="2137" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatASinh"></a><a id="2145" href="primitives.floats.html#2145" class="Primitive">primFloatASinh</a> <a id="2160" class="Symbol">:</a> <a id="2162" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="2168" class="Symbol">→</a> <a id="2170" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatACosh"></a><a id="2178" href="primitives.floats.html#2178" class="Primitive">primFloatACosh</a> <a id="2193" class="Symbol">:</a> <a id="2195" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="2201" class="Symbol">→</a> <a id="2203" href="primitives.floats.html#558" class="Postulate">Float</a>
  <a id="primFloatATanh"></a><a id="2211" href="primitives.floats.html#2211" class="Primitive">primFloatATanh</a> <a id="2226" class="Symbol">:</a> <a id="2228" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="2234" class="Symbol">→</a> <a id="2236" href="primitives.floats.html#558" class="Postulate">Float</a>
</pre>