# The Zariski locale

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="commutative-algebra.zariski-locale.html" class="Module">commutative-algebra.zariski-locale</a> <a id="73" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="129" class="Keyword">open</a> <a id="134" class="Keyword">import</a> <a id="141" href="commutative-algebra.commutative-rings.html" class="Module">commutative-algebra.commutative-rings</a>
<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="commutative-algebra.intersections-radical-ideals-commutative-rings.html" class="Module">commutative-algebra.intersections-radical-ideals-commutative-rings</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="commutative-algebra.joins-radical-ideals-commutative-rings.html" class="Module">commutative-algebra.joins-radical-ideals-commutative-rings</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="commutative-algebra.poset-of-radical-ideals-commutative-rings.html" class="Module">commutative-algebra.poset-of-radical-ideals-commutative-rings</a>

<a id="404" class="Keyword">open</a> <a id="409" class="Keyword">import</a> <a id="416" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="444" class="Keyword">open</a> <a id="449" class="Keyword">import</a> <a id="456" href="order-theory.large-frames.html" class="Module">order-theory.large-frames</a>
<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="order-theory.large-locales.html" class="Module">order-theory.large-locales</a>
</pre>
</details>

## Idea

The **Zariski locale** of a
[commutative ring](commutative-algebra.commutative-rings.md) `A` is the
[large locale](order-theory.large-locales.md) consisting of
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md) of
`A`. Our proof of the fact that meets distribute over arbitrary joins uses the
fact that the intersection `I ∩ J` of radical ideals is equivalently described
as the radical ideal `√ IJ` of the
[product ideal](commutative-algebra.products-ideals-commutative-rings.md).

## Definition

### The Zariski frame

<pre class="Agda"><a id="1099" class="Keyword">module</a> <a id="1106" href="commutative-algebra.zariski-locale.html#1106" class="Module">_</a>
  <a id="1110" class="Symbol">{</a><a id="1111" href="commutative-algebra.zariski-locale.html#1111" class="Bound">l1</a> <a id="1114" class="Symbol">:</a> <a id="1116" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1121" class="Symbol">}</a> <a id="1123" class="Symbol">(</a><a id="1124" href="commutative-algebra.zariski-locale.html#1124" class="Bound">A</a> <a id="1126" class="Symbol">:</a> <a id="1128" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="1145" href="commutative-algebra.zariski-locale.html#1111" class="Bound">l1</a><a id="1147" class="Symbol">)</a>
  <a id="1151" class="Keyword">where</a>

  <a id="1160" href="commutative-algebra.zariski-locale.html#1160" class="Function">zariski-frame-Commutative-Ring</a> <a id="1191" class="Symbol">:</a>
    <a id="1197" href="order-theory.large-frames.html#1062" class="Record">Large-Frame</a> <a id="1209" class="Symbol">(λ</a> <a id="1212" href="commutative-algebra.zariski-locale.html#1212" class="Bound">l2</a> <a id="1215" class="Symbol">→</a> <a id="1217" href="commutative-algebra.zariski-locale.html#1111" class="Bound">l1</a> <a id="1220" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1222" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1227" href="commutative-algebra.zariski-locale.html#1212" class="Bound">l2</a><a id="1229" class="Symbol">)</a> <a id="1231" class="Symbol">(λ</a> <a id="1234" href="commutative-algebra.zariski-locale.html#1234" class="Bound">l2</a> <a id="1237" href="commutative-algebra.zariski-locale.html#1237" class="Bound">l3</a> <a id="1240" class="Symbol">→</a> <a id="1242" href="commutative-algebra.zariski-locale.html#1111" class="Bound">l1</a> <a id="1245" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1247" href="commutative-algebra.zariski-locale.html#1234" class="Bound">l2</a> <a id="1250" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1252" href="commutative-algebra.zariski-locale.html#1237" class="Bound">l3</a><a id="1254" class="Symbol">)</a> <a id="1256" href="commutative-algebra.zariski-locale.html#1111" class="Bound">l1</a>
  <a id="1261" href="order-theory.large-frames.html#1195" class="Field">large-poset-Large-Frame</a>
    <a id="1289" href="commutative-algebra.zariski-locale.html#1160" class="Function">zariski-frame-Commutative-Ring</a> <a id="1320" class="Symbol">=</a>
    <a id="1326" href="commutative-algebra.poset-of-radical-ideals-commutative-rings.html#4564" class="Function">radical-ideal-Commutative-Ring-Large-Poset</a> <a id="1369" href="commutative-algebra.zariski-locale.html#1124" class="Bound">A</a>
  <a id="1373" href="order-theory.large-frames.html#1247" class="Field">is-large-meet-semilattice-Large-Frame</a>
    <a id="1415" href="commutative-algebra.zariski-locale.html#1160" class="Function">zariski-frame-Commutative-Ring</a> <a id="1446" class="Symbol">=</a>
    <a id="1452" href="commutative-algebra.intersections-radical-ideals-commutative-rings.html#4617" class="Function">is-large-meet-semilattice-radical-ideal-Commutative-Ring</a> <a id="1509" href="commutative-algebra.zariski-locale.html#1124" class="Bound">A</a>
  <a id="1513" href="order-theory.large-frames.html#1359" class="Field">is-large-suplattice-Large-Frame</a> <a id="1545" href="commutative-algebra.zariski-locale.html#1160" class="Function">zariski-frame-Commutative-Ring</a> <a id="1576" class="Symbol">=</a>
    <a id="1582" href="commutative-algebra.joins-radical-ideals-commutative-rings.html#6068" class="Function">is-large-suplattice-radical-ideal-Commutative-Ring</a> <a id="1633" href="commutative-algebra.zariski-locale.html#1124" class="Bound">A</a>
  <a id="1637" href="order-theory.large-frames.html#1461" class="Field">distributive-meet-sup-Large-Frame</a> <a id="1671" href="commutative-algebra.zariski-locale.html#1160" class="Function">zariski-frame-Commutative-Ring</a> <a id="1702" class="Symbol">=</a>
    <a id="1708" href="commutative-algebra.joins-radical-ideals-commutative-rings.html#24068" class="Function">distributive-intersection-join-family-of-radical-ideals-Commutative-Ring</a> <a id="1781" href="commutative-algebra.zariski-locale.html#1124" class="Bound">A</a>
</pre>
### The Zariski locale

<pre class="Agda"><a id="1820" class="Keyword">module</a> <a id="1827" href="commutative-algebra.zariski-locale.html#1827" class="Module">_</a>
  <a id="1831" class="Symbol">{</a><a id="1832" href="commutative-algebra.zariski-locale.html#1832" class="Bound">l1</a> <a id="1835" class="Symbol">:</a> <a id="1837" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1842" class="Symbol">}</a> <a id="1844" class="Symbol">(</a><a id="1845" href="commutative-algebra.zariski-locale.html#1845" class="Bound">A</a> <a id="1847" class="Symbol">:</a> <a id="1849" href="commutative-algebra.commutative-rings.html#2100" class="Function">Commutative-Ring</a> <a id="1866" href="commutative-algebra.zariski-locale.html#1832" class="Bound">l1</a><a id="1868" class="Symbol">)</a>
  <a id="1872" class="Keyword">where</a>

  <a id="1881" href="commutative-algebra.zariski-locale.html#1881" class="Function">zariski-locale-Commutative-Ring</a> <a id="1913" class="Symbol">:</a>
    <a id="1919" href="order-theory.large-locales.html#1051" class="Function">Large-Locale</a> <a id="1932" class="Symbol">(λ</a> <a id="1935" href="commutative-algebra.zariski-locale.html#1935" class="Bound">l2</a> <a id="1938" class="Symbol">→</a> <a id="1940" href="commutative-algebra.zariski-locale.html#1832" class="Bound">l1</a> <a id="1943" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1945" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1950" href="commutative-algebra.zariski-locale.html#1935" class="Bound">l2</a><a id="1952" class="Symbol">)</a> <a id="1954" class="Symbol">(λ</a> <a id="1957" href="commutative-algebra.zariski-locale.html#1957" class="Bound">l2</a> <a id="1960" href="commutative-algebra.zariski-locale.html#1960" class="Bound">l3</a> <a id="1963" class="Symbol">→</a> <a id="1965" href="commutative-algebra.zariski-locale.html#1832" class="Bound">l1</a> <a id="1968" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1970" href="commutative-algebra.zariski-locale.html#1957" class="Bound">l2</a> <a id="1973" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1975" href="commutative-algebra.zariski-locale.html#1960" class="Bound">l3</a><a id="1977" class="Symbol">)</a> <a id="1979" href="commutative-algebra.zariski-locale.html#1832" class="Bound">l1</a>
  <a id="1984" href="commutative-algebra.zariski-locale.html#1881" class="Function">zariski-locale-Commutative-Ring</a> <a id="2016" class="Symbol">=</a> <a id="2018" href="commutative-algebra.zariski-locale.html#1160" class="Function">zariski-frame-Commutative-Ring</a> <a id="2049" href="commutative-algebra.zariski-locale.html#1845" class="Bound">A</a>
</pre>