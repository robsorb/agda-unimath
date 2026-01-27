# Top elements in large posets

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="order-theory.top-elements-large-posets.html" class="Module">order-theory.top-elements-large-posets</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="order-theory.dependent-products-large-posets.html" class="Module">order-theory.dependent-products-large-posets</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>
</pre>
</details>

## Idea

We say that a [large poset](order-theory.large-posets.md) `P` has a
{{#concept "largest element" Disambiguation="in a large poset" WD="maximal and minimal elements" WDID=Q1475294 Agda=is-top-element-Large-Poset}}
if it comes equipped with an element `t : type-Large-Poset P lzero` such that
`x ≤ t` holds for every `x : P`

## Definition

### The predicate on elements of posets of being a top element

<pre class="Agda"><a id="715" class="Keyword">module</a> <a id="722" href="order-theory.top-elements-large-posets.html#722" class="Module">_</a>
  <a id="726" class="Symbol">{</a><a id="727" href="order-theory.top-elements-large-posets.html#727" class="Bound">α</a> <a id="729" class="Symbol">:</a> <a id="731" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="737" class="Symbol">→</a> <a id="739" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="744" class="Symbol">}</a> <a id="746" class="Symbol">{</a><a id="747" href="order-theory.top-elements-large-posets.html#747" class="Bound">β</a> <a id="749" class="Symbol">:</a> <a id="751" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="757" class="Symbol">→</a> <a id="759" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="765" class="Symbol">→</a> <a id="767" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="772" class="Symbol">}</a> <a id="774" class="Symbol">(</a><a id="775" href="order-theory.top-elements-large-posets.html#775" class="Bound">P</a> <a id="777" class="Symbol">:</a> <a id="779" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="791" href="order-theory.top-elements-large-posets.html#727" class="Bound">α</a> <a id="793" href="order-theory.top-elements-large-posets.html#747" class="Bound">β</a><a id="794" class="Symbol">)</a>
  <a id="798" class="Keyword">where</a>

  <a id="807" href="order-theory.top-elements-large-posets.html#807" class="Function">is-top-element-Large-Poset</a> <a id="834" class="Symbol">:</a>
    <a id="840" class="Symbol">{</a><a id="841" href="order-theory.top-elements-large-posets.html#841" class="Bound">l1</a> <a id="844" class="Symbol">:</a> <a id="846" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="851" class="Symbol">}</a> <a id="853" class="Symbol">→</a> <a id="855" href="order-theory.large-posets.html#1534" class="Function">type-Large-Poset</a> <a id="872" href="order-theory.top-elements-large-posets.html#775" class="Bound">P</a> <a id="874" href="order-theory.top-elements-large-posets.html#841" class="Bound">l1</a> <a id="877" class="Symbol">→</a> <a id="879" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="885" href="order-theory.top-elements-large-posets.html#807" class="Function">is-top-element-Large-Poset</a> <a id="912" href="order-theory.top-elements-large-posets.html#912" class="Bound">x</a> <a id="914" class="Symbol">=</a>
    <a id="920" class="Symbol">{</a><a id="921" href="order-theory.top-elements-large-posets.html#921" class="Bound">l</a> <a id="923" class="Symbol">:</a> <a id="925" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="930" class="Symbol">}</a> <a id="932" class="Symbol">(</a><a id="933" href="order-theory.top-elements-large-posets.html#933" class="Bound">y</a> <a id="935" class="Symbol">:</a> <a id="937" href="order-theory.large-posets.html#1534" class="Function">type-Large-Poset</a> <a id="954" href="order-theory.top-elements-large-posets.html#775" class="Bound">P</a> <a id="956" href="order-theory.top-elements-large-posets.html#921" class="Bound">l</a><a id="957" class="Symbol">)</a> <a id="959" class="Symbol">→</a> <a id="961" href="order-theory.large-posets.html#1798" class="Function">leq-Large-Poset</a> <a id="977" href="order-theory.top-elements-large-posets.html#775" class="Bound">P</a> <a id="979" href="order-theory.top-elements-large-posets.html#933" class="Bound">y</a> <a id="981" href="order-theory.top-elements-large-posets.html#912" class="Bound">x</a>
</pre>
### The predicate on posets of having a top element

<pre class="Agda"><a id="1049" class="Keyword">module</a> <a id="1056" href="order-theory.top-elements-large-posets.html#1056" class="Module">_</a>
  <a id="1060" class="Symbol">{</a><a id="1061" href="order-theory.top-elements-large-posets.html#1061" class="Bound">α</a> <a id="1063" class="Symbol">:</a> <a id="1065" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1071" class="Symbol">→</a> <a id="1073" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1078" class="Symbol">}</a> <a id="1080" class="Symbol">{</a><a id="1081" href="order-theory.top-elements-large-posets.html#1081" class="Bound">β</a> <a id="1083" class="Symbol">:</a> <a id="1085" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1091" class="Symbol">→</a> <a id="1093" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1099" class="Symbol">→</a> <a id="1101" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1106" class="Symbol">}</a>
  <a id="1110" class="Symbol">(</a><a id="1111" href="order-theory.top-elements-large-posets.html#1111" class="Bound">P</a> <a id="1113" class="Symbol">:</a> <a id="1115" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1127" href="order-theory.top-elements-large-posets.html#1061" class="Bound">α</a> <a id="1129" href="order-theory.top-elements-large-posets.html#1081" class="Bound">β</a><a id="1130" class="Symbol">)</a>
  <a id="1134" class="Keyword">where</a>

  <a id="1143" class="Keyword">record</a>
    <a id="1154" href="order-theory.top-elements-large-posets.html#1154" class="Record">has-top-element-Large-Poset</a> <a id="1182" class="Symbol">:</a> <a id="1184" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
    <a id="1192" class="Keyword">where</a>
    <a id="1202" class="Keyword">field</a>
      <a id="1214" href="order-theory.top-elements-large-posets.html#1214" class="Field">top-has-top-element-Large-Poset</a> <a id="1246" class="Symbol">:</a>
        <a id="1256" href="order-theory.large-posets.html#1534" class="Function">type-Large-Poset</a> <a id="1273" href="order-theory.top-elements-large-posets.html#1111" class="Bound">P</a> <a id="1275" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
      <a id="1287" href="order-theory.top-elements-large-posets.html#1287" class="Field">is-top-element-top-has-top-element-Large-Poset</a> <a id="1334" class="Symbol">:</a>
        <a id="1344" href="order-theory.top-elements-large-posets.html#807" class="Function">is-top-element-Large-Poset</a> <a id="1371" href="order-theory.top-elements-large-posets.html#1111" class="Bound">P</a> <a id="1373" href="order-theory.top-elements-large-posets.html#1214" class="Field">top-has-top-element-Large-Poset</a>

  <a id="1408" class="Keyword">open</a> <a id="1413" href="order-theory.top-elements-large-posets.html#1154" class="Module">has-top-element-Large-Poset</a> <a id="1441" class="Keyword">public</a>
</pre>
## Properties

### If `P` is a family of large posets, then `Π-Large-Poset P` has a largest element

<pre class="Agda"><a id="1562" class="Keyword">module</a> <a id="1569" href="order-theory.top-elements-large-posets.html#1569" class="Module">_</a>
  <a id="1573" class="Symbol">{</a><a id="1574" href="order-theory.top-elements-large-posets.html#1574" class="Bound">α</a> <a id="1576" class="Symbol">:</a> <a id="1578" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1584" class="Symbol">→</a> <a id="1586" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1591" class="Symbol">}</a> <a id="1593" class="Symbol">{</a><a id="1594" href="order-theory.top-elements-large-posets.html#1594" class="Bound">β</a> <a id="1596" class="Symbol">:</a> <a id="1598" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1604" class="Symbol">→</a> <a id="1606" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1612" class="Symbol">→</a> <a id="1614" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1619" class="Symbol">}</a>
  <a id="1623" class="Symbol">{</a><a id="1624" href="order-theory.top-elements-large-posets.html#1624" class="Bound">l1</a> <a id="1627" class="Symbol">:</a> <a id="1629" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1634" class="Symbol">}</a> <a id="1636" class="Symbol">{</a><a id="1637" href="order-theory.top-elements-large-posets.html#1637" class="Bound">I</a> <a id="1639" class="Symbol">:</a> <a id="1641" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1644" href="order-theory.top-elements-large-posets.html#1624" class="Bound">l1</a><a id="1646" class="Symbol">}</a> <a id="1648" class="Symbol">(</a><a id="1649" href="order-theory.top-elements-large-posets.html#1649" class="Bound">P</a> <a id="1651" class="Symbol">:</a> <a id="1653" href="order-theory.top-elements-large-posets.html#1637" class="Bound">I</a> <a id="1655" class="Symbol">→</a> <a id="1657" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1669" href="order-theory.top-elements-large-posets.html#1574" class="Bound">α</a> <a id="1671" href="order-theory.top-elements-large-posets.html#1594" class="Bound">β</a><a id="1672" class="Symbol">)</a>
  <a id="1676" class="Keyword">where</a>

  <a id="1685" href="order-theory.top-elements-large-posets.html#1685" class="Function">has-top-element-Π-Large-Poset</a> <a id="1715" class="Symbol">:</a>
    <a id="1721" class="Symbol">((</a><a id="1723" href="order-theory.top-elements-large-posets.html#1723" class="Bound">i</a> <a id="1725" class="Symbol">:</a> <a id="1727" href="order-theory.top-elements-large-posets.html#1637" class="Bound">I</a><a id="1728" class="Symbol">)</a> <a id="1730" class="Symbol">→</a> <a id="1732" href="order-theory.top-elements-large-posets.html#1154" class="Record">has-top-element-Large-Poset</a> <a id="1760" class="Symbol">(</a><a id="1761" href="order-theory.top-elements-large-posets.html#1649" class="Bound">P</a> <a id="1763" href="order-theory.top-elements-large-posets.html#1723" class="Bound">i</a><a id="1764" class="Symbol">))</a> <a id="1767" class="Symbol">→</a>
    <a id="1773" href="order-theory.top-elements-large-posets.html#1154" class="Record">has-top-element-Large-Poset</a> <a id="1801" class="Symbol">(</a><a id="1802" href="order-theory.dependent-products-large-posets.html#2315" class="Function">Π-Large-Poset</a> <a id="1816" href="order-theory.top-elements-large-posets.html#1649" class="Bound">P</a><a id="1817" class="Symbol">)</a>
  <a id="1821" href="order-theory.top-elements-large-posets.html#1214" class="Field">top-has-top-element-Large-Poset</a>
    <a id="1857" class="Symbol">(</a> <a id="1859" href="order-theory.top-elements-large-posets.html#1685" class="Function">has-top-element-Π-Large-Poset</a> <a id="1889" href="order-theory.top-elements-large-posets.html#1889" class="Bound">H</a><a id="1890" class="Symbol">)</a> <a id="1892" href="order-theory.top-elements-large-posets.html#1892" class="Bound">i</a> <a id="1894" class="Symbol">=</a>
    <a id="1900" href="order-theory.top-elements-large-posets.html#1214" class="Field">top-has-top-element-Large-Poset</a> <a id="1932" class="Symbol">(</a><a id="1933" href="order-theory.top-elements-large-posets.html#1889" class="Bound">H</a> <a id="1935" href="order-theory.top-elements-large-posets.html#1892" class="Bound">i</a><a id="1936" class="Symbol">)</a>
  <a id="1940" href="order-theory.top-elements-large-posets.html#1287" class="Field">is-top-element-top-has-top-element-Large-Poset</a>
    <a id="1991" class="Symbol">(</a> <a id="1993" href="order-theory.top-elements-large-posets.html#1685" class="Function">has-top-element-Π-Large-Poset</a> <a id="2023" href="order-theory.top-elements-large-posets.html#2023" class="Bound">H</a><a id="2024" class="Symbol">)</a> <a id="2026" href="order-theory.top-elements-large-posets.html#2026" class="Bound">x</a> <a id="2028" href="order-theory.top-elements-large-posets.html#2028" class="Bound">i</a> <a id="2030" class="Symbol">=</a>
    <a id="2036" href="order-theory.top-elements-large-posets.html#1287" class="Field">is-top-element-top-has-top-element-Large-Poset</a> <a id="2083" class="Symbol">(</a><a id="2084" href="order-theory.top-elements-large-posets.html#2023" class="Bound">H</a> <a id="2086" href="order-theory.top-elements-large-posets.html#2028" class="Bound">i</a><a id="2087" class="Symbol">)</a> <a id="2089" class="Symbol">(</a><a id="2090" href="order-theory.top-elements-large-posets.html#2026" class="Bound">x</a> <a id="2092" href="order-theory.top-elements-large-posets.html#2028" class="Bound">i</a><a id="2093" class="Symbol">)</a>
</pre>