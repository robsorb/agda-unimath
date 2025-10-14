# Embedding maps between precategories

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="category-theory.embedding-maps-precategories.html" class="Module">category-theory.embedding-maps-precategories</a> <a id="101" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="category-theory.fully-faithful-maps-precategories.html" class="Module">category-theory.fully-faithful-maps-precategories</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="category-theory.maps-precategories.html" class="Module">category-theory.maps-precategories</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="423" class="Keyword">open</a> <a id="428" class="Keyword">import</a> <a id="435" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A [map](category-theory.maps-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is an **embedding
map** if it's an [embedding](foundation-core.embeddings.md) on objects and
[fully faithful](category-theory.fully-faithful-maps-precategories.md). Hence
embedding maps are maps that are embeddings on objects and
[equivalences](foundation-core.equivalences.md) on
hom-[sets](foundation-core.sets.md).

Note that for a map of precategories to be called _an embedding_, it must also
be a [functor](category-theory.functors-precategories.md). This notion is
considered in
[`category-theory.embeddings-precategories`](category-theory.embeddings-precategories.md).

## Definition

### The predicate on maps between precategories of being an embedding map

<pre class="Agda"><a id="1281" class="Keyword">module</a> <a id="1288" href="category-theory.embedding-maps-precategories.html#1288" class="Module">_</a>
  <a id="1292" class="Symbol">{</a><a id="1293" href="category-theory.embedding-maps-precategories.html#1293" class="Bound">l1</a> <a id="1296" href="category-theory.embedding-maps-precategories.html#1296" class="Bound">l2</a> <a id="1299" href="category-theory.embedding-maps-precategories.html#1299" class="Bound">l3</a> <a id="1302" href="category-theory.embedding-maps-precategories.html#1302" class="Bound">l4</a> <a id="1305" class="Symbol">:</a> <a id="1307" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1312" class="Symbol">}</a>
  <a id="1316" class="Symbol">(</a><a id="1317" href="category-theory.embedding-maps-precategories.html#1317" class="Bound">C</a> <a id="1319" class="Symbol">:</a> <a id="1321" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1333" href="category-theory.embedding-maps-precategories.html#1293" class="Bound">l1</a> <a id="1336" href="category-theory.embedding-maps-precategories.html#1296" class="Bound">l2</a><a id="1338" class="Symbol">)</a>
  <a id="1342" class="Symbol">(</a><a id="1343" href="category-theory.embedding-maps-precategories.html#1343" class="Bound">D</a> <a id="1345" class="Symbol">:</a> <a id="1347" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1359" href="category-theory.embedding-maps-precategories.html#1299" class="Bound">l3</a> <a id="1362" href="category-theory.embedding-maps-precategories.html#1302" class="Bound">l4</a><a id="1364" class="Symbol">)</a>
  <a id="1368" class="Symbol">(</a><a id="1369" href="category-theory.embedding-maps-precategories.html#1369" class="Bound">F</a> <a id="1371" class="Symbol">:</a> <a id="1373" href="category-theory.maps-precategories.html#1302" class="Function">map-Precategory</a> <a id="1389" href="category-theory.embedding-maps-precategories.html#1317" class="Bound">C</a> <a id="1391" href="category-theory.embedding-maps-precategories.html#1343" class="Bound">D</a><a id="1392" class="Symbol">)</a>
  <a id="1396" class="Keyword">where</a>

  <a id="1405" href="category-theory.embedding-maps-precategories.html#1405" class="Function">is-embedding-map-prop-map-Precategory</a> <a id="1443" class="Symbol">:</a> <a id="1445" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1450" class="Symbol">(</a><a id="1451" href="category-theory.embedding-maps-precategories.html#1293" class="Bound">l1</a> <a id="1454" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1456" href="category-theory.embedding-maps-precategories.html#1296" class="Bound">l2</a> <a id="1459" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1461" href="category-theory.embedding-maps-precategories.html#1299" class="Bound">l3</a> <a id="1464" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1466" href="category-theory.embedding-maps-precategories.html#1302" class="Bound">l4</a><a id="1468" class="Symbol">)</a>
  <a id="1472" href="category-theory.embedding-maps-precategories.html#1405" class="Function">is-embedding-map-prop-map-Precategory</a> <a id="1510" class="Symbol">=</a>
    <a id="1516" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="1535" class="Symbol">(</a> <a id="1537" href="foundation.embeddings.html#1620" class="Function">is-emb-Prop</a> <a id="1549" class="Symbol">(</a><a id="1550" href="category-theory.maps-precategories.html#1456" class="Function">obj-map-Precategory</a> <a id="1570" href="category-theory.embedding-maps-precategories.html#1317" class="Bound">C</a> <a id="1572" href="category-theory.embedding-maps-precategories.html#1343" class="Bound">D</a> <a id="1574" href="category-theory.embedding-maps-precategories.html#1369" class="Bound">F</a><a id="1575" class="Symbol">))</a>
      <a id="1584" class="Symbol">(</a> <a id="1586" href="category-theory.fully-faithful-maps-precategories.html#1675" class="Function">is-fully-faithful-prop-map-Precategory</a> <a id="1625" href="category-theory.embedding-maps-precategories.html#1317" class="Bound">C</a> <a id="1627" href="category-theory.embedding-maps-precategories.html#1343" class="Bound">D</a> <a id="1629" href="category-theory.embedding-maps-precategories.html#1369" class="Bound">F</a><a id="1630" class="Symbol">)</a>

  <a id="1635" href="category-theory.embedding-maps-precategories.html#1635" class="Function">is-embedding-map-map-Precategory</a> <a id="1668" class="Symbol">:</a> <a id="1670" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1673" class="Symbol">(</a><a id="1674" href="category-theory.embedding-maps-precategories.html#1293" class="Bound">l1</a> <a id="1677" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1679" href="category-theory.embedding-maps-precategories.html#1296" class="Bound">l2</a> <a id="1682" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1684" href="category-theory.embedding-maps-precategories.html#1299" class="Bound">l3</a> <a id="1687" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1689" href="category-theory.embedding-maps-precategories.html#1302" class="Bound">l4</a><a id="1691" class="Symbol">)</a>
  <a id="1695" href="category-theory.embedding-maps-precategories.html#1635" class="Function">is-embedding-map-map-Precategory</a> <a id="1728" class="Symbol">=</a>
    <a id="1734" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1744" href="category-theory.embedding-maps-precategories.html#1405" class="Function">is-embedding-map-prop-map-Precategory</a>

  <a id="1785" href="category-theory.embedding-maps-precategories.html#1785" class="Function">is-prop-is-embedding-map-map-Precategory</a> <a id="1826" class="Symbol">:</a>
    <a id="1832" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1840" href="category-theory.embedding-maps-precategories.html#1635" class="Function">is-embedding-map-map-Precategory</a>
  <a id="1875" href="category-theory.embedding-maps-precategories.html#1785" class="Function">is-prop-is-embedding-map-map-Precategory</a> <a id="1916" class="Symbol">=</a>
    <a id="1922" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1940" href="category-theory.embedding-maps-precategories.html#1405" class="Function">is-embedding-map-prop-map-Precategory</a>
</pre>
### The type of embedding maps between precategories

<pre class="Agda"><a id="2045" class="Keyword">module</a> <a id="2052" href="category-theory.embedding-maps-precategories.html#2052" class="Module">_</a>
  <a id="2056" class="Symbol">{</a><a id="2057" href="category-theory.embedding-maps-precategories.html#2057" class="Bound">l1</a> <a id="2060" href="category-theory.embedding-maps-precategories.html#2060" class="Bound">l2</a> <a id="2063" href="category-theory.embedding-maps-precategories.html#2063" class="Bound">l3</a> <a id="2066" href="category-theory.embedding-maps-precategories.html#2066" class="Bound">l4</a> <a id="2069" class="Symbol">:</a> <a id="2071" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2076" class="Symbol">}</a>
  <a id="2080" class="Symbol">(</a><a id="2081" href="category-theory.embedding-maps-precategories.html#2081" class="Bound">C</a> <a id="2083" class="Symbol">:</a> <a id="2085" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="2097" href="category-theory.embedding-maps-precategories.html#2057" class="Bound">l1</a> <a id="2100" href="category-theory.embedding-maps-precategories.html#2060" class="Bound">l2</a><a id="2102" class="Symbol">)</a>
  <a id="2106" class="Symbol">(</a><a id="2107" href="category-theory.embedding-maps-precategories.html#2107" class="Bound">D</a> <a id="2109" class="Symbol">:</a> <a id="2111" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="2123" href="category-theory.embedding-maps-precategories.html#2063" class="Bound">l3</a> <a id="2126" href="category-theory.embedding-maps-precategories.html#2066" class="Bound">l4</a><a id="2128" class="Symbol">)</a>
  <a id="2132" class="Keyword">where</a>

  <a id="2141" href="category-theory.embedding-maps-precategories.html#2141" class="Function">embedding-map-Precategory</a> <a id="2167" class="Symbol">:</a> <a id="2169" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2172" class="Symbol">(</a><a id="2173" href="category-theory.embedding-maps-precategories.html#2057" class="Bound">l1</a> <a id="2176" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2178" href="category-theory.embedding-maps-precategories.html#2060" class="Bound">l2</a> <a id="2181" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2183" href="category-theory.embedding-maps-precategories.html#2063" class="Bound">l3</a> <a id="2186" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2188" href="category-theory.embedding-maps-precategories.html#2066" class="Bound">l4</a><a id="2190" class="Symbol">)</a>
  <a id="2194" href="category-theory.embedding-maps-precategories.html#2141" class="Function">embedding-map-Precategory</a> <a id="2220" class="Symbol">=</a>
    <a id="2226" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2228" class="Symbol">(</a><a id="2229" href="category-theory.maps-precategories.html#1302" class="Function">map-Precategory</a> <a id="2245" href="category-theory.embedding-maps-precategories.html#2081" class="Bound">C</a> <a id="2247" href="category-theory.embedding-maps-precategories.html#2107" class="Bound">D</a><a id="2248" class="Symbol">)</a> <a id="2250" class="Symbol">(</a><a id="2251" href="category-theory.embedding-maps-precategories.html#1635" class="Function">is-embedding-map-map-Precategory</a> <a id="2284" href="category-theory.embedding-maps-precategories.html#2081" class="Bound">C</a> <a id="2286" href="category-theory.embedding-maps-precategories.html#2107" class="Bound">D</a><a id="2287" class="Symbol">)</a>

  <a id="2292" href="category-theory.embedding-maps-precategories.html#2292" class="Function">map-embedding-map-Precategory</a> <a id="2322" class="Symbol">:</a>
    <a id="2328" href="category-theory.embedding-maps-precategories.html#2141" class="Function">embedding-map-Precategory</a> <a id="2354" class="Symbol">→</a> <a id="2356" href="category-theory.maps-precategories.html#1302" class="Function">map-Precategory</a> <a id="2372" href="category-theory.embedding-maps-precategories.html#2081" class="Bound">C</a> <a id="2374" href="category-theory.embedding-maps-precategories.html#2107" class="Bound">D</a>
  <a id="2378" href="category-theory.embedding-maps-precategories.html#2292" class="Function">map-embedding-map-Precategory</a> <a id="2408" class="Symbol">=</a> <a id="2410" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="2417" href="category-theory.embedding-maps-precategories.html#2417" class="Function">is-embedding-map-embedding-map-Precategory</a> <a id="2460" class="Symbol">:</a>
    <a id="2466" class="Symbol">(</a><a id="2467" href="category-theory.embedding-maps-precategories.html#2467" class="Bound">e</a> <a id="2469" class="Symbol">:</a> <a id="2471" href="category-theory.embedding-maps-precategories.html#2141" class="Function">embedding-map-Precategory</a><a id="2496" class="Symbol">)</a> <a id="2498" class="Symbol">→</a>
    <a id="2504" href="category-theory.embedding-maps-precategories.html#1635" class="Function">is-embedding-map-map-Precategory</a> <a id="2537" href="category-theory.embedding-maps-precategories.html#2081" class="Bound">C</a> <a id="2539" href="category-theory.embedding-maps-precategories.html#2107" class="Bound">D</a> <a id="2541" class="Symbol">(</a><a id="2542" href="category-theory.embedding-maps-precategories.html#2292" class="Function">map-embedding-map-Precategory</a> <a id="2572" href="category-theory.embedding-maps-precategories.html#2467" class="Bound">e</a><a id="2573" class="Symbol">)</a>
  <a id="2577" href="category-theory.embedding-maps-precategories.html#2417" class="Function">is-embedding-map-embedding-map-Precategory</a> <a id="2620" class="Symbol">=</a> <a id="2622" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>