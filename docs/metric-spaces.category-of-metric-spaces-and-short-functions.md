# The category of metric spaces and short maps

<pre class="Agda"><a id="57" class="Keyword">module</a> <a id="64" href="metric-spaces.category-of-metric-spaces-and-short-functions.html" class="Module">metric-spaces.category-of-metric-spaces-and-short-functions</a> <a id="124" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="category-theory.isomorphisms-in-precategories.html" class="Module">category-theory.isomorphisms-in-precategories</a>

<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="320" class="Keyword">open</a> <a id="325" class="Keyword">import</a> <a id="332" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="422" class="Keyword">open</a> <a id="427" class="Keyword">import</a> <a id="434" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="483" class="Keyword">open</a> <a id="488" class="Keyword">import</a> <a id="495" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="530" class="Keyword">open</a> <a id="535" class="Keyword">import</a> <a id="542" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="570" class="Keyword">open</a> <a id="575" class="Keyword">import</a> <a id="582" href="metric-spaces.equality-of-metric-spaces.html" class="Module">metric-spaces.equality-of-metric-spaces</a>
<a id="622" class="Keyword">open</a> <a id="627" class="Keyword">import</a> <a id="634" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="662" class="Keyword">open</a> <a id="667" class="Keyword">import</a> <a id="674" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-short-functions</a>
</pre>
</details>

## Idea

The
[precategory of metric spaces and short maps](metric-spaces.precategory-of-metric-spaces-and-short-functions.md)
is a [category](category-theory.categories.md). We call this the
{{#concept "category of metric spaces and short maps" Agda=category-short-function-Metric-Space WD="category of metric spaces" WDID=Q5051850}}.

## Definitions

### The precategory of metric spaces and short maps is a category

<pre class="Agda"><a id="1181" class="Keyword">module</a> <a id="1188" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1188" class="Module">_</a>
  <a id="1192" class="Symbol">{</a><a id="1193" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1193" class="Bound">l1</a> <a id="1196" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1196" class="Bound">l2</a> <a id="1199" class="Symbol">:</a> <a id="1201" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1206" class="Symbol">}</a>
  <a id="1210" class="Keyword">where</a>

  <a id="1219" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1219" class="Function">is-torsorial-iso-short-function-Metric-Space</a> <a id="1264" class="Symbol">:</a>
    <a id="1270" class="Symbol">(</a><a id="1271" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1271" class="Bound">A</a> <a id="1273" class="Symbol">:</a> <a id="1275" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1288" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1193" class="Bound">l1</a> <a id="1291" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1196" class="Bound">l2</a><a id="1293" class="Symbol">)</a> <a id="1295" class="Symbol">→</a>
    <a id="1301" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="1314" class="Symbol">(</a><a id="1315" href="category-theory.isomorphisms-in-precategories.html#2238" class="Function">iso-Precategory</a> <a id="1331" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#1557" class="Function">precategory-short-function-Metric-Space</a> <a id="1371" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1271" class="Bound">A</a><a id="1372" class="Symbol">)</a>
  <a id="1376" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1219" class="Function">is-torsorial-iso-short-function-Metric-Space</a> <a id="1421" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1421" class="Bound">A</a> <a id="1423" class="Symbol">=</a>
    <a id="1429" href="foundation-core.contractible-types.html#2405" class="Function">is-contr-equiv</a>
      <a id="1450" class="Symbol">(</a> <a id="1452" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1454" class="Symbol">(</a><a id="1455" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1468" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1193" class="Bound">l1</a> <a id="1471" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1196" class="Bound">l2</a><a id="1473" class="Symbol">)</a> <a id="1475" class="Symbol">(</a><a id="1476" href="metric-spaces.equality-of-metric-spaces.html#4263" class="Function">isometric-equiv-Metric-Space&#39;</a> <a id="1506" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1421" class="Bound">A</a><a id="1507" class="Symbol">))</a>
      <a id="1516" class="Symbol">(</a> <a id="1518" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a>
        <a id="1536" class="Symbol">(</a> <a id="1538" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#7387" class="Function">equiv-isometric-equiv-iso-short-function-Metric-Space&#39;</a>
          <a id="1603" class="Symbol">(</a> <a id="1605" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1421" class="Bound">A</a><a id="1606" class="Symbol">)))</a>
      <a id="1616" class="Symbol">(</a> <a id="1618" href="metric-spaces.equality-of-metric-spaces.html#8403" class="Function">is-torsorial-isometric-equiv-Metric-Space&#39;</a> <a id="1661" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1421" class="Bound">A</a><a id="1662" class="Symbol">)</a>

  <a id="1667" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1667" class="Function">is-category-precategory-short-function-Metric-Space</a> <a id="1719" class="Symbol">:</a>
    <a id="1725" href="category-theory.categories.html#1987" class="Function">is-category-Precategory</a> <a id="1749" class="Symbol">(</a><a id="1750" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#1557" class="Function">precategory-short-function-Metric-Space</a> <a id="1790" class="Symbol">{</a><a id="1791" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1193" class="Bound">l1</a><a id="1793" class="Symbol">}</a> <a id="1795" class="Symbol">{</a><a id="1796" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1196" class="Bound">l2</a><a id="1798" class="Symbol">})</a>
  <a id="1803" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1667" class="Function">is-category-precategory-short-function-Metric-Space</a> <a id="1855" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1855" class="Bound">A</a> <a id="1857" class="Symbol">=</a>
    <a id="1863" href="foundation.fundamental-theorem-of-identity-types.html#2039" class="Function">fundamental-theorem-id</a>
      <a id="1892" class="Symbol">(</a> <a id="1894" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1219" class="Function">is-torsorial-iso-short-function-Metric-Space</a> <a id="1939" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1855" class="Bound">A</a><a id="1940" class="Symbol">)</a>
      <a id="1948" class="Symbol">(</a> <a id="1950" href="category-theory.isomorphisms-in-precategories.html#4492" class="Function">iso-eq-Precategory</a> <a id="1969" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#1557" class="Function">precategory-short-function-Metric-Space</a> <a id="2009" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1855" class="Bound">A</a><a id="2010" class="Symbol">)</a>
</pre>
### The category of metric spaces and short maps

<pre class="Agda"><a id="2075" class="Keyword">module</a> <a id="2082" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2082" class="Module">_</a>
  <a id="2086" class="Symbol">{</a><a id="2087" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2087" class="Bound">l1</a> <a id="2090" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2090" class="Bound">l2</a> <a id="2093" class="Symbol">:</a> <a id="2095" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2100" class="Symbol">}</a>
  <a id="2104" class="Keyword">where</a>

  <a id="2113" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2113" class="Function">category-short-function-Metric-Space</a> <a id="2150" class="Symbol">:</a> <a id="2152" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="2161" class="Symbol">(</a><a id="2162" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2167" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2087" class="Bound">l1</a> <a id="2170" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2172" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2177" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2090" class="Bound">l2</a><a id="2179" class="Symbol">)</a> <a id="2181" class="Symbol">(</a><a id="2182" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2087" class="Bound">l1</a> <a id="2185" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2187" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2090" class="Bound">l2</a><a id="2189" class="Symbol">)</a>
  <a id="2193" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2197" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2113" class="Function">category-short-function-Metric-Space</a> <a id="2234" class="Symbol">=</a>
    <a id="2240" href="metric-spaces.precategory-of-metric-spaces-and-short-functions.html#1557" class="Function">precategory-short-function-Metric-Space</a> <a id="2280" class="Symbol">{</a><a id="2281" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2087" class="Bound">l1</a><a id="2283" class="Symbol">}</a> <a id="2285" class="Symbol">{</a><a id="2286" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2090" class="Bound">l2</a><a id="2288" class="Symbol">}</a>
  <a id="2292" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2296" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#2113" class="Function">category-short-function-Metric-Space</a> <a id="2333" class="Symbol">=</a>
    <a id="2339" href="metric-spaces.category-of-metric-spaces-and-short-functions.html#1667" class="Function">is-category-precategory-short-function-Metric-Space</a>
</pre>