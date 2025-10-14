# The category of metric spaces and isometries

<pre class="Agda"><a id="57" class="Keyword">module</a> <a id="64" href="metric-spaces.category-of-metric-spaces-and-isometries.html" class="Module">metric-spaces.category-of-metric-spaces-and-isometries</a> <a id="119" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="category-theory.isomorphisms-in-precategories.html" class="Module">category-theory.isomorphisms-in-precategories</a>

<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="478" class="Keyword">open</a> <a id="483" class="Keyword">import</a> <a id="490" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="565" class="Keyword">open</a> <a id="570" class="Keyword">import</a> <a id="577" href="metric-spaces.equality-of-metric-spaces.html" class="Module">metric-spaces.equality-of-metric-spaces</a>
<a id="617" class="Keyword">open</a> <a id="622" class="Keyword">import</a> <a id="629" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="657" class="Keyword">open</a> <a id="662" class="Keyword">import</a> <a id="669" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html" class="Module">metric-spaces.precategory-of-metric-spaces-and-isometries</a>
</pre>
</details>

## Idea

The
[precategory of metric spaces and isometries](metric-spaces.precategory-of-metric-spaces-and-isometries.md)
is a [category](category-theory.categories.md). We call this the
{{#concept "category of metric spaces and isometries" Agda=category-isometry-Metric-Space}}.

## Definitions

### The precategory of metric spaces and isometries is a category

<pre class="Agda"><a id="1115" class="Keyword">module</a> <a id="1122" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1122" class="Module">_</a>
  <a id="1126" class="Symbol">{</a><a id="1127" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1127" class="Bound">l1</a> <a id="1130" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1130" class="Bound">l2</a> <a id="1133" class="Symbol">:</a> <a id="1135" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1140" class="Symbol">}</a>
  <a id="1144" class="Keyword">where</a>

  <a id="1153" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1153" class="Function">is-torsorial-iso-isometry-Metric-Space</a> <a id="1192" class="Symbol">:</a>
    <a id="1198" class="Symbol">(</a><a id="1199" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1199" class="Bound">A</a> <a id="1201" class="Symbol">:</a> <a id="1203" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1216" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1127" class="Bound">l1</a> <a id="1219" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1130" class="Bound">l2</a><a id="1221" class="Symbol">)</a> <a id="1223" class="Symbol">→</a>
    <a id="1229" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="1242" class="Symbol">(</a><a id="1243" href="category-theory.isomorphisms-in-precategories.html#2238" class="Function">iso-Precategory</a> <a id="1259" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a> <a id="1293" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1199" class="Bound">A</a><a id="1294" class="Symbol">)</a>
  <a id="1298" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1153" class="Function">is-torsorial-iso-isometry-Metric-Space</a> <a id="1337" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1337" class="Bound">A</a> <a id="1339" class="Symbol">=</a>
    <a id="1345" href="foundation-core.contractible-types.html#2405" class="Function">is-contr-equiv</a>
      <a id="1366" class="Symbol">(</a> <a id="1368" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1370" class="Symbol">(</a><a id="1371" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1384" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1127" class="Bound">l1</a> <a id="1387" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1130" class="Bound">l2</a><a id="1389" class="Symbol">)</a> <a id="1391" class="Symbol">(</a><a id="1392" href="metric-spaces.equality-of-metric-spaces.html#4263" class="Function">isometric-equiv-Metric-Space&#39;</a> <a id="1422" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1337" class="Bound">A</a><a id="1423" class="Symbol">))</a>
      <a id="1432" class="Symbol">(</a> <a id="1434" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a> <a id="1444" class="Symbol">(</a><a id="1445" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#3401" class="Function">equiv-iso-isometric-equiv-Metric-Space&#39;</a> <a id="1485" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1337" class="Bound">A</a><a id="1486" class="Symbol">))</a>
      <a id="1495" class="Symbol">(</a> <a id="1497" href="metric-spaces.equality-of-metric-spaces.html#8403" class="Function">is-torsorial-isometric-equiv-Metric-Space&#39;</a> <a id="1540" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1337" class="Bound">A</a><a id="1541" class="Symbol">)</a>

  <a id="1546" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1546" class="Function">is-category-precategory-isometry-Metric-Space</a> <a id="1592" class="Symbol">:</a>
    <a id="1598" href="category-theory.categories.html#1987" class="Function">is-category-Precategory</a> <a id="1622" class="Symbol">(</a><a id="1623" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a> <a id="1657" class="Symbol">{</a><a id="1658" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1127" class="Bound">l1</a><a id="1660" class="Symbol">}</a> <a id="1662" class="Symbol">{</a><a id="1663" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1130" class="Bound">l2</a><a id="1665" class="Symbol">})</a>
  <a id="1670" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1546" class="Function">is-category-precategory-isometry-Metric-Space</a> <a id="1716" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1716" class="Bound">A</a> <a id="1718" class="Symbol">=</a>
    <a id="1724" href="foundation.fundamental-theorem-of-identity-types.html#2039" class="Function">fundamental-theorem-id</a>
      <a id="1753" class="Symbol">(</a> <a id="1755" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1153" class="Function">is-torsorial-iso-isometry-Metric-Space</a> <a id="1794" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1716" class="Bound">A</a><a id="1795" class="Symbol">)</a>
      <a id="1803" class="Symbol">(</a> <a id="1805" href="category-theory.isomorphisms-in-precategories.html#4492" class="Function">iso-eq-Precategory</a> <a id="1824" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a> <a id="1858" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1716" class="Bound">A</a><a id="1859" class="Symbol">)</a>
</pre>
### The category of metric spaces and isometries

<pre class="Agda"><a id="1924" class="Keyword">module</a> <a id="1931" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1931" class="Module">_</a>
  <a id="1935" class="Symbol">{</a><a id="1936" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1936" class="Bound">l1</a> <a id="1939" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1939" class="Bound">l2</a> <a id="1942" class="Symbol">:</a> <a id="1944" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1949" class="Symbol">}</a>
  <a id="1953" class="Keyword">where</a>

  <a id="1962" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1962" class="Function">category-isometry-Metric-Space</a> <a id="1993" class="Symbol">:</a> <a id="1995" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="2004" class="Symbol">(</a><a id="2005" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2010" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1936" class="Bound">l1</a> <a id="2013" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2015" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2020" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1939" class="Bound">l2</a><a id="2022" class="Symbol">)</a> <a id="2024" class="Symbol">(</a><a id="2025" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1936" class="Bound">l1</a> <a id="2028" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2030" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1939" class="Bound">l2</a><a id="2032" class="Symbol">)</a>
  <a id="2036" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2040" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1962" class="Function">category-isometry-Metric-Space</a> <a id="2071" class="Symbol">=</a>
    <a id="2077" href="metric-spaces.precategory-of-metric-spaces-and-isometries.html#1475" class="Function">precategory-isometry-Metric-Space</a> <a id="2111" class="Symbol">{</a><a id="2112" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1936" class="Bound">l1</a><a id="2114" class="Symbol">}</a> <a id="2116" class="Symbol">{</a><a id="2117" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1939" class="Bound">l2</a><a id="2119" class="Symbol">}</a>
  <a id="2123" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2127" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1962" class="Function">category-isometry-Metric-Space</a> <a id="2158" class="Symbol">=</a>
    <a id="2164" href="metric-spaces.category-of-metric-spaces-and-isometries.html#1546" class="Function">is-category-precategory-isometry-Metric-Space</a>
</pre>