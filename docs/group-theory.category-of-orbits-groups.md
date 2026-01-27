# The orbit category of a group

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="group-theory.category-of-orbits-groups.html" class="Module">group-theory.category-of-orbits-groups</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="category-theory.full-large-subcategories.html" class="Module">category-theory.full-large-subcategories</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="category-theory.isomorphisms-in-large-precategories.html" class="Module">category-theory.isomorphisms-in-large-precategories</a>
<a id="300" class="Keyword">open</a> <a id="305" class="Keyword">import</a> <a id="312" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="345" class="Keyword">open</a> <a id="350" class="Keyword">import</a> <a id="357" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="480" class="Keyword">open</a> <a id="485" class="Keyword">import</a> <a id="492" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="581" class="Keyword">open</a> <a id="586" class="Keyword">import</a> <a id="593" href="group-theory.category-of-group-actions.html" class="Module">group-theory.category-of-group-actions</a>
<a id="632" class="Keyword">open</a> <a id="637" class="Keyword">import</a> <a id="644" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="671" class="Keyword">open</a> <a id="676" class="Keyword">import</a> <a id="683" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="703" class="Keyword">open</a> <a id="708" class="Keyword">import</a> <a id="715" href="group-theory.homomorphisms-group-actions.html" class="Module">group-theory.homomorphisms-group-actions</a>
<a id="756" class="Keyword">open</a> <a id="761" class="Keyword">import</a> <a id="768" href="group-theory.isomorphisms-group-actions.html" class="Module">group-theory.isomorphisms-group-actions</a>
<a id="808" class="Keyword">open</a> <a id="813" class="Keyword">import</a> <a id="820" href="group-theory.precategory-of-group-actions.html" class="Module">group-theory.precategory-of-group-actions</a>
<a id="862" class="Keyword">open</a> <a id="867" class="Keyword">import</a> <a id="874" href="group-theory.transitive-group-actions.html" class="Module">group-theory.transitive-group-actions</a>
</pre>
</details>

## Idea

The **orbit category of a group** `𝒪(G)` is the
[full subcategory](category-theory.full-large-subcategories.md) of the
[category of `G`-sets](group-theory.category-of-group-actions.md) consisting of
orbits of `G`, i.e. [transitive](group-theory.transitive-group-actions.md)
[`G`-sets](group-theory.group-actions.md). Equivalently, an orbit of `G` is a
`G`-set that is
[merely equivalent](group-theory.mere-equivalences-group-actions.md) to a
quotient `G`-set `G/H` for some [subgroup](group-theory.subgroups.md) `H`.

## Definitions

### The large orbit category of a group

<pre class="Agda"><a id="1521" class="Keyword">module</a> <a id="1528" href="group-theory.category-of-orbits-groups.html#1528" class="Module">_</a>
  <a id="1532" class="Symbol">{</a><a id="1533" href="group-theory.category-of-orbits-groups.html#1533" class="Bound">l1</a> <a id="1536" class="Symbol">:</a> <a id="1538" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1543" class="Symbol">}</a> <a id="1545" class="Symbol">(</a><a id="1546" href="group-theory.category-of-orbits-groups.html#1546" class="Bound">G</a> <a id="1548" class="Symbol">:</a> <a id="1550" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1556" href="group-theory.category-of-orbits-groups.html#1533" class="Bound">l1</a><a id="1558" class="Symbol">)</a>
  <a id="1562" class="Keyword">where</a>

  <a id="1571" href="group-theory.category-of-orbits-groups.html#1571" class="Function">orbit-Group-Full-Large-Subcategory</a> <a id="1606" class="Symbol">:</a>
    <a id="1612" href="category-theory.full-large-subcategories.html#916" class="Function">Full-Large-Subcategory</a> <a id="1635" class="Symbol">(</a><a id="1636" href="group-theory.category-of-orbits-groups.html#1533" class="Bound">l1</a> <a id="1639" href="Agda.Primitive.html#961" class="Primitive Operator">⊔_</a><a id="1641" class="Symbol">)</a> <a id="1643" class="Symbol">(</a><a id="1644" href="group-theory.category-of-group-actions.html#1440" class="Function">action-Group-Large-Category</a> <a id="1672" href="group-theory.category-of-orbits-groups.html#1546" class="Bound">G</a><a id="1673" class="Symbol">)</a>
  <a id="1677" href="group-theory.category-of-orbits-groups.html#1571" class="Function">orbit-Group-Full-Large-Subcategory</a> <a id="1712" class="Symbol">=</a> <a id="1714" href="group-theory.transitive-group-actions.html#968" class="Function">is-transitive-prop-action-Group</a> <a id="1746" href="group-theory.category-of-orbits-groups.html#1546" class="Bound">G</a>

  <a id="1751" href="group-theory.category-of-orbits-groups.html#1751" class="Function">orbit-Group-Large-Category</a> <a id="1778" class="Symbol">:</a>
    <a id="1784" href="category-theory.large-categories.html#1672" class="Record">Large-Category</a> <a id="1799" class="Symbol">(λ</a> <a id="1802" href="group-theory.category-of-orbits-groups.html#1802" class="Bound">l</a> <a id="1804" class="Symbol">→</a> <a id="1806" href="group-theory.category-of-orbits-groups.html#1533" class="Bound">l1</a> <a id="1809" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1811" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1816" href="group-theory.category-of-orbits-groups.html#1802" class="Bound">l</a><a id="1817" class="Symbol">)</a> <a id="1819" class="Symbol">(λ</a> <a id="1822" href="group-theory.category-of-orbits-groups.html#1822" class="Bound">l2</a> <a id="1825" href="group-theory.category-of-orbits-groups.html#1825" class="Bound">l3</a> <a id="1828" class="Symbol">→</a> <a id="1830" href="group-theory.category-of-orbits-groups.html#1533" class="Bound">l1</a> <a id="1833" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1835" href="group-theory.category-of-orbits-groups.html#1822" class="Bound">l2</a> <a id="1838" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1840" href="group-theory.category-of-orbits-groups.html#1825" class="Bound">l3</a><a id="1842" class="Symbol">)</a>
  <a id="1846" href="group-theory.category-of-orbits-groups.html#1751" class="Function">orbit-Group-Large-Category</a> <a id="1873" class="Symbol">=</a>
    <a id="1879" href="category-theory.full-large-subcategories.html#6893" class="Function">large-category-Full-Large-Subcategory</a>
      <a id="1923" class="Symbol">(</a> <a id="1925" href="group-theory.category-of-group-actions.html#1440" class="Function">action-Group-Large-Category</a> <a id="1953" href="group-theory.category-of-orbits-groups.html#1546" class="Bound">G</a><a id="1954" class="Symbol">)</a>
      <a id="1962" class="Symbol">(</a> <a id="1964" href="group-theory.category-of-orbits-groups.html#1571" class="Function">orbit-Group-Full-Large-Subcategory</a><a id="1998" class="Symbol">)</a>
</pre>
### The large orbit precategory of a group

<pre class="Agda"><a id="2057" class="Keyword">module</a> <a id="2064" href="group-theory.category-of-orbits-groups.html#2064" class="Module">_</a>
  <a id="2068" class="Symbol">{</a><a id="2069" href="group-theory.category-of-orbits-groups.html#2069" class="Bound">l1</a> <a id="2072" class="Symbol">:</a> <a id="2074" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2079" class="Symbol">}</a> <a id="2081" class="Symbol">(</a><a id="2082" href="group-theory.category-of-orbits-groups.html#2082" class="Bound">G</a> <a id="2084" class="Symbol">:</a> <a id="2086" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="2092" href="group-theory.category-of-orbits-groups.html#2069" class="Bound">l1</a><a id="2094" class="Symbol">)</a>
  <a id="2098" class="Keyword">where</a>

  <a id="2107" href="group-theory.category-of-orbits-groups.html#2107" class="Function">orbit-Group-Large-Precategory</a> <a id="2137" class="Symbol">:</a>
    <a id="2143" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="2161" class="Symbol">(λ</a> <a id="2164" href="group-theory.category-of-orbits-groups.html#2164" class="Bound">l</a> <a id="2166" class="Symbol">→</a> <a id="2168" href="group-theory.category-of-orbits-groups.html#2069" class="Bound">l1</a> <a id="2171" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2173" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2178" href="group-theory.category-of-orbits-groups.html#2164" class="Bound">l</a><a id="2179" class="Symbol">)</a> <a id="2181" class="Symbol">(λ</a> <a id="2184" href="group-theory.category-of-orbits-groups.html#2184" class="Bound">l2</a> <a id="2187" href="group-theory.category-of-orbits-groups.html#2187" class="Bound">l3</a> <a id="2190" class="Symbol">→</a> <a id="2192" href="group-theory.category-of-orbits-groups.html#2069" class="Bound">l1</a> <a id="2195" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2197" href="group-theory.category-of-orbits-groups.html#2184" class="Bound">l2</a> <a id="2200" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2202" href="group-theory.category-of-orbits-groups.html#2187" class="Bound">l3</a><a id="2204" class="Symbol">)</a>
  <a id="2208" href="group-theory.category-of-orbits-groups.html#2107" class="Function">orbit-Group-Large-Precategory</a> <a id="2238" class="Symbol">=</a>
    <a id="2244" href="category-theory.large-categories.html#1800" class="Field">large-precategory-Large-Category</a> <a id="2277" class="Symbol">(</a><a id="2278" href="group-theory.category-of-orbits-groups.html#1751" class="Function">orbit-Group-Large-Category</a> <a id="2305" href="group-theory.category-of-orbits-groups.html#2082" class="Bound">G</a><a id="2306" class="Symbol">)</a>
</pre>
### The small orbit category of a group

<pre class="Agda"><a id="2362" class="Keyword">module</a> <a id="2369" href="group-theory.category-of-orbits-groups.html#2369" class="Module">_</a>
  <a id="2373" class="Symbol">{</a><a id="2374" href="group-theory.category-of-orbits-groups.html#2374" class="Bound">l1</a> <a id="2377" class="Symbol">:</a> <a id="2379" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2384" class="Symbol">}</a> <a id="2386" class="Symbol">(</a><a id="2387" href="group-theory.category-of-orbits-groups.html#2387" class="Bound">G</a> <a id="2389" class="Symbol">:</a> <a id="2391" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="2397" href="group-theory.category-of-orbits-groups.html#2374" class="Bound">l1</a><a id="2399" class="Symbol">)</a>
  <a id="2403" class="Keyword">where</a>

  <a id="2412" href="group-theory.category-of-orbits-groups.html#2412" class="Function">orbit-Group-Category</a> <a id="2433" class="Symbol">:</a> <a id="2435" class="Symbol">(</a><a id="2436" href="group-theory.category-of-orbits-groups.html#2436" class="Bound">l2</a> <a id="2439" class="Symbol">:</a> <a id="2441" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2446" class="Symbol">)</a> <a id="2448" class="Symbol">→</a> <a id="2450" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="2459" class="Symbol">(</a><a id="2460" href="group-theory.category-of-orbits-groups.html#2374" class="Bound">l1</a> <a id="2463" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2465" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2470" href="group-theory.category-of-orbits-groups.html#2436" class="Bound">l2</a><a id="2472" class="Symbol">)</a> <a id="2474" class="Symbol">(</a><a id="2475" href="group-theory.category-of-orbits-groups.html#2374" class="Bound">l1</a> <a id="2478" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2480" href="group-theory.category-of-orbits-groups.html#2436" class="Bound">l2</a><a id="2482" class="Symbol">)</a>
  <a id="2486" href="group-theory.category-of-orbits-groups.html#2412" class="Function">orbit-Group-Category</a> <a id="2507" class="Symbol">=</a> <a id="2509" href="category-theory.large-categories.html#7051" class="Function">category-Large-Category</a> <a id="2533" class="Symbol">(</a><a id="2534" href="group-theory.category-of-orbits-groups.html#1751" class="Function">orbit-Group-Large-Category</a> <a id="2561" href="group-theory.category-of-orbits-groups.html#2387" class="Bound">G</a><a id="2562" class="Symbol">)</a>
</pre>
### The small orbit precategory of a group

<pre class="Agda"><a id="2621" class="Keyword">module</a> <a id="2628" href="group-theory.category-of-orbits-groups.html#2628" class="Module">_</a>
  <a id="2632" class="Symbol">{</a><a id="2633" href="group-theory.category-of-orbits-groups.html#2633" class="Bound">l1</a> <a id="2636" class="Symbol">:</a> <a id="2638" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2643" class="Symbol">}</a> <a id="2645" class="Symbol">(</a><a id="2646" href="group-theory.category-of-orbits-groups.html#2646" class="Bound">G</a> <a id="2648" class="Symbol">:</a> <a id="2650" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="2656" href="group-theory.category-of-orbits-groups.html#2633" class="Bound">l1</a><a id="2658" class="Symbol">)</a>
  <a id="2662" class="Keyword">where</a>

  <a id="2671" href="group-theory.category-of-orbits-groups.html#2671" class="Function">orbit-Group-Precategory</a> <a id="2695" class="Symbol">:</a> <a id="2697" class="Symbol">(</a><a id="2698" href="group-theory.category-of-orbits-groups.html#2698" class="Bound">l2</a> <a id="2701" class="Symbol">:</a> <a id="2703" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2708" class="Symbol">)</a> <a id="2710" class="Symbol">→</a> <a id="2712" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="2724" class="Symbol">(</a><a id="2725" href="group-theory.category-of-orbits-groups.html#2633" class="Bound">l1</a> <a id="2728" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2730" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2735" href="group-theory.category-of-orbits-groups.html#2698" class="Bound">l2</a><a id="2737" class="Symbol">)</a> <a id="2739" class="Symbol">(</a><a id="2740" href="group-theory.category-of-orbits-groups.html#2633" class="Bound">l1</a> <a id="2743" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2745" href="group-theory.category-of-orbits-groups.html#2698" class="Bound">l2</a><a id="2747" class="Symbol">)</a>
  <a id="2751" href="group-theory.category-of-orbits-groups.html#2671" class="Function">orbit-Group-Precategory</a> <a id="2775" class="Symbol">=</a>
    <a id="2781" href="category-theory.large-categories.html#6601" class="Function">precategory-Large-Category</a> <a id="2808" class="Symbol">(</a><a id="2809" href="group-theory.category-of-orbits-groups.html#1751" class="Function">orbit-Group-Large-Category</a> <a id="2836" href="group-theory.category-of-orbits-groups.html#2646" class="Bound">G</a><a id="2837" class="Symbol">)</a>
</pre>
## External links

- [orbit category](https://ncatlab.org/nlab/show/orbit+category) at $n$Lab
