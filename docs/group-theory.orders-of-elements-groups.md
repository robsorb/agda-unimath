# The order of an element in a group

<pre class="Agda"><a id="47" class="Keyword">module</a> <a id="54" href="group-theory.orders-of-elements-groups.html" class="Module">group-theory.orders-of-elements-groups</a> <a id="93" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="elementary-number-theory.group-of-integers.html" class="Module">elementary-number-theory.group-of-integers</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>

<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="group-theory.free-groups-with-one-generator.html" class="Module">group-theory.free-groups-with-one-generator</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="group-theory.kernels-homomorphisms-groups.html" class="Module">group-theory.kernels-homomorphisms-groups</a>
<a id="433" class="Keyword">open</a> <a id="438" class="Keyword">import</a> <a id="445" href="group-theory.normal-subgroups.html" class="Module">group-theory.normal-subgroups</a>
<a id="475" class="Keyword">open</a> <a id="480" class="Keyword">import</a> <a id="487" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
<a id="510" class="Keyword">open</a> <a id="515" class="Keyword">import</a> <a id="522" href="group-theory.subsets-groups.html" class="Module">group-theory.subsets-groups</a>
</pre>
</details>

## Idea

For each element `g : G` of a group `G` we have a unique group homomorphism
`f : ℤ → G` such that `f 1 = g`. The order of `g` is defined to be the kernel of
this group homomorphism `f`. Since kernels are ordered by inclusion, it follows
that the orders of elements of a group are ordered by reversed inclusion.

If the group `G` has decidable equality, then we can reduce the order of `g` to
a natural number. In this case, the orders of elements of `G` are ordered by
divisibility.

If the unique group homomorphism `f : ℤ → G` such that `f 1 = g` is injective,
and `G` has decidable equality, then the order of `g` is set to be `0`, which is
a consequence of the point of view that orders are normal subgroups of `ℤ`.

## Definitions

### The order of an element in a group

<pre class="Agda"><a id="1361" class="Keyword">module</a> <a id="1368" href="group-theory.orders-of-elements-groups.html#1368" class="Module">_</a>
  <a id="1372" class="Symbol">{</a><a id="1373" href="group-theory.orders-of-elements-groups.html#1373" class="Bound">l</a> <a id="1375" class="Symbol">:</a> <a id="1377" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1382" class="Symbol">}</a> <a id="1384" class="Symbol">(</a><a id="1385" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1387" class="Symbol">:</a> <a id="1389" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1395" href="group-theory.orders-of-elements-groups.html#1373" class="Bound">l</a><a id="1396" class="Symbol">)</a> <a id="1398" class="Symbol">(</a><a id="1399" href="group-theory.orders-of-elements-groups.html#1399" class="Bound">g</a> <a id="1401" class="Symbol">:</a> <a id="1403" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1414" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a><a id="1415" class="Symbol">)</a>
  <a id="1419" class="Keyword">where</a>

  <a id="1428" href="group-theory.orders-of-elements-groups.html#1428" class="Function">order-element-Group</a> <a id="1448" class="Symbol">:</a> <a id="1450" href="group-theory.normal-subgroups.html#2890" class="Function">Normal-Subgroup</a> <a id="1466" href="group-theory.orders-of-elements-groups.html#1373" class="Bound">l</a> <a id="1468" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a>
  <a id="1478" href="group-theory.orders-of-elements-groups.html#1428" class="Function">order-element-Group</a> <a id="1498" class="Symbol">=</a>
    <a id="1504" href="group-theory.kernels-homomorphisms-groups.html#4560" class="Function">kernel-hom-Group</a> <a id="1521" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a> <a id="1529" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1531" class="Symbol">(</a><a id="1532" href="group-theory.free-groups-with-one-generator.html#2272" class="Function">hom-element-Group</a> <a id="1550" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1552" href="group-theory.orders-of-elements-groups.html#1399" class="Bound">g</a><a id="1553" class="Symbol">)</a>

  <a id="1558" href="group-theory.orders-of-elements-groups.html#1558" class="Function">subgroup-order-element-Group</a> <a id="1587" class="Symbol">:</a> <a id="1589" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="1598" href="group-theory.orders-of-elements-groups.html#1373" class="Bound">l</a> <a id="1600" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a>
  <a id="1610" href="group-theory.orders-of-elements-groups.html#1558" class="Function">subgroup-order-element-Group</a> <a id="1639" class="Symbol">=</a>
    <a id="1645" href="group-theory.kernels-homomorphisms-groups.html#2167" class="Function">subgroup-kernel-hom-Group</a> <a id="1671" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a> <a id="1679" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1681" class="Symbol">(</a><a id="1682" href="group-theory.free-groups-with-one-generator.html#2272" class="Function">hom-element-Group</a> <a id="1700" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1702" href="group-theory.orders-of-elements-groups.html#1399" class="Bound">g</a><a id="1703" class="Symbol">)</a>

  <a id="1708" href="group-theory.orders-of-elements-groups.html#1708" class="Function">subset-order-element-Group</a> <a id="1735" class="Symbol">:</a> <a id="1737" href="group-theory.subsets-groups.html#1216" class="Function">subset-Group</a> <a id="1750" href="group-theory.orders-of-elements-groups.html#1373" class="Bound">l</a> <a id="1752" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a>
  <a id="1762" href="group-theory.orders-of-elements-groups.html#1708" class="Function">subset-order-element-Group</a> <a id="1789" class="Symbol">=</a>
    <a id="1795" href="group-theory.kernels-homomorphisms-groups.html#1171" class="Function">subset-kernel-hom-Group</a> <a id="1819" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a> <a id="1827" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1829" class="Symbol">(</a><a id="1830" href="group-theory.free-groups-with-one-generator.html#2272" class="Function">hom-element-Group</a> <a id="1848" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1850" href="group-theory.orders-of-elements-groups.html#1399" class="Bound">g</a><a id="1851" class="Symbol">)</a>

  <a id="1856" href="group-theory.orders-of-elements-groups.html#1856" class="Function">is-in-order-element-Group</a> <a id="1882" class="Symbol">:</a> <a id="1884" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a> <a id="1886" class="Symbol">→</a> <a id="1888" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1891" href="group-theory.orders-of-elements-groups.html#1373" class="Bound">l</a>
  <a id="1895" href="group-theory.orders-of-elements-groups.html#1856" class="Function">is-in-order-element-Group</a> <a id="1921" class="Symbol">=</a>
    <a id="1927" href="group-theory.kernels-homomorphisms-groups.html#1297" class="Function">is-in-kernel-hom-Group</a> <a id="1950" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a> <a id="1958" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1960" class="Symbol">(</a><a id="1961" href="group-theory.free-groups-with-one-generator.html#2272" class="Function">hom-element-Group</a> <a id="1979" href="group-theory.orders-of-elements-groups.html#1385" class="Bound">G</a> <a id="1981" href="group-theory.orders-of-elements-groups.html#1399" class="Bound">g</a><a id="1982" class="Symbol">)</a>
</pre>
### Divisibility of orders of elements of a group

We say that the order of `x` divides the order of `y` if the normal subgroup
`order-element-Group G y` is contained in the normal subgroup
`order-elemetn-Group G x`. In other words, the order of `x` divides the order of
`y` if for every integer `k` such that `yᵏ ＝ e` we have `xᵏ ＝ e`.

<pre class="Agda"><a id="2335" class="Keyword">module</a> <a id="2342" href="group-theory.orders-of-elements-groups.html#2342" class="Module">_</a>
  <a id="2346" class="Symbol">{</a><a id="2347" href="group-theory.orders-of-elements-groups.html#2347" class="Bound">l</a> <a id="2349" class="Symbol">:</a> <a id="2351" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2356" class="Symbol">}</a> <a id="2358" class="Symbol">(</a><a id="2359" href="group-theory.orders-of-elements-groups.html#2359" class="Bound">G</a> <a id="2361" class="Symbol">:</a> <a id="2363" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="2369" href="group-theory.orders-of-elements-groups.html#2347" class="Bound">l</a><a id="2370" class="Symbol">)</a>
  <a id="2374" class="Keyword">where</a>

  <a id="2383" href="group-theory.orders-of-elements-groups.html#2383" class="Function">div-order-element-Group</a> <a id="2407" class="Symbol">:</a> <a id="2409" class="Symbol">(</a><a id="2410" href="group-theory.orders-of-elements-groups.html#2410" class="Bound">x</a> <a id="2412" href="group-theory.orders-of-elements-groups.html#2412" class="Bound">y</a> <a id="2414" class="Symbol">:</a> <a id="2416" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="2427" href="group-theory.orders-of-elements-groups.html#2359" class="Bound">G</a><a id="2428" class="Symbol">)</a> <a id="2430" class="Symbol">→</a> <a id="2432" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2435" href="group-theory.orders-of-elements-groups.html#2347" class="Bound">l</a>
  <a id="2439" href="group-theory.orders-of-elements-groups.html#2383" class="Function">div-order-element-Group</a> <a id="2463" href="group-theory.orders-of-elements-groups.html#2463" class="Bound">x</a> <a id="2465" href="group-theory.orders-of-elements-groups.html#2465" class="Bound">y</a> <a id="2467" class="Symbol">=</a>
    <a id="2473" href="group-theory.normal-subgroups.html#10521" class="Function">leq-Normal-Subgroup</a>
      <a id="2499" class="Symbol">(</a> <a id="2501" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a><a id="2508" class="Symbol">)</a>
      <a id="2516" class="Symbol">(</a> <a id="2518" href="group-theory.orders-of-elements-groups.html#1428" class="Function">order-element-Group</a> <a id="2538" href="group-theory.orders-of-elements-groups.html#2359" class="Bound">G</a> <a id="2540" href="group-theory.orders-of-elements-groups.html#2465" class="Bound">y</a><a id="2541" class="Symbol">)</a>
      <a id="2549" class="Symbol">(</a> <a id="2551" href="group-theory.orders-of-elements-groups.html#1428" class="Function">order-element-Group</a> <a id="2571" href="group-theory.orders-of-elements-groups.html#2359" class="Bound">G</a> <a id="2573" href="group-theory.orders-of-elements-groups.html#2463" class="Bound">x</a><a id="2574" class="Symbol">)</a>
</pre>