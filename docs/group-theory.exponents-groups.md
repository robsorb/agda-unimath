# Exponents of groups

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="group-theory.exponents-groups.html" class="Module">group-theory.exponents-groups</a> <a id="69" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="125" class="Keyword">open</a> <a id="130" class="Keyword">import</a> <a id="137" href="elementary-number-theory.group-of-integers.html" class="Module">elementary-number-theory.group-of-integers</a>

<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="group-theory.free-groups-with-one-generator.html" class="Module">group-theory.free-groups-with-one-generator</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="group-theory.intersections-subgroups-groups.html" class="Module">group-theory.intersections-subgroups-groups</a>
<a id="365" class="Keyword">open</a> <a id="370" class="Keyword">import</a> <a id="377" href="group-theory.kernels-homomorphisms-groups.html" class="Module">group-theory.kernels-homomorphisms-groups</a>
<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
</pre>
</details>

The **exponent** `exp G` of a [group](group-theory.groups.md) `G` is the
intersection of the kernels of the
[group homomorphisms](group-theory.homomorphisms-groups.md)

```text
  hom-element-Group G g : ℤ → G
```

indexed by all elements `g : G`. In other words, the exponent of `G` is the
[subgroup](group-theory.subgroups.md) `K` of `ℤ` consisting of all
[integers](elementary-number-theory.integers.md) `k` such that the
[integer power](group-theory.integer-powers-of-elements-groups.md) `gᵏ ＝ 1` for
every group element `g`.

Note that our conventions are slightly different from the conventions in
classical mathematics, where the exponent is taken to be the positive integer
`k` that
[generates the subgroup](group-theory.subgroups-generated-by-elements-groups.md)
of `ℤ` that we call the exponent of `G`. In constructive mathematics, however,
such an integer is not always well-defined.

## Definitions

### The exponent of a group

<pre class="Agda"><a id="1419" class="Keyword">module</a> <a id="1426" href="group-theory.exponents-groups.html#1426" class="Module">_</a>
  <a id="1430" class="Symbol">{</a><a id="1431" href="group-theory.exponents-groups.html#1431" class="Bound">l</a> <a id="1433" class="Symbol">:</a> <a id="1435" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1440" class="Symbol">}</a> <a id="1442" class="Symbol">(</a><a id="1443" href="group-theory.exponents-groups.html#1443" class="Bound">G</a> <a id="1445" class="Symbol">:</a> <a id="1447" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1453" href="group-theory.exponents-groups.html#1431" class="Bound">l</a><a id="1454" class="Symbol">)</a>
  <a id="1458" class="Keyword">where</a>

  <a id="1467" href="group-theory.exponents-groups.html#1467" class="Function">exponent-Group</a> <a id="1482" class="Symbol">:</a> <a id="1484" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="1493" href="group-theory.exponents-groups.html#1431" class="Bound">l</a> <a id="1495" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a>
  <a id="1505" href="group-theory.exponents-groups.html#1467" class="Function">exponent-Group</a> <a id="1520" class="Symbol">=</a>
    <a id="1526" href="group-theory.intersections-subgroups-groups.html#4692" class="Function">intersection-family-of-subgroups-Group</a> <a id="1565" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a>
      <a id="1579" class="Symbol">(</a> <a id="1581" class="Symbol">λ</a> <a id="1583" class="Symbol">(</a><a id="1584" href="group-theory.exponents-groups.html#1584" class="Bound">g</a> <a id="1586" class="Symbol">:</a> <a id="1588" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1599" href="group-theory.exponents-groups.html#1443" class="Bound">G</a><a id="1600" class="Symbol">)</a> <a id="1602" class="Symbol">→</a>
        <a id="1612" href="group-theory.kernels-homomorphisms-groups.html#2167" class="Function">subgroup-kernel-hom-Group</a> <a id="1638" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a> <a id="1646" href="group-theory.exponents-groups.html#1443" class="Bound">G</a> <a id="1648" class="Symbol">(</a><a id="1649" href="group-theory.free-groups-with-one-generator.html#2272" class="Function">hom-element-Group</a> <a id="1667" href="group-theory.exponents-groups.html#1443" class="Bound">G</a> <a id="1669" href="group-theory.exponents-groups.html#1584" class="Bound">g</a><a id="1670" class="Symbol">))</a>
</pre>