# Exponents of abelian groups

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="group-theory.exponents-abelian-groups.html" class="Module">group-theory.exponents-abelian-groups</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="elementary-number-theory.group-of-integers.html" class="Module">elementary-number-theory.group-of-integers</a>

<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="group-theory.abelian-groups.html" class="Module">group-theory.abelian-groups</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="group-theory.exponents-groups.html" class="Module">group-theory.exponents-groups</a>
<a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="group-theory.subgroups-abelian-groups.html" class="Module">group-theory.subgroups-abelian-groups</a>
</pre>
</details>

The **exponent** `exp A` of an [abelian group](group-theory.abelian-groups.md)
`A` is the intersection of the kernels of the
[group homomorphisms](group-theory.homomorphisms-groups.md)

```text
  hom-element-Group (group-Ab A) a : ℤ → A
```

indexed by all elements `a : A`. In other words, the exponent of `A` is the
[subgroup](group-theory.subgroups.md) `K` of `ℤ` consisting of all
[integers](elementary-number-theory.integers.md) `k` such that the
[integer multiple](group-theory.integer-multiples-of-elements-abelian-groups.md)
`kx ＝ 1` for every group element `x`.

Note that our conventions are slightly different from the conventions in
classical mathematics, where the exponent is taken to be the positive integer
`k` that
[generates the subgroup](group-theory.subgroups-generated-by-elements-groups.md)
of `ℤ` that we call the exponent of `A`. In constructive mathematics, however,
such an integer is not always well-defined.

## Definitions

### The exponent of an abelian group

<pre class="Agda"><a id="1385" class="Keyword">module</a> <a id="1392" href="group-theory.exponents-abelian-groups.html#1392" class="Module">_</a>
  <a id="1396" class="Symbol">{</a><a id="1397" href="group-theory.exponents-abelian-groups.html#1397" class="Bound">l</a> <a id="1399" class="Symbol">:</a> <a id="1401" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1406" class="Symbol">}</a> <a id="1408" class="Symbol">(</a><a id="1409" href="group-theory.exponents-abelian-groups.html#1409" class="Bound">A</a> <a id="1411" class="Symbol">:</a> <a id="1413" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="1416" href="group-theory.exponents-abelian-groups.html#1397" class="Bound">l</a><a id="1417" class="Symbol">)</a>
  <a id="1421" class="Keyword">where</a>

  <a id="1430" href="group-theory.exponents-abelian-groups.html#1430" class="Function">exponent-Ab</a> <a id="1442" class="Symbol">:</a> <a id="1444" href="group-theory.subgroups-abelian-groups.html#2475" class="Function">Subgroup-Ab</a> <a id="1456" href="group-theory.exponents-abelian-groups.html#1397" class="Bound">l</a> <a id="1458" href="elementary-number-theory.group-of-integers.html#1033" class="Function">ℤ-Ab</a>
  <a id="1465" href="group-theory.exponents-abelian-groups.html#1430" class="Function">exponent-Ab</a> <a id="1477" class="Symbol">=</a> <a id="1479" href="group-theory.exponents-groups.html#1467" class="Function">exponent-Group</a> <a id="1494" class="Symbol">(</a><a id="1495" href="group-theory.abelian-groups.html#2643" class="Function">group-Ab</a> <a id="1504" href="group-theory.exponents-abelian-groups.html#1409" class="Bound">A</a><a id="1505" class="Symbol">)</a>
</pre>