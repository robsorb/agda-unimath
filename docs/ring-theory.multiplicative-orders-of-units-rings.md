# Multiplicative orders of elements of rings

<pre class="Agda"><a id="55" class="Keyword">module</a> <a id="62" href="ring-theory.multiplicative-orders-of-units-rings.html" class="Module">ring-theory.multiplicative-orders-of-units-rings</a> <a id="111" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda">
</pre>
</details>

## Idea

The **multiplicative order** of an
[invertible element](ring-theory.invertible-elements-rings.md) `x` of a
[ring](ring-theory.rings.md) `R` is the order of `x` in the
[group of multiplicative units](ring-theory.groups-of-units-rings.md). In other
words, it is the [normal subgroup](group-theory.normal-subgroups.md) of the
[group of integers](elementary-number-theory.group-of-integers.md) consisting of
all [integers](elementary-number-theory.integers.md) `k` such that `xᵏ ＝ 1`.
