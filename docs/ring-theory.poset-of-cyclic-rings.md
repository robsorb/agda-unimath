# The poset of cyclic rings

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="ring-theory.poset-of-cyclic-rings.html" class="Module">ring-theory.poset-of-cyclic-rings</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>

<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="ring-theory.category-of-cyclic-rings.html" class="Module">ring-theory.category-of-cyclic-rings</a>
</pre>
</details>

## Idea

The **large poset** of [cyclic rings](ring-theory.cyclic-rings.md) is just the
[large category of cyclic rings](ring-theory.category-of-cyclic-rings.md), which
happens to be a [large poset](order-theory.large-posets.md).

The large poset of cyclic rings is dual to the large poset of
[subgroups](group-theory.subgroups.md) of the
[group of integers](elementary-number-theory.group-of-integers.md).

## Definition

### The large poset of cyclic rings

<pre class="Agda"><a id="Cyclic-Ring-Large-Poset"></a><a id="748" href="ring-theory.poset-of-cyclic-rings.html#748" class="Function">Cyclic-Ring-Large-Poset</a> <a id="772" class="Symbol">:</a> <a id="774" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="786" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="791" class="Symbol">(</a><a id="792" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="795" class="Symbol">)</a>
<a id="797" href="ring-theory.poset-of-cyclic-rings.html#748" class="Function">Cyclic-Ring-Large-Poset</a> <a id="821" class="Symbol">=</a>
  <a id="825" href="order-theory.large-posets.html#4169" class="Function">large-poset-Large-Category</a>
    <a id="856" class="Symbol">(</a> <a id="858" href="ring-theory.category-of-cyclic-rings.html#2217" class="Function">Cyclic-Ring-Large-Category</a><a id="884" class="Symbol">)</a>
    <a id="890" class="Symbol">(</a> <a id="892" href="ring-theory.category-of-cyclic-rings.html#2750" class="Function">is-large-poset-Cyclic-Ring-Large-Category</a><a id="933" class="Symbol">)</a>
</pre>
## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
