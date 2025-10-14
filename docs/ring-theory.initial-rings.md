# Initial rings

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="ring-theory.initial-rings.html" class="Module">ring-theory.initial-rings</a> <a id="59" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="115" class="Keyword">open</a> <a id="120" class="Keyword">import</a> <a id="127" href="category-theory.initial-objects-large-categories.html" class="Module">category-theory.initial-objects-large-categories</a>

<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="ring-theory.category-of-rings.html" class="Module">ring-theory.category-of-rings</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

The **initial ring** is a [ring](ring-theory.rings.md) `R` that satisfies the
universal property that for any ring `S`, the type

```text
  hom-Ring R S
```

of [ring homomorphisms](ring-theory.homomorphisms-rings.md) from `R` to `S` is
contractible.

In
[`elementary-number-theory.ring-of-integers`](elementary-number-theory.ring-of-integers.md)
we will show that `ℤ` is the initial ring.

## Definitions

<pre class="Agda"><a id="730" class="Keyword">module</a> <a id="737" href="ring-theory.initial-rings.html#737" class="Module">_</a>
  <a id="741" class="Symbol">{</a><a id="742" href="ring-theory.initial-rings.html#742" class="Bound">l</a> <a id="744" class="Symbol">:</a> <a id="746" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="751" class="Symbol">}</a> <a id="753" class="Symbol">(</a><a id="754" href="ring-theory.initial-rings.html#754" class="Bound">R</a> <a id="756" class="Symbol">:</a> <a id="758" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="763" href="ring-theory.initial-rings.html#742" class="Bound">l</a><a id="764" class="Symbol">)</a>
  <a id="768" class="Keyword">where</a>

  <a id="777" href="ring-theory.initial-rings.html#777" class="Function">is-initial-Ring</a> <a id="793" class="Symbol">:</a> <a id="795" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="801" href="ring-theory.initial-rings.html#777" class="Function">is-initial-Ring</a> <a id="817" class="Symbol">=</a> <a id="819" href="category-theory.initial-objects-large-categories.html#735" class="Function">is-initial-obj-Large-Category</a> <a id="849" href="ring-theory.category-of-rings.html#800" class="Function">Ring-Large-Category</a> <a id="869" href="ring-theory.initial-rings.html#754" class="Bound">R</a>
</pre>