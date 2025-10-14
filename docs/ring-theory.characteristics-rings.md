# Characteristics of rings

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="ring-theory.characteristics-rings.html" class="Module">ring-theory.characteristics-rings</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="elementary-number-theory.ring-of-integers.html" class="Module">elementary-number-theory.ring-of-integers</a>

<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="ring-theory.ideals-rings.html" class="Module">ring-theory.ideals-rings</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="ring-theory.kernels-of-ring-homomorphisms.html" class="Module">ring-theory.kernels-of-ring-homomorphisms</a>
<a id="320" class="Keyword">open</a> <a id="325" class="Keyword">import</a> <a id="332" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

The **characteristic** of a [ring](ring-theory.rings.md) `R` is defined to be
the kernel of the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md) from
the [ring `ℤ` of integers](elementary-number-theory.ring-of-integers.md) to `R`.

## Definitions

### Characteristics of rings

<pre class="Agda"><a id="687" class="Keyword">module</a> <a id="694" href="ring-theory.characteristics-rings.html#694" class="Module">_</a>
  <a id="698" class="Symbol">{</a><a id="699" href="ring-theory.characteristics-rings.html#699" class="Bound">l</a> <a id="701" class="Symbol">:</a> <a id="703" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="708" class="Symbol">}</a> <a id="710" class="Symbol">(</a><a id="711" href="ring-theory.characteristics-rings.html#711" class="Bound">R</a> <a id="713" class="Symbol">:</a> <a id="715" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="720" href="ring-theory.characteristics-rings.html#699" class="Bound">l</a><a id="721" class="Symbol">)</a>
  <a id="725" class="Keyword">where</a>

  <a id="734" href="ring-theory.characteristics-rings.html#734" class="Function">characteristic-Ring</a> <a id="754" class="Symbol">:</a> <a id="756" href="ring-theory.ideals-rings.html#1957" class="Function">ideal-Ring</a> <a id="767" href="ring-theory.characteristics-rings.html#699" class="Bound">l</a> <a id="769" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a>
  <a id="778" href="ring-theory.characteristics-rings.html#734" class="Function">characteristic-Ring</a> <a id="798" class="Symbol">=</a> <a id="800" href="ring-theory.kernels-of-ring-homomorphisms.html#2964" class="Function">kernel-hom-Ring</a> <a id="816" href="elementary-number-theory.ring-of-integers.html#1087" class="Function">ℤ-Ring</a> <a id="823" href="ring-theory.characteristics-rings.html#711" class="Bound">R</a> <a id="825" class="Symbol">(</a><a id="826" href="elementary-number-theory.ring-of-integers.html#4413" class="Function">initial-hom-Ring</a> <a id="843" href="ring-theory.characteristics-rings.html#711" class="Bound">R</a><a id="844" class="Symbol">)</a>
</pre>