# The free ring with one generator

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="ring-theory.free-rings-with-one-generator.html" class="Module">ring-theory.free-rings-with-one-generator</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="ring-theory.homomorphisms-rings.html" class="Module">ring-theory.homomorphisms-rings</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

The **free ring with one generator** is specified as a
[ring](ring-theory.rings.md) `R` equipped with an element `g : R` such that for
every ring `S` the map

```text
  hom-set-Ring R S → type-Ring S
```

given by evaluating at the element `g` is an equivalence. This property is also
called the **universal property of the free ring with one generator**. In other
words, the free ring with one generator is a representing object for the functor
`S ↦ type-Ring S`.

We will show that the polynomial ring `ℤ[x]` of polynomials with
[integer](elementary-number-theory.ring-of-integers.md) coefficients satisfies
the universal property of the free ring with one generator.

## Definitions

### The universal property of the free ring with one generator

<pre class="Agda"><a id="1085" class="Keyword">module</a> <a id="1092" href="ring-theory.free-rings-with-one-generator.html#1092" class="Module">_</a>
  <a id="1096" class="Symbol">{</a><a id="1097" href="ring-theory.free-rings-with-one-generator.html#1097" class="Bound">l</a> <a id="1099" class="Symbol">:</a> <a id="1101" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1106" class="Symbol">}</a> <a id="1108" class="Symbol">(</a><a id="1109" href="ring-theory.free-rings-with-one-generator.html#1109" class="Bound">R</a> <a id="1111" class="Symbol">:</a> <a id="1113" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1118" href="ring-theory.free-rings-with-one-generator.html#1097" class="Bound">l</a><a id="1119" class="Symbol">)</a> <a id="1121" class="Symbol">(</a><a id="1122" href="ring-theory.free-rings-with-one-generator.html#1122" class="Bound">g</a> <a id="1124" class="Symbol">:</a> <a id="1126" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="1136" href="ring-theory.free-rings-with-one-generator.html#1109" class="Bound">R</a><a id="1137" class="Symbol">)</a>
  <a id="1141" class="Keyword">where</a>

  <a id="1150" href="ring-theory.free-rings-with-one-generator.html#1150" class="Function">is-free-ring-with-one-generator</a> <a id="1182" class="Symbol">:</a> <a id="1184" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1190" href="ring-theory.free-rings-with-one-generator.html#1150" class="Function">is-free-ring-with-one-generator</a> <a id="1222" class="Symbol">=</a>
    <a id="1228" class="Symbol">{</a><a id="1229" href="ring-theory.free-rings-with-one-generator.html#1229" class="Bound">l2</a> <a id="1232" class="Symbol">:</a> <a id="1234" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1239" class="Symbol">}</a> <a id="1241" class="Symbol">(</a><a id="1242" href="ring-theory.free-rings-with-one-generator.html#1242" class="Bound">S</a> <a id="1244" class="Symbol">:</a> <a id="1246" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1251" href="ring-theory.free-rings-with-one-generator.html#1229" class="Bound">l2</a><a id="1253" class="Symbol">)</a> <a id="1255" class="Symbol">→</a> <a id="1257" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1266" class="Symbol">(</a><a id="1267" href="ring-theory.homomorphisms-rings.html#8840" class="Function">ev-element-hom-Ring</a> <a id="1287" href="ring-theory.free-rings-with-one-generator.html#1109" class="Bound">R</a> <a id="1289" href="ring-theory.free-rings-with-one-generator.html#1242" class="Bound">S</a> <a id="1291" href="ring-theory.free-rings-with-one-generator.html#1122" class="Bound">g</a><a id="1292" class="Symbol">)</a>
</pre>