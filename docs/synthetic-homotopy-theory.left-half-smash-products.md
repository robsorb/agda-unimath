# Left half-smash products

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="synthetic-homotopy-theory.left-half-smash-products.html" class="Module">synthetic-homotopy-theory.left-half-smash-products</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="282" class="Keyword">open</a> <a id="287" class="Keyword">import</a> <a id="294" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="synthetic-homotopy-theory.cofibers-of-maps.html" class="Module">synthetic-homotopy-theory.cofibers-of-maps</a>
</pre>
</details>

## Idea

Given a type `A` and a [pointed type](structured-types.pointed-types.md) `b : B`
we may form the
{{#concept "left half-smash product" Disambiguation="of a type and a pointed type" Agda=pointed-type-left-half-smash}}
`A ⋉∗ B` as the [cofiber](synthetic-homotopy-theory.cofibers-of-maps.md) of the
canonical inclusion `A → A × B` at the base point of `B`. In other words, the
left half-smash product is the [pushout](synthetic-homotopy-theory.pushouts.md)

```text
    A  -----> A × B
    |           |
    |           |
    ∨         ⌜ ∨
    * ------> A ⋉∗ B.
```

## Definitions

<pre class="Agda"><a id="995" class="Keyword">module</a> <a id="1002" href="synthetic-homotopy-theory.left-half-smash-products.html#1002" class="Module">_</a>
  <a id="1006" class="Symbol">{</a><a id="1007" href="synthetic-homotopy-theory.left-half-smash-products.html#1007" class="Bound">l1</a> <a id="1010" href="synthetic-homotopy-theory.left-half-smash-products.html#1010" class="Bound">l2</a> <a id="1013" class="Symbol">:</a> <a id="1015" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1020" class="Symbol">}</a> <a id="1022" class="Symbol">(</a><a id="1023" href="synthetic-homotopy-theory.left-half-smash-products.html#1023" class="Bound">A</a> <a id="1025" class="Symbol">:</a> <a id="1027" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1030" href="synthetic-homotopy-theory.left-half-smash-products.html#1007" class="Bound">l1</a><a id="1032" class="Symbol">)</a> <a id="1034" class="Symbol">(</a><a id="1035" href="synthetic-homotopy-theory.left-half-smash-products.html#1035" class="Bound">B</a> <a id="1037" class="Symbol">:</a> <a id="1039" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1052" href="synthetic-homotopy-theory.left-half-smash-products.html#1010" class="Bound">l2</a><a id="1054" class="Symbol">)</a>
  <a id="1058" class="Keyword">where</a>

  <a id="1067" href="synthetic-homotopy-theory.left-half-smash-products.html#1067" class="Function">map-left-half-smash</a> <a id="1087" class="Symbol">:</a> <a id="1089" href="synthetic-homotopy-theory.left-half-smash-products.html#1023" class="Bound">A</a> <a id="1091" class="Symbol">→</a> <a id="1093" href="synthetic-homotopy-theory.left-half-smash-products.html#1023" class="Bound">A</a> <a id="1095" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1097" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1115" href="synthetic-homotopy-theory.left-half-smash-products.html#1035" class="Bound">B</a>
  <a id="1119" href="synthetic-homotopy-theory.left-half-smash-products.html#1067" class="Function">map-left-half-smash</a> <a id="1139" href="synthetic-homotopy-theory.left-half-smash-products.html#1139" class="Bound">a</a> <a id="1141" class="Symbol">=</a> <a id="1143" class="Symbol">(</a><a id="1144" href="synthetic-homotopy-theory.left-half-smash-products.html#1139" class="Bound">a</a> <a id="1146" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1148" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1167" href="synthetic-homotopy-theory.left-half-smash-products.html#1035" class="Bound">B</a><a id="1168" class="Symbol">)</a>

  <a id="1173" href="synthetic-homotopy-theory.left-half-smash-products.html#1173" class="Function">type-left-half-smash</a> <a id="1194" class="Symbol">:</a> <a id="1196" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1199" class="Symbol">(</a><a id="1200" href="synthetic-homotopy-theory.left-half-smash-products.html#1007" class="Bound">l1</a> <a id="1203" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1205" href="synthetic-homotopy-theory.left-half-smash-products.html#1010" class="Bound">l2</a><a id="1207" class="Symbol">)</a>
  <a id="1211" href="synthetic-homotopy-theory.left-half-smash-products.html#1173" class="Function">type-left-half-smash</a> <a id="1232" class="Symbol">=</a>
    <a id="1238" href="synthetic-homotopy-theory.cofibers-of-maps.html#1174" class="Function">cofiber</a> <a id="1246" href="synthetic-homotopy-theory.left-half-smash-products.html#1067" class="Function">map-left-half-smash</a>

  <a id="1269" href="synthetic-homotopy-theory.left-half-smash-products.html#1269" class="Function">point-left-half-smash</a> <a id="1291" class="Symbol">:</a> <a id="1293" href="synthetic-homotopy-theory.left-half-smash-products.html#1173" class="Function">type-left-half-smash</a>
  <a id="1316" href="synthetic-homotopy-theory.left-half-smash-products.html#1269" class="Function">point-left-half-smash</a> <a id="1338" class="Symbol">=</a>
    <a id="1344" href="synthetic-homotopy-theory.cofibers-of-maps.html#1483" class="Function">point-cofiber</a> <a id="1358" href="synthetic-homotopy-theory.left-half-smash-products.html#1067" class="Function">map-left-half-smash</a>

  <a id="1381" href="synthetic-homotopy-theory.left-half-smash-products.html#1381" class="Function">pointed-type-left-half-smash</a> <a id="1410" class="Symbol">:</a> <a id="1412" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1425" class="Symbol">(</a><a id="1426" href="synthetic-homotopy-theory.left-half-smash-products.html#1007" class="Bound">l1</a> <a id="1429" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1431" href="synthetic-homotopy-theory.left-half-smash-products.html#1010" class="Bound">l2</a><a id="1433" class="Symbol">)</a>
  <a id="1437" href="synthetic-homotopy-theory.left-half-smash-products.html#1381" class="Function">pointed-type-left-half-smash</a> <a id="1466" class="Symbol">=</a>
    <a id="1472" href="synthetic-homotopy-theory.cofibers-of-maps.html#1545" class="Function">pointed-type-cofiber</a> <a id="1493" href="synthetic-homotopy-theory.left-half-smash-products.html#1067" class="Function">map-left-half-smash</a>

  <a id="1516" class="Keyword">infixr</a> <a id="1523" class="Number">15</a> <a id="1526" href="synthetic-homotopy-theory.left-half-smash-products.html#1533" class="Function Operator">_⋉∗_</a>
  <a id="1533" href="synthetic-homotopy-theory.left-half-smash-products.html#1533" class="Function Operator">_⋉∗_</a> <a id="1538" class="Symbol">:</a> <a id="1540" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1553" class="Symbol">(</a><a id="1554" href="synthetic-homotopy-theory.left-half-smash-products.html#1007" class="Bound">l1</a> <a id="1557" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1559" href="synthetic-homotopy-theory.left-half-smash-products.html#1010" class="Bound">l2</a><a id="1561" class="Symbol">)</a>
  <a id="1565" href="synthetic-homotopy-theory.left-half-smash-products.html#1533" class="Function Operator">_⋉∗_</a> <a id="1570" class="Symbol">=</a> <a id="1572" href="synthetic-homotopy-theory.left-half-smash-products.html#1381" class="Function">pointed-type-left-half-smash</a>
</pre>
> **Notation.** The symbols used for the left half-smash product `_⋉∗_` are the
> [left normal factor semidirect product](https://codepoints.net/U+22c9) `⋉`
> (agda-input: `\ltimes` `\join`), and the
> [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`),
> not the [asterisk](https://codepoints.net/U+002A) `*`.

## Properties

### The left half-smash product is a left tensoring

Given a type `A` and a pointed type `B`, then we have adjunctions

$$
  (A ⋉_* -) ⊣ (A → -) \quad\text{and}\quad (- ⋉_* B) ⊣ (B →_* -)
$$

viewed as functors into pointed types. In other words, we have equivalences

$$
  (A ⋉_* B →_* C) ≃ (B →_* (A → C)) \quad\text{and}\quad (A ⋉_* B →_* C) ≃ (A → (B →_* C))
$$

for every pointed type `C`.

This is Remark 3.2 of {{#cite Lavenir23}}.

**Proof.** This is a consequence of the pullback-property of pushouts.

> This remains to be formalized.

## References

{{#bibliography}}

## See also

- [Smash products of pointed types](synthetic-homotopy-theory.smash-products-of-pointed-types.md)
