# Hasse-Weil species

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="species.hasse-weil-species.html" class="Module">species.hasse-weil-species</a> <a id="65" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="121" class="Keyword">open</a> <a id="126" class="Keyword">import</a> <a id="133" href="finite-algebra.commutative-finite-rings.html" class="Module">finite-algebra.commutative-finite-rings</a>
<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="finite-algebra.products-commutative-finite-rings.html" class="Module">finite-algebra.products-commutative-finite-rings</a>

<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="282" class="Keyword">open</a> <a id="287" class="Keyword">import</a> <a id="294" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="318" class="Keyword">open</a> <a id="323" class="Keyword">import</a> <a id="330" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="358" class="Keyword">open</a> <a id="363" class="Keyword">import</a> <a id="370" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

Let `S` be a function from the type of
[commutative finite rings](finite-algebra.commutative-finite-rings.md) to the
[finite types](univalent-combinatorics.finite-types.md) that preserves cartesian
products. The {{#concept "Hasse-Weil species"}} is a
[species of finite inhabited types](species.species-of-finite-inhabited-types.md)
defined for any
[finite inhabited type](univalent-combinatorics.inhabited-finite-types.md) `k`
as

```text
Σ ( p : structure-semisimple-commutative-ring-Finite-Type k),
  ( S (commutative-finite-ring-finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-Finite-Type k p)).
```

## Definitions

<pre class="Agda"><a id="is-closed-under-products-function-from-Finite-Commutative-Ring"></a><a id="1087" href="species.hasse-weil-species.html#1087" class="Function">is-closed-under-products-function-from-Finite-Commutative-Ring</a> <a id="1150" class="Symbol">:</a>
  <a id="1154" class="Symbol">{</a><a id="1155" href="species.hasse-weil-species.html#1155" class="Bound">l1</a> <a id="1158" href="species.hasse-weil-species.html#1158" class="Bound">l2</a> <a id="1161" class="Symbol">:</a> <a id="1163" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1168" class="Symbol">}</a> <a id="1170" class="Symbol">→</a>
  <a id="1174" class="Symbol">(</a><a id="1175" href="finite-algebra.commutative-finite-rings.html#2193" class="Function">Finite-Commutative-Ring</a> <a id="1199" href="species.hasse-weil-species.html#1155" class="Bound">l1</a> <a id="1202" class="Symbol">→</a> <a id="1204" href="univalent-combinatorics.finite-types.html#2700" class="Function">Finite-Type</a> <a id="1216" href="species.hasse-weil-species.html#1158" class="Bound">l2</a><a id="1218" class="Symbol">)</a> <a id="1220" class="Symbol">→</a>
  <a id="1224" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1227" class="Symbol">(</a><a id="1228" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1233" href="species.hasse-weil-species.html#1155" class="Bound">l1</a> <a id="1236" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1238" href="species.hasse-weil-species.html#1158" class="Bound">l2</a><a id="1240" class="Symbol">)</a>
<a id="1242" href="species.hasse-weil-species.html#1087" class="Function">is-closed-under-products-function-from-Finite-Commutative-Ring</a> <a id="1305" class="Symbol">{</a><a id="1306" href="species.hasse-weil-species.html#1306" class="Bound">l1</a><a id="1308" class="Symbol">}</a> <a id="1310" class="Symbol">{</a><a id="1311" href="species.hasse-weil-species.html#1311" class="Bound">l2</a><a id="1313" class="Symbol">}</a> <a id="1315" href="species.hasse-weil-species.html#1315" class="Bound">S</a> <a id="1317" class="Symbol">=</a>
  <a id="1321" class="Symbol">(</a><a id="1322" href="species.hasse-weil-species.html#1322" class="Bound">R1</a> <a id="1325" href="species.hasse-weil-species.html#1325" class="Bound">R2</a> <a id="1328" class="Symbol">:</a> <a id="1330" href="finite-algebra.commutative-finite-rings.html#2193" class="Function">Finite-Commutative-Ring</a> <a id="1354" href="species.hasse-weil-species.html#1306" class="Bound">l1</a><a id="1356" class="Symbol">)</a> <a id="1358" class="Symbol">→</a>
  <a id="1362" class="Symbol">(</a> <a id="1364" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a> <a id="1381" class="Symbol">(</a><a id="1382" href="species.hasse-weil-species.html#1315" class="Bound">S</a> <a id="1384" class="Symbol">(</a><a id="1385" href="finite-algebra.products-commutative-finite-rings.html#10747" class="Function">product-Finite-Commutative-Ring</a> <a id="1417" href="species.hasse-weil-species.html#1322" class="Bound">R1</a> <a id="1420" href="species.hasse-weil-species.html#1325" class="Bound">R2</a><a id="1422" class="Symbol">)))</a> <a id="1426" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
  <a id="1430" class="Symbol">(</a> <a id="1432" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a> <a id="1449" class="Symbol">(</a><a id="1450" href="species.hasse-weil-species.html#1315" class="Bound">S</a> <a id="1452" href="species.hasse-weil-species.html#1322" class="Bound">R1</a><a id="1454" class="Symbol">)</a> <a id="1456" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1458" href="univalent-combinatorics.finite-types.html#2776" class="Function">type-Finite-Type</a> <a id="1475" class="Symbol">(</a><a id="1476" href="species.hasse-weil-species.html#1315" class="Bound">S</a> <a id="1478" href="species.hasse-weil-species.html#1325" class="Bound">R2</a><a id="1480" class="Symbol">))</a>
</pre>
```text
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (S : Finite-Commutative-Ring l1 → Finite-Type l2)
  (C : is-closed-under-products-function-from-Finite-Commutative-Ring S)
  where

  hasse-weil-species-Inhabited-Finite-Type :
    species-Inhabited-Finite-Type l1 (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  hasse-weil-species-Inhabited-Finite-Type ( k , (f , i)) =
    Σ-Finite-Type
      {!!}
      ( λ p →
        S
          ( commutative-finite-ring-Semisimple-Finite-Commutative-Ring
            ( finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-Finite-Type
              ( l3)
              ( l4)
              ( k , f)
              ( p))))
```
