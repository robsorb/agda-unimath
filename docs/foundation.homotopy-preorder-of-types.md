# The homotopy preorder of types

<pre class="Agda"><a id="43" class="Keyword">module</a>
  <a id="52" href="foundation.homotopy-preorder-of-types.html" class="Module">foundation.homotopy-preorder-of-types</a>
  <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.mere-functions.html" class="Module">foundation.mere-functions</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="416" class="Keyword">open</a> <a id="421" class="Keyword">import</a> <a id="428" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="456" class="Keyword">open</a> <a id="461" class="Keyword">import</a> <a id="468" href="order-theory.large-preorders.html" class="Module">order-theory.large-preorders</a>
<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="529" class="Keyword">open</a> <a id="534" class="Keyword">import</a> <a id="541" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
</pre>
</details>

## Idea

The {{#concept "homotopy preorder of types" Agda=Homotopy-Type-Large-Preorder}}
is the [(large) preorder](order-theory.large-preorders.md) whose objects are
types, and whose ordering relation is defined by
[mere functions](foundation.mere-functions.md), i.e. by the
[propositional truncation](foundation.propositional-truncations.md) of the
function types:

```text
  A ≤ B := ║(A → B)║₋₁.
```

## Definitions

### The large homotopy preorder of types

<pre class="Agda"><a id="Homotopy-Type-Large-Preorder"></a><a id="1051" href="foundation.homotopy-preorder-of-types.html#1051" class="Function">Homotopy-Type-Large-Preorder</a> <a id="1080" class="Symbol">:</a> <a id="1082" href="order-theory.large-preorders.html#926" class="Record">Large-Preorder</a> <a id="1097" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1102" class="Symbol">(</a><a id="1103" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1106" class="Symbol">)</a>
<a id="1108" href="foundation.homotopy-preorder-of-types.html#1051" class="Function">Homotopy-Type-Large-Preorder</a> <a id="1137" class="Symbol">=</a>
  <a id="1141" class="Symbol">λ</a> <a id="1143" class="Keyword">where</a>
  <a id="1151" class="Symbol">.</a><a id="1152" href="order-theory.large-preorders.html#1051" class="Field">type-Large-Preorder</a> <a id="1172" href="foundation.homotopy-preorder-of-types.html#1172" class="Bound">l</a> <a id="1174" class="Symbol">→</a> <a id="1176" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1179" href="foundation.homotopy-preorder-of-types.html#1172" class="Bound">l</a>
  <a id="1183" class="Symbol">.</a><a id="1184" href="order-theory.large-preorders.html#1100" class="Field">leq-prop-Large-Preorder</a> <a id="1208" class="Symbol">→</a> <a id="1210" href="foundation.mere-functions.html#699" class="Function">prop-mere-function</a>
  <a id="1231" class="Symbol">.</a><a id="1232" href="order-theory.large-preorders.html#1172" class="Field">refl-leq-Large-Preorder</a> <a id="1256" class="Symbol">→</a> <a id="1258" href="foundation.mere-functions.html#1583" class="Function">refl-mere-function</a>
  <a id="1279" class="Symbol">.</a><a id="1280" href="order-theory.large-preorders.html#1307" class="Field">transitive-leq-Large-Preorder</a> <a id="1310" href="foundation.homotopy-preorder-of-types.html#1310" class="Bound">X</a> <a id="1312" href="foundation.homotopy-preorder-of-types.html#1312" class="Bound">Y</a> <a id="1314" href="foundation.homotopy-preorder-of-types.html#1314" class="Bound">Z</a> <a id="1316" class="Symbol">→</a> <a id="1318" href="foundation.mere-functions.html#1801" class="Function">transitive-mere-function</a>
</pre>
### The small homotopy preorder of types

<pre class="Agda"><a id="Homotopy-Type-Preorder"></a><a id="1398" href="foundation.homotopy-preorder-of-types.html#1398" class="Function">Homotopy-Type-Preorder</a> <a id="1421" class="Symbol">:</a> <a id="1423" class="Symbol">(</a><a id="1424" href="foundation.homotopy-preorder-of-types.html#1424" class="Bound">l</a> <a id="1426" class="Symbol">:</a> <a id="1428" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1433" class="Symbol">)</a> <a id="1435" class="Symbol">→</a> <a id="1437" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="1446" class="Symbol">(</a><a id="1447" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1452" href="foundation.homotopy-preorder-of-types.html#1424" class="Bound">l</a><a id="1453" class="Symbol">)</a> <a id="1455" href="foundation.homotopy-preorder-of-types.html#1424" class="Bound">l</a>
<a id="1457" href="foundation.homotopy-preorder-of-types.html#1398" class="Function">Homotopy-Type-Preorder</a> <a id="1480" class="Symbol">=</a> <a id="1482" href="order-theory.large-preorders.html#3384" class="Function">preorder-Large-Preorder</a> <a id="1506" href="foundation.homotopy-preorder-of-types.html#1051" class="Function">Homotopy-Type-Large-Preorder</a>
</pre>