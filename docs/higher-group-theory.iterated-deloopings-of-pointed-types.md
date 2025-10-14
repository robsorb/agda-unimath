# Iterated deloopings of pointed types

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="higher-group-theory.iterated-deloopings-of-pointed-types.html" class="Module">higher-group-theory.iterated-deloopings-of-pointed-types</a> <a id="113" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="434" class="Keyword">open</a> <a id="439" class="Keyword">import</a> <a id="446" href="structured-types.pointed-equivalences.html" class="Module">structured-types.pointed-equivalences</a>
<a id="484" class="Keyword">open</a> <a id="489" class="Keyword">import</a> <a id="496" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="528" class="Keyword">open</a> <a id="533" class="Keyword">import</a> <a id="540" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a>
</pre>
</details>

## Idea

The type of {{#concept "`n`-fold deloopings" Disambiguation="pointed type"}} of
a [pointed type](structured-types.pointed-types.md) `X` is the type

```text
  Σ (Y : Pointed-Type), is-connected (n-1) Y × (Ωⁿ X ≃∗ Y).
```

Here, the pointed type `Ωⁿ X` is the `n`-th
[iterated loop space](synthetic-homotopy-theory.iterated-loop-spaces.md) of `X`.

## Definitions

### The type of `n`-fold deloopings of a pointed type, with respect to a universe level

<pre class="Agda"><a id="1074" class="Keyword">module</a> <a id="1081" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1081" class="Module">_</a>
  <a id="1085" class="Symbol">{</a><a id="1086" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1086" class="Bound">l1</a> <a id="1089" class="Symbol">:</a> <a id="1091" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1096" class="Symbol">}</a> <a id="1098" class="Symbol">(</a><a id="1099" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1099" class="Bound">l2</a> <a id="1102" class="Symbol">:</a> <a id="1104" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1109" class="Symbol">)</a> <a id="1111" class="Symbol">(</a><a id="1112" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1112" class="Bound">n</a> <a id="1114" class="Symbol">:</a> <a id="1116" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1117" class="Symbol">)</a> <a id="1119" class="Symbol">(</a><a id="1120" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1120" class="Bound">X</a> <a id="1122" class="Symbol">:</a> <a id="1124" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1137" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1086" class="Bound">l1</a><a id="1139" class="Symbol">)</a>
  <a id="1143" class="Keyword">where</a>

  <a id="1152" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1152" class="Function">iterated-delooping-Level</a> <a id="1177" class="Symbol">:</a> <a id="1179" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1182" class="Symbol">(</a><a id="1183" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1086" class="Bound">l1</a> <a id="1186" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1188" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1193" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1099" class="Bound">l2</a><a id="1195" class="Symbol">)</a>
  <a id="1199" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1152" class="Function">iterated-delooping-Level</a> <a id="1224" class="Symbol">=</a>
    <a id="1230" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1232" class="Symbol">(</a> <a id="1234" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1247" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1099" class="Bound">l2</a><a id="1249" class="Symbol">)</a>
      <a id="1257" class="Symbol">(</a> <a id="1259" class="Symbol">λ</a> <a id="1261" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1261" class="Bound">Y</a> <a id="1263" class="Symbol">→</a>
        <a id="1273" class="Symbol">(</a> <a id="1275" href="foundation.connected-types.html#1379" class="Function">is-connected</a> <a id="1288" class="Symbol">(</a><a id="1289" href="foundation.truncation-levels.html#692" class="Function">truncation-level-minus-one-ℕ</a> <a id="1318" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1112" class="Bound">n</a><a id="1319" class="Symbol">)</a> <a id="1321" class="Symbol">(</a><a id="1322" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1340" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1261" class="Bound">Y</a><a id="1341" class="Symbol">))</a> <a id="1344" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
        <a id="1354" class="Symbol">(</a> <a id="1356" href="synthetic-homotopy-theory.iterated-loop-spaces.html#841" class="Function">iterated-loop-space</a> <a id="1376" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1112" class="Bound">n</a> <a id="1378" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1120" class="Bound">X</a> <a id="1380" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="1383" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1261" class="Bound">Y</a><a id="1384" class="Symbol">))</a>
</pre>
### The type of `n`-fold deloopings of a pointed type

<pre class="Agda"><a id="1455" class="Keyword">module</a> <a id="1462" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1462" class="Module">_</a>
  <a id="1466" class="Symbol">{</a><a id="1467" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1467" class="Bound">l1</a> <a id="1470" class="Symbol">:</a> <a id="1472" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1477" class="Symbol">}</a> <a id="1479" class="Symbol">(</a><a id="1480" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1480" class="Bound">n</a> <a id="1482" class="Symbol">:</a> <a id="1484" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1485" class="Symbol">)</a> <a id="1487" class="Symbol">(</a><a id="1488" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1488" class="Bound">X</a> <a id="1490" class="Symbol">:</a> <a id="1492" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1505" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1467" class="Bound">l1</a><a id="1507" class="Symbol">)</a>
  <a id="1511" class="Keyword">where</a>

  <a id="1520" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1520" class="Function">iterated-delooping</a> <a id="1539" class="Symbol">:</a> <a id="1541" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1544" class="Symbol">(</a><a id="1545" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1550" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1467" class="Bound">l1</a><a id="1552" class="Symbol">)</a>
  <a id="1556" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1520" class="Function">iterated-delooping</a> <a id="1575" class="Symbol">=</a> <a id="1577" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1152" class="Function">iterated-delooping-Level</a> <a id="1602" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1467" class="Bound">l1</a> <a id="1605" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1480" class="Bound">n</a> <a id="1607" href="higher-group-theory.iterated-deloopings-of-pointed-types.html#1488" class="Bound">X</a>
</pre>