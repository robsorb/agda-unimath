# Morphisms of descent data of the circle

<pre class="Agda"><a id="52" class="Keyword">module</a> <a id="59" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html" class="Module">synthetic-homotopy-theory.morphisms-descent-data-circle</a> <a id="115" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="structured-types.morphisms-types-equipped-with-automorphisms.html" class="Module">structured-types.morphisms-types-equipped-with-automorphisms</a>

<a id="334" class="Keyword">open</a> <a id="339" class="Keyword">import</a> <a id="346" href="synthetic-homotopy-theory.descent-circle.html" class="Module">synthetic-homotopy-theory.descent-circle</a>
</pre>
</details>

## Idea

Given two [descent data](synthetic-homotopy-theory.descent-circle.md) `(A,e)`
and `(B,f)` over the [circle](synthetic-homotopy-theory.circle.md), a
**morphism** `h` of descent data between `(A, e)` and `(B, f) `is a map `h` from
`A` to `B` such that the square

```text
      h
  A -----> B
  |        |
 e|        |f
  ∨        ∨
  A -----> B
      h
```

[commutes](foundation.commuting-squares-of-maps.md).

## Definitions

### Morphisms of descent data for the circle

<pre class="Agda"><a id="hom-descent-data-circle"></a><a id="894" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#894" class="Function">hom-descent-data-circle</a> <a id="918" class="Symbol">:</a>
  <a id="922" class="Symbol">{</a> <a id="924" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#924" class="Bound">l1</a> <a id="927" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#927" class="Bound">l2</a> <a id="930" class="Symbol">:</a> <a id="932" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="937" class="Symbol">}</a>
  <a id="941" class="Symbol">(</a> <a id="943" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#943" class="Bound">P</a> <a id="945" class="Symbol">:</a> <a id="947" href="synthetic-homotopy-theory.descent-circle.html#1763" class="Function">descent-data-circle</a> <a id="967" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#924" class="Bound">l1</a><a id="969" class="Symbol">)</a> <a id="971" class="Symbol">(</a><a id="972" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#972" class="Bound">Q</a> <a id="974" class="Symbol">:</a> <a id="976" href="synthetic-homotopy-theory.descent-circle.html#1763" class="Function">descent-data-circle</a> <a id="996" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#927" class="Bound">l2</a><a id="998" class="Symbol">)</a> <a id="1000" class="Symbol">→</a>
  <a id="1004" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1007" class="Symbol">(</a><a id="1008" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#924" class="Bound">l1</a> <a id="1011" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1013" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#927" class="Bound">l2</a><a id="1015" class="Symbol">)</a>
<a id="1017" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#894" class="Function">hom-descent-data-circle</a> <a id="1041" class="Symbol">=</a> <a id="1043" href="structured-types.morphisms-types-equipped-with-automorphisms.html#1165" class="Function">hom-Type-With-Automorphism</a>

<a id="1071" class="Keyword">module</a> <a id="1078" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1078" class="Module">_</a>
  <a id="1082" class="Symbol">{</a> <a id="1084" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1084" class="Bound">l1</a> <a id="1087" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1087" class="Bound">l2</a> <a id="1090" class="Symbol">:</a> <a id="1092" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1097" class="Symbol">}</a> <a id="1099" class="Symbol">(</a><a id="1100" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1100" class="Bound">P</a> <a id="1102" class="Symbol">:</a> <a id="1104" href="synthetic-homotopy-theory.descent-circle.html#1763" class="Function">descent-data-circle</a> <a id="1124" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1084" class="Bound">l1</a><a id="1126" class="Symbol">)</a> <a id="1128" class="Symbol">(</a><a id="1129" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1129" class="Bound">Q</a> <a id="1131" class="Symbol">:</a> <a id="1133" href="synthetic-homotopy-theory.descent-circle.html#1763" class="Function">descent-data-circle</a> <a id="1153" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1087" class="Bound">l2</a><a id="1155" class="Symbol">)</a>
  <a id="1159" class="Symbol">(</a> <a id="1161" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1161" class="Bound">h</a> <a id="1163" class="Symbol">:</a> <a id="1165" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#894" class="Function">hom-descent-data-circle</a> <a id="1189" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1100" class="Bound">P</a> <a id="1191" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1129" class="Bound">Q</a><a id="1192" class="Symbol">)</a>
  <a id="1196" class="Keyword">where</a>

  <a id="1205" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1205" class="Function">map-hom-descent-data-circle</a> <a id="1233" class="Symbol">:</a>
    <a id="1239" href="synthetic-homotopy-theory.descent-circle.html#1927" class="Function">type-descent-data-circle</a> <a id="1264" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1100" class="Bound">P</a> <a id="1266" class="Symbol">→</a> <a id="1268" href="synthetic-homotopy-theory.descent-circle.html#1927" class="Function">type-descent-data-circle</a> <a id="1293" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1129" class="Bound">Q</a>
  <a id="1297" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1205" class="Function">map-hom-descent-data-circle</a> <a id="1325" class="Symbol">=</a>
    <a id="1331" href="structured-types.morphisms-types-equipped-with-automorphisms.html#1386" class="Function">map-hom-Type-With-Automorphism</a> <a id="1362" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1100" class="Bound">P</a> <a id="1364" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1129" class="Bound">Q</a> <a id="1366" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1161" class="Bound">h</a>

  <a id="1371" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1371" class="Function">coherence-square-hom-descent-data-circle</a> <a id="1412" class="Symbol">:</a>
    <a id="1418" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="1446" class="Symbol">(</a> <a id="1448" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1205" class="Function">map-hom-descent-data-circle</a><a id="1475" class="Symbol">)</a>
      <a id="1483" class="Symbol">(</a> <a id="1485" href="synthetic-homotopy-theory.descent-circle.html#2146" class="Function">map-descent-data-circle</a> <a id="1509" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1100" class="Bound">P</a><a id="1510" class="Symbol">)</a>
      <a id="1518" class="Symbol">(</a> <a id="1520" href="synthetic-homotopy-theory.descent-circle.html#2146" class="Function">map-descent-data-circle</a> <a id="1544" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1129" class="Bound">Q</a><a id="1545" class="Symbol">)</a>
      <a id="1553" class="Symbol">(</a> <a id="1555" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1205" class="Function">map-hom-descent-data-circle</a><a id="1582" class="Symbol">)</a>
  <a id="1586" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1371" class="Function">coherence-square-hom-descent-data-circle</a> <a id="1627" class="Symbol">=</a>
    <a id="1633" href="structured-types.morphisms-types-equipped-with-automorphisms.html#1705" class="Function">coherence-square-hom-Type-With-Automorphism</a> <a id="1677" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1100" class="Bound">P</a> <a id="1679" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1129" class="Bound">Q</a> <a id="1681" href="synthetic-homotopy-theory.morphisms-descent-data-circle.html#1161" class="Bound">h</a>
</pre>