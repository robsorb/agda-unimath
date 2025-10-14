# Types equipped with automorphisms

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="structured-types.types-equipped-with-automorphisms.html" class="Module">structured-types.types-equipped-with-automorphisms</a> <a id="104" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="structured-types.types-equipped-with-endomorphisms.html" class="Module">structured-types.types-equipped-with-endomorphisms</a>
</pre>
</details>

## Idea

A **type equipped with an automorphism** is a pair consisting of a type `A` and
an [automorphism](foundation.automorphisms.md) on `e : A ≃ A`.

## Definitions

### Types equipped with automorphisms

<pre class="Agda"><a id="Type-With-Automorphism"></a><a id="613" href="structured-types.types-equipped-with-automorphisms.html#613" class="Function">Type-With-Automorphism</a> <a id="636" class="Symbol">:</a> <a id="638" class="Symbol">(</a><a id="639" href="structured-types.types-equipped-with-automorphisms.html#639" class="Bound">l</a> <a id="641" class="Symbol">:</a> <a id="643" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="648" class="Symbol">)</a> <a id="650" class="Symbol">→</a> <a id="652" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="655" class="Symbol">(</a><a id="656" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="661" href="structured-types.types-equipped-with-automorphisms.html#639" class="Bound">l</a><a id="662" class="Symbol">)</a>
<a id="664" href="structured-types.types-equipped-with-automorphisms.html#613" class="Function">Type-With-Automorphism</a> <a id="687" href="structured-types.types-equipped-with-automorphisms.html#687" class="Bound">l</a> <a id="689" class="Symbol">=</a> <a id="691" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="693" class="Symbol">(</a><a id="694" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="697" href="structured-types.types-equipped-with-automorphisms.html#687" class="Bound">l</a><a id="698" class="Symbol">)</a> <a id="700" class="Symbol">(</a><a id="701" href="foundation.automorphisms.html#538" class="Function">Aut</a><a id="704" class="Symbol">)</a>

<a id="707" class="Keyword">module</a> <a id="714" href="structured-types.types-equipped-with-automorphisms.html#714" class="Module">_</a>
  <a id="718" class="Symbol">{</a><a id="719" href="structured-types.types-equipped-with-automorphisms.html#719" class="Bound">l</a> <a id="721" class="Symbol">:</a> <a id="723" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="728" class="Symbol">}</a> <a id="730" class="Symbol">(</a><a id="731" href="structured-types.types-equipped-with-automorphisms.html#731" class="Bound">A</a> <a id="733" class="Symbol">:</a> <a id="735" href="structured-types.types-equipped-with-automorphisms.html#613" class="Function">Type-With-Automorphism</a> <a id="758" href="structured-types.types-equipped-with-automorphisms.html#719" class="Bound">l</a><a id="759" class="Symbol">)</a>
  <a id="763" class="Keyword">where</a>

  <a id="772" href="structured-types.types-equipped-with-automorphisms.html#772" class="Function">type-Type-With-Automorphism</a> <a id="800" class="Symbol">:</a> <a id="802" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="805" href="structured-types.types-equipped-with-automorphisms.html#719" class="Bound">l</a>
  <a id="809" href="structured-types.types-equipped-with-automorphisms.html#772" class="Function">type-Type-With-Automorphism</a> <a id="837" class="Symbol">=</a> <a id="839" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="843" href="structured-types.types-equipped-with-automorphisms.html#731" class="Bound">A</a>

  <a id="848" href="structured-types.types-equipped-with-automorphisms.html#848" class="Function">automorphism-Type-With-Automorphism</a> <a id="884" class="Symbol">:</a> <a id="886" href="foundation.automorphisms.html#538" class="Function">Aut</a> <a id="890" href="structured-types.types-equipped-with-automorphisms.html#772" class="Function">type-Type-With-Automorphism</a>
  <a id="920" href="structured-types.types-equipped-with-automorphisms.html#848" class="Function">automorphism-Type-With-Automorphism</a> <a id="956" class="Symbol">=</a> <a id="958" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="962" href="structured-types.types-equipped-with-automorphisms.html#731" class="Bound">A</a>

  <a id="967" href="structured-types.types-equipped-with-automorphisms.html#967" class="Function">map-Type-With-Automorphism</a> <a id="994" class="Symbol">:</a>
    <a id="1000" href="structured-types.types-equipped-with-automorphisms.html#772" class="Function">type-Type-With-Automorphism</a> <a id="1028" class="Symbol">→</a> <a id="1030" href="structured-types.types-equipped-with-automorphisms.html#772" class="Function">type-Type-With-Automorphism</a>
  <a id="1060" href="structured-types.types-equipped-with-automorphisms.html#967" class="Function">map-Type-With-Automorphism</a> <a id="1087" class="Symbol">=</a> <a id="1089" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="1099" href="structured-types.types-equipped-with-automorphisms.html#848" class="Function">automorphism-Type-With-Automorphism</a>

  <a id="1138" href="structured-types.types-equipped-with-automorphisms.html#1138" class="Function">type-with-endomorphism-Type-With-Automorphism</a> <a id="1184" class="Symbol">:</a> <a id="1186" href="structured-types.types-equipped-with-endomorphisms.html#530" class="Function">Type-With-Endomorphism</a> <a id="1209" href="structured-types.types-equipped-with-automorphisms.html#719" class="Bound">l</a>
  <a id="1213" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1217" href="structured-types.types-equipped-with-automorphisms.html#1138" class="Function">type-with-endomorphism-Type-With-Automorphism</a> <a id="1263" class="Symbol">=</a>
    <a id="1269" href="structured-types.types-equipped-with-automorphisms.html#772" class="Function">type-Type-With-Automorphism</a>
  <a id="1299" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1303" href="structured-types.types-equipped-with-automorphisms.html#1138" class="Function">type-with-endomorphism-Type-With-Automorphism</a> <a id="1349" class="Symbol">=</a>
    <a id="1355" href="structured-types.types-equipped-with-automorphisms.html#967" class="Function">map-Type-With-Automorphism</a>
</pre>
### Types equipped with the identity automorphism

<pre class="Agda"><a id="trivial-Type-With-Automorphism"></a><a id="1446" href="structured-types.types-equipped-with-automorphisms.html#1446" class="Function">trivial-Type-With-Automorphism</a> <a id="1477" class="Symbol">:</a> <a id="1479" class="Symbol">{</a><a id="1480" href="structured-types.types-equipped-with-automorphisms.html#1480" class="Bound">l</a> <a id="1482" class="Symbol">:</a> <a id="1484" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1489" class="Symbol">}</a> <a id="1491" class="Symbol">→</a> <a id="1493" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1496" href="structured-types.types-equipped-with-automorphisms.html#1480" class="Bound">l</a> <a id="1498" class="Symbol">→</a> <a id="1500" href="structured-types.types-equipped-with-automorphisms.html#613" class="Function">Type-With-Automorphism</a> <a id="1523" href="structured-types.types-equipped-with-automorphisms.html#1480" class="Bound">l</a>
<a id="1525" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1529" class="Symbol">(</a><a id="1530" href="structured-types.types-equipped-with-automorphisms.html#1446" class="Function">trivial-Type-With-Automorphism</a> <a id="1561" href="structured-types.types-equipped-with-automorphisms.html#1561" class="Bound">X</a><a id="1562" class="Symbol">)</a> <a id="1564" class="Symbol">=</a> <a id="1566" href="structured-types.types-equipped-with-automorphisms.html#1561" class="Bound">X</a>
<a id="1568" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1572" class="Symbol">(</a><a id="1573" href="structured-types.types-equipped-with-automorphisms.html#1446" class="Function">trivial-Type-With-Automorphism</a> <a id="1604" href="structured-types.types-equipped-with-automorphisms.html#1604" class="Bound">X</a><a id="1605" class="Symbol">)</a> <a id="1607" class="Symbol">=</a> <a id="1609" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
</pre>
## See also

- Sets equipped with automorphisms are defined in
  [`structured-types.sets-equipped-with-automorphisms`](structured-types.sets-equipped-with-automorphisms.md)
- Cyclic types are
  [sets equipped with automorphisms](structured-types.sets-equipped-with-automorphisms.md)
  of which the automorphism acts transitively.
- The
  [descent property of the circle](synthetic-homotopy-theory.descent-circle.md)
  shows that type families over the
  [circle](synthetic-homotopy-theory.circle.md) are
  [equivalently](foundation.equivalences.md) described as types equipped with
  automorphisms.
