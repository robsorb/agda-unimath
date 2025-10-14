# Transitive well-founded relations

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="order-theory.transitive-well-founded-relations.html" class="Module">order-theory.transitive-well-founded-relations</a> <a id="100" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="order-theory.well-founded-relations.html" class="Module">order-theory.well-founded-relations</a>
</pre>
</details>

## Idea

A
{{#concept "transitive well-founded relation" Agda=Transitive-Well-Founded-Relation}}
is a [relation](foundation.binary-relations.md) that is
[transitive](foundation.binary-relations.md) and
[well-founded](order-theory.well-founded-relations.md). Note, in particular,
that the relation need not be
[proposition](foundation-core.propositions.md)-valued.

## Definitions

### The predicate of being a transitive well-founded relation

<pre class="Agda"><a id="844" class="Keyword">module</a> <a id="851" href="order-theory.transitive-well-founded-relations.html#851" class="Module">_</a>
  <a id="855" class="Symbol">{</a><a id="856" href="order-theory.transitive-well-founded-relations.html#856" class="Bound">l1</a> <a id="859" href="order-theory.transitive-well-founded-relations.html#859" class="Bound">l2</a> <a id="862" class="Symbol">:</a> <a id="864" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="869" class="Symbol">}</a> <a id="871" class="Symbol">{</a><a id="872" href="order-theory.transitive-well-founded-relations.html#872" class="Bound">X</a> <a id="874" class="Symbol">:</a> <a id="876" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="879" href="order-theory.transitive-well-founded-relations.html#856" class="Bound">l1</a><a id="881" class="Symbol">}</a> <a id="883" class="Symbol">(</a><a id="884" href="order-theory.transitive-well-founded-relations.html#884" class="Bound">R</a> <a id="886" class="Symbol">:</a> <a id="888" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="897" href="order-theory.transitive-well-founded-relations.html#859" class="Bound">l2</a> <a id="900" href="order-theory.transitive-well-founded-relations.html#872" class="Bound">X</a><a id="901" class="Symbol">)</a>
  <a id="905" class="Keyword">where</a>

  <a id="914" href="order-theory.transitive-well-founded-relations.html#914" class="Function">is-transitive-well-founded-relation-Relation</a> <a id="959" class="Symbol">:</a> <a id="961" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="964" class="Symbol">(</a><a id="965" href="order-theory.transitive-well-founded-relations.html#856" class="Bound">l1</a> <a id="968" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="970" href="order-theory.transitive-well-founded-relations.html#859" class="Bound">l2</a><a id="972" class="Symbol">)</a>
  <a id="976" href="order-theory.transitive-well-founded-relations.html#914" class="Function">is-transitive-well-founded-relation-Relation</a> <a id="1021" class="Symbol">=</a>
    <a id="1027" href="order-theory.well-founded-relations.html#1492" class="Function">is-well-founded-Relation</a> <a id="1052" href="order-theory.transitive-well-founded-relations.html#884" class="Bound">R</a> <a id="1054" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1056" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="1070" href="order-theory.transitive-well-founded-relations.html#884" class="Bound">R</a>
</pre>
### Transitive well-founded relations

<pre class="Agda"><a id="Transitive-Well-Founded-Relation"></a><a id="1124" href="order-theory.transitive-well-founded-relations.html#1124" class="Function">Transitive-Well-Founded-Relation</a> <a id="1157" class="Symbol">:</a>
  <a id="1161" class="Symbol">{</a><a id="1162" href="order-theory.transitive-well-founded-relations.html#1162" class="Bound">l1</a> <a id="1165" class="Symbol">:</a> <a id="1167" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1172" class="Symbol">}</a> <a id="1174" class="Symbol">(</a><a id="1175" href="order-theory.transitive-well-founded-relations.html#1175" class="Bound">l2</a> <a id="1178" class="Symbol">:</a> <a id="1180" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1185" class="Symbol">)</a> <a id="1187" class="Symbol">→</a> <a id="1189" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1192" href="order-theory.transitive-well-founded-relations.html#1162" class="Bound">l1</a> <a id="1195" class="Symbol">→</a> <a id="1197" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1200" class="Symbol">(</a><a id="1201" href="order-theory.transitive-well-founded-relations.html#1162" class="Bound">l1</a> <a id="1204" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1206" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1211" href="order-theory.transitive-well-founded-relations.html#1175" class="Bound">l2</a><a id="1213" class="Symbol">)</a>
<a id="1215" href="order-theory.transitive-well-founded-relations.html#1124" class="Function">Transitive-Well-Founded-Relation</a> <a id="1248" href="order-theory.transitive-well-founded-relations.html#1248" class="Bound">l2</a> <a id="1251" href="order-theory.transitive-well-founded-relations.html#1251" class="Bound">X</a> <a id="1253" class="Symbol">=</a>
  <a id="1257" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1259" class="Symbol">(</a><a id="1260" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1269" href="order-theory.transitive-well-founded-relations.html#1248" class="Bound">l2</a> <a id="1272" href="order-theory.transitive-well-founded-relations.html#1251" class="Bound">X</a><a id="1273" class="Symbol">)</a> <a id="1275" href="order-theory.transitive-well-founded-relations.html#914" class="Function">is-transitive-well-founded-relation-Relation</a>

<a id="1321" class="Keyword">module</a> <a id="1328" href="order-theory.transitive-well-founded-relations.html#1328" class="Module">_</a>
  <a id="1332" class="Symbol">{</a><a id="1333" href="order-theory.transitive-well-founded-relations.html#1333" class="Bound">l1</a> <a id="1336" href="order-theory.transitive-well-founded-relations.html#1336" class="Bound">l2</a> <a id="1339" class="Symbol">:</a> <a id="1341" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1346" class="Symbol">}</a> <a id="1348" class="Symbol">{</a><a id="1349" href="order-theory.transitive-well-founded-relations.html#1349" class="Bound">X</a> <a id="1351" class="Symbol">:</a> <a id="1353" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1356" href="order-theory.transitive-well-founded-relations.html#1333" class="Bound">l1</a><a id="1358" class="Symbol">}</a> <a id="1360" class="Symbol">(</a><a id="1361" href="order-theory.transitive-well-founded-relations.html#1361" class="Bound">R</a> <a id="1363" class="Symbol">:</a> <a id="1365" href="order-theory.transitive-well-founded-relations.html#1124" class="Function">Transitive-Well-Founded-Relation</a> <a id="1398" href="order-theory.transitive-well-founded-relations.html#1336" class="Bound">l2</a> <a id="1401" href="order-theory.transitive-well-founded-relations.html#1349" class="Bound">X</a><a id="1402" class="Symbol">)</a>
  <a id="1406" class="Keyword">where</a>

  <a id="1415" href="order-theory.transitive-well-founded-relations.html#1415" class="Function">le-Transitive-Well-Founded-Relation</a> <a id="1451" class="Symbol">:</a> <a id="1453" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1462" href="order-theory.transitive-well-founded-relations.html#1336" class="Bound">l2</a> <a id="1465" href="order-theory.transitive-well-founded-relations.html#1349" class="Bound">X</a>
  <a id="1469" href="order-theory.transitive-well-founded-relations.html#1415" class="Function">le-Transitive-Well-Founded-Relation</a> <a id="1505" class="Symbol">=</a> <a id="1507" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1511" href="order-theory.transitive-well-founded-relations.html#1361" class="Bound">R</a>

  <a id="1516" href="order-theory.transitive-well-founded-relations.html#1516" class="Function">is-transitive-well-founded-relation-Transitive-Well-Founded-Relation</a> <a id="1585" class="Symbol">:</a>
    <a id="1591" href="order-theory.transitive-well-founded-relations.html#914" class="Function">is-transitive-well-founded-relation-Relation</a>
      <a id="1642" href="order-theory.transitive-well-founded-relations.html#1415" class="Function">le-Transitive-Well-Founded-Relation</a>
  <a id="1680" href="order-theory.transitive-well-founded-relations.html#1516" class="Function">is-transitive-well-founded-relation-Transitive-Well-Founded-Relation</a> <a id="1749" class="Symbol">=</a> <a id="1751" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1755" href="order-theory.transitive-well-founded-relations.html#1361" class="Bound">R</a>

  <a id="1760" href="order-theory.transitive-well-founded-relations.html#1760" class="Function">is-well-founded-relation-le-Transitive-Well-Founded-Relation</a> <a id="1821" class="Symbol">:</a>
    <a id="1827" href="order-theory.well-founded-relations.html#1492" class="Function">is-well-founded-Relation</a> <a id="1852" href="order-theory.transitive-well-founded-relations.html#1415" class="Function">le-Transitive-Well-Founded-Relation</a>
  <a id="1890" href="order-theory.transitive-well-founded-relations.html#1760" class="Function">is-well-founded-relation-le-Transitive-Well-Founded-Relation</a> <a id="1951" class="Symbol">=</a>
    <a id="1957" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1961" href="order-theory.transitive-well-founded-relations.html#1516" class="Function">is-transitive-well-founded-relation-Transitive-Well-Founded-Relation</a>

  <a id="2033" href="order-theory.transitive-well-founded-relations.html#2033" class="Function">is-transitive-le-Transitive-Well-Founded-Relation</a> <a id="2083" class="Symbol">:</a>
    <a id="2089" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2103" href="order-theory.transitive-well-founded-relations.html#1415" class="Function">le-Transitive-Well-Founded-Relation</a>
  <a id="2141" href="order-theory.transitive-well-founded-relations.html#2033" class="Function">is-transitive-le-Transitive-Well-Founded-Relation</a> <a id="2191" class="Symbol">=</a>
    <a id="2197" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2201" href="order-theory.transitive-well-founded-relations.html#1516" class="Function">is-transitive-well-founded-relation-Transitive-Well-Founded-Relation</a>

  <a id="2273" href="order-theory.transitive-well-founded-relations.html#2273" class="Function">well-founded-relation-Transitive-Well-Founded-Relation</a> <a id="2328" class="Symbol">:</a>
    <a id="2334" href="order-theory.well-founded-relations.html#1649" class="Function">Well-Founded-Relation</a> <a id="2356" href="order-theory.transitive-well-founded-relations.html#1336" class="Bound">l2</a> <a id="2359" href="order-theory.transitive-well-founded-relations.html#1349" class="Bound">X</a>
  <a id="2363" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2367" href="order-theory.transitive-well-founded-relations.html#2273" class="Function">well-founded-relation-Transitive-Well-Founded-Relation</a> <a id="2422" class="Symbol">=</a>
    <a id="2428" href="order-theory.transitive-well-founded-relations.html#1415" class="Function">le-Transitive-Well-Founded-Relation</a>
  <a id="2466" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2470" href="order-theory.transitive-well-founded-relations.html#2273" class="Function">well-founded-relation-Transitive-Well-Founded-Relation</a> <a id="2525" class="Symbol">=</a>
    <a id="2531" href="order-theory.transitive-well-founded-relations.html#1760" class="Function">is-well-founded-relation-le-Transitive-Well-Founded-Relation</a>

  <a id="2595" href="order-theory.transitive-well-founded-relations.html#2595" class="Function">is-asymmetric-le-Transitive-Well-Founded-Relation</a> <a id="2645" class="Symbol">:</a>
    <a id="2651" href="foundation.binary-relations.html#6086" class="Function">is-asymmetric</a> <a id="2665" href="order-theory.transitive-well-founded-relations.html#1415" class="Function">le-Transitive-Well-Founded-Relation</a>
  <a id="2703" href="order-theory.transitive-well-founded-relations.html#2595" class="Function">is-asymmetric-le-Transitive-Well-Founded-Relation</a> <a id="2753" class="Symbol">=</a>
    <a id="2759" href="order-theory.well-founded-relations.html#2626" class="Function">is-asymmetric-le-Well-Founded-Relation</a>
      <a id="2804" class="Symbol">(</a> <a id="2806" href="order-theory.transitive-well-founded-relations.html#2273" class="Function">well-founded-relation-Transitive-Well-Founded-Relation</a><a id="2860" class="Symbol">)</a>

  <a id="2865" href="order-theory.transitive-well-founded-relations.html#2865" class="Function">is-irreflexive-le-Transitive-Well-Founded-Relation</a> <a id="2916" class="Symbol">:</a>
    <a id="2922" href="foundation.binary-relations.html#5565" class="Function">is-irreflexive</a> <a id="2937" href="order-theory.transitive-well-founded-relations.html#1415" class="Function">le-Transitive-Well-Founded-Relation</a>
  <a id="2975" href="order-theory.transitive-well-founded-relations.html#2865" class="Function">is-irreflexive-le-Transitive-Well-Founded-Relation</a> <a id="3026" class="Symbol">=</a>
    <a id="3032" href="order-theory.well-founded-relations.html#2875" class="Function">is-irreflexive-le-Well-Founded-Relation</a>
      <a id="3078" class="Symbol">(</a> <a id="3080" href="order-theory.transitive-well-founded-relations.html#2273" class="Function">well-founded-relation-Transitive-Well-Founded-Relation</a><a id="3134" class="Symbol">)</a>
</pre>
### The associated reflexive relation of a transitive well-founded relation

Given a transitive well-founded relation `P` there is an associated reflexive
relation given by

$$
  (x ≤ y) := (u : X) → u ∈ x → u ∈ y.
$$

<pre class="Agda"><a id="3368" class="Keyword">module</a> <a id="3375" href="order-theory.transitive-well-founded-relations.html#3375" class="Module">_</a>
  <a id="3379" class="Symbol">{</a><a id="3380" href="order-theory.transitive-well-founded-relations.html#3380" class="Bound">l1</a> <a id="3383" href="order-theory.transitive-well-founded-relations.html#3383" class="Bound">l2</a> <a id="3386" class="Symbol">:</a> <a id="3388" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3393" class="Symbol">}</a> <a id="3395" class="Symbol">{</a><a id="3396" href="order-theory.transitive-well-founded-relations.html#3396" class="Bound">X</a> <a id="3398" class="Symbol">:</a> <a id="3400" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3403" href="order-theory.transitive-well-founded-relations.html#3380" class="Bound">l1</a><a id="3405" class="Symbol">}</a> <a id="3407" class="Symbol">(</a><a id="3408" href="order-theory.transitive-well-founded-relations.html#3408" class="Bound">R</a> <a id="3410" class="Symbol">:</a> <a id="3412" href="order-theory.transitive-well-founded-relations.html#1124" class="Function">Transitive-Well-Founded-Relation</a> <a id="3445" href="order-theory.transitive-well-founded-relations.html#3383" class="Bound">l2</a> <a id="3448" href="order-theory.transitive-well-founded-relations.html#3396" class="Bound">X</a><a id="3449" class="Symbol">)</a>
  <a id="3453" class="Keyword">where</a>

  <a id="3462" href="order-theory.transitive-well-founded-relations.html#3462" class="Function">leq-Transitive-Well-Founded-Relation</a> <a id="3499" class="Symbol">:</a>
    <a id="3505" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="3514" class="Symbol">(</a><a id="3515" href="order-theory.transitive-well-founded-relations.html#3380" class="Bound">l1</a> <a id="3518" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3520" href="order-theory.transitive-well-founded-relations.html#3383" class="Bound">l2</a><a id="3522" class="Symbol">)</a> <a id="3524" href="order-theory.transitive-well-founded-relations.html#3396" class="Bound">X</a>
  <a id="3528" href="order-theory.transitive-well-founded-relations.html#3462" class="Function">leq-Transitive-Well-Founded-Relation</a> <a id="3565" class="Symbol">=</a>
    <a id="3571" href="order-theory.well-founded-relations.html#3440" class="Function">leq-Well-Founded-Relation</a>
      <a id="3603" class="Symbol">(</a> <a id="3605" href="order-theory.transitive-well-founded-relations.html#2273" class="Function">well-founded-relation-Transitive-Well-Founded-Relation</a> <a id="3660" href="order-theory.transitive-well-founded-relations.html#3408" class="Bound">R</a><a id="3661" class="Symbol">)</a>

  <a id="3666" href="order-theory.transitive-well-founded-relations.html#3666" class="Function">refl-leq-Transitive-Well-Founded-Relation</a> <a id="3708" class="Symbol">:</a>
    <a id="3714" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="3727" href="order-theory.transitive-well-founded-relations.html#3462" class="Function">leq-Transitive-Well-Founded-Relation</a>
  <a id="3766" href="order-theory.transitive-well-founded-relations.html#3666" class="Function">refl-leq-Transitive-Well-Founded-Relation</a> <a id="3808" class="Symbol">=</a>
    <a id="3814" href="order-theory.well-founded-relations.html#3550" class="Function">refl-leq-Well-Founded-Relation</a>
      <a id="3851" class="Symbol">(</a> <a id="3853" href="order-theory.transitive-well-founded-relations.html#2273" class="Function">well-founded-relation-Transitive-Well-Founded-Relation</a> <a id="3908" href="order-theory.transitive-well-founded-relations.html#3408" class="Bound">R</a><a id="3909" class="Symbol">)</a>

  <a id="3914" href="order-theory.transitive-well-founded-relations.html#3914" class="Function">transitive-leq-Transitive-Well-Founded-Relation</a> <a id="3962" class="Symbol">:</a>
    <a id="3968" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="3982" href="order-theory.transitive-well-founded-relations.html#3462" class="Function">leq-Transitive-Well-Founded-Relation</a>
  <a id="4021" href="order-theory.transitive-well-founded-relations.html#3914" class="Function">transitive-leq-Transitive-Well-Founded-Relation</a> <a id="4069" class="Symbol">=</a>
    <a id="4075" href="order-theory.well-founded-relations.html#3830" class="Function">transitive-leq-Well-Founded-Relation</a>
      <a id="4118" class="Symbol">(</a> <a id="4120" href="order-theory.transitive-well-founded-relations.html#2273" class="Function">well-founded-relation-Transitive-Well-Founded-Relation</a> <a id="4175" href="order-theory.transitive-well-founded-relations.html#3408" class="Bound">R</a><a id="4176" class="Symbol">)</a>
</pre>