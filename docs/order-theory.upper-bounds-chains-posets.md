# Upper bounds of chains in posets

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="order-theory.upper-bounds-chains-posets.html" class="Module">order-theory.upper-bounds-chains-posets</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>

<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="order-theory.chains-posets.html" class="Module">order-theory.chains-posets</a>
<a id="362" class="Keyword">open</a> <a id="367" class="Keyword">import</a> <a id="374" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="order-theory.upper-bounds-posets.html" class="Module">order-theory.upper-bounds-posets</a>
</pre>
</details>

## Idea

An
{{#concept "upper bound" Disambiguation="on a chain in a poset" Agda=is-upper-bound-chain-Poset}}
on a [chain](order-theory.chains-posets.md) `C` in a
[poset](order-theory.posets.md) `P` is an element `x` such that for every
element `y` in `C`, `y ≤ x` holds.

## Definition

<pre class="Agda"><a id="752" class="Keyword">module</a> <a id="759" href="order-theory.upper-bounds-chains-posets.html#759" class="Module">_</a>
  <a id="763" class="Symbol">{</a><a id="764" href="order-theory.upper-bounds-chains-posets.html#764" class="Bound">l1</a> <a id="767" href="order-theory.upper-bounds-chains-posets.html#767" class="Bound">l2</a> <a id="770" href="order-theory.upper-bounds-chains-posets.html#770" class="Bound">l3</a> <a id="773" class="Symbol">:</a> <a id="775" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="780" class="Symbol">}</a> <a id="782" class="Symbol">(</a><a id="783" href="order-theory.upper-bounds-chains-posets.html#783" class="Bound">X</a> <a id="785" class="Symbol">:</a> <a id="787" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="793" href="order-theory.upper-bounds-chains-posets.html#764" class="Bound">l1</a> <a id="796" href="order-theory.upper-bounds-chains-posets.html#767" class="Bound">l2</a><a id="798" class="Symbol">)</a> <a id="800" class="Symbol">(</a><a id="801" href="order-theory.upper-bounds-chains-posets.html#801" class="Bound">C</a> <a id="803" class="Symbol">:</a> <a id="805" href="order-theory.chains-posets.html#1586" class="Function">chain-Poset</a> <a id="817" href="order-theory.upper-bounds-chains-posets.html#770" class="Bound">l3</a> <a id="820" href="order-theory.upper-bounds-chains-posets.html#783" class="Bound">X</a><a id="821" class="Symbol">)</a>
  <a id="825" class="Keyword">where</a>

  <a id="834" href="order-theory.upper-bounds-chains-posets.html#834" class="Function">is-upper-bound-chain-prop-Poset</a> <a id="866" class="Symbol">:</a> <a id="868" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="879" href="order-theory.upper-bounds-chains-posets.html#783" class="Bound">X</a> <a id="881" class="Symbol">→</a> <a id="883" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="888" class="Symbol">(</a><a id="889" href="order-theory.upper-bounds-chains-posets.html#764" class="Bound">l1</a> <a id="892" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="894" href="order-theory.upper-bounds-chains-posets.html#767" class="Bound">l2</a> <a id="897" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="899" href="order-theory.upper-bounds-chains-posets.html#770" class="Bound">l3</a><a id="901" class="Symbol">)</a>
  <a id="905" href="order-theory.upper-bounds-chains-posets.html#834" class="Function">is-upper-bound-chain-prop-Poset</a> <a id="937" class="Symbol">=</a>
    <a id="943" href="order-theory.upper-bounds-posets.html#1679" class="Function">is-upper-bound-family-of-elements-prop-Poset</a> <a id="988" href="order-theory.upper-bounds-chains-posets.html#783" class="Bound">X</a>
      <a id="996" class="Symbol">(</a> <a id="998" href="order-theory.chains-posets.html#2198" class="Function">inclusion-type-chain-Poset</a> <a id="1025" href="order-theory.upper-bounds-chains-posets.html#783" class="Bound">X</a> <a id="1027" href="order-theory.upper-bounds-chains-posets.html#801" class="Bound">C</a><a id="1028" class="Symbol">)</a>

  <a id="1033" href="order-theory.upper-bounds-chains-posets.html#1033" class="Function">is-upper-bound-chain-Poset</a> <a id="1060" class="Symbol">:</a> <a id="1062" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1073" href="order-theory.upper-bounds-chains-posets.html#783" class="Bound">X</a> <a id="1075" class="Symbol">→</a> <a id="1077" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1080" class="Symbol">(</a><a id="1081" href="order-theory.upper-bounds-chains-posets.html#764" class="Bound">l1</a> <a id="1084" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1086" href="order-theory.upper-bounds-chains-posets.html#767" class="Bound">l2</a> <a id="1089" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1091" href="order-theory.upper-bounds-chains-posets.html#770" class="Bound">l3</a><a id="1093" class="Symbol">)</a>
  <a id="1097" href="order-theory.upper-bounds-chains-posets.html#1033" class="Function">is-upper-bound-chain-Poset</a> <a id="1124" class="Symbol">=</a> <a id="1126" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1136" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1138" href="order-theory.upper-bounds-chains-posets.html#834" class="Function">is-upper-bound-chain-prop-Poset</a>

  <a id="1173" href="order-theory.upper-bounds-chains-posets.html#1173" class="Function">has-upper-bound-chain-prop-Poset</a> <a id="1206" class="Symbol">:</a> <a id="1208" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1213" class="Symbol">(</a><a id="1214" href="order-theory.upper-bounds-chains-posets.html#764" class="Bound">l1</a> <a id="1217" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1219" href="order-theory.upper-bounds-chains-posets.html#767" class="Bound">l2</a> <a id="1222" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1224" href="order-theory.upper-bounds-chains-posets.html#770" class="Bound">l3</a><a id="1226" class="Symbol">)</a>
  <a id="1230" href="order-theory.upper-bounds-chains-posets.html#1173" class="Function">has-upper-bound-chain-prop-Poset</a> <a id="1263" class="Symbol">=</a>
    <a id="1269" href="foundation.existential-quantification.html#4308" class="Function">∃</a> <a id="1271" class="Symbol">(</a><a id="1272" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="1283" href="order-theory.upper-bounds-chains-posets.html#783" class="Bound">X</a><a id="1284" class="Symbol">)</a> <a id="1286" href="order-theory.upper-bounds-chains-posets.html#834" class="Function">is-upper-bound-chain-prop-Poset</a>

  <a id="1321" href="order-theory.upper-bounds-chains-posets.html#1321" class="Function">has-upper-bound-chain-Poset</a> <a id="1349" class="Symbol">:</a> <a id="1351" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1354" class="Symbol">(</a><a id="1355" href="order-theory.upper-bounds-chains-posets.html#764" class="Bound">l1</a> <a id="1358" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1360" href="order-theory.upper-bounds-chains-posets.html#767" class="Bound">l2</a> <a id="1363" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1365" href="order-theory.upper-bounds-chains-posets.html#770" class="Bound">l3</a><a id="1367" class="Symbol">)</a>
  <a id="1371" href="order-theory.upper-bounds-chains-posets.html#1321" class="Function">has-upper-bound-chain-Poset</a> <a id="1399" class="Symbol">=</a> <a id="1401" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1411" href="order-theory.upper-bounds-chains-posets.html#1173" class="Function">has-upper-bound-chain-prop-Poset</a>
</pre>