# Mere spheres

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="synthetic-homotopy-theory.mere-spheres.html" class="Module">synthetic-homotopy-theory.mere-spheres</a> <a id="71" class="Keyword">where</a>
</pre>
<details></summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="267" class="Keyword">open</a> <a id="272" class="Keyword">import</a> <a id="279" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="synthetic-homotopy-theory.spheres.html" class="Module">synthetic-homotopy-theory.spheres</a>
</pre>
</details>

## Idea

A **mere `n`-sphere** is a type `X` that is
[merely equivalent](foundation.mere-equivalences.md) to the
[`n`-sphere](synthetic-homotopy-theory.spheres.md).

## Definitions

### The predicate of being a mere `n`-sphere

<pre class="Agda"><a id="642" class="Keyword">module</a> <a id="649" href="synthetic-homotopy-theory.mere-spheres.html#649" class="Module">_</a>
  <a id="653" class="Symbol">{</a><a id="654" href="synthetic-homotopy-theory.mere-spheres.html#654" class="Bound">l</a> <a id="656" class="Symbol">:</a> <a id="658" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="663" class="Symbol">}</a> <a id="665" class="Symbol">(</a><a id="666" href="synthetic-homotopy-theory.mere-spheres.html#666" class="Bound">n</a> <a id="668" class="Symbol">:</a> <a id="670" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="671" class="Symbol">)</a> <a id="673" class="Symbol">(</a><a id="674" href="synthetic-homotopy-theory.mere-spheres.html#674" class="Bound">X</a> <a id="676" class="Symbol">:</a> <a id="678" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="681" href="synthetic-homotopy-theory.mere-spheres.html#654" class="Bound">l</a><a id="682" class="Symbol">)</a>
  <a id="686" class="Keyword">where</a>

  <a id="695" href="synthetic-homotopy-theory.mere-spheres.html#695" class="Function">is-mere-sphere-Prop</a> <a id="715" class="Symbol">:</a> <a id="717" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="722" href="synthetic-homotopy-theory.mere-spheres.html#654" class="Bound">l</a>
  <a id="726" href="synthetic-homotopy-theory.mere-spheres.html#695" class="Function">is-mere-sphere-Prop</a> <a id="746" class="Symbol">=</a> <a id="748" href="foundation.mere-equivalences.html#849" class="Function">mere-equiv-Prop</a> <a id="764" class="Symbol">(</a><a id="765" href="synthetic-homotopy-theory.spheres.html#961" class="Function">sphere</a> <a id="772" href="synthetic-homotopy-theory.mere-spheres.html#666" class="Bound">n</a><a id="773" class="Symbol">)</a> <a id="775" href="synthetic-homotopy-theory.mere-spheres.html#674" class="Bound">X</a>

  <a id="780" href="synthetic-homotopy-theory.mere-spheres.html#780" class="Function">is-mere-sphere</a> <a id="795" class="Symbol">:</a> <a id="797" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="800" href="synthetic-homotopy-theory.mere-spheres.html#654" class="Bound">l</a>
  <a id="804" href="synthetic-homotopy-theory.mere-spheres.html#780" class="Function">is-mere-sphere</a> <a id="819" class="Symbol">=</a> <a id="821" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="831" href="synthetic-homotopy-theory.mere-spheres.html#695" class="Function">is-mere-sphere-Prop</a>

  <a id="854" href="synthetic-homotopy-theory.mere-spheres.html#854" class="Function">is-prop-is-mere-sphere</a> <a id="877" class="Symbol">:</a> <a id="879" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="887" href="synthetic-homotopy-theory.mere-spheres.html#780" class="Function">is-mere-sphere</a>
  <a id="904" href="synthetic-homotopy-theory.mere-spheres.html#854" class="Function">is-prop-is-mere-sphere</a> <a id="927" class="Symbol">=</a> <a id="929" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="947" href="synthetic-homotopy-theory.mere-spheres.html#695" class="Function">is-mere-sphere-Prop</a>
</pre>
### Mere spheres

<pre class="Agda"><a id="mere-sphere"></a><a id="998" href="synthetic-homotopy-theory.mere-spheres.html#998" class="Function">mere-sphere</a> <a id="1010" class="Symbol">:</a> <a id="1012" class="Symbol">(</a><a id="1013" href="synthetic-homotopy-theory.mere-spheres.html#1013" class="Bound">l</a> <a id="1015" class="Symbol">:</a> <a id="1017" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1022" class="Symbol">)</a> <a id="1024" class="Symbol">(</a><a id="1025" href="synthetic-homotopy-theory.mere-spheres.html#1025" class="Bound">n</a> <a id="1027" class="Symbol">:</a> <a id="1029" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1030" class="Symbol">)</a> <a id="1032" class="Symbol">→</a> <a id="1034" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1037" class="Symbol">(</a><a id="1038" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1043" href="synthetic-homotopy-theory.mere-spheres.html#1013" class="Bound">l</a><a id="1044" class="Symbol">)</a>
<a id="1046" href="synthetic-homotopy-theory.mere-spheres.html#998" class="Function">mere-sphere</a> <a id="1058" href="synthetic-homotopy-theory.mere-spheres.html#1058" class="Bound">l</a> <a id="1060" href="synthetic-homotopy-theory.mere-spheres.html#1060" class="Bound">n</a> <a id="1062" class="Symbol">=</a> <a id="1064" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1066" class="Symbol">(</a><a id="1067" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1070" href="synthetic-homotopy-theory.mere-spheres.html#1058" class="Bound">l</a><a id="1071" class="Symbol">)</a> <a id="1073" class="Symbol">(</a><a id="1074" href="synthetic-homotopy-theory.mere-spheres.html#780" class="Function">is-mere-sphere</a> <a id="1089" href="synthetic-homotopy-theory.mere-spheres.html#1060" class="Bound">n</a><a id="1090" class="Symbol">)</a>

<a id="1093" class="Keyword">module</a> <a id="1100" href="synthetic-homotopy-theory.mere-spheres.html#1100" class="Module">_</a>
  <a id="1104" class="Symbol">{</a><a id="1105" href="synthetic-homotopy-theory.mere-spheres.html#1105" class="Bound">l</a> <a id="1107" class="Symbol">:</a> <a id="1109" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1114" class="Symbol">}</a> <a id="1116" class="Symbol">(</a><a id="1117" href="synthetic-homotopy-theory.mere-spheres.html#1117" class="Bound">n</a> <a id="1119" class="Symbol">:</a> <a id="1121" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1122" class="Symbol">)</a> <a id="1124" class="Symbol">(</a><a id="1125" href="synthetic-homotopy-theory.mere-spheres.html#1125" class="Bound">X</a> <a id="1127" class="Symbol">:</a> <a id="1129" href="synthetic-homotopy-theory.mere-spheres.html#998" class="Function">mere-sphere</a> <a id="1141" href="synthetic-homotopy-theory.mere-spheres.html#1105" class="Bound">l</a> <a id="1143" href="synthetic-homotopy-theory.mere-spheres.html#1117" class="Bound">n</a><a id="1144" class="Symbol">)</a>
  <a id="1148" class="Keyword">where</a>

  <a id="1157" href="synthetic-homotopy-theory.mere-spheres.html#1157" class="Function">type-mere-sphere</a> <a id="1174" class="Symbol">:</a> <a id="1176" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1179" href="synthetic-homotopy-theory.mere-spheres.html#1105" class="Bound">l</a>
  <a id="1183" href="synthetic-homotopy-theory.mere-spheres.html#1157" class="Function">type-mere-sphere</a> <a id="1200" class="Symbol">=</a> <a id="1202" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1206" href="synthetic-homotopy-theory.mere-spheres.html#1125" class="Bound">X</a>

  <a id="1211" href="synthetic-homotopy-theory.mere-spheres.html#1211" class="Function">mere-equiv-mere-sphere</a> <a id="1234" class="Symbol">:</a> <a id="1236" href="foundation.mere-equivalences.html#960" class="Function">mere-equiv</a> <a id="1247" class="Symbol">(</a><a id="1248" href="synthetic-homotopy-theory.spheres.html#961" class="Function">sphere</a> <a id="1255" href="synthetic-homotopy-theory.mere-spheres.html#1117" class="Bound">n</a><a id="1256" class="Symbol">)</a> <a id="1258" href="synthetic-homotopy-theory.mere-spheres.html#1157" class="Function">type-mere-sphere</a>
  <a id="1277" href="synthetic-homotopy-theory.mere-spheres.html#1211" class="Function">mere-equiv-mere-sphere</a> <a id="1300" class="Symbol">=</a> <a id="1302" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1306" href="synthetic-homotopy-theory.mere-spheres.html#1125" class="Bound">X</a>
</pre>