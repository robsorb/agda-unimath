# Spheres

<pre class="Agda"><a id="20" class="Keyword">module</a> <a id="27" href="synthetic-homotopy-theory.spheres.html" class="Module">synthetic-homotopy-theory.spheres</a> <a id="61" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="117" class="Keyword">open</a> <a id="122" class="Keyword">import</a> <a id="129" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="331" class="Keyword">open</a> <a id="336" class="Keyword">import</a> <a id="343" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html" class="Module">synthetic-homotopy-theory.iterated-suspensions-of-pointed-types</a>
<a id="451" class="Keyword">open</a> <a id="456" class="Keyword">import</a> <a id="463" href="synthetic-homotopy-theory.suspensions-of-types.html" class="Module">synthetic-homotopy-theory.suspensions-of-types</a>

<a id="511" class="Keyword">open</a> <a id="516" class="Keyword">import</a> <a id="523" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The **spheres** are defined as
[iterated suspensions](synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.md)
of the
[standard two-element type `Fin 2`](univalent-combinatorics.standard-finite-types.md).

## Definition

<pre class="Agda"><a id="sphere-Pointed-Type"></a><a id="835" href="synthetic-homotopy-theory.spheres.html#835" class="Function">sphere-Pointed-Type</a> <a id="855" class="Symbol">:</a> <a id="857" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="859" class="Symbol">→</a> <a id="861" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="874" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="880" href="synthetic-homotopy-theory.spheres.html#835" class="Function">sphere-Pointed-Type</a> <a id="900" href="synthetic-homotopy-theory.spheres.html#900" class="Bound">n</a> <a id="902" class="Symbol">=</a> <a id="904" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html#710" class="Function">iterated-suspension-Pointed-Type</a> <a id="937" href="synthetic-homotopy-theory.spheres.html#900" class="Bound">n</a> <a id="939" class="Symbol">(</a><a id="940" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="944" class="Number">2</a> <a id="946" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="948" href="univalent-combinatorics.standard-finite-types.html#5750" class="Function">zero-Fin</a> <a id="957" class="Number">1</a><a id="958" class="Symbol">)</a>

<a id="sphere"></a><a id="961" href="synthetic-homotopy-theory.spheres.html#961" class="Function">sphere</a> <a id="968" class="Symbol">:</a> <a id="970" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="972" class="Symbol">→</a> <a id="974" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="977" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="983" href="synthetic-homotopy-theory.spheres.html#961" class="Function">sphere</a> <a id="990" class="Symbol">=</a> <a id="992" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1010" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1012" href="synthetic-homotopy-theory.spheres.html#835" class="Function">sphere-Pointed-Type</a>

<a id="north-sphere"></a><a id="1033" href="synthetic-homotopy-theory.spheres.html#1033" class="Function">north-sphere</a> <a id="1046" class="Symbol">:</a> <a id="1048" class="Symbol">(</a><a id="1049" href="synthetic-homotopy-theory.spheres.html#1049" class="Bound">n</a> <a id="1051" class="Symbol">:</a> <a id="1053" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1054" class="Symbol">)</a> <a id="1056" class="Symbol">→</a> <a id="1058" href="synthetic-homotopy-theory.spheres.html#961" class="Function">sphere</a> <a id="1065" href="synthetic-homotopy-theory.spheres.html#1049" class="Bound">n</a>
<a id="1067" href="synthetic-homotopy-theory.spheres.html#1033" class="Function">north-sphere</a> <a id="1080" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1087" class="Symbol">=</a> <a id="1089" href="univalent-combinatorics.standard-finite-types.html#5750" class="Function">zero-Fin</a> <a id="1098" class="Number">1</a>
<a id="1100" href="synthetic-homotopy-theory.spheres.html#1033" class="Function">north-sphere</a> <a id="1113" class="Symbol">(</a><a id="1114" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1121" href="synthetic-homotopy-theory.spheres.html#1121" class="Bound">n</a><a id="1122" class="Symbol">)</a> <a id="1124" class="Symbol">=</a> <a id="1126" href="synthetic-homotopy-theory.suspensions-of-types.html#2737" class="Function">north-suspension</a>

<a id="south-sphere"></a><a id="1144" href="synthetic-homotopy-theory.spheres.html#1144" class="Function">south-sphere</a> <a id="1157" class="Symbol">:</a> <a id="1159" class="Symbol">(</a><a id="1160" href="synthetic-homotopy-theory.spheres.html#1160" class="Bound">n</a> <a id="1162" class="Symbol">:</a> <a id="1164" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1165" class="Symbol">)</a> <a id="1167" class="Symbol">→</a> <a id="1169" href="synthetic-homotopy-theory.spheres.html#961" class="Function">sphere</a> <a id="1176" href="synthetic-homotopy-theory.spheres.html#1160" class="Bound">n</a>
<a id="1178" href="synthetic-homotopy-theory.spheres.html#1144" class="Function">south-sphere</a> <a id="1191" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1198" class="Symbol">=</a> <a id="1200" href="univalent-combinatorics.standard-finite-types.html#9359" class="Function">one-Fin</a> <a id="1208" class="Number">1</a>
<a id="1210" href="synthetic-homotopy-theory.spheres.html#1144" class="Function">south-sphere</a> <a id="1223" class="Symbol">(</a><a id="1224" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1231" href="synthetic-homotopy-theory.spheres.html#1231" class="Bound">n</a><a id="1232" class="Symbol">)</a> <a id="1234" class="Symbol">=</a> <a id="1236" href="synthetic-homotopy-theory.suspensions-of-types.html#2877" class="Function">south-suspension</a>

<a id="meridian-sphere"></a><a id="1254" href="synthetic-homotopy-theory.spheres.html#1254" class="Function">meridian-sphere</a> <a id="1270" class="Symbol">:</a>
  <a id="1274" class="Symbol">(</a><a id="1275" href="synthetic-homotopy-theory.spheres.html#1275" class="Bound">n</a> <a id="1277" class="Symbol">:</a> <a id="1279" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1280" class="Symbol">)</a> <a id="1282" class="Symbol">→</a> <a id="1284" href="synthetic-homotopy-theory.spheres.html#961" class="Function">sphere</a> <a id="1291" href="synthetic-homotopy-theory.spheres.html#1275" class="Bound">n</a> <a id="1293" class="Symbol">→</a> <a id="1295" href="synthetic-homotopy-theory.spheres.html#1033" class="Function">north-sphere</a> <a id="1308" class="Symbol">(</a><a id="1309" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1316" href="synthetic-homotopy-theory.spheres.html#1275" class="Bound">n</a><a id="1317" class="Symbol">)</a> <a id="1319" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1321" href="synthetic-homotopy-theory.spheres.html#1144" class="Function">south-sphere</a> <a id="1334" class="Symbol">(</a><a id="1335" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1342" href="synthetic-homotopy-theory.spheres.html#1275" class="Bound">n</a><a id="1343" class="Symbol">)</a>
<a id="1345" href="synthetic-homotopy-theory.spheres.html#1254" class="Function">meridian-sphere</a> <a id="1361" href="synthetic-homotopy-theory.spheres.html#1361" class="Bound">n</a> <a id="1363" class="Symbol">=</a> <a id="1365" href="synthetic-homotopy-theory.suspensions-of-types.html#3017" class="Function">meridian-suspension</a>
</pre>