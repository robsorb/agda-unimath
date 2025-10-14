# Iterated loop spaces

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.iterating-functions.html" class="Module">foundation.iterating-functions</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="structured-types.h-spaces.html" class="Module">structured-types.h-spaces</a>
<a id="318" class="Keyword">open</a> <a id="323" class="Keyword">import</a> <a id="330" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="362" class="Keyword">open</a> <a id="367" class="Keyword">import</a> <a id="374" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
</pre>
</details>

## Idea

The
{{#concept "iterated loop space" Disambiguation="of a pointed type" Agda=iterated-loop-space}}
`ΩⁿA` of a [pointed type](structured-types.pointed-types.md) `A` is obtained by
[iteratively](foundation.iterating-functions.md) applying the
[loop space](synthetic-homotopy-theory.loop-spaces.md) operation `Ω` to `A`.

## Definitions

### Iterated loop spaces

<pre class="Agda"><a id="807" class="Keyword">module</a> <a id="814" href="synthetic-homotopy-theory.iterated-loop-spaces.html#814" class="Module">_</a>
  <a id="818" class="Symbol">{</a><a id="819" href="synthetic-homotopy-theory.iterated-loop-spaces.html#819" class="Bound">l</a> <a id="821" class="Symbol">:</a> <a id="823" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="828" class="Symbol">}</a>
  <a id="832" class="Keyword">where</a>

  <a id="841" href="synthetic-homotopy-theory.iterated-loop-spaces.html#841" class="Function">iterated-loop-space</a> <a id="861" class="Symbol">:</a> <a id="863" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="865" class="Symbol">→</a> <a id="867" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="880" href="synthetic-homotopy-theory.iterated-loop-spaces.html#819" class="Bound">l</a> <a id="882" class="Symbol">→</a> <a id="884" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="897" href="synthetic-homotopy-theory.iterated-loop-spaces.html#819" class="Bound">l</a>
  <a id="901" href="synthetic-homotopy-theory.iterated-loop-spaces.html#841" class="Function">iterated-loop-space</a> <a id="921" href="synthetic-homotopy-theory.iterated-loop-spaces.html#921" class="Bound">n</a> <a id="923" class="Symbol">=</a> <a id="925" href="foundation-core.iterating-functions.html#724" class="Function">iterate</a> <a id="933" href="synthetic-homotopy-theory.iterated-loop-spaces.html#921" class="Bound">n</a> <a id="935" href="synthetic-homotopy-theory.loop-spaces.html#1152" class="Function">Ω</a>

  <a id="940" href="synthetic-homotopy-theory.iterated-loop-spaces.html#940" class="Function">type-iterated-loop-space</a> <a id="965" class="Symbol">:</a> <a id="967" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="969" class="Symbol">→</a> <a id="971" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="984" href="synthetic-homotopy-theory.iterated-loop-spaces.html#819" class="Bound">l</a> <a id="986" class="Symbol">→</a> <a id="988" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="991" href="synthetic-homotopy-theory.iterated-loop-spaces.html#819" class="Bound">l</a>
  <a id="995" href="synthetic-homotopy-theory.iterated-loop-spaces.html#940" class="Function">type-iterated-loop-space</a> <a id="1020" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1020" class="Bound">n</a> <a id="1022" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1022" class="Bound">A</a> <a id="1024" class="Symbol">=</a> <a id="1026" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1044" class="Symbol">(</a><a id="1045" href="synthetic-homotopy-theory.iterated-loop-spaces.html#841" class="Function">iterated-loop-space</a> <a id="1065" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1020" class="Bound">n</a> <a id="1067" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1022" class="Bound">A</a><a id="1068" class="Symbol">)</a>

  <a id="1073" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1073" class="Function">point-iterated-loop-space</a> <a id="1099" class="Symbol">:</a>
    <a id="1105" class="Symbol">(</a><a id="1106" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1106" class="Bound">n</a> <a id="1108" class="Symbol">:</a> <a id="1110" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1111" class="Symbol">)</a> <a id="1113" class="Symbol">(</a><a id="1114" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1114" class="Bound">A</a> <a id="1116" class="Symbol">:</a> <a id="1118" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1131" href="synthetic-homotopy-theory.iterated-loop-spaces.html#819" class="Bound">l</a><a id="1132" class="Symbol">)</a> <a id="1134" class="Symbol">→</a> <a id="1136" href="synthetic-homotopy-theory.iterated-loop-spaces.html#940" class="Function">type-iterated-loop-space</a> <a id="1161" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1106" class="Bound">n</a> <a id="1163" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1114" class="Bound">A</a>
  <a id="1167" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1073" class="Function">point-iterated-loop-space</a> <a id="1193" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1193" class="Bound">n</a> <a id="1195" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1195" class="Bound">A</a> <a id="1197" class="Symbol">=</a> <a id="1199" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1218" class="Symbol">(</a><a id="1219" href="synthetic-homotopy-theory.iterated-loop-spaces.html#841" class="Function">iterated-loop-space</a> <a id="1239" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1193" class="Bound">n</a> <a id="1241" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1195" class="Bound">A</a><a id="1242" class="Symbol">)</a>
</pre>
### Iterated loop spaces of H-spaces

<pre class="Agda"><a id="1295" class="Keyword">module</a> <a id="1302" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1302" class="Module">_</a>
  <a id="1306" class="Symbol">{</a><a id="1307" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1307" class="Bound">l</a> <a id="1309" class="Symbol">:</a> <a id="1311" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1316" class="Symbol">}</a>
  <a id="1320" class="Keyword">where</a>

  <a id="1329" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1329" class="Function">iterated-loop-space-H-Space</a> <a id="1357" class="Symbol">:</a> <a id="1359" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1361" class="Symbol">→</a> <a id="1363" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="1371" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1307" class="Bound">l</a> <a id="1373" class="Symbol">→</a> <a id="1375" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="1383" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1307" class="Bound">l</a>
  <a id="1387" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1329" class="Function">iterated-loop-space-H-Space</a> <a id="1415" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1422" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1422" class="Bound">X</a> <a id="1424" class="Symbol">=</a> <a id="1426" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1422" class="Bound">X</a>
  <a id="1430" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1329" class="Function">iterated-loop-space-H-Space</a> <a id="1458" class="Symbol">(</a><a id="1459" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1466" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1466" class="Bound">n</a><a id="1467" class="Symbol">)</a> <a id="1469" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1469" class="Bound">X</a> <a id="1471" class="Symbol">=</a>
    <a id="1477" href="synthetic-homotopy-theory.loop-spaces.html#1879" class="Function">Ω-H-Space</a> <a id="1487" class="Symbol">(</a><a id="1488" href="synthetic-homotopy-theory.iterated-loop-spaces.html#841" class="Function">iterated-loop-space</a> <a id="1508" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1466" class="Bound">n</a> <a id="1510" class="Symbol">(</a><a id="1511" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="1532" href="synthetic-homotopy-theory.iterated-loop-spaces.html#1469" class="Bound">X</a><a id="1533" class="Symbol">))</a>
</pre>
## See also

- [Double loop spaces](synthetic-homotopy-theory.double-loop-spaces.md)
- [Triple loop spaces](synthetic-homotopy-theory.triple-loop-spaces.md)

## External links

- [Loop space](https://www.wikidata.org/wiki/Q2066070) on Wikidata
- [Function iteration](https://www.wikidata.org/wiki/Q5254619) on Wikidata
