# Coslice precategories

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="category-theory.coslice-precategories.html" class="Module">category-theory.coslice-precategories</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="category-theory.opposite-precategories.html" class="Module">category-theory.opposite-precategories</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="category-theory.slice-precategories.html" class="Module">category-theory.slice-precategories</a>

<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The {{#concept "coslice precategory" Agda=Coslice-Precategory}} of a
[precategory](category-theory.precategories.md) `C` under an object `X` of `C`
is the category of objects of `C` equipped with a morphism from `X`.

Equivalently, it is the opposite of the slice precategory of `Cᵒᵖ`.

## Definitions

<pre class="Agda"><a id="704" class="Keyword">module</a> <a id="711" href="category-theory.coslice-precategories.html#711" class="Module">_</a>
  <a id="715" class="Symbol">{</a><a id="716" href="category-theory.coslice-precategories.html#716" class="Bound">l1</a> <a id="719" href="category-theory.coslice-precategories.html#719" class="Bound">l2</a> <a id="722" class="Symbol">:</a> <a id="724" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="729" class="Symbol">}</a> <a id="731" class="Symbol">(</a><a id="732" href="category-theory.coslice-precategories.html#732" class="Bound">C</a> <a id="734" class="Symbol">:</a> <a id="736" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="748" href="category-theory.coslice-precategories.html#716" class="Bound">l1</a> <a id="751" href="category-theory.coslice-precategories.html#719" class="Bound">l2</a><a id="753" class="Symbol">)</a> <a id="755" class="Symbol">(</a><a id="756" href="category-theory.coslice-precategories.html#756" class="Bound">X</a> <a id="758" class="Symbol">:</a> <a id="760" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="776" href="category-theory.coslice-precategories.html#732" class="Bound">C</a><a id="777" class="Symbol">)</a>
  <a id="781" class="Keyword">where</a>

  <a id="790" href="category-theory.coslice-precategories.html#790" class="Function">Coslice-Precategory</a> <a id="810" class="Symbol">:</a> <a id="812" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="824" class="Symbol">(</a><a id="825" href="category-theory.coslice-precategories.html#716" class="Bound">l1</a> <a id="828" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="830" href="category-theory.coslice-precategories.html#719" class="Bound">l2</a><a id="832" class="Symbol">)</a> <a id="834" href="category-theory.coslice-precategories.html#719" class="Bound">l2</a>
  <a id="839" href="category-theory.coslice-precategories.html#790" class="Function">Coslice-Precategory</a> <a id="859" class="Symbol">=</a>
    <a id="865" href="category-theory.opposite-precategories.html#3169" class="Function">opposite-Precategory</a> <a id="886" class="Symbol">(</a><a id="887" href="category-theory.slice-precategories.html#6140" class="Function">Slice-Precategory</a> <a id="905" class="Symbol">(</a><a id="906" href="category-theory.opposite-precategories.html#3169" class="Function">opposite-Precategory</a> <a id="927" href="category-theory.coslice-precategories.html#732" class="Bound">C</a><a id="928" class="Symbol">)</a> <a id="930" href="category-theory.coslice-precategories.html#756" class="Bound">X</a><a id="931" class="Symbol">)</a>
</pre>
## Properties

### The coslice precategory has a forgetful functor

<pre class="Agda"><a id="1014" class="Keyword">module</a> <a id="1021" href="category-theory.coslice-precategories.html#1021" class="Module">_</a>
  <a id="1025" class="Symbol">{</a><a id="1026" href="category-theory.coslice-precategories.html#1026" class="Bound">l1</a> <a id="1029" href="category-theory.coslice-precategories.html#1029" class="Bound">l2</a> <a id="1032" class="Symbol">:</a> <a id="1034" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1039" class="Symbol">}</a> <a id="1041" class="Symbol">(</a><a id="1042" href="category-theory.coslice-precategories.html#1042" class="Bound">C</a> <a id="1044" class="Symbol">:</a> <a id="1046" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1058" href="category-theory.coslice-precategories.html#1026" class="Bound">l1</a> <a id="1061" href="category-theory.coslice-precategories.html#1029" class="Bound">l2</a><a id="1063" class="Symbol">)</a> <a id="1065" class="Symbol">(</a><a id="1066" href="category-theory.coslice-precategories.html#1066" class="Bound">X</a> <a id="1068" class="Symbol">:</a> <a id="1070" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="1086" href="category-theory.coslice-precategories.html#1042" class="Bound">C</a><a id="1087" class="Symbol">)</a>
  <a id="1091" class="Keyword">where</a>

  <a id="1100" href="category-theory.coslice-precategories.html#1100" class="Function">forgetful-functor-Coslice-Precategory</a> <a id="1138" class="Symbol">:</a>
    <a id="1144" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="1164" class="Symbol">(</a><a id="1165" href="category-theory.coslice-precategories.html#790" class="Function">Coslice-Precategory</a> <a id="1185" href="category-theory.coslice-precategories.html#1042" class="Bound">C</a> <a id="1187" href="category-theory.coslice-precategories.html#1066" class="Bound">X</a><a id="1188" class="Symbol">)</a> <a id="1190" href="category-theory.coslice-precategories.html#1042" class="Bound">C</a>
  <a id="1194" href="category-theory.coslice-precategories.html#1100" class="Function">forgetful-functor-Coslice-Precategory</a> <a id="1232" class="Symbol">=</a>
    <a id="1238" href="category-theory.functors-precategories.html#14719" class="Function">opposite-functor-Precategory</a>
      <a id="1273" class="Symbol">(</a> <a id="1275" href="category-theory.slice-precategories.html#6140" class="Function">Slice-Precategory</a> <a id="1293" class="Symbol">(</a><a id="1294" href="category-theory.opposite-precategories.html#3169" class="Function">opposite-Precategory</a> <a id="1315" href="category-theory.coslice-precategories.html#1042" class="Bound">C</a><a id="1316" class="Symbol">)</a> <a id="1318" href="category-theory.coslice-precategories.html#1066" class="Bound">X</a><a id="1319" class="Symbol">)</a>
      <a id="1327" class="Symbol">(</a> <a id="1329" href="category-theory.opposite-precategories.html#3169" class="Function">opposite-Precategory</a> <a id="1350" href="category-theory.coslice-precategories.html#1042" class="Bound">C</a><a id="1351" class="Symbol">)</a>
      <a id="1359" class="Symbol">(</a> <a id="1361" href="category-theory.slice-precategories.html#16124" class="Function">forgetful-functor-Slice-Precategory</a> <a id="1397" class="Symbol">(</a><a id="1398" href="category-theory.opposite-precategories.html#3169" class="Function">opposite-Precategory</a> <a id="1419" href="category-theory.coslice-precategories.html#1042" class="Bound">C</a><a id="1420" class="Symbol">)</a> <a id="1422" href="category-theory.coslice-precategories.html#1066" class="Bound">X</a><a id="1423" class="Symbol">)</a>
</pre>