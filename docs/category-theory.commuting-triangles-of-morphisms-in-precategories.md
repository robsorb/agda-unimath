# Commuting triangles of morphisms in precategories

<pre class="Agda"><a id="62" class="Keyword">module</a> <a id="69" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html" class="Module">category-theory.commuting-triangles-of-morphisms-in-precategories</a> <a id="135" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html" class="Module">category-theory.commuting-triangles-of-morphisms-in-set-magmoids</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A triangle of morphisms

```text
        top
     x ----> y
      \     /
  left \   / right
        ∨ ∨
         z
```

in a [precategory](category-theory.precategories.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between:

```text
  left ＝ right ∘ top.
```

Such a identification is called the
{{#concept "coherence" Disambiguation="commuting triangle of morphisms in precategories" Agda=coherence-triangle-hom-Precategory}}
of the commuting triangle.

## Definitions

<pre class="Agda"><a id="coherence-triangle-hom-Precategory"></a><a id="946" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#946" class="Function">coherence-triangle-hom-Precategory</a> <a id="981" class="Symbol">:</a>
  <a id="985" class="Symbol">{</a><a id="986" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#986" class="Bound">l1</a> <a id="989" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#989" class="Bound">l2</a> <a id="992" class="Symbol">:</a> <a id="994" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="999" class="Symbol">}</a> <a id="1001" class="Symbol">(</a><a id="1002" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1002" class="Bound">C</a> <a id="1004" class="Symbol">:</a> <a id="1006" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1018" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#986" class="Bound">l1</a> <a id="1021" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#989" class="Bound">l2</a><a id="1023" class="Symbol">)</a>
  <a id="1027" class="Symbol">{</a><a id="1028" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1028" class="Bound">x</a> <a id="1030" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1030" class="Bound">y</a> <a id="1032" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1032" class="Bound">z</a> <a id="1034" class="Symbol">:</a> <a id="1036" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="1052" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1002" class="Bound">C</a><a id="1053" class="Symbol">}</a>
  <a id="1057" class="Symbol">(</a><a id="1058" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1058" class="Bound">top</a> <a id="1062" class="Symbol">:</a> <a id="1064" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="1080" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1002" class="Bound">C</a> <a id="1082" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1028" class="Bound">x</a> <a id="1084" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1030" class="Bound">y</a><a id="1085" class="Symbol">)</a>
  <a id="1089" class="Symbol">(</a><a id="1090" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1090" class="Bound">left</a> <a id="1095" class="Symbol">:</a> <a id="1097" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="1113" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1002" class="Bound">C</a> <a id="1115" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1028" class="Bound">x</a> <a id="1117" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1032" class="Bound">z</a><a id="1118" class="Symbol">)</a>
  <a id="1122" class="Symbol">(</a><a id="1123" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1123" class="Bound">right</a> <a id="1129" class="Symbol">:</a> <a id="1131" href="category-theory.precategories.html#4780" class="Function">hom-Precategory</a> <a id="1147" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1002" class="Bound">C</a> <a id="1149" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1030" class="Bound">y</a> <a id="1151" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1032" class="Bound">z</a><a id="1152" class="Symbol">)</a> <a id="1154" class="Symbol">→</a>
  <a id="1158" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1161" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#989" class="Bound">l2</a>
<a id="1164" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#946" class="Function">coherence-triangle-hom-Precategory</a> <a id="1199" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1199" class="Bound">C</a> <a id="1201" class="Symbol">=</a>
  <a id="1205" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#865" class="Function">coherence-triangle-hom-Set-Magmoid</a> <a id="1240" class="Symbol">(</a><a id="1241" href="category-theory.precategories.html#8116" class="Function">set-magmoid-Precategory</a> <a id="1265" href="category-theory.commuting-triangles-of-morphisms-in-precategories.html#1199" class="Bound">C</a><a id="1266" class="Symbol">)</a>
</pre>