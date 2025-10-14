# Complete precategories

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="category-theory.complete-precategories.html" class="Module">category-theory.complete-precategories</a> <a id="81" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="category-theory.cones-precategories.html" class="Module">category-theory.cones-precategories</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="category-theory.limits-precategories.html" class="Module">category-theory.limits-precategories</a>
<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="category-theory.terminal-objects-precategories.html" class="Module">category-theory.terminal-objects-precategories</a>

<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A {{#concept "complete precategory" Agda=is-complete-Precategory}} is a
[precategory](category-theory.precategories.md) that has all
[limits](category-theory.limits-precategories.md) for diagrams from a specified
universe.

More precisely, we say that a precategory `D` is `(l1 , l2)`-complete if for any
`C : Precategory l1 l2` and any
[functor](category-theory.functors-precategories.md) `F : C → D` the type of
limits of `F` is inhabited.

## Definition

<pre class="Agda"><a id="is-complete-Precategory"></a><a id="918" href="category-theory.complete-precategories.html#918" class="Function">is-complete-Precategory</a> <a id="942" class="Symbol">:</a>
  <a id="946" class="Symbol">(</a><a id="947" href="category-theory.complete-precategories.html#947" class="Bound">l1</a> <a id="950" href="category-theory.complete-precategories.html#950" class="Bound">l2</a> <a id="953" class="Symbol">:</a> <a id="955" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="960" class="Symbol">)</a> <a id="962" class="Symbol">{</a><a id="963" href="category-theory.complete-precategories.html#963" class="Bound">l3</a> <a id="966" href="category-theory.complete-precategories.html#966" class="Bound">l4</a> <a id="969" class="Symbol">:</a> <a id="971" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="976" class="Symbol">}</a>
  <a id="980" class="Symbol">(</a><a id="981" href="category-theory.complete-precategories.html#981" class="Bound">D</a> <a id="983" class="Symbol">:</a> <a id="985" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="997" href="category-theory.complete-precategories.html#963" class="Bound">l3</a> <a id="1000" href="category-theory.complete-precategories.html#966" class="Bound">l4</a><a id="1002" class="Symbol">)</a> <a id="1004" class="Symbol">→</a>
  <a id="1008" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1011" class="Symbol">(</a><a id="1012" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1017" href="category-theory.complete-precategories.html#947" class="Bound">l1</a> <a id="1020" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1022" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1027" href="category-theory.complete-precategories.html#950" class="Bound">l2</a> <a id="1030" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1032" href="category-theory.complete-precategories.html#963" class="Bound">l3</a> <a id="1035" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1037" href="category-theory.complete-precategories.html#966" class="Bound">l4</a><a id="1039" class="Symbol">)</a>
<a id="1041" href="category-theory.complete-precategories.html#918" class="Function">is-complete-Precategory</a> <a id="1065" href="category-theory.complete-precategories.html#1065" class="Bound">l1</a> <a id="1068" href="category-theory.complete-precategories.html#1068" class="Bound">l2</a> <a id="1071" href="category-theory.complete-precategories.html#1071" class="Bound">D</a> <a id="1073" class="Symbol">=</a>
  <a id="1077" class="Symbol">(</a><a id="1078" href="category-theory.complete-precategories.html#1078" class="Bound">C</a> <a id="1080" class="Symbol">:</a> <a id="1082" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1094" href="category-theory.complete-precategories.html#1065" class="Bound">l1</a> <a id="1097" href="category-theory.complete-precategories.html#1068" class="Bound">l2</a><a id="1099" class="Symbol">)</a> <a id="1101" class="Symbol">(</a><a id="1102" href="category-theory.complete-precategories.html#1102" class="Bound">F</a> <a id="1104" class="Symbol">:</a> <a id="1106" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="1126" href="category-theory.complete-precategories.html#1078" class="Bound">C</a> <a id="1128" href="category-theory.complete-precategories.html#1071" class="Bound">D</a><a id="1129" class="Symbol">)</a> <a id="1131" class="Symbol">→</a>
  <a id="1135" href="category-theory.limits-precategories.html#2378" class="Function">limit-Precategory</a> <a id="1153" href="category-theory.complete-precategories.html#1078" class="Bound">C</a> <a id="1155" href="category-theory.complete-precategories.html#1071" class="Bound">D</a> <a id="1157" href="category-theory.complete-precategories.html#1102" class="Bound">F</a>
</pre>