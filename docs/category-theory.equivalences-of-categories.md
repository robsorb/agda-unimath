# Equivalences between categories

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="category-theory.equivalences-of-categories.html" class="Module">category-theory.equivalences-of-categories</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="category-theory.equivalences-of-precategories.html" class="Module">category-theory.equivalences-of-precategories</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="category-theory.functors-categories.html" class="Module">category-theory.functors-categories</a>

<a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A [functor](category-theory.functors-categories.md) `F : C → D` on
[categories](category-theory.categories.md) is an **equivalence** if it is an
[equivalence on the underlying precategories](category-theory.equivalences-of-precategories.md).

## Definition

<pre class="Agda"><a id="627" class="Keyword">module</a> <a id="634" href="category-theory.equivalences-of-categories.html#634" class="Module">_</a>
  <a id="638" class="Symbol">{</a><a id="639" href="category-theory.equivalences-of-categories.html#639" class="Bound">l1</a> <a id="642" href="category-theory.equivalences-of-categories.html#642" class="Bound">l2</a> <a id="645" href="category-theory.equivalences-of-categories.html#645" class="Bound">l3</a> <a id="648" href="category-theory.equivalences-of-categories.html#648" class="Bound">l4</a> <a id="651" class="Symbol">:</a> <a id="653" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="658" class="Symbol">}</a>
  <a id="662" class="Symbol">(</a><a id="663" href="category-theory.equivalences-of-categories.html#663" class="Bound">C</a> <a id="665" class="Symbol">:</a> <a id="667" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="676" href="category-theory.equivalences-of-categories.html#639" class="Bound">l1</a> <a id="679" href="category-theory.equivalences-of-categories.html#642" class="Bound">l2</a><a id="681" class="Symbol">)</a>
  <a id="685" class="Symbol">(</a><a id="686" href="category-theory.equivalences-of-categories.html#686" class="Bound">D</a> <a id="688" class="Symbol">:</a> <a id="690" href="category-theory.categories.html#2290" class="Function">Category</a> <a id="699" href="category-theory.equivalences-of-categories.html#645" class="Bound">l3</a> <a id="702" href="category-theory.equivalences-of-categories.html#648" class="Bound">l4</a><a id="704" class="Symbol">)</a>
  <a id="708" class="Keyword">where</a>

  <a id="717" href="category-theory.equivalences-of-categories.html#717" class="Function">is-equiv-functor-Category</a> <a id="743" class="Symbol">:</a> <a id="745" href="category-theory.functors-categories.html#2227" class="Function">functor-Category</a> <a id="762" href="category-theory.equivalences-of-categories.html#663" class="Bound">C</a> <a id="764" href="category-theory.equivalences-of-categories.html#686" class="Bound">D</a> <a id="766" class="Symbol">→</a> <a id="768" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="771" class="Symbol">(</a><a id="772" href="category-theory.equivalences-of-categories.html#639" class="Bound">l1</a> <a id="775" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="777" href="category-theory.equivalences-of-categories.html#642" class="Bound">l2</a> <a id="780" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="782" href="category-theory.equivalences-of-categories.html#645" class="Bound">l3</a> <a id="785" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="787" href="category-theory.equivalences-of-categories.html#648" class="Bound">l4</a><a id="789" class="Symbol">)</a>
  <a id="793" href="category-theory.equivalences-of-categories.html#717" class="Function">is-equiv-functor-Category</a> <a id="819" class="Symbol">=</a>
    <a id="825" href="category-theory.equivalences-of-precategories.html#1098" class="Function">is-equiv-functor-Precategory</a>
      <a id="860" class="Symbol">(</a> <a id="862" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="883" href="category-theory.equivalences-of-categories.html#663" class="Bound">C</a><a id="884" class="Symbol">)</a>
      <a id="892" class="Symbol">(</a> <a id="894" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="915" href="category-theory.equivalences-of-categories.html#686" class="Bound">D</a><a id="916" class="Symbol">)</a>

  <a id="921" href="category-theory.equivalences-of-categories.html#921" class="Function">equiv-Category</a> <a id="936" class="Symbol">:</a> <a id="938" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="941" class="Symbol">(</a><a id="942" href="category-theory.equivalences-of-categories.html#639" class="Bound">l1</a> <a id="945" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="947" href="category-theory.equivalences-of-categories.html#642" class="Bound">l2</a> <a id="950" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="952" href="category-theory.equivalences-of-categories.html#645" class="Bound">l3</a> <a id="955" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="957" href="category-theory.equivalences-of-categories.html#648" class="Bound">l4</a><a id="959" class="Symbol">)</a>
  <a id="963" href="category-theory.equivalences-of-categories.html#921" class="Function">equiv-Category</a> <a id="978" class="Symbol">=</a>
    <a id="984" href="category-theory.equivalences-of-precategories.html#1643" class="Function">equiv-Precategory</a> <a id="1002" class="Symbol">(</a><a id="1003" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1024" href="category-theory.equivalences-of-categories.html#663" class="Bound">C</a><a id="1025" class="Symbol">)</a> <a id="1027" class="Symbol">(</a><a id="1028" href="category-theory.categories.html#2467" class="Function">precategory-Category</a> <a id="1049" href="category-theory.equivalences-of-categories.html#686" class="Bound">D</a><a id="1050" class="Symbol">)</a>
</pre>