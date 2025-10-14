# Isomorphisms of concrete groups

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="group-theory.isomorphisms-concrete-groups.html" class="Module">group-theory.isomorphisms-concrete-groups</a> <a id="93" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="category-theory.isomorphisms-in-large-precategories.html" class="Module">category-theory.isomorphisms-in-large-precategories</a>

<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="group-theory.precategory-of-concrete-groups.html" class="Module">group-theory.precategory-of-concrete-groups</a>
</pre>
</details>

## Idea

**Isomorphisms** of [concrete groups](group-theory.concrete-groups.md) are
[isomorphisms](category-theory.isomorphisms-in-large-precategories.md) in the
[large precategory of concrete groups](group-theory.precategory-of-concrete-groups.md).

## Definition

<pre class="Agda"><a id="iso-Concrete-Group"></a><a id="642" href="group-theory.isomorphisms-concrete-groups.html#642" class="Function">iso-Concrete-Group</a> <a id="661" class="Symbol">:</a>
  <a id="665" class="Symbol">{</a><a id="666" href="group-theory.isomorphisms-concrete-groups.html#666" class="Bound">l1</a> <a id="669" href="group-theory.isomorphisms-concrete-groups.html#669" class="Bound">l2</a> <a id="672" class="Symbol">:</a> <a id="674" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="679" class="Symbol">}</a> <a id="681" class="Symbol">→</a> <a id="683" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="698" href="group-theory.isomorphisms-concrete-groups.html#666" class="Bound">l1</a> <a id="701" class="Symbol">→</a> <a id="703" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="718" href="group-theory.isomorphisms-concrete-groups.html#669" class="Bound">l2</a> <a id="721" class="Symbol">→</a> <a id="723" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="726" class="Symbol">(</a><a id="727" href="group-theory.isomorphisms-concrete-groups.html#666" class="Bound">l1</a> <a id="730" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="732" href="group-theory.isomorphisms-concrete-groups.html#669" class="Bound">l2</a><a id="734" class="Symbol">)</a>
<a id="736" href="group-theory.isomorphisms-concrete-groups.html#642" class="Function">iso-Concrete-Group</a> <a id="755" class="Symbol">=</a> <a id="757" href="category-theory.isomorphisms-in-large-precategories.html#2497" class="Function">iso-Large-Precategory</a> <a id="779" href="group-theory.precategory-of-concrete-groups.html#426" class="Function">Concrete-Group-Large-Precategory</a>
</pre>
## Properties

### Equivalences of concrete groups are isomorphisms of concrete groups

This remains to be shown.
[#736](https://github.com/UniMath/agda-unimath/issues/736)
