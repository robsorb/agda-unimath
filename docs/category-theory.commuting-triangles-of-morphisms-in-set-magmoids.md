# Commuting triangles of morphisms in set-magmoids

<pre class="Agda"><a id="61" class="Keyword">module</a> <a id="68" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html" class="Module">category-theory.commuting-triangles-of-morphisms-in-set-magmoids</a> <a id="133" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="category-theory.set-magmoids.html" class="Module">category-theory.set-magmoids</a>

<a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="269" class="Keyword">open</a> <a id="274" class="Keyword">import</a> <a id="281" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
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

in a [set-magmoid](category-theory.set-magmoids.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between:

```text
  left ＝ right ∘ top.
```

Such a identification is called the
{{#concept "coherence" Disambiguation="commuting triangle of morphisms in set-magmaoids" Agda=coherence-triangle-hom-Set-Magmoid}}
of the commuting triangle.

## Definitions

<pre class="Agda"><a id="coherence-triangle-hom-Set-Magmoid"></a><a id="865" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#865" class="Function">coherence-triangle-hom-Set-Magmoid</a> <a id="900" class="Symbol">:</a>
  <a id="904" class="Symbol">{</a><a id="905" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#905" class="Bound">l1</a> <a id="908" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#908" class="Bound">l2</a> <a id="911" class="Symbol">:</a> <a id="913" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="918" class="Symbol">}</a> <a id="920" class="Symbol">(</a><a id="921" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#921" class="Bound">C</a> <a id="923" class="Symbol">:</a> <a id="925" href="category-theory.set-magmoids.html#1597" class="Function">Set-Magmoid</a> <a id="937" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#905" class="Bound">l1</a> <a id="940" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#908" class="Bound">l2</a><a id="942" class="Symbol">)</a>
  <a id="946" class="Symbol">{</a><a id="947" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#947" class="Bound">x</a> <a id="949" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#949" class="Bound">y</a> <a id="951" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#951" class="Bound">z</a> <a id="953" class="Symbol">:</a> <a id="955" href="category-theory.set-magmoids.html#1840" class="Function">obj-Set-Magmoid</a> <a id="971" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#921" class="Bound">C</a><a id="972" class="Symbol">}</a>
  <a id="976" class="Symbol">(</a><a id="977" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#977" class="Bound">top</a> <a id="981" class="Symbol">:</a> <a id="983" href="category-theory.set-magmoids.html#1987" class="Function">hom-Set-Magmoid</a> <a id="999" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#921" class="Bound">C</a> <a id="1001" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#947" class="Bound">x</a> <a id="1003" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#949" class="Bound">y</a><a id="1004" class="Symbol">)</a>
  <a id="1008" class="Symbol">(</a><a id="1009" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1009" class="Bound">left</a> <a id="1014" class="Symbol">:</a> <a id="1016" href="category-theory.set-magmoids.html#1987" class="Function">hom-Set-Magmoid</a> <a id="1032" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#921" class="Bound">C</a> <a id="1034" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#947" class="Bound">x</a> <a id="1036" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#951" class="Bound">z</a><a id="1037" class="Symbol">)</a>
  <a id="1041" class="Symbol">(</a><a id="1042" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1042" class="Bound">right</a> <a id="1048" class="Symbol">:</a> <a id="1050" href="category-theory.set-magmoids.html#1987" class="Function">hom-Set-Magmoid</a> <a id="1066" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#921" class="Bound">C</a> <a id="1068" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#949" class="Bound">y</a> <a id="1070" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#951" class="Bound">z</a><a id="1071" class="Symbol">)</a> <a id="1073" class="Symbol">→</a>
  <a id="1077" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1080" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#908" class="Bound">l2</a>
<a id="1083" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#865" class="Function">coherence-triangle-hom-Set-Magmoid</a> <a id="1118" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1118" class="Bound">C</a> <a id="1120" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1120" class="Bound">top</a> <a id="1124" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1124" class="Bound">left</a> <a id="1129" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1129" class="Bound">right</a> <a id="1135" class="Symbol">=</a>
  <a id="1139" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1124" class="Bound">left</a> <a id="1144" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1146" href="category-theory.set-magmoids.html#2263" class="Function">comp-hom-Set-Magmoid</a> <a id="1167" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1118" class="Bound">C</a> <a id="1169" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1129" class="Bound">right</a> <a id="1175" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids.html#1120" class="Bound">top</a>
</pre>