# Commuting squares of morphisms in set-magmoids

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html" class="Module">category-theory.commuting-squares-of-morphisms-in-set-magmoids</a> <a id="129" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="category-theory.set-magmoids.html" class="Module">category-theory.set-magmoids</a>

<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A square of morphisms

```text
  x ------> y
  |         |
  |         |
  ∨         ∨
  z ------> w
```

in a [set-magmoid](category-theory.set-magmoids.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between both
composites:

```text
  bottom ∘ left ＝ right ∘ top.
```

## Definitions

<pre class="Agda"><a id="coherence-square-hom-Set-Magmoid"></a><a id="676" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#676" class="Function">coherence-square-hom-Set-Magmoid</a> <a id="709" class="Symbol">:</a>
  <a id="713" class="Symbol">{</a><a id="714" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#714" class="Bound">l1</a> <a id="717" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#717" class="Bound">l2</a> <a id="720" class="Symbol">:</a> <a id="722" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="727" class="Symbol">}</a> <a id="729" class="Symbol">(</a><a id="730" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#730" class="Bound">C</a> <a id="732" class="Symbol">:</a> <a id="734" href="category-theory.set-magmoids.html#1597" class="Function">Set-Magmoid</a> <a id="746" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#714" class="Bound">l1</a> <a id="749" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#717" class="Bound">l2</a><a id="751" class="Symbol">)</a>
  <a id="755" class="Symbol">{</a><a id="756" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#756" class="Bound">x</a> <a id="758" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#758" class="Bound">y</a> <a id="760" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#760" class="Bound">z</a> <a id="762" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#762" class="Bound">w</a> <a id="764" class="Symbol">:</a> <a id="766" href="category-theory.set-magmoids.html#1840" class="Function">obj-Set-Magmoid</a> <a id="782" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#730" class="Bound">C</a><a id="783" class="Symbol">}</a>
  <a id="787" class="Symbol">(</a><a id="788" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#788" class="Bound">top</a> <a id="792" class="Symbol">:</a> <a id="794" href="category-theory.set-magmoids.html#1987" class="Function">hom-Set-Magmoid</a> <a id="810" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#730" class="Bound">C</a> <a id="812" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#756" class="Bound">x</a> <a id="814" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#758" class="Bound">y</a><a id="815" class="Symbol">)</a>
  <a id="819" class="Symbol">(</a><a id="820" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#820" class="Bound">left</a> <a id="825" class="Symbol">:</a> <a id="827" href="category-theory.set-magmoids.html#1987" class="Function">hom-Set-Magmoid</a> <a id="843" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#730" class="Bound">C</a> <a id="845" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#756" class="Bound">x</a> <a id="847" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#760" class="Bound">z</a><a id="848" class="Symbol">)</a>
  <a id="852" class="Symbol">(</a><a id="853" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#853" class="Bound">right</a> <a id="859" class="Symbol">:</a> <a id="861" href="category-theory.set-magmoids.html#1987" class="Function">hom-Set-Magmoid</a> <a id="877" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#730" class="Bound">C</a> <a id="879" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#758" class="Bound">y</a> <a id="881" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#762" class="Bound">w</a><a id="882" class="Symbol">)</a>
  <a id="886" class="Symbol">(</a><a id="887" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#887" class="Bound">bottom</a> <a id="894" class="Symbol">:</a> <a id="896" href="category-theory.set-magmoids.html#1987" class="Function">hom-Set-Magmoid</a> <a id="912" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#730" class="Bound">C</a> <a id="914" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#760" class="Bound">z</a> <a id="916" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#762" class="Bound">w</a><a id="917" class="Symbol">)</a> <a id="919" class="Symbol">→</a>
  <a id="923" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="926" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#717" class="Bound">l2</a>
<a id="929" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#676" class="Function">coherence-square-hom-Set-Magmoid</a> <a id="962" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#962" class="Bound">C</a> <a id="964" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#964" class="Bound">top</a> <a id="968" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#968" class="Bound">left</a> <a id="973" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#973" class="Bound">right</a> <a id="979" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#979" class="Bound">bottom</a> <a id="986" class="Symbol">=</a>
  <a id="990" class="Symbol">(</a> <a id="992" href="category-theory.set-magmoids.html#2263" class="Function">comp-hom-Set-Magmoid</a> <a id="1013" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#962" class="Bound">C</a> <a id="1015" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#979" class="Bound">bottom</a> <a id="1022" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#968" class="Bound">left</a><a id="1026" class="Symbol">)</a> <a id="1028" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
  <a id="1032" class="Symbol">(</a> <a id="1034" href="category-theory.set-magmoids.html#2263" class="Function">comp-hom-Set-Magmoid</a> <a id="1055" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#962" class="Bound">C</a> <a id="1057" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#973" class="Bound">right</a> <a id="1063" href="category-theory.commuting-squares-of-morphisms-in-set-magmoids.html#964" class="Bound">top</a><a id="1066" class="Symbol">)</a>
</pre>