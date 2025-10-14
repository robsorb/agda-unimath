# Orbits of group actions

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="group-theory.orbits-group-actions.html" class="Module">group-theory.orbits-group-actions</a> <a id="77" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="133" class="Keyword">open</a> <a id="138" class="Keyword">import</a> <a id="145" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="group-theory.groups.html" class="Module">group-theory.groups</a>
</pre>
</details>

## Idea

The [groupoid](category-theory.groupoids.md) of **orbits** of a
[group action](group-theory.group-actions.md) consists of elements of `X`, and a
morphism from `x` to `y` is given by an element `g` of the
[group](group-theory.groups.md) `G` such that `gx ＝ y`.

## Definition

<pre class="Agda"><a id="636" class="Keyword">module</a> <a id="643" href="group-theory.orbits-group-actions.html#643" class="Module">_</a>
  <a id="647" class="Symbol">{</a><a id="648" href="group-theory.orbits-group-actions.html#648" class="Bound">l1</a> <a id="651" href="group-theory.orbits-group-actions.html#651" class="Bound">l2</a> <a id="654" class="Symbol">:</a> <a id="656" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="661" class="Symbol">}</a> <a id="663" class="Symbol">(</a><a id="664" href="group-theory.orbits-group-actions.html#664" class="Bound">G</a> <a id="666" class="Symbol">:</a> <a id="668" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="674" href="group-theory.orbits-group-actions.html#648" class="Bound">l1</a><a id="676" class="Symbol">)</a> <a id="678" class="Symbol">(</a><a id="679" href="group-theory.orbits-group-actions.html#679" class="Bound">X</a> <a id="681" class="Symbol">:</a> <a id="683" href="group-theory.group-actions.html#1098" class="Function">action-Group</a> <a id="696" href="group-theory.orbits-group-actions.html#664" class="Bound">G</a> <a id="698" href="group-theory.orbits-group-actions.html#651" class="Bound">l2</a><a id="700" class="Symbol">)</a>
  <a id="704" class="Keyword">where</a>

  <a id="713" href="group-theory.orbits-group-actions.html#713" class="Function">hom-orbit-action-Group</a> <a id="736" class="Symbol">:</a>
    <a id="742" class="Symbol">(</a><a id="743" href="group-theory.orbits-group-actions.html#743" class="Bound">x</a> <a id="745" href="group-theory.orbits-group-actions.html#745" class="Bound">y</a> <a id="747" class="Symbol">:</a> <a id="749" href="group-theory.group-actions.html#1351" class="Function">type-action-Group</a> <a id="767" href="group-theory.orbits-group-actions.html#664" class="Bound">G</a> <a id="769" href="group-theory.orbits-group-actions.html#679" class="Bound">X</a><a id="770" class="Symbol">)</a> <a id="772" class="Symbol">→</a> <a id="774" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="777" class="Symbol">(</a><a id="778" href="group-theory.orbits-group-actions.html#648" class="Bound">l1</a> <a id="781" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="783" href="group-theory.orbits-group-actions.html#651" class="Bound">l2</a><a id="785" class="Symbol">)</a>
  <a id="789" href="group-theory.orbits-group-actions.html#713" class="Function">hom-orbit-action-Group</a> <a id="812" href="group-theory.orbits-group-actions.html#812" class="Bound">x</a> <a id="814" href="group-theory.orbits-group-actions.html#814" class="Bound">y</a> <a id="816" class="Symbol">=</a>
    <a id="822" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="824" class="Symbol">(</a><a id="825" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="836" href="group-theory.orbits-group-actions.html#664" class="Bound">G</a><a id="837" class="Symbol">)</a> <a id="839" class="Symbol">(λ</a> <a id="842" href="group-theory.orbits-group-actions.html#842" class="Bound">g</a> <a id="844" class="Symbol">→</a> <a id="846" href="group-theory.group-actions.html#1716" class="Function">mul-action-Group</a> <a id="863" href="group-theory.orbits-group-actions.html#664" class="Bound">G</a> <a id="865" href="group-theory.orbits-group-actions.html#679" class="Bound">X</a> <a id="867" href="group-theory.orbits-group-actions.html#842" class="Bound">g</a> <a id="869" href="group-theory.orbits-group-actions.html#812" class="Bound">x</a> <a id="871" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="873" href="group-theory.orbits-group-actions.html#814" class="Bound">y</a><a id="874" class="Symbol">)</a>
</pre>