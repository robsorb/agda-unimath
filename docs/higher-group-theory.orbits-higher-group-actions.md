# Orbits of higher group actions

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="higher-group-theory.orbits-higher-group-actions.html" class="Module">higher-group-theory.orbits-higher-group-actions</a> <a id="98" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="higher-group-theory.higher-group-actions.html" class="Module">higher-group-theory.higher-group-actions</a>
<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>
</pre>
</details>

## Idea

The type of orbits of a higher group action `X` acted upon by `G` is the total
space of `X`.

## Definition

<pre class="Agda"><a id="orbit-action-∞-Group"></a><a id="480" href="higher-group-theory.orbits-higher-group-actions.html#480" class="Function">orbit-action-∞-Group</a> <a id="501" class="Symbol">:</a>
  <a id="505" class="Symbol">{</a><a id="506" href="higher-group-theory.orbits-higher-group-actions.html#506" class="Bound">l1</a> <a id="509" href="higher-group-theory.orbits-higher-group-actions.html#509" class="Bound">l2</a> <a id="512" class="Symbol">:</a> <a id="514" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="519" class="Symbol">}</a> <a id="521" class="Symbol">(</a><a id="522" href="higher-group-theory.orbits-higher-group-actions.html#522" class="Bound">G</a> <a id="524" class="Symbol">:</a> <a id="526" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="534" href="higher-group-theory.orbits-higher-group-actions.html#506" class="Bound">l1</a><a id="536" class="Symbol">)</a> <a id="538" class="Symbol">(</a><a id="539" href="higher-group-theory.orbits-higher-group-actions.html#539" class="Bound">X</a> <a id="541" class="Symbol">:</a> <a id="543" href="higher-group-theory.higher-group-actions.html#485" class="Function">action-∞-Group</a> <a id="558" href="higher-group-theory.orbits-higher-group-actions.html#509" class="Bound">l2</a> <a id="561" href="higher-group-theory.orbits-higher-group-actions.html#522" class="Bound">G</a><a id="562" class="Symbol">)</a> <a id="564" class="Symbol">→</a> <a id="566" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="569" class="Symbol">(</a><a id="570" href="higher-group-theory.orbits-higher-group-actions.html#506" class="Bound">l1</a> <a id="573" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="575" href="higher-group-theory.orbits-higher-group-actions.html#509" class="Bound">l2</a><a id="577" class="Symbol">)</a>
<a id="579" href="higher-group-theory.orbits-higher-group-actions.html#480" class="Function">orbit-action-∞-Group</a> <a id="600" href="higher-group-theory.orbits-higher-group-actions.html#600" class="Bound">G</a> <a id="602" href="higher-group-theory.orbits-higher-group-actions.html#602" class="Bound">X</a> <a id="604" class="Symbol">=</a> <a id="606" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="608" class="Symbol">(</a><a id="609" href="higher-group-theory.higher-groups.html#1252" class="Function">classifying-type-∞-Group</a> <a id="634" href="higher-group-theory.orbits-higher-group-actions.html#600" class="Bound">G</a><a id="635" class="Symbol">)</a> <a id="637" href="higher-group-theory.orbits-higher-group-actions.html#602" class="Bound">X</a>
</pre>