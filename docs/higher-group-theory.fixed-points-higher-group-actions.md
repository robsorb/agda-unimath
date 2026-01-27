# Fixed points of higher group actions

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="higher-group-theory.fixed-points-higher-group-actions.html" class="Module">higher-group-theory.fixed-points-higher-group-actions</a> <a id="110" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="higher-group-theory.higher-group-actions.html" class="Module">higher-group-theory.higher-group-actions</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>
</pre>
</details>

## Idea

The type of fixed points of a higher group action `X : BG → UU` is the type of
sections `(u : BG) → X u`.

## Definition

<pre class="Agda"><a id="fixed-point-action-∞-Group"></a><a id="461" href="higher-group-theory.fixed-points-higher-group-actions.html#461" class="Function">fixed-point-action-∞-Group</a> <a id="488" class="Symbol">:</a>
  <a id="492" class="Symbol">{</a><a id="493" href="higher-group-theory.fixed-points-higher-group-actions.html#493" class="Bound">l1</a> <a id="496" href="higher-group-theory.fixed-points-higher-group-actions.html#496" class="Bound">l2</a> <a id="499" class="Symbol">:</a> <a id="501" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="506" class="Symbol">}</a> <a id="508" class="Symbol">(</a><a id="509" href="higher-group-theory.fixed-points-higher-group-actions.html#509" class="Bound">G</a> <a id="511" class="Symbol">:</a> <a id="513" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="521" href="higher-group-theory.fixed-points-higher-group-actions.html#493" class="Bound">l1</a><a id="523" class="Symbol">)</a> <a id="525" class="Symbol">(</a><a id="526" href="higher-group-theory.fixed-points-higher-group-actions.html#526" class="Bound">X</a> <a id="528" class="Symbol">:</a> <a id="530" href="higher-group-theory.higher-group-actions.html#485" class="Function">action-∞-Group</a> <a id="545" href="higher-group-theory.fixed-points-higher-group-actions.html#496" class="Bound">l2</a> <a id="548" href="higher-group-theory.fixed-points-higher-group-actions.html#509" class="Bound">G</a><a id="549" class="Symbol">)</a> <a id="551" class="Symbol">→</a> <a id="553" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="556" class="Symbol">(</a><a id="557" href="higher-group-theory.fixed-points-higher-group-actions.html#493" class="Bound">l1</a> <a id="560" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="562" href="higher-group-theory.fixed-points-higher-group-actions.html#496" class="Bound">l2</a><a id="564" class="Symbol">)</a>
<a id="566" href="higher-group-theory.fixed-points-higher-group-actions.html#461" class="Function">fixed-point-action-∞-Group</a> <a id="593" href="higher-group-theory.fixed-points-higher-group-actions.html#593" class="Bound">G</a> <a id="595" href="higher-group-theory.fixed-points-higher-group-actions.html#595" class="Bound">X</a> <a id="597" class="Symbol">=</a> <a id="599" class="Symbol">(</a><a id="600" href="higher-group-theory.fixed-points-higher-group-actions.html#600" class="Bound">u</a> <a id="602" class="Symbol">:</a> <a id="604" href="higher-group-theory.higher-groups.html#1252" class="Function">classifying-type-∞-Group</a> <a id="629" href="higher-group-theory.fixed-points-higher-group-actions.html#593" class="Bound">G</a><a id="630" class="Symbol">)</a> <a id="632" class="Symbol">→</a> <a id="634" href="higher-group-theory.fixed-points-higher-group-actions.html#595" class="Bound">X</a> <a id="636" href="higher-group-theory.fixed-points-higher-group-actions.html#600" class="Bound">u</a>
</pre>