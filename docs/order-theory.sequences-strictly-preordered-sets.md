# Sequences in strictly preordered sets

<pre class="Agda"><a id="50" class="Keyword">module</a> <a id="57" href="order-theory.sequences-strictly-preordered-sets.html" class="Module">order-theory.sequences-strictly-preordered-sets</a> <a id="105" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="lists.sequences.html" class="Module">lists.sequences</a>

<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="order-theory.strictly-preordered-sets.html" class="Module">order-theory.strictly-preordered-sets</a>
</pre>
</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a strictly preordered set" Agda=type-sequence-Strictly-Preordered-Set}}
in a [strictly preordered set](order-theory.strictly-preordered-sets.md) is a
[sequence](lists.sequences.md) in its underlying type.

## Definition

### Sequences in a strictly preordered set

<pre class="Agda"><a id="622" class="Keyword">module</a> <a id="629" href="order-theory.sequences-strictly-preordered-sets.html#629" class="Module">_</a>
  <a id="633" class="Symbol">{</a><a id="634" href="order-theory.sequences-strictly-preordered-sets.html#634" class="Bound">l1</a> <a id="637" href="order-theory.sequences-strictly-preordered-sets.html#637" class="Bound">l2</a> <a id="640" class="Symbol">:</a> <a id="642" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="647" class="Symbol">}</a> <a id="649" class="Symbol">(</a><a id="650" href="order-theory.sequences-strictly-preordered-sets.html#650" class="Bound">A</a> <a id="652" class="Symbol">:</a> <a id="654" href="order-theory.strictly-preordered-sets.html#1192" class="Function">Strictly-Preordered-Set</a> <a id="678" href="order-theory.sequences-strictly-preordered-sets.html#634" class="Bound">l1</a> <a id="681" href="order-theory.sequences-strictly-preordered-sets.html#637" class="Bound">l2</a><a id="683" class="Symbol">)</a>
  <a id="687" class="Keyword">where</a>

  <a id="696" href="order-theory.sequences-strictly-preordered-sets.html#696" class="Function">type-sequence-Strictly-Preordered-Set</a> <a id="734" class="Symbol">:</a> <a id="736" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="739" href="order-theory.sequences-strictly-preordered-sets.html#634" class="Bound">l1</a>
  <a id="744" href="order-theory.sequences-strictly-preordered-sets.html#696" class="Function">type-sequence-Strictly-Preordered-Set</a> <a id="782" class="Symbol">=</a>
    <a id="788" href="lists.sequences.html#682" class="Function">sequence</a> <a id="797" class="Symbol">(</a><a id="798" href="order-theory.strictly-preordered-sets.html#1842" class="Function">type-Strictly-Preordered-Set</a> <a id="827" href="order-theory.sequences-strictly-preordered-sets.html#650" class="Bound">A</a><a id="828" class="Symbol">)</a>
</pre>