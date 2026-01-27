# The metric space of convergent sequences in metric spaces

<pre class="Agda"><a id="70" class="Keyword">module</a> <a id="77" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html" class="Module">metric-spaces.metric-space-of-convergent-sequences-metric-spaces</a> <a id="142" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="metric-spaces.convergent-sequences-metric-spaces.html" class="Module">metric-spaces.convergent-sequences-metric-spaces</a>
<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="metric-spaces.sequences-metric-spaces.html" class="Module">metric-spaces.sequences-metric-spaces</a>
<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="metric-spaces.subspaces-metric-spaces.html" class="Module">metric-spaces.subspaces-metric-spaces</a>
</pre>
</details>

## Idea

The [convergent sequences](metric-spaces.convergent-sequences-metric-spaces.md)
in a [metric space](metric-spaces.metric-spaces.md) inherit the
[subbspace metric structure](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of sequences](metric-spaces.sequences-metric-spaces.md). This
defines the
{{#concept "metric space of convergent sequences in a metric space" Agda=metric-space-of-convergent-sequences-Metric-Space}}.

## Definitions

<pre class="Agda"><a id="926" class="Keyword">module</a> <a id="933" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#933" class="Module">_</a>
  <a id="937" class="Symbol">{</a><a id="938" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#938" class="Bound">l1</a> <a id="941" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#941" class="Bound">l2</a> <a id="944" class="Symbol">:</a> <a id="946" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="951" class="Symbol">}</a> <a id="953" class="Symbol">(</a><a id="954" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#954" class="Bound">M</a> <a id="956" class="Symbol">:</a> <a id="958" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="971" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#938" class="Bound">l1</a> <a id="974" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#941" class="Bound">l2</a><a id="976" class="Symbol">)</a>
  <a id="980" class="Keyword">where</a>

  <a id="989" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#989" class="Function">metric-space-of-convergent-sequences-Metric-Space</a> <a id="1039" class="Symbol">:</a> <a id="1041" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1054" class="Symbol">(</a><a id="1055" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#938" class="Bound">l1</a> <a id="1058" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1060" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#941" class="Bound">l2</a><a id="1062" class="Symbol">)</a> <a id="1064" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#941" class="Bound">l2</a>
  <a id="1069" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#989" class="Function">metric-space-of-convergent-sequences-Metric-Space</a> <a id="1119" class="Symbol">=</a>
    <a id="1125" href="metric-spaces.subspaces-metric-spaces.html#4219" class="Function">subspace-Metric-Space</a>
      <a id="1153" class="Symbol">(</a> <a id="1155" href="metric-spaces.sequences-metric-spaces.html#705" class="Function">sequence-Metric-Space</a> <a id="1177" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#954" class="Bound">M</a><a id="1178" class="Symbol">)</a>
      <a id="1186" class="Symbol">(</a> <a id="1188" href="metric-spaces.convergent-sequences-metric-spaces.html#1113" class="Function">subtype-convergent-sequence-Metric-Space</a> <a id="1229" href="metric-spaces.metric-space-of-convergent-sequences-metric-spaces.html#954" class="Bound">M</a><a id="1230" class="Symbol">)</a>
</pre>