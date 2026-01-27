# The metric space of short functions between metric spaces

<pre class="Agda"><a id="70" class="Keyword">module</a> <a id="77" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html" class="Module">metric-spaces.metric-space-of-short-functions-metric-spaces</a> <a id="137" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="metric-spaces.metric-space-of-functions-metric-spaces.html" class="Module">metric-spaces.metric-space-of-functions-metric-spaces</a>
<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="metric-spaces.short-functions-metric-spaces.html" class="Module">metric-spaces.short-functions-metric-spaces</a>
<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="metric-spaces.subspaces-metric-spaces.html" class="Module">metric-spaces.subspaces-metric-spaces</a>
</pre>
</details>

## Idea

[Short functions](metric-spaces.short-functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) inherit the
[metric subspace](metric-spaces.subspaces-metric-spaces.md) structure of the
[function metric space](metric-spaces.metric-space-of-functions-metric-spaces.md).
This defines the
{{#concept "metric space of short functions between metric spaces" Agda=metric-space-of-short-functions-Metric-Space}}.

## Definitions

### The metric space of short functions between metric spaces

<pre class="Agda"><a id="990" class="Keyword">module</a> <a id="997" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#997" class="Module">_</a>
  <a id="1001" class="Symbol">{</a><a id="1002" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1002" class="Bound">l1</a> <a id="1005" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1005" class="Bound">l2</a> <a id="1008" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1008" class="Bound">l1&#39;</a> <a id="1012" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1012" class="Bound">l2&#39;</a> <a id="1016" class="Symbol">:</a> <a id="1018" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1023" class="Symbol">}</a>
  <a id="1027" class="Symbol">(</a><a id="1028" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1028" class="Bound">A</a> <a id="1030" class="Symbol">:</a> <a id="1032" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1045" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1002" class="Bound">l1</a> <a id="1048" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1005" class="Bound">l2</a><a id="1050" class="Symbol">)</a> <a id="1052" class="Symbol">(</a><a id="1053" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1053" class="Bound">B</a> <a id="1055" class="Symbol">:</a> <a id="1057" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1070" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1008" class="Bound">l1&#39;</a> <a id="1074" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1012" class="Bound">l2&#39;</a><a id="1077" class="Symbol">)</a>
  <a id="1081" class="Keyword">where</a>

  <a id="1090" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1090" class="Function">metric-space-of-short-functions-Metric-Space</a> <a id="1135" class="Symbol">:</a>
    <a id="1141" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1154" class="Symbol">(</a><a id="1155" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1002" class="Bound">l1</a> <a id="1158" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1160" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1005" class="Bound">l2</a> <a id="1163" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1165" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1008" class="Bound">l1&#39;</a> <a id="1169" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1171" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1012" class="Bound">l2&#39;</a><a id="1174" class="Symbol">)</a> <a id="1176" class="Symbol">(</a><a id="1177" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1002" class="Bound">l1</a> <a id="1180" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1182" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1012" class="Bound">l2&#39;</a><a id="1185" class="Symbol">)</a>
  <a id="1189" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1090" class="Function">metric-space-of-short-functions-Metric-Space</a> <a id="1234" class="Symbol">=</a>
    <a id="1240" href="metric-spaces.subspaces-metric-spaces.html#4219" class="Function">subspace-Metric-Space</a>
      <a id="1268" class="Symbol">(</a> <a id="1270" href="metric-spaces.metric-space-of-functions-metric-spaces.html#1288" class="Function">metric-space-of-functions-Metric-Space</a> <a id="1309" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1028" class="Bound">A</a> <a id="1311" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1053" class="Bound">B</a><a id="1312" class="Symbol">)</a>
      <a id="1320" class="Symbol">(</a> <a id="1322" href="metric-spaces.short-functions-metric-spaces.html#2207" class="Function">is-short-function-prop-Metric-Space</a> <a id="1358" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1028" class="Bound">A</a> <a id="1360" href="metric-spaces.metric-space-of-short-functions-metric-spaces.html#1053" class="Bound">B</a><a id="1361" class="Symbol">)</a>
</pre>