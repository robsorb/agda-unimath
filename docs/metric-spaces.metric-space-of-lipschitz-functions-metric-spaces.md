# The metric space of Lipschitz functions between metric spaces

<pre class="Agda"><a id="74" class="Keyword">module</a> <a id="81" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html" class="Module">metric-spaces.metric-space-of-lipschitz-functions-metric-spaces</a> <a id="145" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="201" class="Keyword">open</a> <a id="206" class="Keyword">import</a> <a id="213" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="metric-spaces.lipschitz-functions-metric-spaces.html" class="Module">metric-spaces.lipschitz-functions-metric-spaces</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="metric-spaces.metric-space-of-functions-metric-spaces.html" class="Module">metric-spaces.metric-space-of-functions-metric-spaces</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="407" class="Keyword">open</a> <a id="412" class="Keyword">import</a> <a id="419" href="metric-spaces.subspaces-metric-spaces.html" class="Module">metric-spaces.subspaces-metric-spaces</a>
</pre>
</details>

## Idea

[Lipschitz functions](metric-spaces.lipschitz-functions-metric-spaces.md)
between [metric spaces](metric-spaces.metric-spaces.md) inherit the
[metric subspace](metric-spaces.subspaces-metric-spaces.md) structure of the
[function metric space](metric-spaces.metric-space-of-functions-metric-spaces.md).
This defines the
{{#concept "metric space of Lipschitz functions between metric spaces" Agda=metric-space-of-lipschitz-functions-Metric-Space}}.

## Definitions

### The metric space of Lipschitz functions between metric spaces

<pre class="Agda"><a id="1022" class="Keyword">module</a> <a id="1029" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1029" class="Module">_</a>
  <a id="1033" class="Symbol">{</a><a id="1034" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1034" class="Bound">l1</a> <a id="1037" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1037" class="Bound">l2</a> <a id="1040" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1040" class="Bound">l1&#39;</a> <a id="1044" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1044" class="Bound">l2&#39;</a> <a id="1048" class="Symbol">:</a> <a id="1050" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1055" class="Symbol">}</a>
  <a id="1059" class="Symbol">(</a><a id="1060" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1060" class="Bound">A</a> <a id="1062" class="Symbol">:</a> <a id="1064" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1077" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1034" class="Bound">l1</a> <a id="1080" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1037" class="Bound">l2</a><a id="1082" class="Symbol">)</a> <a id="1084" class="Symbol">(</a><a id="1085" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1085" class="Bound">B</a> <a id="1087" class="Symbol">:</a> <a id="1089" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1102" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1040" class="Bound">l1&#39;</a> <a id="1106" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1044" class="Bound">l2&#39;</a><a id="1109" class="Symbol">)</a>
  <a id="1113" class="Keyword">where</a>

  <a id="1122" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1122" class="Function">metric-space-of-lipschitz-functions-Metric-Space</a> <a id="1171" class="Symbol">:</a>
    <a id="1177" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1190" class="Symbol">(</a><a id="1191" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1034" class="Bound">l1</a> <a id="1194" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1196" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1037" class="Bound">l2</a> <a id="1199" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1201" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1040" class="Bound">l1&#39;</a> <a id="1205" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1207" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1044" class="Bound">l2&#39;</a><a id="1210" class="Symbol">)</a> <a id="1212" class="Symbol">(</a><a id="1213" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1034" class="Bound">l1</a> <a id="1216" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1218" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1044" class="Bound">l2&#39;</a><a id="1221" class="Symbol">)</a>
  <a id="1225" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1122" class="Function">metric-space-of-lipschitz-functions-Metric-Space</a> <a id="1274" class="Symbol">=</a>
    <a id="1280" href="metric-spaces.subspaces-metric-spaces.html#4219" class="Function">subspace-Metric-Space</a>
      <a id="1308" class="Symbol">(</a> <a id="1310" href="metric-spaces.metric-space-of-functions-metric-spaces.html#1288" class="Function">metric-space-of-functions-Metric-Space</a> <a id="1349" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1060" class="Bound">A</a> <a id="1351" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1085" class="Bound">B</a><a id="1352" class="Symbol">)</a>
      <a id="1360" class="Symbol">(</a> <a id="1362" href="metric-spaces.lipschitz-functions-metric-spaces.html#4079" class="Function">is-lipschitz-function-prop-Metric-Space</a> <a id="1402" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1060" class="Bound">A</a> <a id="1404" href="metric-spaces.metric-space-of-lipschitz-functions-metric-spaces.html#1085" class="Bound">B</a><a id="1405" class="Symbol">)</a>
</pre>