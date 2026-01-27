# The metric space of isometries between metric spaces

<pre class="Agda"><a id="65" class="Keyword">module</a> <a id="72" href="metric-spaces.metric-space-of-isometries-metric-spaces.html" class="Module">metric-spaces.metric-space-of-isometries-metric-spaces</a> <a id="127" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="metric-spaces.isometries-metric-spaces.html" class="Module">metric-spaces.isometries-metric-spaces</a>
<a id="274" class="Keyword">open</a> <a id="279" class="Keyword">import</a> <a id="286" href="metric-spaces.metric-space-of-functions-metric-spaces.html" class="Module">metric-spaces.metric-space-of-functions-metric-spaces</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="metric-spaces.subspaces-metric-spaces.html" class="Module">metric-spaces.subspaces-metric-spaces</a>
</pre>
</details>

## Idea

[Isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) inherit the
[metric subspace](metric-spaces.subspaces-metric-spaces.md) structure of the
[function metric space](metric-spaces.metric-space-of-functions-metric-spaces.md).
This defines the
{{#concept "metric space of isometries between metric spaces" Agda=metric-space-of-isometries-Metric-Space}}.

## Definitions

### The metric space of isometries between metric spaces

<pre class="Agda"><a id="950" class="Keyword">module</a> <a id="957" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#957" class="Module">_</a>
  <a id="961" class="Symbol">{</a><a id="962" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#962" class="Bound">l1</a> <a id="965" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#965" class="Bound">l2</a> <a id="968" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#968" class="Bound">l1&#39;</a> <a id="972" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#972" class="Bound">l2&#39;</a> <a id="976" class="Symbol">:</a> <a id="978" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="983" class="Symbol">}</a>
  <a id="987" class="Symbol">(</a><a id="988" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#988" class="Bound">A</a> <a id="990" class="Symbol">:</a> <a id="992" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1005" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#962" class="Bound">l1</a> <a id="1008" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#965" class="Bound">l2</a><a id="1010" class="Symbol">)</a> <a id="1012" class="Symbol">(</a><a id="1013" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#1013" class="Bound">B</a> <a id="1015" class="Symbol">:</a> <a id="1017" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1030" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#968" class="Bound">l1&#39;</a> <a id="1034" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#972" class="Bound">l2&#39;</a><a id="1037" class="Symbol">)</a>
  <a id="1041" class="Keyword">where</a>

  <a id="1050" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#1050" class="Function">metric-space-of-isometries-Metric-Space</a> <a id="1090" class="Symbol">:</a>
    <a id="1096" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1109" class="Symbol">(</a><a id="1110" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#962" class="Bound">l1</a> <a id="1113" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1115" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#965" class="Bound">l2</a> <a id="1118" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1120" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#968" class="Bound">l1&#39;</a> <a id="1124" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1126" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#972" class="Bound">l2&#39;</a><a id="1129" class="Symbol">)</a> <a id="1131" class="Symbol">(</a><a id="1132" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#962" class="Bound">l1</a> <a id="1135" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1137" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#972" class="Bound">l2&#39;</a><a id="1140" class="Symbol">)</a>
  <a id="1144" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#1050" class="Function">metric-space-of-isometries-Metric-Space</a> <a id="1184" class="Symbol">=</a>
    <a id="1190" href="metric-spaces.subspaces-metric-spaces.html#4219" class="Function">subspace-Metric-Space</a>
      <a id="1218" class="Symbol">(</a> <a id="1220" href="metric-spaces.metric-space-of-functions-metric-spaces.html#1288" class="Function">metric-space-of-functions-Metric-Space</a> <a id="1259" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#988" class="Bound">A</a> <a id="1261" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#1013" class="Bound">B</a><a id="1262" class="Symbol">)</a>
      <a id="1270" class="Symbol">(</a> <a id="1272" href="metric-spaces.isometries-metric-spaces.html#1943" class="Function">is-isometry-prop-Metric-Space</a> <a id="1302" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#988" class="Bound">A</a> <a id="1304" href="metric-spaces.metric-space-of-isometries-metric-spaces.html#1013" class="Bound">B</a><a id="1305" class="Symbol">)</a>
</pre>