# Functions between metric spaces

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="metric-spaces.functions-metric-spaces.html" class="Module">metric-spaces.functions-metric-spaces</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
</pre>
</details>

## Idea

{{#concept "Functions" Disambiguation="between metric spaces" Agda=type-function-Metric-Space}}
between [metric spaces](metric-spaces.metric-spaces.md) are functions between
their carrier types.

## Definitions

### The set of functions between metric spaces

<pre class="Agda"><a id="629" class="Keyword">module</a> <a id="636" href="metric-spaces.functions-metric-spaces.html#636" class="Module">_</a>
  <a id="640" class="Symbol">{</a><a id="641" href="metric-spaces.functions-metric-spaces.html#641" class="Bound">lx</a> <a id="644" href="metric-spaces.functions-metric-spaces.html#644" class="Bound">lx&#39;</a> <a id="648" href="metric-spaces.functions-metric-spaces.html#648" class="Bound">ly</a> <a id="651" href="metric-spaces.functions-metric-spaces.html#651" class="Bound">ly&#39;</a> <a id="655" class="Symbol">:</a> <a id="657" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="662" class="Symbol">}</a>
  <a id="666" class="Symbol">(</a><a id="667" href="metric-spaces.functions-metric-spaces.html#667" class="Bound">X</a> <a id="669" class="Symbol">:</a> <a id="671" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="684" href="metric-spaces.functions-metric-spaces.html#641" class="Bound">lx</a> <a id="687" href="metric-spaces.functions-metric-spaces.html#644" class="Bound">lx&#39;</a><a id="690" class="Symbol">)</a> <a id="692" class="Symbol">(</a><a id="693" href="metric-spaces.functions-metric-spaces.html#693" class="Bound">Y</a> <a id="695" class="Symbol">:</a> <a id="697" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="710" href="metric-spaces.functions-metric-spaces.html#648" class="Bound">ly</a> <a id="713" href="metric-spaces.functions-metric-spaces.html#651" class="Bound">ly&#39;</a><a id="716" class="Symbol">)</a>
  <a id="720" class="Keyword">where</a>

  <a id="729" href="metric-spaces.functions-metric-spaces.html#729" class="Function">set-function-Metric-Space</a> <a id="755" class="Symbol">:</a> <a id="757" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="761" class="Symbol">(</a><a id="762" href="metric-spaces.functions-metric-spaces.html#641" class="Bound">lx</a> <a id="765" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="767" href="metric-spaces.functions-metric-spaces.html#648" class="Bound">ly</a><a id="769" class="Symbol">)</a>
  <a id="773" href="metric-spaces.functions-metric-spaces.html#729" class="Function">set-function-Metric-Space</a> <a id="799" class="Symbol">=</a>
    <a id="805" href="foundation.sets.html#4326" class="Function">hom-set-Set</a> <a id="817" class="Symbol">(</a><a id="818" href="metric-spaces.metric-spaces.html#11131" class="Function">set-Metric-Space</a> <a id="835" href="metric-spaces.functions-metric-spaces.html#667" class="Bound">X</a><a id="836" class="Symbol">)</a> <a id="838" class="Symbol">(</a><a id="839" href="metric-spaces.metric-spaces.html#11131" class="Function">set-Metric-Space</a> <a id="856" href="metric-spaces.functions-metric-spaces.html#693" class="Bound">Y</a><a id="857" class="Symbol">)</a>

  <a id="862" href="metric-spaces.functions-metric-spaces.html#862" class="Function">type-function-Metric-Space</a> <a id="889" class="Symbol">:</a> <a id="891" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="894" class="Symbol">(</a><a id="895" href="metric-spaces.functions-metric-spaces.html#641" class="Bound">lx</a> <a id="898" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="900" href="metric-spaces.functions-metric-spaces.html#648" class="Bound">ly</a><a id="902" class="Symbol">)</a>
  <a id="906" href="metric-spaces.functions-metric-spaces.html#862" class="Function">type-function-Metric-Space</a> <a id="933" class="Symbol">=</a>
    <a id="939" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="957" href="metric-spaces.functions-metric-spaces.html#667" class="Bound">X</a> <a id="959" class="Symbol">→</a> <a id="961" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="979" href="metric-spaces.functions-metric-spaces.html#693" class="Bound">Y</a>
</pre>
### The identity function on a metric space

<pre class="Agda"><a id="1039" class="Keyword">module</a> <a id="1046" href="metric-spaces.functions-metric-spaces.html#1046" class="Module">_</a>
  <a id="1050" class="Symbol">{</a><a id="1051" href="metric-spaces.functions-metric-spaces.html#1051" class="Bound">l1</a> <a id="1054" href="metric-spaces.functions-metric-spaces.html#1054" class="Bound">l2</a> <a id="1057" class="Symbol">:</a> <a id="1059" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1064" class="Symbol">}</a> <a id="1066" class="Symbol">(</a><a id="1067" href="metric-spaces.functions-metric-spaces.html#1067" class="Bound">M</a> <a id="1069" class="Symbol">:</a> <a id="1071" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="1084" href="metric-spaces.functions-metric-spaces.html#1051" class="Bound">l1</a> <a id="1087" href="metric-spaces.functions-metric-spaces.html#1054" class="Bound">l2</a><a id="1089" class="Symbol">)</a>
  <a id="1093" class="Keyword">where</a>

  <a id="1102" href="metric-spaces.functions-metric-spaces.html#1102" class="Function">id-Metric-Space</a> <a id="1118" class="Symbol">:</a> <a id="1120" href="metric-spaces.functions-metric-spaces.html#862" class="Function">type-function-Metric-Space</a> <a id="1147" href="metric-spaces.functions-metric-spaces.html#1067" class="Bound">M</a> <a id="1149" href="metric-spaces.functions-metric-spaces.html#1067" class="Bound">M</a>
  <a id="1153" href="metric-spaces.functions-metric-spaces.html#1102" class="Function">id-Metric-Space</a> <a id="1169" class="Symbol">=</a> <a id="1171" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>