# Images of metric spaces

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="metric-spaces.images-metric-spaces.html" class="Module">metric-spaces.images-metric-spaces</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="foundation.images.html" class="Module">foundation.images</a>
<a id="164" class="Keyword">open</a> <a id="169" class="Keyword">import</a> <a id="176" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="metric-spaces.functions-metric-spaces.html" class="Module">metric-spaces.functions-metric-spaces</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="metric-spaces.subspaces-metric-spaces.html" class="Module">metric-spaces.subspaces-metric-spaces</a>
</pre>
</details>

## Idea

Given a [function](metric-spaces.functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) `f : X → Y`, the
[image](foundation.images.md) of `X` under `f` is a
[subspace](metric-spaces.subspaces-metric-spaces.md) of `Y`.

## Definition

<pre class="Agda"><a id="641" class="Keyword">module</a> <a id="648" href="metric-spaces.images-metric-spaces.html#648" class="Module">_</a>
  <a id="652" class="Symbol">{</a><a id="653" href="metric-spaces.images-metric-spaces.html#653" class="Bound">l1</a> <a id="656" href="metric-spaces.images-metric-spaces.html#656" class="Bound">l2</a> <a id="659" href="metric-spaces.images-metric-spaces.html#659" class="Bound">l3</a> <a id="662" href="metric-spaces.images-metric-spaces.html#662" class="Bound">l4</a> <a id="665" class="Symbol">:</a> <a id="667" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="672" class="Symbol">}</a> <a id="674" class="Symbol">(</a><a id="675" href="metric-spaces.images-metric-spaces.html#675" class="Bound">X</a> <a id="677" class="Symbol">:</a> <a id="679" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="692" href="metric-spaces.images-metric-spaces.html#653" class="Bound">l1</a> <a id="695" href="metric-spaces.images-metric-spaces.html#656" class="Bound">l2</a><a id="697" class="Symbol">)</a> <a id="699" class="Symbol">(</a><a id="700" href="metric-spaces.images-metric-spaces.html#700" class="Bound">Y</a> <a id="702" class="Symbol">:</a> <a id="704" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="717" href="metric-spaces.images-metric-spaces.html#659" class="Bound">l3</a> <a id="720" href="metric-spaces.images-metric-spaces.html#662" class="Bound">l4</a><a id="722" class="Symbol">)</a>
  <a id="726" class="Symbol">(</a><a id="727" href="metric-spaces.images-metric-spaces.html#727" class="Bound">f</a> <a id="729" class="Symbol">:</a> <a id="731" href="metric-spaces.functions-metric-spaces.html#862" class="Function">type-function-Metric-Space</a> <a id="758" href="metric-spaces.images-metric-spaces.html#675" class="Bound">X</a> <a id="760" href="metric-spaces.images-metric-spaces.html#700" class="Bound">Y</a><a id="761" class="Symbol">)</a>
  <a id="765" class="Keyword">where</a>

  <a id="774" href="metric-spaces.images-metric-spaces.html#774" class="Function">im-Metric-Space</a> <a id="790" class="Symbol">:</a> <a id="792" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="805" class="Symbol">(</a><a id="806" href="metric-spaces.images-metric-spaces.html#653" class="Bound">l1</a> <a id="809" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="811" href="metric-spaces.images-metric-spaces.html#659" class="Bound">l3</a><a id="813" class="Symbol">)</a> <a id="815" href="metric-spaces.images-metric-spaces.html#662" class="Bound">l4</a>
  <a id="820" href="metric-spaces.images-metric-spaces.html#774" class="Function">im-Metric-Space</a> <a id="836" class="Symbol">=</a> <a id="838" href="metric-spaces.subspaces-metric-spaces.html#4219" class="Function">subspace-Metric-Space</a> <a id="860" href="metric-spaces.images-metric-spaces.html#700" class="Bound">Y</a> <a id="862" class="Symbol">(</a><a id="863" href="foundation.images.html#1616" class="Function">subtype-im</a> <a id="874" href="metric-spaces.images-metric-spaces.html#727" class="Bound">f</a><a id="875" class="Symbol">)</a>
</pre>