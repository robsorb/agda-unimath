# The unit reflexive globular type

<pre class="Agda"><a id="45" class="Symbol">{-#</a> <a id="49" class="Keyword">OPTIONS</a> <a id="57" class="Pragma">--guardedness</a> <a id="71" class="Symbol">#-}</a>

<a id="76" class="Keyword">module</a> <a id="83" href="globular-types.unit-reflexive-globular-type.html" class="Module">globular-types.unit-reflexive-globular-type</a> <a id="127" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
<a id="308" class="Keyword">open</a> <a id="313" class="Keyword">import</a> <a id="320" href="globular-types.unit-globular-type.html" class="Module">globular-types.unit-globular-type</a>
</pre>
</details>

## Idea

The
{{#concept "unit reflexive globular type" Agda=unit-Reflexive-Globular-Type}} is
the [reflexive globular type](globular-types.reflexive-globular-types.md) `𝟏`
given by

```text
  𝟏₀ := unit
  𝟏' x y := 𝟏
  refl 𝟏 x := star.
```

## Definitions

### The unit reflexive globular type

<pre class="Agda"><a id="is-reflexive-unit-Globular-Type"></a><a id="675" href="globular-types.unit-reflexive-globular-type.html#675" class="Function">is-reflexive-unit-Globular-Type</a> <a id="707" class="Symbol">:</a>
  <a id="711" href="globular-types.reflexive-globular-types.html#744" class="Record">is-reflexive-Globular-Type</a> <a id="738" href="globular-types.unit-globular-type.html#733" class="Function">unit-Globular-Type</a>
<a id="757" href="globular-types.reflexive-globular-types.html#867" class="Field">is-reflexive-1-cell-is-reflexive-Globular-Type</a>
  <a id="806" href="globular-types.unit-reflexive-globular-type.html#675" class="Function">is-reflexive-unit-Globular-Type</a> <a id="838" href="globular-types.unit-reflexive-globular-type.html#838" class="Bound">x</a> <a id="840" class="Symbol">=</a>
  <a id="844" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a>
<a id="849" href="globular-types.reflexive-globular-types.html#973" class="Field">is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type</a>
  <a id="912" href="globular-types.unit-reflexive-globular-type.html#675" class="Function">is-reflexive-unit-Globular-Type</a> <a id="944" class="Symbol">=</a>
  <a id="948" href="globular-types.unit-reflexive-globular-type.html#675" class="Function">is-reflexive-unit-Globular-Type</a>

<a id="unit-Reflexive-Globular-Type"></a><a id="981" href="globular-types.unit-reflexive-globular-type.html#981" class="Function">unit-Reflexive-Globular-Type</a> <a id="1010" class="Symbol">:</a> <a id="1012" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="1036" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1042" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1048" href="globular-types.reflexive-globular-types.html#4067" class="Field">globular-type-Reflexive-Globular-Type</a> <a id="1086" href="globular-types.unit-reflexive-globular-type.html#981" class="Function">unit-Reflexive-Globular-Type</a> <a id="1115" class="Symbol">=</a>
  <a id="1119" href="globular-types.unit-globular-type.html#733" class="Function">unit-Globular-Type</a>
<a id="1138" href="globular-types.reflexive-globular-types.html#5323" class="Field">refl-Reflexive-Globular-Type</a> <a id="1167" href="globular-types.unit-reflexive-globular-type.html#981" class="Function">unit-Reflexive-Globular-Type</a> <a id="1196" class="Symbol">=</a>
  <a id="1200" href="globular-types.unit-reflexive-globular-type.html#675" class="Function">is-reflexive-unit-Globular-Type</a>
</pre>