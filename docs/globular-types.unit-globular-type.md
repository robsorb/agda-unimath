# The unit globular type

<pre class="Agda"><a id="35" class="Symbol">{-#</a> <a id="39" class="Keyword">OPTIONS</a> <a id="47" class="Pragma">--guardedness</a> <a id="61" class="Symbol">#-}</a>

<a id="66" class="Keyword">module</a> <a id="73" href="globular-types.unit-globular-type.html" class="Module">globular-types.unit-globular-type</a> <a id="107" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="globular-types.constant-globular-types.html" class="Module">globular-types.constant-globular-types</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

The {{#concept "unit globular type" Agda=unit-Globular-Type}} is the
[constant globular type](globular-types.constant-globular-types.md) at the
[unit type](foundation.unit-type.md). That is, the unit globular type is the
[globular type](globular-types.globular-types.md) `𝟏` given by

```text
  𝟏₀ := unit
  𝟏' x y := 𝟏.
```

## Definitions

### The unit globular type

<pre class="Agda"><a id="unit-Globular-Type"></a><a id="733" href="globular-types.unit-globular-type.html#733" class="Function">unit-Globular-Type</a> <a id="752" class="Symbol">:</a> <a id="754" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="768" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="774" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="780" href="globular-types.unit-globular-type.html#733" class="Function">unit-Globular-Type</a> <a id="799" class="Symbol">=</a> <a id="801" href="globular-types.constant-globular-types.html#595" class="Function">constant-Globular-Type</a> <a id="824" href="foundation.unit-type.html#950" class="Record">unit</a>
</pre>