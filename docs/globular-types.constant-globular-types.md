# Constant globular types

<pre class="Agda"><a id="36" class="Symbol">{-#</a> <a id="40" class="Keyword">OPTIONS</a> <a id="48" class="Pragma">--guardedness</a> <a id="62" class="Symbol">#-}</a>

<a id="67" class="Keyword">module</a> <a id="74" href="globular-types.constant-globular-types.html" class="Module">globular-types.constant-globular-types</a> <a id="113" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

Consider a type `A`. The
{{#concept "constant globular type" Agda=constant-Globular-Type}} at `A` is the
[globular type](globular-types.globular-types.md) `𝐀` given by

```text
  𝐀₀ := A
  𝐀₁ x y := 𝐀.
```

## Definitions

### The constant globular type at a type

<pre class="Agda"><a id="550" class="Keyword">module</a> <a id="557" href="globular-types.constant-globular-types.html#557" class="Module">_</a>
  <a id="561" class="Symbol">{</a><a id="562" href="globular-types.constant-globular-types.html#562" class="Bound">l</a> <a id="564" class="Symbol">:</a> <a id="566" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="571" class="Symbol">}</a> <a id="573" class="Symbol">(</a><a id="574" href="globular-types.constant-globular-types.html#574" class="Bound">A</a> <a id="576" class="Symbol">:</a> <a id="578" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="581" href="globular-types.constant-globular-types.html#562" class="Bound">l</a><a id="582" class="Symbol">)</a>
  <a id="586" class="Keyword">where</a>

  <a id="595" href="globular-types.constant-globular-types.html#595" class="Function">constant-Globular-Type</a> <a id="618" class="Symbol">:</a> <a id="620" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="634" href="globular-types.constant-globular-types.html#562" class="Bound">l</a> <a id="636" href="globular-types.constant-globular-types.html#562" class="Bound">l</a>
  <a id="640" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="661" href="globular-types.constant-globular-types.html#595" class="Function">constant-Globular-Type</a> <a id="684" class="Symbol">=</a>
    <a id="690" href="globular-types.constant-globular-types.html#574" class="Bound">A</a>
  <a id="694" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="729" href="globular-types.constant-globular-types.html#595" class="Function">constant-Globular-Type</a> <a id="752" href="globular-types.constant-globular-types.html#752" class="Bound">x</a> <a id="754" href="globular-types.constant-globular-types.html#754" class="Bound">y</a> <a id="756" class="Symbol">=</a>
    <a id="762" href="globular-types.constant-globular-types.html#595" class="Function">constant-Globular-Type</a>
</pre>