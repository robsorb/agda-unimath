# Empty globular types

<pre class="Agda"><a id="33" class="Symbol">{-#</a> <a id="37" class="Keyword">OPTIONS</a> <a id="45" class="Pragma">--guardedness</a> <a id="59" class="Symbol">#-}</a>

<a id="64" class="Keyword">module</a> <a id="71" href="globular-types.empty-globular-types.html" class="Module">globular-types.empty-globular-types</a> <a id="107" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="globular-types.constant-globular-types.html" class="Module">globular-types.constant-globular-types</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

A [globular type](globular-types.globular-types.md) is said to be
{{#concept "empty" Disambiguation="globular type"}} if its type of 0-cells is
[empty](foundation.empty-types.md).

The {{#concept "standard empty globular type" Agda=empty-Globular-Type}} is
defined to be the
[constant globular type](globular-types.constant-globular-types.md) at the empty
type. That is, the standard empty globular type is the globular type `𝟎` given
by

```text
  𝟎₀ := ∅
  𝟎' x y := 𝟎.
```

## Definitions

### The predicate of being an empty globular type

<pre class="Agda"><a id="909" class="Keyword">module</a> <a id="916" href="globular-types.empty-globular-types.html#916" class="Module">_</a>
  <a id="920" class="Symbol">{</a><a id="921" href="globular-types.empty-globular-types.html#921" class="Bound">l1</a> <a id="924" href="globular-types.empty-globular-types.html#924" class="Bound">l2</a> <a id="927" class="Symbol">:</a> <a id="929" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="934" class="Symbol">}</a> <a id="936" class="Symbol">(</a><a id="937" href="globular-types.empty-globular-types.html#937" class="Bound">G</a> <a id="939" class="Symbol">:</a> <a id="941" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="955" href="globular-types.empty-globular-types.html#921" class="Bound">l1</a> <a id="958" href="globular-types.empty-globular-types.html#924" class="Bound">l2</a><a id="960" class="Symbol">)</a>
  <a id="964" class="Keyword">where</a>

  <a id="973" href="globular-types.empty-globular-types.html#973" class="Function">is-empty-Globular-Type</a> <a id="996" class="Symbol">:</a> <a id="998" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1001" href="globular-types.empty-globular-types.html#921" class="Bound">l1</a>
  <a id="1006" href="globular-types.empty-globular-types.html#973" class="Function">is-empty-Globular-Type</a> <a id="1029" class="Symbol">=</a> <a id="1031" href="foundation-core.empty-types.html#972" class="Function">is-empty</a> <a id="1040" class="Symbol">(</a><a id="1041" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1062" href="globular-types.empty-globular-types.html#937" class="Bound">G</a><a id="1063" class="Symbol">)</a>
</pre>
### The standard empty globular type

<pre class="Agda"><a id="empty-Globular-Type"></a><a id="1116" href="globular-types.empty-globular-types.html#1116" class="Function">empty-Globular-Type</a> <a id="1136" class="Symbol">:</a> <a id="1138" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1152" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1158" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1164" href="globular-types.empty-globular-types.html#1116" class="Function">empty-Globular-Type</a> <a id="1184" class="Symbol">=</a> <a id="1186" href="globular-types.constant-globular-types.html#595" class="Function">constant-Globular-Type</a> <a id="1209" href="foundation-core.empty-types.html#801" class="Datatype">empty</a>
</pre>