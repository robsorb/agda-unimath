# Constant span diagrams

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="foundation.constant-span-diagrams.html" class="Module">foundation.constant-span-diagrams</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
</pre>
</details>

## Idea

The {{#concept "constant span diagram" Agda=constant-span-diagram}} at a type
`X` is the [span diagram](foundation.span-diagrams.md)

```text
      id       id
  X <----- X -----> X.
```

Alternatively, a span diagram

```text
       f       g
  A <----- S -----> B
```

is said to be constant if both `f` and `g` are
[equivalences](foundation-core.equivalences.md).

## Definitions

### Constant span diagrams at a type

<pre class="Agda"><a id="826" class="Keyword">module</a> <a id="833" href="foundation.constant-span-diagrams.html#833" class="Module">_</a>
  <a id="837" class="Symbol">{</a><a id="838" href="foundation.constant-span-diagrams.html#838" class="Bound">l1</a> <a id="841" class="Symbol">:</a> <a id="843" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="848" class="Symbol">}</a>
  <a id="852" class="Keyword">where</a>

  <a id="861" href="foundation.constant-span-diagrams.html#861" class="Function">constant-span-diagram</a> <a id="883" class="Symbol">:</a> <a id="885" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="888" href="foundation.constant-span-diagrams.html#838" class="Bound">l1</a> <a id="891" class="Symbol">→</a> <a id="893" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="906" href="foundation.constant-span-diagrams.html#838" class="Bound">l1</a> <a id="909" href="foundation.constant-span-diagrams.html#838" class="Bound">l1</a> <a id="912" href="foundation.constant-span-diagrams.html#838" class="Bound">l1</a>
  <a id="917" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="921" class="Symbol">(</a><a id="922" href="foundation.constant-span-diagrams.html#861" class="Function">constant-span-diagram</a> <a id="944" href="foundation.constant-span-diagrams.html#944" class="Bound">X</a><a id="945" class="Symbol">)</a> <a id="947" class="Symbol">=</a> <a id="949" href="foundation.constant-span-diagrams.html#944" class="Bound">X</a>
  <a id="953" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="957" class="Symbol">(</a><a id="958" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="962" class="Symbol">(</a><a id="963" href="foundation.constant-span-diagrams.html#861" class="Function">constant-span-diagram</a> <a id="985" href="foundation.constant-span-diagrams.html#985" class="Bound">X</a><a id="986" class="Symbol">))</a> <a id="989" class="Symbol">=</a> <a id="991" href="foundation.constant-span-diagrams.html#985" class="Bound">X</a>
  <a id="995" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="999" class="Symbol">(</a><a id="1000" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1004" class="Symbol">(</a><a id="1005" href="foundation.constant-span-diagrams.html#861" class="Function">constant-span-diagram</a> <a id="1027" href="foundation.constant-span-diagrams.html#1027" class="Bound">X</a><a id="1028" class="Symbol">))</a> <a id="1031" class="Symbol">=</a> <a id="1033" href="foundation.spans.html#2331" class="Function">id-span</a>
</pre>
### The predicate of being a constant span diagram

<pre class="Agda"><a id="1106" class="Keyword">module</a> <a id="1113" href="foundation.constant-span-diagrams.html#1113" class="Module">_</a>
  <a id="1117" class="Symbol">{</a><a id="1118" href="foundation.constant-span-diagrams.html#1118" class="Bound">l1</a> <a id="1121" href="foundation.constant-span-diagrams.html#1121" class="Bound">l2</a> <a id="1124" href="foundation.constant-span-diagrams.html#1124" class="Bound">l3</a> <a id="1127" class="Symbol">:</a> <a id="1129" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1134" class="Symbol">}</a> <a id="1136" class="Symbol">(</a><a id="1137" href="foundation.constant-span-diagrams.html#1137" class="Bound">𝒮</a> <a id="1139" class="Symbol">:</a> <a id="1141" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1154" href="foundation.constant-span-diagrams.html#1118" class="Bound">l1</a> <a id="1157" href="foundation.constant-span-diagrams.html#1121" class="Bound">l2</a> <a id="1160" href="foundation.constant-span-diagrams.html#1124" class="Bound">l3</a><a id="1162" class="Symbol">)</a>
  <a id="1166" class="Keyword">where</a>

  <a id="1175" href="foundation.constant-span-diagrams.html#1175" class="Function">is-constant-span-diagram</a> <a id="1200" class="Symbol">:</a> <a id="1202" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1205" class="Symbol">(</a><a id="1206" href="foundation.constant-span-diagrams.html#1118" class="Bound">l1</a> <a id="1209" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1211" href="foundation.constant-span-diagrams.html#1121" class="Bound">l2</a> <a id="1214" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1216" href="foundation.constant-span-diagrams.html#1124" class="Bound">l3</a><a id="1218" class="Symbol">)</a>
  <a id="1222" href="foundation.constant-span-diagrams.html#1175" class="Function">is-constant-span-diagram</a> <a id="1247" class="Symbol">=</a>
    <a id="1253" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1262" class="Symbol">(</a><a id="1263" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="1285" href="foundation.constant-span-diagrams.html#1137" class="Bound">𝒮</a><a id="1286" class="Symbol">)</a> <a id="1288" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1290" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1299" class="Symbol">(</a><a id="1300" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="1323" href="foundation.constant-span-diagrams.html#1137" class="Bound">𝒮</a><a id="1324" class="Symbol">)</a>
</pre>