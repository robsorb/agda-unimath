# Transfinite cocomposition of maps

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="foundation.transfinite-cocomposition-of-maps.html" class="Module">foundation.transfinite-cocomposition-of-maps</a> <a id="98" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.inverse-sequential-diagrams.html" class="Module">foundation.inverse-sequential-diagrams</a>
<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.sequential-limits.html" class="Module">foundation.sequential-limits</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Given an
[inverse sequential diagram of types](foundation.inverse-sequential-diagrams.md),
i.e. a certain infinite [sequence](lists.dependent-sequences.md) of maps `fₙ`:

```text
      ⋯        fₙ      ⋯      f₁      f₀
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₁ ---> A₀,
```

we can form the **transfinite cocomposition** of `f` by taking the canonical map
from the [standard sequential limit](foundation.sequential-limits.md) `limₙ Aₙ`
into `A₀`.

## Definitions

### The transfinite cocomposition of an inverse sequential diagram of maps

<pre class="Agda"><a id="855" class="Keyword">module</a> <a id="862" href="foundation.transfinite-cocomposition-of-maps.html#862" class="Module">_</a>
  <a id="866" class="Symbol">{</a><a id="867" href="foundation.transfinite-cocomposition-of-maps.html#867" class="Bound">l</a> <a id="869" class="Symbol">:</a> <a id="871" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="876" class="Symbol">}</a> <a id="878" class="Symbol">(</a><a id="879" href="foundation.transfinite-cocomposition-of-maps.html#879" class="Bound">f</a> <a id="881" class="Symbol">:</a> <a id="883" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="910" href="foundation.transfinite-cocomposition-of-maps.html#867" class="Bound">l</a><a id="911" class="Symbol">)</a>
  <a id="915" class="Keyword">where</a>

  <a id="924" href="foundation.transfinite-cocomposition-of-maps.html#924" class="Function">transfinite-cocomp</a> <a id="943" class="Symbol">:</a>
    <a id="949" href="foundation.sequential-limits.html#2101" class="Function">standard-sequential-limit</a> <a id="975" href="foundation.transfinite-cocomposition-of-maps.html#879" class="Bound">f</a> <a id="977" class="Symbol">→</a> <a id="979" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="1013" href="foundation.transfinite-cocomposition-of-maps.html#879" class="Bound">f</a> <a id="1015" class="Number">0</a>
  <a id="1019" href="foundation.transfinite-cocomposition-of-maps.html#924" class="Function">transfinite-cocomp</a> <a id="1038" href="foundation.transfinite-cocomposition-of-maps.html#1038" class="Bound">x</a> <a id="1040" class="Symbol">=</a> <a id="1042" href="foundation.sequential-limits.html#2372" class="Function">sequence-standard-sequential-limit</a> <a id="1077" href="foundation.transfinite-cocomposition-of-maps.html#879" class="Bound">f</a> <a id="1079" href="foundation.transfinite-cocomposition-of-maps.html#1038" class="Bound">x</a> <a id="1081" class="Number">0</a>
</pre>
## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
