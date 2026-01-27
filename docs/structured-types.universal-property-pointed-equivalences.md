# The universal property of pointed equivalences

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="structured-types.universal-property-pointed-equivalences.html" class="Module">structured-types.universal-property-pointed-equivalences</a> <a id="123" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="structured-types.precomposition-pointed-maps.html" class="Module">structured-types.precomposition-pointed-maps</a>
</pre>
</details>

## Idea

Analogous to the
[universal property of equivalences](foundation.universal-property-equivalences.md),
the
{{#concept "universal property of pointed equivalences" Agda=universal-property-pointed-equiv}}
asserts about a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B`
that the
[precomposition function](structured-types.precomposition-pointed-maps.md)

```text
  - ∘∗ f : (B →∗ C) → (A →∗ C)
```

is an [equivalence](foundation.equivalences.md) for every
[pointed type](structured-types.pointed-types.md) `C`.

## Definitions

### The universal property of pointed equivalences

<pre class="Agda"><a id="1021" class="Keyword">module</a> <a id="1028" href="structured-types.universal-property-pointed-equivalences.html#1028" class="Module">_</a>
  <a id="1032" class="Symbol">{</a><a id="1033" href="structured-types.universal-property-pointed-equivalences.html#1033" class="Bound">l1</a> <a id="1036" href="structured-types.universal-property-pointed-equivalences.html#1036" class="Bound">l2</a> <a id="1039" class="Symbol">:</a> <a id="1041" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1046" class="Symbol">}</a> <a id="1048" class="Symbol">{</a><a id="1049" href="structured-types.universal-property-pointed-equivalences.html#1049" class="Bound">A</a> <a id="1051" class="Symbol">:</a> <a id="1053" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1066" href="structured-types.universal-property-pointed-equivalences.html#1033" class="Bound">l1</a><a id="1068" class="Symbol">}</a> <a id="1070" class="Symbol">{</a><a id="1071" href="structured-types.universal-property-pointed-equivalences.html#1071" class="Bound">B</a> <a id="1073" class="Symbol">:</a> <a id="1075" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1088" href="structured-types.universal-property-pointed-equivalences.html#1036" class="Bound">l2</a><a id="1090" class="Symbol">}</a> <a id="1092" class="Symbol">(</a><a id="1093" href="structured-types.universal-property-pointed-equivalences.html#1093" class="Bound">f</a> <a id="1095" class="Symbol">:</a> <a id="1097" href="structured-types.universal-property-pointed-equivalences.html#1049" class="Bound">A</a> <a id="1099" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1102" href="structured-types.universal-property-pointed-equivalences.html#1071" class="Bound">B</a><a id="1103" class="Symbol">)</a>
  <a id="1107" class="Keyword">where</a>

  <a id="1116" href="structured-types.universal-property-pointed-equivalences.html#1116" class="Function">universal-property-pointed-equiv</a> <a id="1149" class="Symbol">:</a> <a id="1151" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1157" href="structured-types.universal-property-pointed-equivalences.html#1116" class="Function">universal-property-pointed-equiv</a> <a id="1190" class="Symbol">=</a>
    <a id="1196" class="Symbol">{</a><a id="1197" href="structured-types.universal-property-pointed-equivalences.html#1197" class="Bound">l</a> <a id="1199" class="Symbol">:</a> <a id="1201" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1206" class="Symbol">}</a> <a id="1208" class="Symbol">(</a><a id="1209" href="structured-types.universal-property-pointed-equivalences.html#1209" class="Bound">C</a> <a id="1211" class="Symbol">:</a> <a id="1213" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1226" href="structured-types.universal-property-pointed-equivalences.html#1197" class="Bound">l</a><a id="1227" class="Symbol">)</a> <a id="1229" class="Symbol">→</a> <a id="1231" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1240" class="Symbol">(</a><a id="1241" href="structured-types.precomposition-pointed-maps.html#683" class="Function">precomp-pointed-map</a> <a id="1261" href="structured-types.universal-property-pointed-equivalences.html#1093" class="Bound">f</a> <a id="1263" href="structured-types.universal-property-pointed-equivalences.html#1209" class="Bound">C</a><a id="1264" class="Symbol">)</a>
</pre>