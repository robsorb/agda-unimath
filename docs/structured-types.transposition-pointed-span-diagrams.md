# Transposition of pointed span diagrams

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="structured-types.transposition-pointed-span-diagrams.html" class="Module">structured-types.transposition-pointed-span-diagrams</a> <a id="111" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="structured-types.opposite-pointed-spans.html" class="Module">structured-types.opposite-pointed-spans</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="structured-types.pointed-span-diagrams.html" class="Module">structured-types.pointed-span-diagrams</a>
</pre>
</details>

## Idea

The
{{#concept "transposition" Disambiguation="pointed span diagram" Agda=transposition-pointed-span-diagram}}
of a [pointed span diagram](structured-types.pointed-span-diagrams.md)

```text
       f       g
  A <----- S -----> B
```

is the pointed span diagram

```text
       g       f
  B <----- S -----> A.
```

In other words, the transposition of a pointed span diagram `(A , B , s)` is the
pointed span diagram `(B , A , opposite-pointed-span s)` where
`opposite-pointed-span s` is the
[opposite](structured-types.opposite-pointed-spans.md) of the
[pointed span](structured-types.pointed-spans.md) `s` from `A` to `B`.

## Definitions

### Transposition of pointed span diagrams

<pre class="Agda"><a id="1076" class="Keyword">module</a> <a id="1083" href="structured-types.transposition-pointed-span-diagrams.html#1083" class="Module">_</a>
  <a id="1087" class="Symbol">{</a><a id="1088" href="structured-types.transposition-pointed-span-diagrams.html#1088" class="Bound">l1</a> <a id="1091" href="structured-types.transposition-pointed-span-diagrams.html#1091" class="Bound">l2</a> <a id="1094" href="structured-types.transposition-pointed-span-diagrams.html#1094" class="Bound">l3</a> <a id="1097" class="Symbol">:</a> <a id="1099" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1104" class="Symbol">}</a> <a id="1106" class="Symbol">(</a><a id="1107" href="structured-types.transposition-pointed-span-diagrams.html#1107" class="Bound">𝒮</a> <a id="1109" class="Symbol">:</a> <a id="1111" href="structured-types.pointed-span-diagrams.html#955" class="Function">pointed-span-diagram</a> <a id="1132" href="structured-types.transposition-pointed-span-diagrams.html#1088" class="Bound">l1</a> <a id="1135" href="structured-types.transposition-pointed-span-diagrams.html#1091" class="Bound">l2</a> <a id="1138" href="structured-types.transposition-pointed-span-diagrams.html#1094" class="Bound">l3</a><a id="1140" class="Symbol">)</a>
  <a id="1144" class="Keyword">where</a>

  <a id="1153" href="structured-types.transposition-pointed-span-diagrams.html#1153" class="Function">transposition-pointed-span-diagram</a> <a id="1188" class="Symbol">:</a> <a id="1190" href="structured-types.pointed-span-diagrams.html#955" class="Function">pointed-span-diagram</a> <a id="1211" href="structured-types.transposition-pointed-span-diagrams.html#1091" class="Bound">l2</a> <a id="1214" href="structured-types.transposition-pointed-span-diagrams.html#1088" class="Bound">l1</a> <a id="1217" href="structured-types.transposition-pointed-span-diagrams.html#1094" class="Bound">l3</a>
  <a id="1222" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1226" href="structured-types.transposition-pointed-span-diagrams.html#1153" class="Function">transposition-pointed-span-diagram</a> <a id="1261" class="Symbol">=</a>
    <a id="1267" href="structured-types.pointed-span-diagrams.html#1868" class="Function">pointed-codomain-pointed-span-diagram</a> <a id="1305" href="structured-types.transposition-pointed-span-diagrams.html#1107" class="Bound">𝒮</a>
  <a id="1309" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1313" class="Symbol">(</a><a id="1314" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1318" href="structured-types.transposition-pointed-span-diagrams.html#1153" class="Function">transposition-pointed-span-diagram</a><a id="1352" class="Symbol">)</a> <a id="1354" class="Symbol">=</a>
    <a id="1360" href="structured-types.pointed-span-diagrams.html#1468" class="Function">pointed-domain-pointed-span-diagram</a> <a id="1396" href="structured-types.transposition-pointed-span-diagrams.html#1107" class="Bound">𝒮</a>
  <a id="1400" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1404" class="Symbol">(</a><a id="1405" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1409" href="structured-types.transposition-pointed-span-diagrams.html#1153" class="Function">transposition-pointed-span-diagram</a><a id="1443" class="Symbol">)</a> <a id="1445" class="Symbol">=</a>
    <a id="1451" href="structured-types.opposite-pointed-spans.html#891" class="Function">opposite-pointed-span</a> <a id="1473" class="Symbol">(</a><a id="1474" href="structured-types.pointed-span-diagrams.html#2292" class="Function">pointed-span-pointed-span-diagram</a> <a id="1508" href="structured-types.transposition-pointed-span-diagrams.html#1107" class="Bound">𝒮</a><a id="1509" class="Symbol">)</a>
</pre>