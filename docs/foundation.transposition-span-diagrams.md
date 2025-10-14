# Transposition of span diagrams

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="foundation.transposition-span-diagrams.html" class="Module">foundation.transposition-span-diagrams</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.opposite-spans.html" class="Module">foundation.opposite-spans</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The
{{#concept "transposition" Disambiguation="span diagram" Agda=transposition-span-diagram}}
of a [span diagram](foundation.span-diagrams.md)

```text
       f       g
  A <----- S -----> B
```

is the span diagram

```text
       g       f
  B <----- S -----> A.
```

In other words, the transposition of a span diagram `(A , B , s)` is the span
diagram `(B , A , opposite-span s)` where `opposite-span s` is the
[opposite](foundation.opposite-spans.md) of the [span](foundation.spans.md) `s`
from `A` to `B`.

## Definitions

### Transposition of span diagrams

<pre class="Agda"><a id="932" class="Keyword">module</a> <a id="939" href="foundation.transposition-span-diagrams.html#939" class="Module">_</a>
  <a id="943" class="Symbol">{</a><a id="944" href="foundation.transposition-span-diagrams.html#944" class="Bound">l1</a> <a id="947" href="foundation.transposition-span-diagrams.html#947" class="Bound">l2</a> <a id="950" href="foundation.transposition-span-diagrams.html#950" class="Bound">l3</a> <a id="953" class="Symbol">:</a> <a id="955" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="960" class="Symbol">}</a> <a id="962" class="Symbol">(</a><a id="963" href="foundation.transposition-span-diagrams.html#963" class="Bound">𝒮</a> <a id="965" class="Symbol">:</a> <a id="967" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="980" href="foundation.transposition-span-diagrams.html#944" class="Bound">l1</a> <a id="983" href="foundation.transposition-span-diagrams.html#947" class="Bound">l2</a> <a id="986" href="foundation.transposition-span-diagrams.html#950" class="Bound">l3</a><a id="988" class="Symbol">)</a>
  <a id="992" class="Keyword">where</a>

  <a id="1001" href="foundation.transposition-span-diagrams.html#1001" class="Function">transposition-span-diagram</a> <a id="1028" class="Symbol">:</a> <a id="1030" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1043" href="foundation.transposition-span-diagrams.html#947" class="Bound">l2</a> <a id="1046" href="foundation.transposition-span-diagrams.html#944" class="Bound">l1</a> <a id="1049" href="foundation.transposition-span-diagrams.html#950" class="Bound">l3</a>
  <a id="1054" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1058" href="foundation.transposition-span-diagrams.html#1001" class="Function">transposition-span-diagram</a> <a id="1085" class="Symbol">=</a> <a id="1087" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="1109" href="foundation.transposition-span-diagrams.html#963" class="Bound">𝒮</a>
  <a id="1113" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1117" class="Symbol">(</a><a id="1118" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1122" href="foundation.transposition-span-diagrams.html#1001" class="Function">transposition-span-diagram</a><a id="1148" class="Symbol">)</a> <a id="1150" class="Symbol">=</a> <a id="1152" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="1172" href="foundation.transposition-span-diagrams.html#963" class="Bound">𝒮</a>
  <a id="1176" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1180" class="Symbol">(</a><a id="1181" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1185" href="foundation.transposition-span-diagrams.html#1001" class="Function">transposition-span-diagram</a><a id="1211" class="Symbol">)</a> <a id="1213" class="Symbol">=</a> <a id="1215" href="foundation.opposite-spans.html#957" class="Function">opposite-span</a> <a id="1229" class="Symbol">(</a><a id="1230" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="1248" href="foundation.transposition-span-diagrams.html#963" class="Bound">𝒮</a><a id="1249" class="Symbol">)</a>
</pre>