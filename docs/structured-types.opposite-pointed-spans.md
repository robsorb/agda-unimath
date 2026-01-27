# Opposite pointed spans

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="structured-types.opposite-pointed-spans.html" class="Module">structured-types.opposite-pointed-spans</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="structured-types.pointed-spans.html" class="Module">structured-types.pointed-spans</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

Consider a [pointed span](structured-types.pointed-spans.md) `𝒮 := (S , f , g)`
from `A` to `B`. The
{{#concept "opposite pointed span" Agda=opposite-pointed-span}} of
`𝒮 := (S , f , g)` is the pointed span `(S , g , f)` from `B` to `A`. In other
words, the opposite of a pointed span

```text
       f       g
  A <----- S -----> B
```

is the pointed span

```text
       g       f
  B <----- S -----> A.
```

## Definitions

### The opposite of a pointed span

<pre class="Agda"><a id="806" class="Keyword">module</a> <a id="813" href="structured-types.opposite-pointed-spans.html#813" class="Module">_</a>
  <a id="817" class="Symbol">{</a><a id="818" href="structured-types.opposite-pointed-spans.html#818" class="Bound">l1</a> <a id="821" href="structured-types.opposite-pointed-spans.html#821" class="Bound">l2</a> <a id="824" href="structured-types.opposite-pointed-spans.html#824" class="Bound">l3</a> <a id="827" class="Symbol">:</a> <a id="829" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="834" class="Symbol">}</a> <a id="836" class="Symbol">{</a><a id="837" href="structured-types.opposite-pointed-spans.html#837" class="Bound">A</a> <a id="839" class="Symbol">:</a> <a id="841" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="854" href="structured-types.opposite-pointed-spans.html#818" class="Bound">l1</a><a id="856" class="Symbol">}</a> <a id="858" class="Symbol">{</a><a id="859" href="structured-types.opposite-pointed-spans.html#859" class="Bound">B</a> <a id="861" class="Symbol">:</a> <a id="863" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="876" href="structured-types.opposite-pointed-spans.html#821" class="Bound">l2</a><a id="878" class="Symbol">}</a>
  <a id="882" class="Keyword">where</a>

  <a id="891" href="structured-types.opposite-pointed-spans.html#891" class="Function">opposite-pointed-span</a> <a id="913" class="Symbol">:</a>
    <a id="919" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="932" href="structured-types.opposite-pointed-spans.html#824" class="Bound">l3</a> <a id="935" href="structured-types.opposite-pointed-spans.html#837" class="Bound">A</a> <a id="937" href="structured-types.opposite-pointed-spans.html#859" class="Bound">B</a> <a id="939" class="Symbol">→</a> <a id="941" href="structured-types.pointed-spans.html#1168" class="Function">pointed-span</a> <a id="954" href="structured-types.opposite-pointed-spans.html#824" class="Bound">l3</a> <a id="957" href="structured-types.opposite-pointed-spans.html#859" class="Bound">B</a> <a id="959" href="structured-types.opposite-pointed-spans.html#837" class="Bound">A</a>
  <a id="963" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="967" class="Symbol">(</a><a id="968" href="structured-types.opposite-pointed-spans.html#891" class="Function">opposite-pointed-span</a> <a id="990" href="structured-types.opposite-pointed-spans.html#990" class="Bound">s</a><a id="991" class="Symbol">)</a> <a id="993" class="Symbol">=</a>
    <a id="999" href="structured-types.pointed-spans.html#1465" class="Function">spanning-pointed-type-pointed-span</a> <a id="1034" href="structured-types.opposite-pointed-spans.html#990" class="Bound">s</a>
  <a id="1038" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1042" class="Symbol">(</a><a id="1043" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1047" class="Symbol">(</a><a id="1048" href="structured-types.opposite-pointed-spans.html#891" class="Function">opposite-pointed-span</a> <a id="1070" href="structured-types.opposite-pointed-spans.html#1070" class="Bound">s</a><a id="1071" class="Symbol">))</a> <a id="1074" class="Symbol">=</a>
    <a id="1080" href="structured-types.pointed-spans.html#2366" class="Function">right-pointed-map-pointed-span</a> <a id="1111" href="structured-types.opposite-pointed-spans.html#1070" class="Bound">s</a>
  <a id="1115" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1119" class="Symbol">(</a><a id="1120" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1124" class="Symbol">(</a><a id="1125" href="structured-types.opposite-pointed-spans.html#891" class="Function">opposite-pointed-span</a> <a id="1147" href="structured-types.opposite-pointed-spans.html#1147" class="Bound">s</a><a id="1148" class="Symbol">))</a> <a id="1151" class="Symbol">=</a>
    <a id="1157" href="structured-types.pointed-spans.html#1852" class="Function">left-pointed-map-pointed-span</a> <a id="1187" href="structured-types.opposite-pointed-spans.html#1147" class="Bound">s</a>
</pre>
## See also

- [Transpositions of span diagrams](foundation.transposition-span-diagrams.md)
