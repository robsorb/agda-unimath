# Opposite spans

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="foundation.opposite-spans.html" class="Module">foundation.opposite-spans</a> <a id="60" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="116" class="Keyword">open</a> <a id="121" class="Keyword">import</a> <a id="128" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Consider a [span](foundation.spans.md) `(S , f , g)` from `A` to `B`. The
{{#concept "opposite span" Agda=opposite-span}} of `(S , f , g)` is the span
`(S , g , f)` from `B` to `A`. In other words, the opposite of a span

```text
       f       g
  A <----- S -----> B
```

is the span

```text
       g       f
  B <----- S -----> A.
```

Recall that [binary type duality](foundation.binary-type-duality.md) shows that
spans are equivalent to [binary relations](foundation.binary-relations.md) from
`A` to `B`. The opposite of a span corresponds to the opposite of a binary
relation.

## Definitions

### The opposite of a span

<pre class="Agda"><a id="892" class="Keyword">module</a> <a id="899" href="foundation.opposite-spans.html#899" class="Module">_</a>
  <a id="903" class="Symbol">{</a><a id="904" href="foundation.opposite-spans.html#904" class="Bound">l1</a> <a id="907" href="foundation.opposite-spans.html#907" class="Bound">l2</a> <a id="910" href="foundation.opposite-spans.html#910" class="Bound">l3</a> <a id="913" class="Symbol">:</a> <a id="915" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="920" class="Symbol">}</a> <a id="922" class="Symbol">{</a><a id="923" href="foundation.opposite-spans.html#923" class="Bound">A</a> <a id="925" class="Symbol">:</a> <a id="927" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="930" href="foundation.opposite-spans.html#904" class="Bound">l1</a><a id="932" class="Symbol">}</a> <a id="934" class="Symbol">{</a><a id="935" href="foundation.opposite-spans.html#935" class="Bound">B</a> <a id="937" class="Symbol">:</a> <a id="939" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="942" href="foundation.opposite-spans.html#907" class="Bound">l2</a><a id="944" class="Symbol">}</a>
  <a id="948" class="Keyword">where</a>

  <a id="957" href="foundation.opposite-spans.html#957" class="Function">opposite-span</a> <a id="971" class="Symbol">:</a> <a id="973" href="foundation.spans.html#1830" class="Function">span</a> <a id="978" href="foundation.opposite-spans.html#910" class="Bound">l3</a> <a id="981" href="foundation.opposite-spans.html#923" class="Bound">A</a> <a id="983" href="foundation.opposite-spans.html#935" class="Bound">B</a> <a id="985" class="Symbol">→</a> <a id="987" href="foundation.spans.html#1830" class="Function">span</a> <a id="992" href="foundation.opposite-spans.html#910" class="Bound">l3</a> <a id="995" href="foundation.opposite-spans.html#935" class="Bound">B</a> <a id="997" href="foundation.opposite-spans.html#923" class="Bound">A</a>
  <a id="1001" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1005" class="Symbol">(</a><a id="1006" href="foundation.opposite-spans.html#957" class="Function">opposite-span</a> <a id="1020" href="foundation.opposite-spans.html#1020" class="Bound">s</a><a id="1021" class="Symbol">)</a> <a id="1023" class="Symbol">=</a> <a id="1025" href="foundation.spans.html#2049" class="Function">spanning-type-span</a> <a id="1044" href="foundation.opposite-spans.html#1020" class="Bound">s</a>
  <a id="1048" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1052" class="Symbol">(</a><a id="1053" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1057" class="Symbol">(</a><a id="1058" href="foundation.opposite-spans.html#957" class="Function">opposite-span</a> <a id="1072" href="foundation.opposite-spans.html#1072" class="Bound">s</a><a id="1073" class="Symbol">))</a> <a id="1076" class="Symbol">=</a> <a id="1078" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="1093" href="foundation.opposite-spans.html#1072" class="Bound">s</a>
  <a id="1097" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1101" class="Symbol">(</a><a id="1102" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1106" class="Symbol">(</a><a id="1107" href="foundation.opposite-spans.html#957" class="Function">opposite-span</a> <a id="1121" href="foundation.opposite-spans.html#1121" class="Bound">s</a><a id="1122" class="Symbol">))</a> <a id="1125" class="Symbol">=</a> <a id="1127" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="1141" href="foundation.opposite-spans.html#1121" class="Bound">s</a>
</pre>
## See also

- [Transpositions of span diagrams](foundation.transposition-span-diagrams.md)
