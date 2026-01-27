# Spans of families of types

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="foundation.spans-families-of-types.html" class="Module">foundation.spans-families-of-types</a> <a id="81" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

Consider a family of types `A i` indexed by `i : I`. A
{{#concept "span" Disambiguation="family of types" Agda=span-type-family}} on
`A` consists of a type `S` equipped with a family of maps

```text
  (i : I) → S → A i.
```

The type `S` is called the
{{#concept "spanning type" Disambiguation="span of family of types" Agda=spanning-type-span-type-family}}
of the span.

## Definitions

### Spans on families of types

<pre class="Agda"><a id="760" class="Keyword">module</a> <a id="767" href="foundation.spans-families-of-types.html#767" class="Module">_</a>
  <a id="771" class="Symbol">{</a><a id="772" href="foundation.spans-families-of-types.html#772" class="Bound">l1</a> <a id="775" href="foundation.spans-families-of-types.html#775" class="Bound">l2</a> <a id="778" class="Symbol">:</a> <a id="780" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="785" class="Symbol">}</a> <a id="787" class="Symbol">(</a><a id="788" href="foundation.spans-families-of-types.html#788" class="Bound">l3</a> <a id="791" class="Symbol">:</a> <a id="793" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="798" class="Symbol">)</a> <a id="800" class="Symbol">{</a><a id="801" href="foundation.spans-families-of-types.html#801" class="Bound">I</a> <a id="803" class="Symbol">:</a> <a id="805" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="808" href="foundation.spans-families-of-types.html#772" class="Bound">l1</a><a id="810" class="Symbol">}</a> <a id="812" class="Symbol">(</a><a id="813" href="foundation.spans-families-of-types.html#813" class="Bound">A</a> <a id="815" class="Symbol">:</a> <a id="817" href="foundation.spans-families-of-types.html#801" class="Bound">I</a> <a id="819" class="Symbol">→</a> <a id="821" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="824" href="foundation.spans-families-of-types.html#775" class="Bound">l2</a><a id="826" class="Symbol">)</a>
  <a id="830" class="Keyword">where</a>

  <a id="839" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="856" class="Symbol">:</a> <a id="858" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="861" class="Symbol">(</a><a id="862" href="foundation.spans-families-of-types.html#772" class="Bound">l1</a> <a id="865" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="867" href="foundation.spans-families-of-types.html#775" class="Bound">l2</a> <a id="870" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="872" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="877" href="foundation.spans-families-of-types.html#788" class="Bound">l3</a><a id="879" class="Symbol">)</a>
  <a id="883" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="900" class="Symbol">=</a> <a id="902" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="904" class="Symbol">(</a><a id="905" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="908" href="foundation.spans-families-of-types.html#788" class="Bound">l3</a><a id="910" class="Symbol">)</a> <a id="912" class="Symbol">(λ</a> <a id="915" href="foundation.spans-families-of-types.html#915" class="Bound">S</a> <a id="917" class="Symbol">→</a> <a id="919" class="Symbol">(</a><a id="920" href="foundation.spans-families-of-types.html#920" class="Bound">i</a> <a id="922" class="Symbol">:</a> <a id="924" href="foundation.spans-families-of-types.html#801" class="Bound">I</a><a id="925" class="Symbol">)</a> <a id="927" class="Symbol">→</a> <a id="929" href="foundation.spans-families-of-types.html#915" class="Bound">S</a> <a id="931" class="Symbol">→</a> <a id="933" href="foundation.spans-families-of-types.html#813" class="Bound">A</a> <a id="935" href="foundation.spans-families-of-types.html#920" class="Bound">i</a><a id="936" class="Symbol">)</a>

<a id="939" class="Keyword">module</a> <a id="946" href="foundation.spans-families-of-types.html#946" class="Module">_</a>
  <a id="950" class="Symbol">{</a><a id="951" href="foundation.spans-families-of-types.html#951" class="Bound">l1</a> <a id="954" href="foundation.spans-families-of-types.html#954" class="Bound">l2</a> <a id="957" href="foundation.spans-families-of-types.html#957" class="Bound">l3</a> <a id="960" class="Symbol">:</a> <a id="962" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="967" class="Symbol">}</a> <a id="969" class="Symbol">{</a><a id="970" href="foundation.spans-families-of-types.html#970" class="Bound">I</a> <a id="972" class="Symbol">:</a> <a id="974" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="977" href="foundation.spans-families-of-types.html#951" class="Bound">l1</a><a id="979" class="Symbol">}</a> <a id="981" class="Symbol">{</a><a id="982" href="foundation.spans-families-of-types.html#982" class="Bound">A</a> <a id="984" class="Symbol">:</a> <a id="986" href="foundation.spans-families-of-types.html#970" class="Bound">I</a> <a id="988" class="Symbol">→</a> <a id="990" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="993" href="foundation.spans-families-of-types.html#954" class="Bound">l2</a><a id="995" class="Symbol">}</a>
  <a id="999" class="Symbol">(</a><a id="1000" href="foundation.spans-families-of-types.html#1000" class="Bound">s</a> <a id="1002" class="Symbol">:</a> <a id="1004" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="1021" href="foundation.spans-families-of-types.html#957" class="Bound">l3</a> <a id="1024" href="foundation.spans-families-of-types.html#982" class="Bound">A</a><a id="1025" class="Symbol">)</a>
  <a id="1029" class="Keyword">where</a>

  <a id="1038" href="foundation.spans-families-of-types.html#1038" class="Function">spanning-type-span-type-family</a> <a id="1069" class="Symbol">:</a> <a id="1071" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1074" href="foundation.spans-families-of-types.html#957" class="Bound">l3</a>
  <a id="1079" href="foundation.spans-families-of-types.html#1038" class="Function">spanning-type-span-type-family</a> <a id="1110" class="Symbol">=</a> <a id="1112" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1116" href="foundation.spans-families-of-types.html#1000" class="Bound">s</a>

  <a id="1121" href="foundation.spans-families-of-types.html#1121" class="Function">map-span-type-family</a> <a id="1142" class="Symbol">:</a>
    <a id="1148" class="Symbol">(</a><a id="1149" href="foundation.spans-families-of-types.html#1149" class="Bound">i</a> <a id="1151" class="Symbol">:</a> <a id="1153" href="foundation.spans-families-of-types.html#970" class="Bound">I</a><a id="1154" class="Symbol">)</a> <a id="1156" class="Symbol">→</a> <a id="1158" href="foundation.spans-families-of-types.html#1038" class="Function">spanning-type-span-type-family</a> <a id="1189" class="Symbol">→</a> <a id="1191" href="foundation.spans-families-of-types.html#982" class="Bound">A</a> <a id="1193" href="foundation.spans-families-of-types.html#1149" class="Bound">i</a>
  <a id="1197" href="foundation.spans-families-of-types.html#1121" class="Function">map-span-type-family</a> <a id="1218" class="Symbol">=</a> <a id="1220" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1224" href="foundation.spans-families-of-types.html#1000" class="Bound">s</a>
</pre>
## See also

- [(Binary) spans](foundation.spans.md)
- [Span diagrams on families of types](foundation.span-diagrams-families-of-types.md)
- [Permutations of spans of on families of types](foundation.permutations-spans-families-of-types.md)
