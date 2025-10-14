# Top elements in preorders

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="order-theory.top-elements-preorders.html" class="Module">order-theory.top-elements-preorders</a> <a id="81" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
</pre>
</details>

## Idea

A
{{#concept "largest element" Disambiguation="in a preorder" WD="maximal and minimal elements" WDID=Q1475294 Agda=is-top-element-Preorder}}
in a [preorder](order-theory.preorders.md) `P` is an element `t` such that
`x ≤ t` holds for every `x : P`.

## Definition

<pre class="Agda"><a id="591" class="Keyword">module</a> <a id="598" href="order-theory.top-elements-preorders.html#598" class="Module">_</a>
  <a id="602" class="Symbol">{</a><a id="603" href="order-theory.top-elements-preorders.html#603" class="Bound">l1</a> <a id="606" href="order-theory.top-elements-preorders.html#606" class="Bound">l2</a> <a id="609" class="Symbol">:</a> <a id="611" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="616" class="Symbol">}</a> <a id="618" class="Symbol">(</a><a id="619" href="order-theory.top-elements-preorders.html#619" class="Bound">X</a> <a id="621" class="Symbol">:</a> <a id="623" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="632" href="order-theory.top-elements-preorders.html#603" class="Bound">l1</a> <a id="635" href="order-theory.top-elements-preorders.html#606" class="Bound">l2</a><a id="637" class="Symbol">)</a>
  <a id="641" class="Keyword">where</a>

  <a id="650" href="order-theory.top-elements-preorders.html#650" class="Function">is-top-element-prop-Preorder</a> <a id="679" class="Symbol">:</a> <a id="681" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="695" href="order-theory.top-elements-preorders.html#619" class="Bound">X</a> <a id="697" class="Symbol">→</a> <a id="699" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="704" class="Symbol">(</a><a id="705" href="order-theory.top-elements-preorders.html#603" class="Bound">l1</a> <a id="708" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="710" href="order-theory.top-elements-preorders.html#606" class="Bound">l2</a><a id="712" class="Symbol">)</a>
  <a id="716" href="order-theory.top-elements-preorders.html#650" class="Function">is-top-element-prop-Preorder</a> <a id="745" href="order-theory.top-elements-preorders.html#745" class="Bound">x</a> <a id="747" class="Symbol">=</a>
    <a id="753" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="760" class="Symbol">(</a><a id="761" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="775" href="order-theory.top-elements-preorders.html#619" class="Bound">X</a><a id="776" class="Symbol">)</a> <a id="778" class="Symbol">(λ</a> <a id="781" href="order-theory.top-elements-preorders.html#781" class="Bound">y</a> <a id="783" class="Symbol">→</a> <a id="785" href="order-theory.preorders.html#1322" class="Function">leq-prop-Preorder</a> <a id="803" href="order-theory.top-elements-preorders.html#619" class="Bound">X</a> <a id="805" href="order-theory.top-elements-preorders.html#781" class="Bound">y</a> <a id="807" href="order-theory.top-elements-preorders.html#745" class="Bound">x</a><a id="808" class="Symbol">)</a>

  <a id="813" href="order-theory.top-elements-preorders.html#813" class="Function">is-top-element-Preorder</a> <a id="837" class="Symbol">:</a> <a id="839" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="853" href="order-theory.top-elements-preorders.html#619" class="Bound">X</a> <a id="855" class="Symbol">→</a> <a id="857" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="860" class="Symbol">(</a><a id="861" href="order-theory.top-elements-preorders.html#603" class="Bound">l1</a> <a id="864" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="866" href="order-theory.top-elements-preorders.html#606" class="Bound">l2</a><a id="868" class="Symbol">)</a>
  <a id="872" href="order-theory.top-elements-preorders.html#813" class="Function">is-top-element-Preorder</a> <a id="896" href="order-theory.top-elements-preorders.html#896" class="Bound">x</a> <a id="898" class="Symbol">=</a> <a id="900" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="910" class="Symbol">(</a><a id="911" href="order-theory.top-elements-preorders.html#650" class="Function">is-top-element-prop-Preorder</a> <a id="940" href="order-theory.top-elements-preorders.html#896" class="Bound">x</a><a id="941" class="Symbol">)</a>

  <a id="946" href="order-theory.top-elements-preorders.html#946" class="Function">is-prop-is-top-element-Preorder</a> <a id="978" class="Symbol">:</a>
    <a id="984" class="Symbol">(</a><a id="985" href="order-theory.top-elements-preorders.html#985" class="Bound">x</a> <a id="987" class="Symbol">:</a> <a id="989" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1003" href="order-theory.top-elements-preorders.html#619" class="Bound">X</a><a id="1004" class="Symbol">)</a> <a id="1006" class="Symbol">→</a> <a id="1008" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1016" class="Symbol">(</a><a id="1017" href="order-theory.top-elements-preorders.html#813" class="Function">is-top-element-Preorder</a> <a id="1041" href="order-theory.top-elements-preorders.html#985" class="Bound">x</a><a id="1042" class="Symbol">)</a>
  <a id="1046" href="order-theory.top-elements-preorders.html#946" class="Function">is-prop-is-top-element-Preorder</a> <a id="1078" href="order-theory.top-elements-preorders.html#1078" class="Bound">x</a> <a id="1080" class="Symbol">=</a>
    <a id="1086" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1104" class="Symbol">(</a><a id="1105" href="order-theory.top-elements-preorders.html#650" class="Function">is-top-element-prop-Preorder</a> <a id="1134" href="order-theory.top-elements-preorders.html#1078" class="Bound">x</a><a id="1135" class="Symbol">)</a>

  <a id="1140" href="order-theory.top-elements-preorders.html#1140" class="Function">has-top-element-Preorder</a> <a id="1165" class="Symbol">:</a> <a id="1167" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1170" class="Symbol">(</a><a id="1171" href="order-theory.top-elements-preorders.html#603" class="Bound">l1</a> <a id="1174" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1176" href="order-theory.top-elements-preorders.html#606" class="Bound">l2</a><a id="1178" class="Symbol">)</a>
  <a id="1182" href="order-theory.top-elements-preorders.html#1140" class="Function">has-top-element-Preorder</a> <a id="1207" class="Symbol">=</a> <a id="1209" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1211" class="Symbol">(</a><a id="1212" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1226" href="order-theory.top-elements-preorders.html#619" class="Bound">X</a><a id="1227" class="Symbol">)</a> <a id="1229" href="order-theory.top-elements-preorders.html#813" class="Function">is-top-element-Preorder</a>
</pre>
## External links

- [Maximal and minimal elements](https://en.wikipedia.org/wiki/Maximal_and_minimal_elements)
  at Wikipedia
- [maximal element](https://ncatlab.org/nlab/show/maximal+element) at $n$Lab
