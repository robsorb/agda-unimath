# Precomposition of pointed maps

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="structured-types.precomposition-pointed-maps.html" class="Module">structured-types.precomposition-pointed-maps</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The
{{#concept "precomposition operation" Disambiguation="pointed maps" Agda=precomp-pointed-map}}
on [pointed maps](structured-types.pointed-maps.md) by a pointed map
`f : A →∗ B` is a family of operations

```text
  - ∘∗ f : (B →∗ C) → (A →∗ C)
```

indexed by a [pointed type](structured-types.pointed-types.md) `C`.

## Definitions

### Precomposition by pointed maps

<pre class="Agda"><a id="precomp-pointed-map"></a><a id="683" href="structured-types.precomposition-pointed-maps.html#683" class="Function">precomp-pointed-map</a> <a id="703" class="Symbol">:</a>
  <a id="707" class="Symbol">{</a><a id="708" href="structured-types.precomposition-pointed-maps.html#708" class="Bound">l1</a> <a id="711" href="structured-types.precomposition-pointed-maps.html#711" class="Bound">l2</a> <a id="714" href="structured-types.precomposition-pointed-maps.html#714" class="Bound">l3</a> <a id="717" class="Symbol">:</a> <a id="719" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="724" class="Symbol">}</a> <a id="726" class="Symbol">{</a><a id="727" href="structured-types.precomposition-pointed-maps.html#727" class="Bound">A</a> <a id="729" class="Symbol">:</a> <a id="731" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="744" href="structured-types.precomposition-pointed-maps.html#708" class="Bound">l1</a><a id="746" class="Symbol">}</a> <a id="748" class="Symbol">{</a><a id="749" href="structured-types.precomposition-pointed-maps.html#749" class="Bound">B</a> <a id="751" class="Symbol">:</a> <a id="753" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="766" href="structured-types.precomposition-pointed-maps.html#711" class="Bound">l2</a><a id="768" class="Symbol">}</a> <a id="770" class="Symbol">(</a><a id="771" href="structured-types.precomposition-pointed-maps.html#771" class="Bound">f</a> <a id="773" class="Symbol">:</a> <a id="775" href="structured-types.precomposition-pointed-maps.html#727" class="Bound">A</a> <a id="777" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="780" href="structured-types.precomposition-pointed-maps.html#749" class="Bound">B</a><a id="781" class="Symbol">)</a>
  <a id="785" class="Symbol">(</a><a id="786" href="structured-types.precomposition-pointed-maps.html#786" class="Bound">C</a> <a id="788" class="Symbol">:</a> <a id="790" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="803" href="structured-types.precomposition-pointed-maps.html#714" class="Bound">l3</a><a id="805" class="Symbol">)</a> <a id="807" class="Symbol">→</a> <a id="809" class="Symbol">(</a><a id="810" href="structured-types.precomposition-pointed-maps.html#749" class="Bound">B</a> <a id="812" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="815" href="structured-types.precomposition-pointed-maps.html#786" class="Bound">C</a><a id="816" class="Symbol">)</a> <a id="818" class="Symbol">→</a> <a id="820" class="Symbol">(</a><a id="821" href="structured-types.precomposition-pointed-maps.html#727" class="Bound">A</a> <a id="823" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="826" href="structured-types.precomposition-pointed-maps.html#786" class="Bound">C</a><a id="827" class="Symbol">)</a>
<a id="829" href="structured-types.precomposition-pointed-maps.html#683" class="Function">precomp-pointed-map</a> <a id="849" href="structured-types.precomposition-pointed-maps.html#849" class="Bound">f</a> <a id="851" href="structured-types.precomposition-pointed-maps.html#851" class="Bound">C</a> <a id="853" href="structured-types.precomposition-pointed-maps.html#853" class="Bound">g</a> <a id="855" class="Symbol">=</a> <a id="857" href="structured-types.pointed-maps.html#3226" class="Function">comp-pointed-map</a> <a id="874" href="structured-types.precomposition-pointed-maps.html#853" class="Bound">g</a> <a id="876" href="structured-types.precomposition-pointed-maps.html#849" class="Bound">f</a>
</pre>