# Postcomposition of pointed maps

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="structured-types.postcomposition-pointed-maps.html" class="Module">structured-types.postcomposition-pointed-maps</a> <a id="97" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The
{{#concept "postcomposition operation" Disambiguation="pointed maps" Agda=postcomp-pointed-map}}
on [pointed maps](structured-types.pointed-maps.md) by a pointed map
`f : A →∗ B` is a family of operations

```text
  f ∘∗ - : (X →∗ A) → (X →∗ B)
```

indexed by a [pointed type](structured-types.pointed-types.md) `X`.

## Definitions

### Postcomposition by pointed maps

<pre class="Agda"><a id="postcomp-pointed-map"></a><a id="688" href="structured-types.postcomposition-pointed-maps.html#688" class="Function">postcomp-pointed-map</a> <a id="709" class="Symbol">:</a>
  <a id="713" class="Symbol">{</a><a id="714" href="structured-types.postcomposition-pointed-maps.html#714" class="Bound">l1</a> <a id="717" href="structured-types.postcomposition-pointed-maps.html#717" class="Bound">l2</a> <a id="720" href="structured-types.postcomposition-pointed-maps.html#720" class="Bound">l3</a> <a id="723" class="Symbol">:</a> <a id="725" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="730" class="Symbol">}</a> <a id="732" class="Symbol">{</a><a id="733" href="structured-types.postcomposition-pointed-maps.html#733" class="Bound">A</a> <a id="735" class="Symbol">:</a> <a id="737" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="750" href="structured-types.postcomposition-pointed-maps.html#714" class="Bound">l1</a><a id="752" class="Symbol">}</a> <a id="754" class="Symbol">{</a><a id="755" href="structured-types.postcomposition-pointed-maps.html#755" class="Bound">B</a> <a id="757" class="Symbol">:</a> <a id="759" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="772" href="structured-types.postcomposition-pointed-maps.html#717" class="Bound">l2</a><a id="774" class="Symbol">}</a> <a id="776" class="Symbol">(</a><a id="777" href="structured-types.postcomposition-pointed-maps.html#777" class="Bound">f</a> <a id="779" class="Symbol">:</a> <a id="781" href="structured-types.postcomposition-pointed-maps.html#733" class="Bound">A</a> <a id="783" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="786" href="structured-types.postcomposition-pointed-maps.html#755" class="Bound">B</a><a id="787" class="Symbol">)</a>
  <a id="791" class="Symbol">(</a><a id="792" href="structured-types.postcomposition-pointed-maps.html#792" class="Bound">X</a> <a id="794" class="Symbol">:</a> <a id="796" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="809" href="structured-types.postcomposition-pointed-maps.html#720" class="Bound">l3</a><a id="811" class="Symbol">)</a> <a id="813" class="Symbol">→</a> <a id="815" class="Symbol">(</a><a id="816" href="structured-types.postcomposition-pointed-maps.html#792" class="Bound">X</a> <a id="818" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="821" href="structured-types.postcomposition-pointed-maps.html#733" class="Bound">A</a><a id="822" class="Symbol">)</a> <a id="824" class="Symbol">→</a> <a id="826" class="Symbol">(</a><a id="827" href="structured-types.postcomposition-pointed-maps.html#792" class="Bound">X</a> <a id="829" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="832" href="structured-types.postcomposition-pointed-maps.html#755" class="Bound">B</a><a id="833" class="Symbol">)</a>
<a id="835" href="structured-types.postcomposition-pointed-maps.html#688" class="Function">postcomp-pointed-map</a> <a id="856" href="structured-types.postcomposition-pointed-maps.html#856" class="Bound">f</a> <a id="858" href="structured-types.postcomposition-pointed-maps.html#858" class="Bound">X</a> <a id="860" href="structured-types.postcomposition-pointed-maps.html#860" class="Bound">g</a> <a id="862" class="Symbol">=</a> <a id="864" href="structured-types.pointed-maps.html#3226" class="Function">comp-pointed-map</a> <a id="881" href="structured-types.postcomposition-pointed-maps.html#856" class="Bound">f</a> <a id="883" href="structured-types.postcomposition-pointed-maps.html#860" class="Bound">g</a>
</pre>