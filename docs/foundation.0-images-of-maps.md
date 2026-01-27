# `0`-Images of maps

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="foundation.0-images-of-maps.html" class="Module">foundation.0-images-of-maps</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="foundation.truncation-images-of-maps.html" class="Module">foundation.truncation-images-of-maps</a>
<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

## Idea

The {{#concept "0-image" Disambiguation="of a map of types" Agda=0-im}} of a map
`f : A → B` is the type

```text
  0-im f := Σ (b : B), type-trunc-Set (fiber f b).
```

The map `A → 0-im f` is 0-[connected](foundation.connected-maps.md) and the map
`0-im f → B` is 0-[truncated](foundation.truncated-maps.md).

## Definition

<pre class="Agda"><a id="618" class="Keyword">module</a> <a id="625" href="foundation.0-images-of-maps.html#625" class="Module">_</a>
  <a id="629" class="Symbol">{</a><a id="630" href="foundation.0-images-of-maps.html#630" class="Bound">l1</a> <a id="633" href="foundation.0-images-of-maps.html#633" class="Bound">l2</a> <a id="636" class="Symbol">:</a> <a id="638" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="643" class="Symbol">}</a> <a id="645" class="Symbol">{</a><a id="646" href="foundation.0-images-of-maps.html#646" class="Bound">A</a> <a id="648" class="Symbol">:</a> <a id="650" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="653" href="foundation.0-images-of-maps.html#630" class="Bound">l1</a><a id="655" class="Symbol">}</a> <a id="657" class="Symbol">{</a><a id="658" href="foundation.0-images-of-maps.html#658" class="Bound">B</a> <a id="660" class="Symbol">:</a> <a id="662" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="665" href="foundation.0-images-of-maps.html#633" class="Bound">l2</a><a id="667" class="Symbol">}</a> <a id="669" class="Symbol">(</a><a id="670" href="foundation.0-images-of-maps.html#670" class="Bound">f</a> <a id="672" class="Symbol">:</a> <a id="674" href="foundation.0-images-of-maps.html#646" class="Bound">A</a> <a id="676" class="Symbol">→</a> <a id="678" href="foundation.0-images-of-maps.html#658" class="Bound">B</a><a id="679" class="Symbol">)</a>
  <a id="683" class="Keyword">where</a>

  <a id="692" href="foundation.0-images-of-maps.html#692" class="Function">0-im</a> <a id="697" class="Symbol">:</a> <a id="699" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="702" class="Symbol">(</a><a id="703" href="foundation.0-images-of-maps.html#630" class="Bound">l1</a> <a id="706" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="708" href="foundation.0-images-of-maps.html#633" class="Bound">l2</a><a id="710" class="Symbol">)</a>
  <a id="714" href="foundation.0-images-of-maps.html#692" class="Function">0-im</a> <a id="719" class="Symbol">=</a> <a id="721" href="foundation.truncation-images-of-maps.html#1160" class="Function">trunc-im</a> <a id="730" href="foundation-core.truncation-levels.html#672" class="Function">zero-𝕋</a> <a id="737" href="foundation.0-images-of-maps.html#670" class="Bound">f</a>

  <a id="742" href="foundation.0-images-of-maps.html#742" class="Function">unit-0-im</a> <a id="752" class="Symbol">:</a> <a id="754" href="foundation.0-images-of-maps.html#646" class="Bound">A</a> <a id="756" class="Symbol">→</a> <a id="758" href="foundation.0-images-of-maps.html#692" class="Function">0-im</a>
  <a id="765" href="foundation.0-images-of-maps.html#742" class="Function">unit-0-im</a> <a id="775" class="Symbol">=</a> <a id="777" href="foundation.truncation-images-of-maps.html#1237" class="Function">unit-trunc-im</a> <a id="791" href="foundation-core.truncation-levels.html#672" class="Function">zero-𝕋</a> <a id="798" href="foundation.0-images-of-maps.html#670" class="Bound">f</a>

  <a id="803" href="foundation.0-images-of-maps.html#803" class="Function">projection-0-im</a> <a id="819" class="Symbol">:</a> <a id="821" href="foundation.0-images-of-maps.html#692" class="Function">0-im</a> <a id="826" class="Symbol">→</a> <a id="828" href="foundation.0-images-of-maps.html#658" class="Bound">B</a>
  <a id="832" href="foundation.0-images-of-maps.html#803" class="Function">projection-0-im</a> <a id="848" class="Symbol">=</a> <a id="850" href="foundation.truncation-images-of-maps.html#1350" class="Function">projection-trunc-im</a> <a id="870" href="foundation-core.truncation-levels.html#672" class="Function">zero-𝕋</a> <a id="877" href="foundation.0-images-of-maps.html#670" class="Bound">f</a>
</pre>
## Properties

### Characterization of the identity type of `0-im f`

<pre class="Agda"><a id="962" class="Keyword">module</a> <a id="969" href="foundation.0-images-of-maps.html#969" class="Module">_</a>
  <a id="973" class="Symbol">{</a><a id="974" href="foundation.0-images-of-maps.html#974" class="Bound">l1</a> <a id="977" href="foundation.0-images-of-maps.html#977" class="Bound">l2</a> <a id="980" class="Symbol">:</a> <a id="982" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="987" class="Symbol">}</a> <a id="989" class="Symbol">{</a><a id="990" href="foundation.0-images-of-maps.html#990" class="Bound">A</a> <a id="992" class="Symbol">:</a> <a id="994" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="997" href="foundation.0-images-of-maps.html#974" class="Bound">l1</a><a id="999" class="Symbol">}</a> <a id="1001" class="Symbol">{</a><a id="1002" href="foundation.0-images-of-maps.html#1002" class="Bound">B</a> <a id="1004" class="Symbol">:</a> <a id="1006" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1009" href="foundation.0-images-of-maps.html#977" class="Bound">l2</a><a id="1011" class="Symbol">}</a> <a id="1013" class="Symbol">(</a><a id="1014" href="foundation.0-images-of-maps.html#1014" class="Bound">f</a> <a id="1016" class="Symbol">:</a> <a id="1018" href="foundation.0-images-of-maps.html#990" class="Bound">A</a> <a id="1020" class="Symbol">→</a> <a id="1022" href="foundation.0-images-of-maps.html#1002" class="Bound">B</a><a id="1023" class="Symbol">)</a>
  <a id="1027" class="Keyword">where</a>

  <a id="1036" href="foundation.0-images-of-maps.html#1036" class="Function">Eq-unit-0-im</a> <a id="1049" class="Symbol">:</a> <a id="1051" href="foundation.0-images-of-maps.html#990" class="Bound">A</a> <a id="1053" class="Symbol">→</a> <a id="1055" href="foundation.0-images-of-maps.html#990" class="Bound">A</a> <a id="1057" class="Symbol">→</a> <a id="1059" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1062" class="Symbol">(</a><a id="1063" href="foundation.0-images-of-maps.html#974" class="Bound">l1</a> <a id="1066" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1068" href="foundation.0-images-of-maps.html#977" class="Bound">l2</a><a id="1070" class="Symbol">)</a>
  <a id="1074" href="foundation.0-images-of-maps.html#1036" class="Function">Eq-unit-0-im</a> <a id="1087" class="Symbol">=</a> <a id="1089" href="foundation.truncation-images-of-maps.html#1594" class="Function">Eq-unit-trunc-im</a> <a id="1106" href="foundation-core.truncation-levels.html#628" class="Function">neg-one-𝕋</a> <a id="1116" href="foundation.0-images-of-maps.html#1014" class="Bound">f</a>
</pre>