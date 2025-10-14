# Binary globular maps

<pre class="Agda"><a id="33" class="Symbol">{-#</a> <a id="37" class="Keyword">OPTIONS</a> <a id="45" class="Pragma">--guardedness</a> <a id="59" class="Symbol">#-}</a>

<a id="64" class="Keyword">module</a> <a id="71" href="globular-types.binary-globular-maps.html" class="Module">globular-types.binary-globular-maps</a> <a id="107" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="globular-types.globular-maps.html" class="Module">globular-types.globular-maps</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

Consider three [globular types](globular-types.globular-types.md) `G`, `H`, and
`K`. A {{#concept "binary globular map" Agda=binary-globular-map}}
`f : G → H → K` consists of a binary map

```text
  f₀ : G₀ → H₀ → K₀
```

and for every `x x' : G₀`, `y y' : H₀` a binary globular map

```text
  f' : G' x x' → H' y y' → K (f x y) (f x' y')
```

on the `1`-cells of `G` and `H`.

## Definitions

### Binary globular maps

<pre class="Agda"><a id="740" class="Keyword">record</a>
  <a id="binary-globular-map"></a><a id="749" href="globular-types.binary-globular-maps.html#749" class="Record">binary-globular-map</a>
    <a id="773" class="Symbol">{</a><a id="774" href="globular-types.binary-globular-maps.html#774" class="Bound">l1</a> <a id="777" href="globular-types.binary-globular-maps.html#777" class="Bound">l2</a> <a id="780" href="globular-types.binary-globular-maps.html#780" class="Bound">l3</a> <a id="783" href="globular-types.binary-globular-maps.html#783" class="Bound">l4</a> <a id="786" href="globular-types.binary-globular-maps.html#786" class="Bound">l5</a> <a id="789" href="globular-types.binary-globular-maps.html#789" class="Bound">l6</a> <a id="792" class="Symbol">:</a> <a id="794" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="799" class="Symbol">}</a>
    <a id="805" class="Symbol">(</a><a id="806" href="globular-types.binary-globular-maps.html#806" class="Bound">G</a> <a id="808" class="Symbol">:</a> <a id="810" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="824" href="globular-types.binary-globular-maps.html#774" class="Bound">l1</a> <a id="827" href="globular-types.binary-globular-maps.html#777" class="Bound">l2</a><a id="829" class="Symbol">)</a> <a id="831" class="Symbol">(</a><a id="832" href="globular-types.binary-globular-maps.html#832" class="Bound">H</a> <a id="834" class="Symbol">:</a> <a id="836" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="850" href="globular-types.binary-globular-maps.html#780" class="Bound">l3</a> <a id="853" href="globular-types.binary-globular-maps.html#783" class="Bound">l4</a><a id="855" class="Symbol">)</a>
    <a id="861" class="Symbol">(</a><a id="862" href="globular-types.binary-globular-maps.html#862" class="Bound">K</a> <a id="864" class="Symbol">:</a> <a id="866" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="880" href="globular-types.binary-globular-maps.html#786" class="Bound">l5</a> <a id="883" href="globular-types.binary-globular-maps.html#789" class="Bound">l6</a><a id="885" class="Symbol">)</a> <a id="887" class="Symbol">:</a> <a id="889" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="892" class="Symbol">(</a><a id="893" href="globular-types.binary-globular-maps.html#774" class="Bound">l1</a> <a id="896" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="898" href="globular-types.binary-globular-maps.html#777" class="Bound">l2</a> <a id="901" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="903" href="globular-types.binary-globular-maps.html#780" class="Bound">l3</a> <a id="906" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="908" href="globular-types.binary-globular-maps.html#783" class="Bound">l4</a> <a id="911" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="913" href="globular-types.binary-globular-maps.html#786" class="Bound">l5</a> <a id="916" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="918" href="globular-types.binary-globular-maps.html#789" class="Bound">l6</a><a id="920" class="Symbol">)</a>
    <a id="926" class="Keyword">where</a>
    <a id="936" class="Keyword">coinductive</a>
    <a id="952" class="Keyword">field</a>
      <a id="binary-globular-map.0-cell-binary-globular-map"></a><a id="964" href="globular-types.binary-globular-maps.html#964" class="Field">0-cell-binary-globular-map</a> <a id="991" class="Symbol">:</a>
        <a id="1001" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1022" href="globular-types.binary-globular-maps.html#806" class="Bound">G</a> <a id="1024" class="Symbol">→</a> <a id="1026" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1047" href="globular-types.binary-globular-maps.html#832" class="Bound">H</a> <a id="1049" class="Symbol">→</a>
        <a id="1059" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1080" href="globular-types.binary-globular-maps.html#862" class="Bound">K</a>
      <a id="binary-globular-map.1-cell-binary-globular-map-binary-globular-map"></a><a id="1088" href="globular-types.binary-globular-maps.html#1088" class="Field">1-cell-binary-globular-map-binary-globular-map</a> <a id="1135" class="Symbol">:</a>
        <a id="1145" class="Symbol">{</a><a id="1146" href="globular-types.binary-globular-maps.html#1146" class="Bound">x</a> <a id="1148" href="globular-types.binary-globular-maps.html#1148" class="Bound">x&#39;</a> <a id="1151" class="Symbol">:</a> <a id="1153" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1174" href="globular-types.binary-globular-maps.html#806" class="Bound">G</a><a id="1175" class="Symbol">}</a>
        <a id="1185" class="Symbol">{</a><a id="1186" href="globular-types.binary-globular-maps.html#1186" class="Bound">y</a> <a id="1188" href="globular-types.binary-globular-maps.html#1188" class="Bound">y&#39;</a> <a id="1191" class="Symbol">:</a> <a id="1193" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1214" href="globular-types.binary-globular-maps.html#832" class="Bound">H</a><a id="1215" class="Symbol">}</a> <a id="1217" class="Symbol">→</a>
        <a id="1227" href="globular-types.binary-globular-maps.html#749" class="Record">binary-globular-map</a>
          <a id="1257" class="Symbol">(</a> <a id="1259" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1294" href="globular-types.binary-globular-maps.html#806" class="Bound">G</a> <a id="1296" href="globular-types.binary-globular-maps.html#1146" class="Bound">x</a> <a id="1298" href="globular-types.binary-globular-maps.html#1148" class="Bound">x&#39;</a><a id="1300" class="Symbol">)</a>
          <a id="1312" class="Symbol">(</a> <a id="1314" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1349" href="globular-types.binary-globular-maps.html#832" class="Bound">H</a> <a id="1351" href="globular-types.binary-globular-maps.html#1186" class="Bound">y</a> <a id="1353" href="globular-types.binary-globular-maps.html#1188" class="Bound">y&#39;</a><a id="1355" class="Symbol">)</a>
          <a id="1367" class="Symbol">(</a> <a id="1369" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1404" href="globular-types.binary-globular-maps.html#862" class="Bound">K</a>
            <a id="1418" class="Symbol">(</a> <a id="1420" href="globular-types.binary-globular-maps.html#964" class="Field">0-cell-binary-globular-map</a> <a id="1447" href="globular-types.binary-globular-maps.html#1146" class="Bound">x</a> <a id="1449" href="globular-types.binary-globular-maps.html#1186" class="Bound">y</a><a id="1450" class="Symbol">)</a>
            <a id="1464" class="Symbol">(</a> <a id="1466" href="globular-types.binary-globular-maps.html#964" class="Field">0-cell-binary-globular-map</a> <a id="1493" href="globular-types.binary-globular-maps.html#1148" class="Bound">x&#39;</a> <a id="1496" href="globular-types.binary-globular-maps.html#1188" class="Bound">y&#39;</a><a id="1498" class="Symbol">))</a>
</pre>