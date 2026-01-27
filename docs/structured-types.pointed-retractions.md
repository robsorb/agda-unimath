# Pointed retractions of pointed maps

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="structured-types.pointed-retractions.html" class="Module">structured-types.pointed-retractions</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.commuting-squares-of-identifications.html" class="Module">foundation.commuting-squares-of-identifications</a>
<a id="267" class="Keyword">open</a> <a id="272" class="Keyword">import</a> <a id="279" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="435" class="Keyword">open</a> <a id="440" class="Keyword">import</a> <a id="447" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>

<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="571" class="Keyword">open</a> <a id="576" class="Keyword">import</a> <a id="583" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="613" class="Keyword">open</a> <a id="618" class="Keyword">import</a> <a id="625" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

A
{{#concept "pointed retraction" Disambiguation="pointed map" Agda=pointed-retraction}}
of a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` consists of a
pointed map `g : B →∗ A` equipped with a
[pointed homotopy](structured-types.pointed-homotopies.md) `H : g ∘∗ f ~∗ id`.

## Definitions

### The predicate of being a pointed retraction of a pointed map

<pre class="Agda"><a id="1062" class="Keyword">module</a> <a id="1069" href="structured-types.pointed-retractions.html#1069" class="Module">_</a>
  <a id="1073" class="Symbol">{</a><a id="1074" href="structured-types.pointed-retractions.html#1074" class="Bound">l1</a> <a id="1077" href="structured-types.pointed-retractions.html#1077" class="Bound">l2</a> <a id="1080" class="Symbol">:</a> <a id="1082" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1087" class="Symbol">}</a> <a id="1089" class="Symbol">{</a><a id="1090" href="structured-types.pointed-retractions.html#1090" class="Bound">A</a> <a id="1092" class="Symbol">:</a> <a id="1094" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1107" href="structured-types.pointed-retractions.html#1074" class="Bound">l1</a><a id="1109" class="Symbol">}</a> <a id="1111" class="Symbol">{</a><a id="1112" href="structured-types.pointed-retractions.html#1112" class="Bound">B</a> <a id="1114" class="Symbol">:</a> <a id="1116" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1129" href="structured-types.pointed-retractions.html#1077" class="Bound">l2</a><a id="1131" class="Symbol">}</a> <a id="1133" class="Symbol">(</a><a id="1134" href="structured-types.pointed-retractions.html#1134" class="Bound">f</a> <a id="1136" class="Symbol">:</a> <a id="1138" href="structured-types.pointed-retractions.html#1090" class="Bound">A</a> <a id="1140" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1143" href="structured-types.pointed-retractions.html#1112" class="Bound">B</a><a id="1144" class="Symbol">)</a>
  <a id="1148" class="Keyword">where</a>

  <a id="1157" href="structured-types.pointed-retractions.html#1157" class="Function">is-pointed-retraction</a> <a id="1179" class="Symbol">:</a> <a id="1181" class="Symbol">(</a><a id="1182" href="structured-types.pointed-retractions.html#1112" class="Bound">B</a> <a id="1184" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1187" href="structured-types.pointed-retractions.html#1090" class="Bound">A</a><a id="1188" class="Symbol">)</a> <a id="1190" class="Symbol">→</a> <a id="1192" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1195" href="structured-types.pointed-retractions.html#1074" class="Bound">l1</a>
  <a id="1200" href="structured-types.pointed-retractions.html#1157" class="Function">is-pointed-retraction</a> <a id="1222" href="structured-types.pointed-retractions.html#1222" class="Bound">g</a> <a id="1224" class="Symbol">=</a> <a id="1226" href="structured-types.pointed-retractions.html#1222" class="Bound">g</a> <a id="1228" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="1231" href="structured-types.pointed-retractions.html#1134" class="Bound">f</a> <a id="1233" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1236" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a>
</pre>
### The type of pointed retractions of a pointed map

<pre class="Agda"><a id="1318" class="Keyword">module</a> <a id="1325" href="structured-types.pointed-retractions.html#1325" class="Module">_</a>
  <a id="1329" class="Symbol">{</a><a id="1330" href="structured-types.pointed-retractions.html#1330" class="Bound">l1</a> <a id="1333" href="structured-types.pointed-retractions.html#1333" class="Bound">l2</a> <a id="1336" class="Symbol">:</a> <a id="1338" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1343" class="Symbol">}</a> <a id="1345" class="Symbol">{</a><a id="1346" href="structured-types.pointed-retractions.html#1346" class="Bound">A</a> <a id="1348" class="Symbol">:</a> <a id="1350" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1363" href="structured-types.pointed-retractions.html#1330" class="Bound">l1</a><a id="1365" class="Symbol">}</a> <a id="1367" class="Symbol">{</a><a id="1368" href="structured-types.pointed-retractions.html#1368" class="Bound">B</a> <a id="1370" class="Symbol">:</a> <a id="1372" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1385" href="structured-types.pointed-retractions.html#1333" class="Bound">l2</a><a id="1387" class="Symbol">}</a> <a id="1389" class="Symbol">(</a><a id="1390" href="structured-types.pointed-retractions.html#1390" class="Bound">f</a> <a id="1392" class="Symbol">:</a> <a id="1394" href="structured-types.pointed-retractions.html#1346" class="Bound">A</a> <a id="1396" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1399" href="structured-types.pointed-retractions.html#1368" class="Bound">B</a><a id="1400" class="Symbol">)</a>
  <a id="1404" class="Keyword">where</a>

  <a id="1413" href="structured-types.pointed-retractions.html#1413" class="Function">pointed-retraction</a> <a id="1432" class="Symbol">:</a> <a id="1434" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1437" class="Symbol">(</a><a id="1438" href="structured-types.pointed-retractions.html#1330" class="Bound">l1</a> <a id="1441" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1443" href="structured-types.pointed-retractions.html#1333" class="Bound">l2</a><a id="1445" class="Symbol">)</a>
  <a id="1449" href="structured-types.pointed-retractions.html#1413" class="Function">pointed-retraction</a> <a id="1468" class="Symbol">=</a>
    <a id="1474" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1476" class="Symbol">(</a><a id="1477" href="structured-types.pointed-retractions.html#1368" class="Bound">B</a> <a id="1479" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1482" href="structured-types.pointed-retractions.html#1346" class="Bound">A</a><a id="1483" class="Symbol">)</a> <a id="1485" class="Symbol">(</a><a id="1486" href="structured-types.pointed-retractions.html#1157" class="Function">is-pointed-retraction</a> <a id="1508" href="structured-types.pointed-retractions.html#1390" class="Bound">f</a><a id="1509" class="Symbol">)</a>

  <a id="1514" class="Keyword">module</a> <a id="1521" href="structured-types.pointed-retractions.html#1521" class="Module">_</a>
    <a id="1527" class="Symbol">(</a><a id="1528" href="structured-types.pointed-retractions.html#1528" class="Bound">r</a> <a id="1530" class="Symbol">:</a> <a id="1532" href="structured-types.pointed-retractions.html#1413" class="Function">pointed-retraction</a><a id="1550" class="Symbol">)</a>
    <a id="1556" class="Keyword">where</a>

    <a id="1567" href="structured-types.pointed-retractions.html#1567" class="Function">pointed-map-pointed-retraction</a> <a id="1598" class="Symbol">:</a> <a id="1600" href="structured-types.pointed-retractions.html#1368" class="Bound">B</a> <a id="1602" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1605" href="structured-types.pointed-retractions.html#1346" class="Bound">A</a>
    <a id="1611" href="structured-types.pointed-retractions.html#1567" class="Function">pointed-map-pointed-retraction</a> <a id="1642" class="Symbol">=</a> <a id="1644" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1648" href="structured-types.pointed-retractions.html#1528" class="Bound">r</a>

    <a id="1655" href="structured-types.pointed-retractions.html#1655" class="Function">is-pointed-retraction-pointed-retraction</a> <a id="1696" class="Symbol">:</a>
      <a id="1704" href="structured-types.pointed-retractions.html#1157" class="Function">is-pointed-retraction</a> <a id="1726" href="structured-types.pointed-retractions.html#1390" class="Bound">f</a> <a id="1728" href="structured-types.pointed-retractions.html#1567" class="Function">pointed-map-pointed-retraction</a>
    <a id="1763" href="structured-types.pointed-retractions.html#1655" class="Function">is-pointed-retraction-pointed-retraction</a> <a id="1804" class="Symbol">=</a> <a id="1806" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1810" href="structured-types.pointed-retractions.html#1528" class="Bound">r</a>

    <a id="1817" href="structured-types.pointed-retractions.html#1817" class="Function">map-pointed-retraction</a> <a id="1840" class="Symbol">:</a> <a id="1842" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1860" href="structured-types.pointed-retractions.html#1368" class="Bound">B</a> <a id="1862" class="Symbol">→</a> <a id="1864" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1882" href="structured-types.pointed-retractions.html#1346" class="Bound">A</a>
    <a id="1888" href="structured-types.pointed-retractions.html#1817" class="Function">map-pointed-retraction</a> <a id="1911" class="Symbol">=</a> <a id="1913" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="1929" href="structured-types.pointed-retractions.html#1567" class="Function">pointed-map-pointed-retraction</a>

    <a id="1965" href="structured-types.pointed-retractions.html#1965" class="Function">preserves-point-pointed-map-pointed-retraction</a> <a id="2012" class="Symbol">:</a>
      <a id="2020" href="structured-types.pointed-retractions.html#1817" class="Function">map-pointed-retraction</a> <a id="2043" class="Symbol">(</a><a id="2044" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="2063" href="structured-types.pointed-retractions.html#1368" class="Bound">B</a><a id="2064" class="Symbol">)</a> <a id="2066" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2068" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="2087" href="structured-types.pointed-retractions.html#1346" class="Bound">A</a>
    <a id="2093" href="structured-types.pointed-retractions.html#1965" class="Function">preserves-point-pointed-map-pointed-retraction</a> <a id="2140" class="Symbol">=</a>
      <a id="2148" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="2176" href="structured-types.pointed-retractions.html#1567" class="Function">pointed-map-pointed-retraction</a>

    <a id="2212" href="structured-types.pointed-retractions.html#2212" class="Function">is-retraction-pointed-retraction</a> <a id="2245" class="Symbol">:</a>
      <a id="2253" href="foundation-core.retractions.html#790" class="Function">is-retraction</a> <a id="2267" class="Symbol">(</a><a id="2268" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2284" href="structured-types.pointed-retractions.html#1390" class="Bound">f</a><a id="2285" class="Symbol">)</a> <a id="2287" href="structured-types.pointed-retractions.html#1817" class="Function">map-pointed-retraction</a>
    <a id="2314" href="structured-types.pointed-retractions.html#2212" class="Function">is-retraction-pointed-retraction</a> <a id="2347" class="Symbol">=</a>
      <a id="2355" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="2373" href="structured-types.pointed-retractions.html#1655" class="Function">is-pointed-retraction-pointed-retraction</a>

    <a id="2419" href="structured-types.pointed-retractions.html#2419" class="Function">retraction-pointed-retraction</a> <a id="2449" class="Symbol">:</a> <a id="2451" href="foundation-core.retractions.html#874" class="Function">retraction</a> <a id="2462" class="Symbol">(</a><a id="2463" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2479" href="structured-types.pointed-retractions.html#1390" class="Bound">f</a><a id="2480" class="Symbol">)</a>
    <a id="2486" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2490" href="structured-types.pointed-retractions.html#2419" class="Function">retraction-pointed-retraction</a> <a id="2520" class="Symbol">=</a> <a id="2522" href="structured-types.pointed-retractions.html#1817" class="Function">map-pointed-retraction</a>
    <a id="2549" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2553" href="structured-types.pointed-retractions.html#2419" class="Function">retraction-pointed-retraction</a> <a id="2583" class="Symbol">=</a> <a id="2585" href="structured-types.pointed-retractions.html#2212" class="Function">is-retraction-pointed-retraction</a>

    <a id="2623" href="structured-types.pointed-retractions.html#2623" class="Function">coherence-point-is-retraction-pointed-retraction</a> <a id="2672" class="Symbol">:</a>
      <a id="2680" href="structured-types.pointed-homotopies.html#5970" class="Function">coherence-point-unpointed-htpy-pointed-Π</a>
        <a id="2729" class="Symbol">(</a> <a id="2731" href="structured-types.pointed-retractions.html#1567" class="Function">pointed-map-pointed-retraction</a> <a id="2762" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="2765" href="structured-types.pointed-retractions.html#1390" class="Bound">f</a><a id="2766" class="Symbol">)</a>
        <a id="2776" class="Symbol">(</a> <a id="2778" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a><a id="2792" class="Symbol">)</a>
        <a id="2802" class="Symbol">(</a> <a id="2804" href="structured-types.pointed-retractions.html#2212" class="Function">is-retraction-pointed-retraction</a><a id="2836" class="Symbol">)</a>
    <a id="2842" href="structured-types.pointed-retractions.html#2623" class="Function">coherence-point-is-retraction-pointed-retraction</a> <a id="2891" class="Symbol">=</a>
      <a id="2899" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="2928" href="structured-types.pointed-retractions.html#1655" class="Function">is-pointed-retraction-pointed-retraction</a>
</pre>
## Properties

### Any retraction of a pointed map preserves the base point in a unique way making the retracting homotopy pointed

Consider a [retraction](foundation-core.retractions.md) `g : B → A` of a pointed
map `f := (f₀ , f₁) : A →∗ B`. Then `g` is base point preserving.

**Proof.** Our goal is to show that `g * ＝ *`. Since `f` is pointed, we have
`f * ＝ *` and hence

```text
       (ap g f₁)⁻¹              H *
  g * -------------> g (f₀ *) -------> *.
```

In order to show that the retracting homotopy `H : g ∘ f₀ ~ id` is pointed, we
have to show that the triangle of identifications

```text
                                   H *
                         g (f₀ *) -----> *
                                \       /
  ap g f₁ ∙ ((ap g f₁)⁻¹ ∙ H *)  \     / refl
                                  \   /
                                   ∨ ∨
                                    *
```

commutes. This follows by the fact that concatenating with an inverse
identification is inverse to concatenating with the original identification, and
the right unit law of concatenation.

Note that the pointing of `g` chosen above is the unique way making the
retracting homotopy pointed, because the map `p ↦ ap g f₁ ∙ p` is an equivalence
with a contractible fiber at `H * ∙ refl`.

<pre class="Agda"><a id="4267" class="Keyword">module</a> <a id="4274" href="structured-types.pointed-retractions.html#4274" class="Module">_</a>
  <a id="4278" class="Symbol">{</a><a id="4279" href="structured-types.pointed-retractions.html#4279" class="Bound">l1</a> <a id="4282" href="structured-types.pointed-retractions.html#4282" class="Bound">l2</a> <a id="4285" class="Symbol">:</a> <a id="4287" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4292" class="Symbol">}</a> <a id="4294" class="Symbol">{</a><a id="4295" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a> <a id="4297" class="Symbol">:</a> <a id="4299" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4312" href="structured-types.pointed-retractions.html#4279" class="Bound">l1</a><a id="4314" class="Symbol">}</a> <a id="4316" class="Symbol">{</a><a id="4317" href="structured-types.pointed-retractions.html#4317" class="Bound">B</a> <a id="4319" class="Symbol">:</a> <a id="4321" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4334" href="structured-types.pointed-retractions.html#4282" class="Bound">l2</a><a id="4336" class="Symbol">}</a> <a id="4338" class="Symbol">(</a><a id="4339" href="structured-types.pointed-retractions.html#4339" class="Bound">f</a> <a id="4341" class="Symbol">:</a> <a id="4343" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a> <a id="4345" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="4348" href="structured-types.pointed-retractions.html#4317" class="Bound">B</a><a id="4349" class="Symbol">)</a>
  <a id="4353" class="Symbol">(</a><a id="4354" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a> <a id="4356" class="Symbol">:</a> <a id="4358" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="4376" href="structured-types.pointed-retractions.html#4317" class="Bound">B</a> <a id="4378" class="Symbol">→</a> <a id="4380" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="4398" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a><a id="4399" class="Symbol">)</a>
  <a id="4403" class="Symbol">(</a><a id="4404" href="structured-types.pointed-retractions.html#4404" class="Bound">H</a> <a id="4406" class="Symbol">:</a> <a id="4408" href="foundation-core.retractions.html#790" class="Function">is-retraction</a> <a id="4422" class="Symbol">(</a><a id="4423" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="4439" href="structured-types.pointed-retractions.html#4339" class="Bound">f</a><a id="4440" class="Symbol">)</a> <a id="4442" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a><a id="4443" class="Symbol">)</a>
  <a id="4447" class="Keyword">where</a>

  <a id="4456" class="Keyword">abstract</a>
    <a id="4469" href="structured-types.pointed-retractions.html#4469" class="Function">uniquely-preserves-point-is-retraction-pointed-map</a> <a id="4520" class="Symbol">:</a>
      <a id="4528" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a>
        <a id="4545" class="Symbol">(</a> <a id="4547" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="4549" class="Symbol">(</a> <a id="4551" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a> <a id="4553" class="Symbol">(</a><a id="4554" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="4573" href="structured-types.pointed-retractions.html#4317" class="Bound">B</a><a id="4574" class="Symbol">)</a> <a id="4576" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4578" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="4597" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a><a id="4598" class="Symbol">)</a>
            <a id="4612" class="Symbol">(</a> <a id="4614" href="foundation-core.commuting-squares-of-identifications.html#1275" class="Function">coherence-square-identifications</a>
              <a id="4661" class="Symbol">(</a> <a id="4663" href="structured-types.pointed-retractions.html#4404" class="Bound">H</a> <a id="4665" class="Symbol">(</a><a id="4666" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="4685" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a><a id="4686" class="Symbol">))</a>
              <a id="4703" class="Symbol">(</a> <a id="4705" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4708" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a> <a id="4710" class="Symbol">(</a><a id="4711" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="4739" href="structured-types.pointed-retractions.html#4339" class="Bound">f</a><a id="4740" class="Symbol">))</a>
              <a id="4757" class="Symbol">(</a> <a id="4759" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="4763" class="Symbol">)))</a>
    <a id="4771" href="structured-types.pointed-retractions.html#4469" class="Function">uniquely-preserves-point-is-retraction-pointed-map</a> <a id="4822" class="Symbol">=</a>
      <a id="4830" href="foundation-core.contractible-maps.html#3782" class="Function">is-contr-map-is-equiv</a>
        <a id="4860" class="Symbol">(</a> <a id="4862" href="foundation.identity-types.html#2101" class="Function">is-equiv-concat</a> <a id="4878" class="Symbol">(</a><a id="4879" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4882" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a> <a id="4884" class="Symbol">(</a><a id="4885" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="4913" href="structured-types.pointed-retractions.html#4339" class="Bound">f</a><a id="4914" class="Symbol">))</a> <a id="4917" class="Symbol">_)</a>
        <a id="4928" class="Symbol">(</a> <a id="4930" href="structured-types.pointed-retractions.html#4404" class="Bound">H</a> <a id="4932" class="Symbol">(</a><a id="4933" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="4952" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a><a id="4953" class="Symbol">)</a> <a id="4955" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a> <a id="4957" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="4961" class="Symbol">)</a>

  <a id="4966" href="structured-types.pointed-retractions.html#4966" class="Function">preserves-point-is-retraction-pointed-map</a> <a id="5008" class="Symbol">:</a>
    <a id="5014" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a> <a id="5016" class="Symbol">(</a><a id="5017" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5036" href="structured-types.pointed-retractions.html#4317" class="Bound">B</a><a id="5037" class="Symbol">)</a> <a id="5039" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="5041" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5060" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a>
  <a id="5064" href="structured-types.pointed-retractions.html#4966" class="Function">preserves-point-is-retraction-pointed-map</a> <a id="5106" class="Symbol">=</a>
    <a id="5112" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="5116" class="Symbol">(</a><a id="5117" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="5120" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a> <a id="5122" class="Symbol">(</a><a id="5123" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="5151" href="structured-types.pointed-retractions.html#4339" class="Bound">f</a><a id="5152" class="Symbol">))</a> <a id="5155" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a> <a id="5157" href="structured-types.pointed-retractions.html#4404" class="Bound">H</a> <a id="5159" class="Symbol">(</a><a id="5160" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="5179" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a><a id="5180" class="Symbol">)</a>

  <a id="5185" href="structured-types.pointed-retractions.html#5185" class="Function">pointed-map-is-retraction-pointed-map</a> <a id="5223" class="Symbol">:</a>
    <a id="5229" href="structured-types.pointed-retractions.html#4317" class="Bound">B</a> <a id="5231" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="5234" href="structured-types.pointed-retractions.html#4295" class="Bound">A</a>
  <a id="5238" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5242" href="structured-types.pointed-retractions.html#5185" class="Function">pointed-map-is-retraction-pointed-map</a> <a id="5280" class="Symbol">=</a> <a id="5282" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a>
  <a id="5286" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5290" href="structured-types.pointed-retractions.html#5185" class="Function">pointed-map-is-retraction-pointed-map</a> <a id="5328" class="Symbol">=</a>
    <a id="5334" href="structured-types.pointed-retractions.html#4966" class="Function">preserves-point-is-retraction-pointed-map</a>

  <a id="5379" href="structured-types.pointed-retractions.html#5379" class="Function">coherence-point-is-retraction-pointed-map</a> <a id="5421" class="Symbol">:</a>
    <a id="5427" href="structured-types.pointed-homotopies.html#5970" class="Function">coherence-point-unpointed-htpy-pointed-Π</a>
      <a id="5474" class="Symbol">(</a> <a id="5476" href="structured-types.pointed-retractions.html#5185" class="Function">pointed-map-is-retraction-pointed-map</a> <a id="5514" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="5517" href="structured-types.pointed-retractions.html#4339" class="Bound">f</a><a id="5518" class="Symbol">)</a>
      <a id="5526" class="Symbol">(</a> <a id="5528" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a><a id="5542" class="Symbol">)</a>
      <a id="5550" class="Symbol">(</a> <a id="5552" href="structured-types.pointed-retractions.html#4404" class="Bound">H</a><a id="5553" class="Symbol">)</a>
  <a id="5557" href="structured-types.pointed-retractions.html#5379" class="Function">coherence-point-is-retraction-pointed-map</a> <a id="5599" class="Symbol">=</a>
    <a id="5605" class="Symbol">(</a> <a id="5607" href="foundation-core.identity-types.html#10116" class="Function">is-section-inv-concat</a> <a id="5629" class="Symbol">(</a><a id="5630" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="5633" href="structured-types.pointed-retractions.html#4354" class="Bound">g</a> <a id="5635" class="Symbol">(</a><a id="5636" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="5664" href="structured-types.pointed-retractions.html#4339" class="Bound">f</a><a id="5665" class="Symbol">))</a> <a id="5668" class="Symbol">_)</a> <a id="5671" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="5677" class="Symbol">(</a> <a id="5679" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="5683" href="foundation-core.identity-types.html#8440" class="Function">right-unit</a><a id="5693" class="Symbol">)</a>

  <a id="5698" href="structured-types.pointed-retractions.html#5698" class="Function">is-pointed-retraction-is-retraction-pointed-map</a> <a id="5746" class="Symbol">:</a>
    <a id="5752" href="structured-types.pointed-retractions.html#1157" class="Function">is-pointed-retraction</a> <a id="5774" href="structured-types.pointed-retractions.html#4339" class="Bound">f</a> <a id="5776" href="structured-types.pointed-retractions.html#5185" class="Function">pointed-map-is-retraction-pointed-map</a>
  <a id="5816" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5820" href="structured-types.pointed-retractions.html#5698" class="Function">is-pointed-retraction-is-retraction-pointed-map</a> <a id="5868" class="Symbol">=</a>
    <a id="5874" href="structured-types.pointed-retractions.html#4404" class="Bound">H</a>
  <a id="5878" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5882" href="structured-types.pointed-retractions.html#5698" class="Function">is-pointed-retraction-is-retraction-pointed-map</a> <a id="5930" class="Symbol">=</a>
    <a id="5936" href="structured-types.pointed-retractions.html#5379" class="Function">coherence-point-is-retraction-pointed-map</a>
</pre>