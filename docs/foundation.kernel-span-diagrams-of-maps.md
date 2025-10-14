# Kernel span diagrams of maps

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation.kernel-span-diagrams-of-maps.html" class="Module">foundation.kernel-span-diagrams-of-maps</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

Consider a map `f : A → B`. The
{{#concept "kernel span diagram" Disambiguation="map" Agda=kernel-span-diagram}}
of `f` is the [span diagram](foundation.span-diagrams.md)

```text
      pr1                           pr1 ∘ pr2
  A <----- Σ (x y : A), f x ＝ f y -----------> A.
```

We call this the kernel span diagram, since the pair `(pr1 , pr1 ∘ pr2)` is
often called the kernel pair of a map.

## Definitions

### Kernel span diagrams of maps

<pre class="Agda"><a id="861" class="Keyword">module</a> <a id="868" href="foundation.kernel-span-diagrams-of-maps.html#868" class="Module">_</a>
  <a id="872" class="Symbol">{</a><a id="873" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a> <a id="876" href="foundation.kernel-span-diagrams-of-maps.html#876" class="Bound">l2</a> <a id="879" class="Symbol">:</a> <a id="881" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="886" class="Symbol">}</a> <a id="888" class="Symbol">{</a><a id="889" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a> <a id="891" class="Symbol">:</a> <a id="893" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="896" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a><a id="898" class="Symbol">}</a> <a id="900" class="Symbol">{</a><a id="901" href="foundation.kernel-span-diagrams-of-maps.html#901" class="Bound">B</a> <a id="903" class="Symbol">:</a> <a id="905" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="908" href="foundation.kernel-span-diagrams-of-maps.html#876" class="Bound">l2</a><a id="910" class="Symbol">}</a> <a id="912" class="Symbol">(</a><a id="913" href="foundation.kernel-span-diagrams-of-maps.html#913" class="Bound">f</a> <a id="915" class="Symbol">:</a> <a id="917" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a> <a id="919" class="Symbol">→</a> <a id="921" href="foundation.kernel-span-diagrams-of-maps.html#901" class="Bound">B</a><a id="922" class="Symbol">)</a>
  <a id="926" class="Keyword">where</a>

  <a id="935" href="foundation.kernel-span-diagrams-of-maps.html#935" class="Function">spanning-type-kernel-span</a> <a id="961" class="Symbol">:</a> <a id="963" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="966" class="Symbol">(</a><a id="967" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a> <a id="970" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="972" href="foundation.kernel-span-diagrams-of-maps.html#876" class="Bound">l2</a><a id="974" class="Symbol">)</a>
  <a id="978" href="foundation.kernel-span-diagrams-of-maps.html#935" class="Function">spanning-type-kernel-span</a> <a id="1004" class="Symbol">=</a>
    <a id="1010" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1012" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a> <a id="1014" class="Symbol">(λ</a> <a id="1017" href="foundation.kernel-span-diagrams-of-maps.html#1017" class="Bound">x</a> <a id="1019" class="Symbol">→</a> <a id="1021" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1023" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a> <a id="1025" class="Symbol">(λ</a> <a id="1028" href="foundation.kernel-span-diagrams-of-maps.html#1028" class="Bound">y</a> <a id="1030" class="Symbol">→</a> <a id="1032" href="foundation.kernel-span-diagrams-of-maps.html#913" class="Bound">f</a> <a id="1034" href="foundation.kernel-span-diagrams-of-maps.html#1017" class="Bound">x</a> <a id="1036" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1038" href="foundation.kernel-span-diagrams-of-maps.html#913" class="Bound">f</a> <a id="1040" href="foundation.kernel-span-diagrams-of-maps.html#1028" class="Bound">y</a><a id="1041" class="Symbol">))</a>

  <a id="1047" href="foundation.kernel-span-diagrams-of-maps.html#1047" class="Function">left-map-kernel-span</a> <a id="1068" class="Symbol">:</a>
    <a id="1074" href="foundation.kernel-span-diagrams-of-maps.html#935" class="Function">spanning-type-kernel-span</a> <a id="1100" class="Symbol">→</a> <a id="1102" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a>
  <a id="1106" href="foundation.kernel-span-diagrams-of-maps.html#1047" class="Function">left-map-kernel-span</a> <a id="1127" class="Symbol">=</a> <a id="1129" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="1136" href="foundation.kernel-span-diagrams-of-maps.html#1136" class="Function">right-map-kernel-span</a> <a id="1158" class="Symbol">:</a>
    <a id="1164" href="foundation.kernel-span-diagrams-of-maps.html#935" class="Function">spanning-type-kernel-span</a> <a id="1190" class="Symbol">→</a> <a id="1192" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a>
  <a id="1196" href="foundation.kernel-span-diagrams-of-maps.html#1136" class="Function">right-map-kernel-span</a> <a id="1218" class="Symbol">=</a> <a id="1220" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1224" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1226" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>

  <a id="1233" href="foundation.kernel-span-diagrams-of-maps.html#1233" class="Function">kernel-span</a> <a id="1245" class="Symbol">:</a> <a id="1247" href="foundation.spans.html#1830" class="Function">span</a> <a id="1252" class="Symbol">(</a><a id="1253" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a> <a id="1256" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1258" href="foundation.kernel-span-diagrams-of-maps.html#876" class="Bound">l2</a><a id="1260" class="Symbol">)</a> <a id="1262" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a> <a id="1264" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a>
  <a id="1268" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1272" href="foundation.kernel-span-diagrams-of-maps.html#1233" class="Function">kernel-span</a> <a id="1284" class="Symbol">=</a>
    <a id="1290" href="foundation.kernel-span-diagrams-of-maps.html#935" class="Function">spanning-type-kernel-span</a>
  <a id="1318" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1322" class="Symbol">(</a><a id="1323" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1327" href="foundation.kernel-span-diagrams-of-maps.html#1233" class="Function">kernel-span</a><a id="1338" class="Symbol">)</a> <a id="1340" class="Symbol">=</a>
    <a id="1346" href="foundation.kernel-span-diagrams-of-maps.html#1047" class="Function">left-map-kernel-span</a>
  <a id="1369" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1373" class="Symbol">(</a><a id="1374" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1378" href="foundation.kernel-span-diagrams-of-maps.html#1233" class="Function">kernel-span</a><a id="1389" class="Symbol">)</a> <a id="1391" class="Symbol">=</a>
    <a id="1397" href="foundation.kernel-span-diagrams-of-maps.html#1136" class="Function">right-map-kernel-span</a>

  <a id="1422" href="foundation.kernel-span-diagrams-of-maps.html#1422" class="Function">domain-kernel-span-diagram</a> <a id="1449" class="Symbol">:</a> <a id="1451" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1454" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a>
  <a id="1459" href="foundation.kernel-span-diagrams-of-maps.html#1422" class="Function">domain-kernel-span-diagram</a> <a id="1486" class="Symbol">=</a> <a id="1488" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a>

  <a id="1493" href="foundation.kernel-span-diagrams-of-maps.html#1493" class="Function">codomain-kernel-span-diagram</a> <a id="1522" class="Symbol">:</a> <a id="1524" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1527" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a>
  <a id="1532" href="foundation.kernel-span-diagrams-of-maps.html#1493" class="Function">codomain-kernel-span-diagram</a> <a id="1561" class="Symbol">=</a> <a id="1563" href="foundation.kernel-span-diagrams-of-maps.html#889" class="Bound">A</a>

  <a id="1568" href="foundation.kernel-span-diagrams-of-maps.html#1568" class="Function">kernel-span-diagram</a> <a id="1588" class="Symbol">:</a> <a id="1590" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1603" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a> <a id="1606" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a> <a id="1609" class="Symbol">(</a><a id="1610" href="foundation.kernel-span-diagrams-of-maps.html#873" class="Bound">l1</a> <a id="1613" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1615" href="foundation.kernel-span-diagrams-of-maps.html#876" class="Bound">l2</a><a id="1617" class="Symbol">)</a>
  <a id="1621" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1625" href="foundation.kernel-span-diagrams-of-maps.html#1568" class="Function">kernel-span-diagram</a> <a id="1645" class="Symbol">=</a> <a id="1647" href="foundation.kernel-span-diagrams-of-maps.html#1422" class="Function">domain-kernel-span-diagram</a>
  <a id="1676" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1680" class="Symbol">(</a><a id="1681" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1685" href="foundation.kernel-span-diagrams-of-maps.html#1568" class="Function">kernel-span-diagram</a><a id="1704" class="Symbol">)</a> <a id="1706" class="Symbol">=</a> <a id="1708" href="foundation.kernel-span-diagrams-of-maps.html#1493" class="Function">codomain-kernel-span-diagram</a>
  <a id="1739" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1743" class="Symbol">(</a><a id="1744" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1748" href="foundation.kernel-span-diagrams-of-maps.html#1568" class="Function">kernel-span-diagram</a><a id="1767" class="Symbol">)</a> <a id="1769" class="Symbol">=</a> <a id="1771" href="foundation.kernel-span-diagrams-of-maps.html#1233" class="Function">kernel-span</a>
</pre>