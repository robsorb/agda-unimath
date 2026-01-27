# Morphisms of cospans

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="foundation.morphisms-cospans.html" class="Module">foundation.morphisms-cospans</a> <a id="69" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="125" class="Keyword">open</a> <a id="130" class="Keyword">import</a> <a id="137" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="foundation.cospans.html" class="Module">foundation.cospans</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation-core.commuting-triangles-of-maps.html" class="Module">foundation-core.commuting-triangles-of-maps</a>
</pre>
</details>

## Idea

Consider two [cospans](foundation.cospans.md) `c := (X , f , g)` and
`d := (Y , h , k)` from `A` to `B`. A
{{#concept "morphism of cospans" Agda=hom-cospan}} from `c` to `d` consists of a
map `u : X → Y` equipped with [homotopies](foundation-core.homotopies.md)
witnessing that the two triangles

```text
      u              u
  X ----> Y      X ----> Y
   \     /        \     /
  f \   / h      g \   / k
     ∨ ∨            ∨ ∨
      A              B
```

[commute](foundation.commuting-triangles-of-maps.md).

## Definitions

### Morphisms of cospans

<pre class="Agda"><a id="934" class="Keyword">module</a> <a id="941" href="foundation.morphisms-cospans.html#941" class="Module">_</a>
  <a id="945" class="Symbol">{</a><a id="946" href="foundation.morphisms-cospans.html#946" class="Bound">l1</a> <a id="949" href="foundation.morphisms-cospans.html#949" class="Bound">l2</a> <a id="952" href="foundation.morphisms-cospans.html#952" class="Bound">l3</a> <a id="955" href="foundation.morphisms-cospans.html#955" class="Bound">l4</a> <a id="958" class="Symbol">:</a> <a id="960" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="965" class="Symbol">}</a> <a id="967" class="Symbol">{</a><a id="968" href="foundation.morphisms-cospans.html#968" class="Bound">A</a> <a id="970" class="Symbol">:</a> <a id="972" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="975" href="foundation.morphisms-cospans.html#946" class="Bound">l1</a><a id="977" class="Symbol">}</a> <a id="979" class="Symbol">{</a><a id="980" href="foundation.morphisms-cospans.html#980" class="Bound">B</a> <a id="982" class="Symbol">:</a> <a id="984" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="987" href="foundation.morphisms-cospans.html#949" class="Bound">l2</a><a id="989" class="Symbol">}</a>
  <a id="993" class="Symbol">(</a><a id="994" href="foundation.morphisms-cospans.html#994" class="Bound">c</a> <a id="996" class="Symbol">:</a> <a id="998" href="foundation.cospans.html#1683" class="Function">cospan</a> <a id="1005" href="foundation.morphisms-cospans.html#952" class="Bound">l3</a> <a id="1008" href="foundation.morphisms-cospans.html#968" class="Bound">A</a> <a id="1010" href="foundation.morphisms-cospans.html#980" class="Bound">B</a><a id="1011" class="Symbol">)</a> <a id="1013" class="Symbol">(</a><a id="1014" href="foundation.morphisms-cospans.html#1014" class="Bound">d</a> <a id="1016" class="Symbol">:</a> <a id="1018" href="foundation.cospans.html#1683" class="Function">cospan</a> <a id="1025" href="foundation.morphisms-cospans.html#955" class="Bound">l4</a> <a id="1028" href="foundation.morphisms-cospans.html#968" class="Bound">A</a> <a id="1030" href="foundation.morphisms-cospans.html#980" class="Bound">B</a><a id="1031" class="Symbol">)</a>
  <a id="1035" class="Keyword">where</a>

  <a id="1044" href="foundation.morphisms-cospans.html#1044" class="Function">coherence-hom-cospan</a> <a id="1065" class="Symbol">:</a>
    <a id="1071" class="Symbol">(</a><a id="1072" href="foundation.cospans.html#1916" class="Function">codomain-cospan</a> <a id="1088" href="foundation.morphisms-cospans.html#994" class="Bound">c</a> <a id="1090" class="Symbol">→</a> <a id="1092" href="foundation.cospans.html#1916" class="Function">codomain-cospan</a> <a id="1108" href="foundation.morphisms-cospans.html#1014" class="Bound">d</a><a id="1109" class="Symbol">)</a> <a id="1111" class="Symbol">→</a> <a id="1113" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1116" class="Symbol">(</a><a id="1117" href="foundation.morphisms-cospans.html#946" class="Bound">l1</a> <a id="1120" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1122" href="foundation.morphisms-cospans.html#949" class="Bound">l2</a> <a id="1125" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1127" href="foundation.morphisms-cospans.html#955" class="Bound">l4</a><a id="1129" class="Symbol">)</a>
  <a id="1133" href="foundation.morphisms-cospans.html#1044" class="Function">coherence-hom-cospan</a> <a id="1154" href="foundation.morphisms-cospans.html#1154" class="Bound">h</a> <a id="1156" class="Symbol">=</a>
    <a id="1162" class="Symbol">(</a> <a id="1164" href="foundation-core.commuting-triangles-of-maps.html#867" class="Function">coherence-triangle-maps</a> <a id="1188" class="Symbol">(</a><a id="1189" href="foundation.cospans.html#1968" class="Function">left-map-cospan</a> <a id="1205" href="foundation.morphisms-cospans.html#1014" class="Bound">d</a><a id="1206" class="Symbol">)</a> <a id="1208" href="foundation.morphisms-cospans.html#1154" class="Bound">h</a> <a id="1210" class="Symbol">(</a><a id="1211" href="foundation.cospans.html#1968" class="Function">left-map-cospan</a> <a id="1227" href="foundation.morphisms-cospans.html#994" class="Bound">c</a><a id="1228" class="Symbol">))</a> <a id="1231" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
    <a id="1237" class="Symbol">(</a> <a id="1239" href="foundation-core.commuting-triangles-of-maps.html#867" class="Function">coherence-triangle-maps</a> <a id="1263" class="Symbol">(</a><a id="1264" href="foundation.cospans.html#2041" class="Function">right-map-cospan</a> <a id="1281" href="foundation.morphisms-cospans.html#1014" class="Bound">d</a><a id="1282" class="Symbol">)</a> <a id="1284" href="foundation.morphisms-cospans.html#1154" class="Bound">h</a> <a id="1286" class="Symbol">(</a><a id="1287" href="foundation.cospans.html#2041" class="Function">right-map-cospan</a> <a id="1304" href="foundation.morphisms-cospans.html#994" class="Bound">c</a><a id="1305" class="Symbol">))</a>

  <a id="1311" href="foundation.morphisms-cospans.html#1311" class="Function">hom-cospan</a> <a id="1322" class="Symbol">:</a> <a id="1324" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1327" class="Symbol">(</a><a id="1328" href="foundation.morphisms-cospans.html#946" class="Bound">l1</a> <a id="1331" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1333" href="foundation.morphisms-cospans.html#949" class="Bound">l2</a> <a id="1336" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1338" href="foundation.morphisms-cospans.html#952" class="Bound">l3</a> <a id="1341" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1343" href="foundation.morphisms-cospans.html#955" class="Bound">l4</a><a id="1345" class="Symbol">)</a>
  <a id="1349" href="foundation.morphisms-cospans.html#1311" class="Function">hom-cospan</a> <a id="1360" class="Symbol">=</a>
    <a id="1366" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1368" class="Symbol">(</a> <a id="1370" href="foundation.cospans.html#1916" class="Function">codomain-cospan</a> <a id="1386" href="foundation.morphisms-cospans.html#994" class="Bound">c</a> <a id="1388" class="Symbol">→</a> <a id="1390" href="foundation.cospans.html#1916" class="Function">codomain-cospan</a> <a id="1406" href="foundation.morphisms-cospans.html#1014" class="Bound">d</a><a id="1407" class="Symbol">)</a>
      <a id="1415" class="Symbol">(</a> <a id="1417" href="foundation.morphisms-cospans.html#1044" class="Function">coherence-hom-cospan</a><a id="1437" class="Symbol">)</a>
</pre>