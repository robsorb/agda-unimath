# Morphisms of twisted arrows

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="foundation.morphisms-twisted-arrows.html" class="Module">foundation.morphisms-twisted-arrows</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
</pre>
</details>

## Idea

A **morphism of twisted arrows** from `f : A → B` to `g : X → Y` is a triple
`(i , j , H)` consisting of

- a map `i : X → A`
- a map `j : B → Y`, and
- a [homotopy](foundation-core.homotopies.md) `H : j ∘ f ∘ i ~ g` witnessing
  that the square

  ```text
           i
      A <----- X
      |        |
    f |        | g
      ∨        ∨
      B -----> Y
          j
  ```

  commutes.

Thus, a morphism of twisted arrows can also be understood as _a factorization of
`g` through `f`_.

## Definitions

<pre class="Agda"><a id="844" class="Keyword">module</a> <a id="851" href="foundation.morphisms-twisted-arrows.html#851" class="Module">_</a>
  <a id="855" class="Symbol">{</a><a id="856" href="foundation.morphisms-twisted-arrows.html#856" class="Bound">l1</a> <a id="859" href="foundation.morphisms-twisted-arrows.html#859" class="Bound">l2</a> <a id="862" href="foundation.morphisms-twisted-arrows.html#862" class="Bound">l3</a> <a id="865" href="foundation.morphisms-twisted-arrows.html#865" class="Bound">l4</a> <a id="868" class="Symbol">:</a> <a id="870" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="875" class="Symbol">}</a> <a id="877" class="Symbol">{</a><a id="878" href="foundation.morphisms-twisted-arrows.html#878" class="Bound">A</a> <a id="880" class="Symbol">:</a> <a id="882" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="885" href="foundation.morphisms-twisted-arrows.html#856" class="Bound">l1</a><a id="887" class="Symbol">}</a> <a id="889" class="Symbol">{</a><a id="890" href="foundation.morphisms-twisted-arrows.html#890" class="Bound">B</a> <a id="892" class="Symbol">:</a> <a id="894" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="897" href="foundation.morphisms-twisted-arrows.html#859" class="Bound">l2</a><a id="899" class="Symbol">}</a> <a id="901" class="Symbol">{</a><a id="902" href="foundation.morphisms-twisted-arrows.html#902" class="Bound">X</a> <a id="904" class="Symbol">:</a> <a id="906" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="909" href="foundation.morphisms-twisted-arrows.html#862" class="Bound">l3</a><a id="911" class="Symbol">}</a> <a id="913" class="Symbol">{</a><a id="914" href="foundation.morphisms-twisted-arrows.html#914" class="Bound">Y</a> <a id="916" class="Symbol">:</a> <a id="918" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="921" href="foundation.morphisms-twisted-arrows.html#865" class="Bound">l4</a><a id="923" class="Symbol">}</a>
  <a id="927" class="Symbol">(</a><a id="928" href="foundation.morphisms-twisted-arrows.html#928" class="Bound">f</a> <a id="930" class="Symbol">:</a> <a id="932" href="foundation.morphisms-twisted-arrows.html#878" class="Bound">A</a> <a id="934" class="Symbol">→</a> <a id="936" href="foundation.morphisms-twisted-arrows.html#890" class="Bound">B</a><a id="937" class="Symbol">)</a> <a id="939" class="Symbol">(</a><a id="940" href="foundation.morphisms-twisted-arrows.html#940" class="Bound">g</a> <a id="942" class="Symbol">:</a> <a id="944" href="foundation.morphisms-twisted-arrows.html#902" class="Bound">X</a> <a id="946" class="Symbol">→</a> <a id="948" href="foundation.morphisms-twisted-arrows.html#914" class="Bound">Y</a><a id="949" class="Symbol">)</a>
  <a id="953" class="Keyword">where</a>

  <a id="962" href="foundation.morphisms-twisted-arrows.html#962" class="Function">coherence-hom-twisted-arrow</a> <a id="990" class="Symbol">:</a>
    <a id="996" class="Symbol">(</a><a id="997" href="foundation.morphisms-twisted-arrows.html#902" class="Bound">X</a> <a id="999" class="Symbol">→</a> <a id="1001" href="foundation.morphisms-twisted-arrows.html#878" class="Bound">A</a><a id="1002" class="Symbol">)</a> <a id="1004" class="Symbol">→</a> <a id="1006" class="Symbol">(</a><a id="1007" href="foundation.morphisms-twisted-arrows.html#890" class="Bound">B</a> <a id="1009" class="Symbol">→</a> <a id="1011" href="foundation.morphisms-twisted-arrows.html#914" class="Bound">Y</a><a id="1012" class="Symbol">)</a> <a id="1014" class="Symbol">→</a> <a id="1016" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1019" class="Symbol">(</a><a id="1020" href="foundation.morphisms-twisted-arrows.html#862" class="Bound">l3</a> <a id="1023" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1025" href="foundation.morphisms-twisted-arrows.html#865" class="Bound">l4</a><a id="1027" class="Symbol">)</a>
  <a id="1031" href="foundation.morphisms-twisted-arrows.html#962" class="Function">coherence-hom-twisted-arrow</a> <a id="1059" href="foundation.morphisms-twisted-arrows.html#1059" class="Bound">i</a> <a id="1061" href="foundation.morphisms-twisted-arrows.html#1061" class="Bound">j</a> <a id="1063" class="Symbol">=</a> <a id="1065" href="foundation.morphisms-twisted-arrows.html#1061" class="Bound">j</a> <a id="1067" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1069" href="foundation.morphisms-twisted-arrows.html#928" class="Bound">f</a> <a id="1071" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1073" href="foundation.morphisms-twisted-arrows.html#1059" class="Bound">i</a> <a id="1075" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1077" href="foundation.morphisms-twisted-arrows.html#940" class="Bound">g</a>

  <a id="1082" href="foundation.morphisms-twisted-arrows.html#1082" class="Function">hom-twisted-arrow</a> <a id="1100" class="Symbol">:</a> <a id="1102" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1105" class="Symbol">(</a><a id="1106" href="foundation.morphisms-twisted-arrows.html#856" class="Bound">l1</a> <a id="1109" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1111" href="foundation.morphisms-twisted-arrows.html#859" class="Bound">l2</a> <a id="1114" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1116" href="foundation.morphisms-twisted-arrows.html#862" class="Bound">l3</a> <a id="1119" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1121" href="foundation.morphisms-twisted-arrows.html#865" class="Bound">l4</a><a id="1123" class="Symbol">)</a>
  <a id="1127" href="foundation.morphisms-twisted-arrows.html#1082" class="Function">hom-twisted-arrow</a> <a id="1145" class="Symbol">=</a>
    <a id="1151" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1153" class="Symbol">(</a><a id="1154" href="foundation.morphisms-twisted-arrows.html#902" class="Bound">X</a> <a id="1156" class="Symbol">→</a> <a id="1158" href="foundation.morphisms-twisted-arrows.html#878" class="Bound">A</a><a id="1159" class="Symbol">)</a> <a id="1161" class="Symbol">(λ</a> <a id="1164" href="foundation.morphisms-twisted-arrows.html#1164" class="Bound">i</a> <a id="1166" class="Symbol">→</a> <a id="1168" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1170" class="Symbol">(</a><a id="1171" href="foundation.morphisms-twisted-arrows.html#890" class="Bound">B</a> <a id="1173" class="Symbol">→</a> <a id="1175" href="foundation.morphisms-twisted-arrows.html#914" class="Bound">Y</a><a id="1176" class="Symbol">)</a> <a id="1178" class="Symbol">(</a><a id="1179" href="foundation.morphisms-twisted-arrows.html#962" class="Function">coherence-hom-twisted-arrow</a> <a id="1207" href="foundation.morphisms-twisted-arrows.html#1164" class="Bound">i</a><a id="1208" class="Symbol">))</a>

  <a id="1214" class="Keyword">module</a> <a id="1221" href="foundation.morphisms-twisted-arrows.html#1221" class="Module">_</a>
    <a id="1227" class="Symbol">(</a><a id="1228" href="foundation.morphisms-twisted-arrows.html#1228" class="Bound">α</a> <a id="1230" class="Symbol">:</a> <a id="1232" href="foundation.morphisms-twisted-arrows.html#1082" class="Function">hom-twisted-arrow</a><a id="1249" class="Symbol">)</a>
    <a id="1255" class="Keyword">where</a>

    <a id="1266" href="foundation.morphisms-twisted-arrows.html#1266" class="Function">map-domain-hom-twisted-arrow</a> <a id="1295" class="Symbol">:</a> <a id="1297" href="foundation.morphisms-twisted-arrows.html#902" class="Bound">X</a> <a id="1299" class="Symbol">→</a> <a id="1301" href="foundation.morphisms-twisted-arrows.html#878" class="Bound">A</a>
    <a id="1307" href="foundation.morphisms-twisted-arrows.html#1266" class="Function">map-domain-hom-twisted-arrow</a> <a id="1336" class="Symbol">=</a> <a id="1338" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1342" href="foundation.morphisms-twisted-arrows.html#1228" class="Bound">α</a>

    <a id="1349" href="foundation.morphisms-twisted-arrows.html#1349" class="Function">map-codomain-hom-twisted-arrow</a> <a id="1380" class="Symbol">:</a> <a id="1382" href="foundation.morphisms-twisted-arrows.html#890" class="Bound">B</a> <a id="1384" class="Symbol">→</a> <a id="1386" href="foundation.morphisms-twisted-arrows.html#914" class="Bound">Y</a>
    <a id="1392" href="foundation.morphisms-twisted-arrows.html#1349" class="Function">map-codomain-hom-twisted-arrow</a> <a id="1423" class="Symbol">=</a> <a id="1425" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1429" class="Symbol">(</a><a id="1430" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1434" href="foundation.morphisms-twisted-arrows.html#1228" class="Bound">α</a><a id="1435" class="Symbol">)</a>

    <a id="1442" href="foundation.morphisms-twisted-arrows.html#1442" class="Function">coh-hom-twisted-arrow</a> <a id="1464" class="Symbol">:</a>
      <a id="1472" href="foundation.morphisms-twisted-arrows.html#1349" class="Function">map-codomain-hom-twisted-arrow</a> <a id="1503" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1505" href="foundation.morphisms-twisted-arrows.html#928" class="Bound">f</a> <a id="1507" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1509" href="foundation.morphisms-twisted-arrows.html#1266" class="Function">map-domain-hom-twisted-arrow</a> <a id="1538" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1540" href="foundation.morphisms-twisted-arrows.html#940" class="Bound">g</a>
    <a id="1546" href="foundation.morphisms-twisted-arrows.html#1442" class="Function">coh-hom-twisted-arrow</a> <a id="1568" class="Symbol">=</a> <a id="1570" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1574" class="Symbol">(</a><a id="1575" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1579" href="foundation.morphisms-twisted-arrows.html#1228" class="Bound">α</a><a id="1580" class="Symbol">)</a>
</pre>
## See also

- [Morphisms of arrows](foundation.morphisms-arrows.md).
