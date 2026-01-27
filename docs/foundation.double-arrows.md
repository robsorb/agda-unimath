# Double arrows

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="foundation.double-arrows.html" class="Module">foundation.double-arrows</a> <a id="58" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="114" class="Keyword">open</a> <a id="119" class="Keyword">import</a> <a id="126" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A {{#concept "double arrow" Disambiguation="between types" Agda=double-arrow}}
is a [pair](foundation.dependent-pair-types.md) of types `A`, `B`
[equipped](foundation.structure.md) with a pair of
[maps](foundation.function-types.md) `f, g : A → B`.

We draw a double arrow as

```text
     A
    | |
  f | | g
    | |
    ∨ ∨
     B
```

where `f` is the first map in the structure and `g` is the second map in the
structure. We also call `f` the _left map_ and `g` the _right map_. By
convention, [homotopies](foundation-core.homotopies.md) go from left to right.

## Definitions

### Double arrows

<pre class="Agda"><a id="double-arrow"></a><a id="879" href="foundation.double-arrows.html#879" class="Function">double-arrow</a> <a id="892" class="Symbol">:</a> <a id="894" class="Symbol">(</a><a id="895" href="foundation.double-arrows.html#895" class="Bound">l1</a> <a id="898" href="foundation.double-arrows.html#898" class="Bound">l2</a> <a id="901" class="Symbol">:</a> <a id="903" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="908" class="Symbol">)</a> <a id="910" class="Symbol">→</a> <a id="912" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="915" class="Symbol">(</a><a id="916" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="921" href="foundation.double-arrows.html#895" class="Bound">l1</a> <a id="924" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="926" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="931" href="foundation.double-arrows.html#898" class="Bound">l2</a><a id="933" class="Symbol">)</a>
<a id="935" href="foundation.double-arrows.html#879" class="Function">double-arrow</a> <a id="948" href="foundation.double-arrows.html#948" class="Bound">l1</a> <a id="951" href="foundation.double-arrows.html#951" class="Bound">l2</a> <a id="954" class="Symbol">=</a> <a id="956" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="958" class="Symbol">(</a><a id="959" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="962" href="foundation.double-arrows.html#948" class="Bound">l1</a><a id="964" class="Symbol">)</a> <a id="966" class="Symbol">(λ</a> <a id="969" href="foundation.double-arrows.html#969" class="Bound">A</a> <a id="971" class="Symbol">→</a> <a id="973" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="975" class="Symbol">(</a><a id="976" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="979" href="foundation.double-arrows.html#951" class="Bound">l2</a><a id="981" class="Symbol">)</a> <a id="983" class="Symbol">(λ</a> <a id="986" href="foundation.double-arrows.html#986" class="Bound">B</a> <a id="988" class="Symbol">→</a> <a id="990" class="Symbol">(</a><a id="991" href="foundation.double-arrows.html#969" class="Bound">A</a> <a id="993" class="Symbol">→</a> <a id="995" href="foundation.double-arrows.html#986" class="Bound">B</a><a id="996" class="Symbol">)</a> <a id="998" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1000" class="Symbol">(</a><a id="1001" href="foundation.double-arrows.html#969" class="Bound">A</a> <a id="1003" class="Symbol">→</a> <a id="1005" href="foundation.double-arrows.html#986" class="Bound">B</a><a id="1006" class="Symbol">)))</a>

<a id="1011" class="Keyword">module</a> <a id="1018" href="foundation.double-arrows.html#1018" class="Module">_</a>
  <a id="1022" class="Symbol">{</a><a id="1023" href="foundation.double-arrows.html#1023" class="Bound">l1</a> <a id="1026" href="foundation.double-arrows.html#1026" class="Bound">l2</a> <a id="1029" class="Symbol">:</a> <a id="1031" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1036" class="Symbol">}</a> <a id="1038" class="Symbol">{</a><a id="1039" href="foundation.double-arrows.html#1039" class="Bound">A</a> <a id="1041" class="Symbol">:</a> <a id="1043" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1046" href="foundation.double-arrows.html#1023" class="Bound">l1</a><a id="1048" class="Symbol">}</a> <a id="1050" class="Symbol">{</a><a id="1051" href="foundation.double-arrows.html#1051" class="Bound">B</a> <a id="1053" class="Symbol">:</a> <a id="1055" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1058" href="foundation.double-arrows.html#1026" class="Bound">l2</a><a id="1060" class="Symbol">}</a>
  <a id="1064" class="Symbol">(</a><a id="1065" href="foundation.double-arrows.html#1065" class="Bound">f</a> <a id="1067" class="Symbol">:</a> <a id="1069" href="foundation.double-arrows.html#1039" class="Bound">A</a> <a id="1071" class="Symbol">→</a> <a id="1073" href="foundation.double-arrows.html#1051" class="Bound">B</a><a id="1074" class="Symbol">)</a> <a id="1076" class="Symbol">(</a><a id="1077" href="foundation.double-arrows.html#1077" class="Bound">g</a> <a id="1079" class="Symbol">:</a> <a id="1081" href="foundation.double-arrows.html#1039" class="Bound">A</a> <a id="1083" class="Symbol">→</a> <a id="1085" href="foundation.double-arrows.html#1051" class="Bound">B</a><a id="1086" class="Symbol">)</a>
  <a id="1090" class="Keyword">where</a>

  <a id="1099" href="foundation.double-arrows.html#1099" class="Function">make-double-arrow</a> <a id="1117" class="Symbol">:</a> <a id="1119" href="foundation.double-arrows.html#879" class="Function">double-arrow</a> <a id="1132" href="foundation.double-arrows.html#1023" class="Bound">l1</a> <a id="1135" href="foundation.double-arrows.html#1026" class="Bound">l2</a>
  <a id="1140" href="foundation.double-arrows.html#1099" class="Function">make-double-arrow</a> <a id="1158" class="Symbol">=</a> <a id="1160" class="Symbol">(</a><a id="1161" href="foundation.double-arrows.html#1039" class="Bound">A</a> <a id="1163" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1165" href="foundation.double-arrows.html#1051" class="Bound">B</a> <a id="1167" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1169" href="foundation.double-arrows.html#1065" class="Bound">f</a> <a id="1171" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1173" href="foundation.double-arrows.html#1077" class="Bound">g</a><a id="1174" class="Symbol">)</a>

  <a id="1179" class="Symbol">{-#</a> <a id="1183" class="Keyword">INLINE</a> <a id="1190" href="foundation.double-arrows.html#1099" class="Function">make-double-arrow</a> <a id="1208" class="Symbol">#-}</a>
</pre>
### Components of a double arrow

<pre class="Agda"><a id="1259" class="Keyword">module</a> <a id="1266" href="foundation.double-arrows.html#1266" class="Module">_</a>
  <a id="1270" class="Symbol">{</a><a id="1271" href="foundation.double-arrows.html#1271" class="Bound">l1</a> <a id="1274" href="foundation.double-arrows.html#1274" class="Bound">l2</a> <a id="1277" class="Symbol">:</a> <a id="1279" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1284" class="Symbol">}</a> <a id="1286" class="Symbol">(</a><a id="1287" href="foundation.double-arrows.html#1287" class="Bound">a</a> <a id="1289" class="Symbol">:</a> <a id="1291" href="foundation.double-arrows.html#879" class="Function">double-arrow</a> <a id="1304" href="foundation.double-arrows.html#1271" class="Bound">l1</a> <a id="1307" href="foundation.double-arrows.html#1274" class="Bound">l2</a><a id="1309" class="Symbol">)</a>
  <a id="1313" class="Keyword">where</a>

  <a id="1322" href="foundation.double-arrows.html#1322" class="Function">domain-double-arrow</a> <a id="1342" class="Symbol">:</a> <a id="1344" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1347" href="foundation.double-arrows.html#1271" class="Bound">l1</a>
  <a id="1352" href="foundation.double-arrows.html#1322" class="Function">domain-double-arrow</a> <a id="1372" class="Symbol">=</a> <a id="1374" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1378" href="foundation.double-arrows.html#1287" class="Bound">a</a>

  <a id="1383" href="foundation.double-arrows.html#1383" class="Function">codomain-double-arrow</a> <a id="1405" class="Symbol">:</a> <a id="1407" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1410" href="foundation.double-arrows.html#1274" class="Bound">l2</a>
  <a id="1415" href="foundation.double-arrows.html#1383" class="Function">codomain-double-arrow</a> <a id="1437" class="Symbol">=</a> <a id="1439" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1443" class="Symbol">(</a><a id="1444" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1448" href="foundation.double-arrows.html#1287" class="Bound">a</a><a id="1449" class="Symbol">)</a>

  <a id="1454" href="foundation.double-arrows.html#1454" class="Function">left-map-double-arrow</a> <a id="1476" class="Symbol">:</a> <a id="1478" href="foundation.double-arrows.html#1322" class="Function">domain-double-arrow</a> <a id="1498" class="Symbol">→</a> <a id="1500" href="foundation.double-arrows.html#1383" class="Function">codomain-double-arrow</a>
  <a id="1524" href="foundation.double-arrows.html#1454" class="Function">left-map-double-arrow</a> <a id="1546" class="Symbol">=</a> <a id="1548" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1552" class="Symbol">(</a><a id="1553" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1557" class="Symbol">(</a><a id="1558" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1562" href="foundation.double-arrows.html#1287" class="Bound">a</a><a id="1563" class="Symbol">))</a>

  <a id="1569" href="foundation.double-arrows.html#1569" class="Function">right-map-double-arrow</a> <a id="1592" class="Symbol">:</a> <a id="1594" href="foundation.double-arrows.html#1322" class="Function">domain-double-arrow</a> <a id="1614" class="Symbol">→</a> <a id="1616" href="foundation.double-arrows.html#1383" class="Function">codomain-double-arrow</a>
  <a id="1640" href="foundation.double-arrows.html#1569" class="Function">right-map-double-arrow</a> <a id="1663" class="Symbol">=</a> <a id="1665" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1669" class="Symbol">(</a><a id="1670" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1674" class="Symbol">(</a><a id="1675" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1679" href="foundation.double-arrows.html#1287" class="Bound">a</a><a id="1680" class="Symbol">))</a>
</pre>
## See also

- Colimits of double arrows are
  [coequalizers](synthetic-homotopy-theory.coequalizers.md)
