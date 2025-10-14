# Span diagrams on families of types

<pre class="Agda"><a id="47" class="Keyword">module</a> <a id="54" href="foundation.span-diagrams-families-of-types.html" class="Module">foundation.span-diagrams-families-of-types</a> <a id="97" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.spans-families-of-types.html" class="Module">foundation.spans-families-of-types</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A {{#concept "span diagram" Disambiguation="family of types"}} on a family of
types indexed by a type `I` consists of a type family `A : I → 𝒰`, and a
[span](foundation.spans-families-of-types.md) on the type family `A`. More
explicitly, a span diagram on a family of types indexed by `I` consists of a
type family `A : I → 𝒰`, a
{{#concept "spanning type" Disambiguation="span diagram on a family of types"}}
`S`, and a family of maps `f : (i : I) → S → A i`.

## Definitions

### Span diagrams of families of types

<pre class="Agda"><a id="span-diagram-type-family"></a><a id="835" href="foundation.span-diagrams-families-of-types.html#835" class="Function">span-diagram-type-family</a> <a id="860" class="Symbol">:</a>
  <a id="864" class="Symbol">{</a><a id="865" href="foundation.span-diagrams-families-of-types.html#865" class="Bound">l1</a> <a id="868" class="Symbol">:</a> <a id="870" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="875" class="Symbol">}</a> <a id="877" class="Symbol">(</a><a id="878" href="foundation.span-diagrams-families-of-types.html#878" class="Bound">l2</a> <a id="881" href="foundation.span-diagrams-families-of-types.html#881" class="Bound">l3</a> <a id="884" class="Symbol">:</a> <a id="886" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="891" class="Symbol">)</a> <a id="893" class="Symbol">→</a> <a id="895" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="898" href="foundation.span-diagrams-families-of-types.html#865" class="Bound">l1</a> <a id="901" class="Symbol">→</a> <a id="903" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="906" class="Symbol">(</a><a id="907" href="foundation.span-diagrams-families-of-types.html#865" class="Bound">l1</a> <a id="910" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="912" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="917" href="foundation.span-diagrams-families-of-types.html#878" class="Bound">l2</a> <a id="920" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="922" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="927" href="foundation.span-diagrams-families-of-types.html#881" class="Bound">l3</a><a id="929" class="Symbol">)</a>
<a id="931" href="foundation.span-diagrams-families-of-types.html#835" class="Function">span-diagram-type-family</a> <a id="956" href="foundation.span-diagrams-families-of-types.html#956" class="Bound">l2</a> <a id="959" href="foundation.span-diagrams-families-of-types.html#959" class="Bound">l3</a> <a id="962" href="foundation.span-diagrams-families-of-types.html#962" class="Bound">I</a> <a id="964" class="Symbol">=</a>
  <a id="968" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="970" class="Symbol">(</a><a id="971" href="foundation.span-diagrams-families-of-types.html#962" class="Bound">I</a> <a id="973" class="Symbol">→</a> <a id="975" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="978" href="foundation.span-diagrams-families-of-types.html#956" class="Bound">l2</a><a id="980" class="Symbol">)</a> <a id="982" class="Symbol">(λ</a> <a id="985" href="foundation.span-diagrams-families-of-types.html#985" class="Bound">A</a> <a id="987" class="Symbol">→</a> <a id="989" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="1006" href="foundation.span-diagrams-families-of-types.html#959" class="Bound">l3</a> <a id="1009" href="foundation.span-diagrams-families-of-types.html#985" class="Bound">A</a><a id="1010" class="Symbol">)</a>

<a id="1013" class="Keyword">module</a> <a id="1020" href="foundation.span-diagrams-families-of-types.html#1020" class="Module">_</a>
  <a id="1024" class="Symbol">{</a><a id="1025" href="foundation.span-diagrams-families-of-types.html#1025" class="Bound">l1</a> <a id="1028" href="foundation.span-diagrams-families-of-types.html#1028" class="Bound">l2</a> <a id="1031" href="foundation.span-diagrams-families-of-types.html#1031" class="Bound">l3</a> <a id="1034" class="Symbol">:</a> <a id="1036" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1041" class="Symbol">}</a> <a id="1043" class="Symbol">{</a><a id="1044" href="foundation.span-diagrams-families-of-types.html#1044" class="Bound">I</a> <a id="1046" class="Symbol">:</a> <a id="1048" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1051" href="foundation.span-diagrams-families-of-types.html#1025" class="Bound">l1</a><a id="1053" class="Symbol">}</a> <a id="1055" class="Symbol">(</a><a id="1056" href="foundation.span-diagrams-families-of-types.html#1056" class="Bound">s</a> <a id="1058" class="Symbol">:</a> <a id="1060" href="foundation.span-diagrams-families-of-types.html#835" class="Function">span-diagram-type-family</a> <a id="1085" href="foundation.span-diagrams-families-of-types.html#1028" class="Bound">l2</a> <a id="1088" href="foundation.span-diagrams-families-of-types.html#1031" class="Bound">l3</a> <a id="1091" href="foundation.span-diagrams-families-of-types.html#1044" class="Bound">I</a><a id="1092" class="Symbol">)</a>
  <a id="1096" class="Keyword">where</a>

  <a id="1105" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="1137" class="Symbol">:</a> <a id="1139" href="foundation.span-diagrams-families-of-types.html#1044" class="Bound">I</a> <a id="1141" class="Symbol">→</a> <a id="1143" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1146" href="foundation.span-diagrams-families-of-types.html#1028" class="Bound">l2</a>
  <a id="1151" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="1183" class="Symbol">=</a> <a id="1185" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1189" href="foundation.span-diagrams-families-of-types.html#1056" class="Bound">s</a>

  <a id="1194" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="1224" class="Symbol">:</a>
    <a id="1230" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="1247" href="foundation.span-diagrams-families-of-types.html#1031" class="Bound">l3</a> <a id="1250" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a>
  <a id="1284" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a> <a id="1314" class="Symbol">=</a> <a id="1316" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1320" href="foundation.span-diagrams-families-of-types.html#1056" class="Bound">s</a>

  <a id="1325" href="foundation.span-diagrams-families-of-types.html#1325" class="Function">spanning-type-span-diagram-type-family</a> <a id="1364" class="Symbol">:</a> <a id="1366" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1369" href="foundation.span-diagrams-families-of-types.html#1031" class="Bound">l3</a>
  <a id="1374" href="foundation.span-diagrams-families-of-types.html#1325" class="Function">spanning-type-span-diagram-type-family</a> <a id="1413" class="Symbol">=</a>
    <a id="1419" href="foundation.spans-families-of-types.html#1038" class="Function">spanning-type-span-type-family</a>
      <a id="1456" class="Symbol">(</a> <a id="1458" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a><a id="1487" class="Symbol">)</a>

  <a id="1492" href="foundation.span-diagrams-families-of-types.html#1492" class="Function">map-span-diagram-type-family</a> <a id="1521" class="Symbol">:</a>
    <a id="1527" class="Symbol">(</a><a id="1528" href="foundation.span-diagrams-families-of-types.html#1528" class="Bound">i</a> <a id="1530" class="Symbol">:</a> <a id="1532" href="foundation.span-diagrams-families-of-types.html#1044" class="Bound">I</a><a id="1533" class="Symbol">)</a> <a id="1535" class="Symbol">→</a> <a id="1537" href="foundation.span-diagrams-families-of-types.html#1325" class="Function">spanning-type-span-diagram-type-family</a> <a id="1576" class="Symbol">→</a>
    <a id="1582" href="foundation.span-diagrams-families-of-types.html#1105" class="Function">family-span-diagram-type-family</a> <a id="1614" href="foundation.span-diagrams-families-of-types.html#1528" class="Bound">i</a>
  <a id="1618" href="foundation.span-diagrams-families-of-types.html#1492" class="Function">map-span-diagram-type-family</a> <a id="1647" class="Symbol">=</a>
    <a id="1653" href="foundation.spans-families-of-types.html#1121" class="Function">map-span-type-family</a>
      <a id="1680" class="Symbol">(</a> <a id="1682" href="foundation.span-diagrams-families-of-types.html#1194" class="Function">span-span-diagram-type-family</a><a id="1711" class="Symbol">)</a>
</pre>