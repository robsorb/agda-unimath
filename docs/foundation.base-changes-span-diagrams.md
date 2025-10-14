# Base changes of span diagrams

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="foundation.base-changes-span-diagrams.html" class="Module">foundation.base-changes-span-diagrams</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="foundation.cartesian-morphisms-arrows.html" class="Module">foundation.cartesian-morphisms-arrows</a>
<a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="foundation.cartesian-morphisms-span-diagrams.html" class="Module">foundation.cartesian-morphisms-span-diagrams</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="foundation.morphisms-span-diagrams.html" class="Module">foundation.morphisms-span-diagrams</a>
<a id="430" class="Keyword">open</a> <a id="435" class="Keyword">import</a> <a id="442" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="467" class="Keyword">open</a> <a id="472" class="Keyword">import</a> <a id="479" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮 := (A <-f- S -g-> B)`.
A
{{#concept "base change" Disambiguation="span diagram" Agda=base-change-span-diagram}}
of `𝒮` consists of a span diagram `𝒯` and a
[cartesian morphism](foundation.cartesian-morphisms-span-diagrams.md) of span
diagrams `𝒯 → 𝒮`.

## Definitions

### Base changes of span diagrams

<pre class="Agda"><a id="902" class="Keyword">module</a> <a id="909" href="foundation.base-changes-span-diagrams.html#909" class="Module">_</a>
  <a id="913" class="Symbol">{</a><a id="914" href="foundation.base-changes-span-diagrams.html#914" class="Bound">l1</a> <a id="917" href="foundation.base-changes-span-diagrams.html#917" class="Bound">l2</a> <a id="920" href="foundation.base-changes-span-diagrams.html#920" class="Bound">l3</a> <a id="923" class="Symbol">:</a> <a id="925" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="930" class="Symbol">}</a> <a id="932" class="Symbol">(</a><a id="933" href="foundation.base-changes-span-diagrams.html#933" class="Bound">l4</a> <a id="936" href="foundation.base-changes-span-diagrams.html#936" class="Bound">l5</a> <a id="939" href="foundation.base-changes-span-diagrams.html#939" class="Bound">l6</a> <a id="942" class="Symbol">:</a> <a id="944" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="949" class="Symbol">)</a> <a id="951" class="Symbol">(</a><a id="952" href="foundation.base-changes-span-diagrams.html#952" class="Bound">𝒮</a> <a id="954" class="Symbol">:</a> <a id="956" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="969" href="foundation.base-changes-span-diagrams.html#914" class="Bound">l1</a> <a id="972" href="foundation.base-changes-span-diagrams.html#917" class="Bound">l2</a> <a id="975" href="foundation.base-changes-span-diagrams.html#920" class="Bound">l3</a><a id="977" class="Symbol">)</a>
  <a id="981" class="Keyword">where</a>

  <a id="990" href="foundation.base-changes-span-diagrams.html#990" class="Function">base-change-span-diagram</a> <a id="1015" class="Symbol">:</a>
    <a id="1021" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1024" class="Symbol">(</a><a id="1025" href="foundation.base-changes-span-diagrams.html#914" class="Bound">l1</a> <a id="1028" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1030" href="foundation.base-changes-span-diagrams.html#917" class="Bound">l2</a> <a id="1033" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1035" href="foundation.base-changes-span-diagrams.html#920" class="Bound">l3</a> <a id="1038" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1040" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1045" href="foundation.base-changes-span-diagrams.html#933" class="Bound">l4</a> <a id="1048" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1050" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1055" href="foundation.base-changes-span-diagrams.html#936" class="Bound">l5</a> <a id="1058" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1060" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1065" href="foundation.base-changes-span-diagrams.html#939" class="Bound">l6</a><a id="1067" class="Symbol">)</a>
  <a id="1071" href="foundation.base-changes-span-diagrams.html#990" class="Function">base-change-span-diagram</a> <a id="1096" class="Symbol">=</a>
    <a id="1102" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1104" class="Symbol">(</a><a id="1105" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1118" href="foundation.base-changes-span-diagrams.html#933" class="Bound">l4</a> <a id="1121" href="foundation.base-changes-span-diagrams.html#936" class="Bound">l5</a> <a id="1124" href="foundation.base-changes-span-diagrams.html#939" class="Bound">l6</a><a id="1126" class="Symbol">)</a> <a id="1128" class="Symbol">(λ</a> <a id="1131" href="foundation.base-changes-span-diagrams.html#1131" class="Bound">𝒯</a> <a id="1133" class="Symbol">→</a> <a id="1135" href="foundation.cartesian-morphisms-span-diagrams.html#7979" class="Function">cartesian-hom-span-diagram</a> <a id="1162" href="foundation.base-changes-span-diagrams.html#1131" class="Bound">𝒯</a> <a id="1164" href="foundation.base-changes-span-diagrams.html#952" class="Bound">𝒮</a><a id="1165" class="Symbol">)</a>

<a id="1168" class="Keyword">module</a> <a id="1175" href="foundation.base-changes-span-diagrams.html#1175" class="Module">_</a>
  <a id="1179" class="Symbol">{</a><a id="1180" href="foundation.base-changes-span-diagrams.html#1180" class="Bound">l1</a> <a id="1183" href="foundation.base-changes-span-diagrams.html#1183" class="Bound">l2</a> <a id="1186" href="foundation.base-changes-span-diagrams.html#1186" class="Bound">l3</a> <a id="1189" href="foundation.base-changes-span-diagrams.html#1189" class="Bound">l4</a> <a id="1192" href="foundation.base-changes-span-diagrams.html#1192" class="Bound">l5</a> <a id="1195" href="foundation.base-changes-span-diagrams.html#1195" class="Bound">l6</a> <a id="1198" class="Symbol">:</a> <a id="1200" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1205" class="Symbol">}</a> <a id="1207" class="Symbol">(</a><a id="1208" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a> <a id="1210" class="Symbol">:</a> <a id="1212" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1225" href="foundation.base-changes-span-diagrams.html#1180" class="Bound">l1</a> <a id="1228" href="foundation.base-changes-span-diagrams.html#1183" class="Bound">l2</a> <a id="1231" href="foundation.base-changes-span-diagrams.html#1186" class="Bound">l3</a><a id="1233" class="Symbol">)</a>
  <a id="1237" class="Symbol">(</a><a id="1238" href="foundation.base-changes-span-diagrams.html#1238" class="Bound">f</a> <a id="1240" class="Symbol">:</a> <a id="1242" href="foundation.base-changes-span-diagrams.html#990" class="Function">base-change-span-diagram</a> <a id="1267" href="foundation.base-changes-span-diagrams.html#1189" class="Bound">l4</a> <a id="1270" href="foundation.base-changes-span-diagrams.html#1192" class="Bound">l5</a> <a id="1273" href="foundation.base-changes-span-diagrams.html#1195" class="Bound">l6</a> <a id="1276" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="1277" class="Symbol">)</a>
  <a id="1281" class="Keyword">where</a>

  <a id="1290" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a> <a id="1328" class="Symbol">:</a> <a id="1330" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1343" href="foundation.base-changes-span-diagrams.html#1189" class="Bound">l4</a> <a id="1346" href="foundation.base-changes-span-diagrams.html#1192" class="Bound">l5</a> <a id="1349" href="foundation.base-changes-span-diagrams.html#1195" class="Bound">l6</a>
  <a id="1354" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a> <a id="1392" class="Symbol">=</a> <a id="1394" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1398" href="foundation.base-changes-span-diagrams.html#1238" class="Bound">f</a>

  <a id="1403" href="foundation.base-changes-span-diagrams.html#1403" class="Function">domain-span-diagram-base-change-span-diagram</a> <a id="1448" class="Symbol">:</a> <a id="1450" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1453" href="foundation.base-changes-span-diagrams.html#1189" class="Bound">l4</a>
  <a id="1458" href="foundation.base-changes-span-diagrams.html#1403" class="Function">domain-span-diagram-base-change-span-diagram</a> <a id="1503" class="Symbol">=</a>
    <a id="1509" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="1529" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a>

  <a id="1570" href="foundation.base-changes-span-diagrams.html#1570" class="Function">codomain-span-diagram-base-change-span-diagram</a> <a id="1617" class="Symbol">:</a> <a id="1619" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1622" href="foundation.base-changes-span-diagrams.html#1192" class="Bound">l5</a>
  <a id="1627" href="foundation.base-changes-span-diagrams.html#1570" class="Function">codomain-span-diagram-base-change-span-diagram</a> <a id="1674" class="Symbol">=</a>
    <a id="1680" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="1702" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a>

  <a id="1743" href="foundation.base-changes-span-diagrams.html#1743" class="Function">spanning-type-span-diagram-base-change-span-diagram</a> <a id="1795" class="Symbol">:</a> <a id="1797" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1800" href="foundation.base-changes-span-diagrams.html#1195" class="Bound">l6</a>
  <a id="1805" href="foundation.base-changes-span-diagrams.html#1743" class="Function">spanning-type-span-diagram-base-change-span-diagram</a> <a id="1857" class="Symbol">=</a>
    <a id="1863" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="1890" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a>

  <a id="1931" href="foundation.base-changes-span-diagrams.html#1931" class="Function">left-map-span-diagram-base-change-span-diagram</a> <a id="1978" class="Symbol">:</a>
    <a id="1984" href="foundation.base-changes-span-diagrams.html#1743" class="Function">spanning-type-span-diagram-base-change-span-diagram</a> <a id="2036" class="Symbol">→</a>
    <a id="2042" href="foundation.base-changes-span-diagrams.html#1403" class="Function">domain-span-diagram-base-change-span-diagram</a>
  <a id="2089" href="foundation.base-changes-span-diagrams.html#1931" class="Function">left-map-span-diagram-base-change-span-diagram</a> <a id="2136" class="Symbol">=</a>
    <a id="2142" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="2164" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a>

  <a id="2205" href="foundation.base-changes-span-diagrams.html#2205" class="Function">right-map-span-diagram-base-change-span-diagram</a> <a id="2253" class="Symbol">:</a>
    <a id="2259" href="foundation.base-changes-span-diagrams.html#1743" class="Function">spanning-type-span-diagram-base-change-span-diagram</a> <a id="2311" class="Symbol">→</a>
    <a id="2317" href="foundation.base-changes-span-diagrams.html#1570" class="Function">codomain-span-diagram-base-change-span-diagram</a>
  <a id="2366" href="foundation.base-changes-span-diagrams.html#2205" class="Function">right-map-span-diagram-base-change-span-diagram</a> <a id="2414" class="Symbol">=</a>
    <a id="2420" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="2443" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a>

  <a id="2484" href="foundation.base-changes-span-diagrams.html#2484" class="Function">cartesian-hom-base-change-span-diagram</a> <a id="2523" class="Symbol">:</a>
    <a id="2529" href="foundation.cartesian-morphisms-span-diagrams.html#7979" class="Function">cartesian-hom-span-diagram</a> <a id="2556" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a> <a id="2594" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a>
  <a id="2598" href="foundation.base-changes-span-diagrams.html#2484" class="Function">cartesian-hom-base-change-span-diagram</a> <a id="2637" class="Symbol">=</a> <a id="2639" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2643" href="foundation.base-changes-span-diagrams.html#1238" class="Bound">f</a>

  <a id="2648" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a> <a id="2691" class="Symbol">:</a>
    <a id="2697" href="foundation.morphisms-span-diagrams.html#2435" class="Function">hom-span-diagram</a> <a id="2714" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a> <a id="2752" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a>
  <a id="2756" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a> <a id="2799" class="Symbol">=</a>
    <a id="2805" href="foundation.cartesian-morphisms-span-diagrams.html#8201" class="Function">hom-cartesian-hom-span-diagram</a>
      <a id="2842" class="Symbol">(</a> <a id="2844" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="2881" class="Symbol">)</a>
      <a id="2889" class="Symbol">(</a> <a id="2891" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="2892" class="Symbol">)</a>
      <a id="2900" class="Symbol">(</a> <a id="2902" href="foundation.base-changes-span-diagrams.html#2484" class="Function">cartesian-hom-base-change-span-diagram</a><a id="2940" class="Symbol">)</a>

  <a id="2945" href="foundation.base-changes-span-diagrams.html#2945" class="Function">map-domain-cartesian-hom-base-change-span-diagram</a> <a id="2995" class="Symbol">:</a>
    <a id="3001" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="3021" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a> <a id="3059" class="Symbol">→</a>
    <a id="3065" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="3085" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a>
  <a id="3089" href="foundation.base-changes-span-diagrams.html#2945" class="Function">map-domain-cartesian-hom-base-change-span-diagram</a> <a id="3139" class="Symbol">=</a>
    <a id="3145" href="foundation.morphisms-span-diagrams.html#2966" class="Function">map-domain-hom-span-diagram</a>
      <a id="3179" class="Symbol">(</a> <a id="3181" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="3218" class="Symbol">)</a>
      <a id="3226" class="Symbol">(</a> <a id="3228" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="3229" class="Symbol">)</a>
      <a id="3237" class="Symbol">(</a> <a id="3239" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="3281" class="Symbol">)</a>

  <a id="3286" href="foundation.base-changes-span-diagrams.html#3286" class="Function">map-codomain-cartesian-hom-base-change-span-diagram</a> <a id="3338" class="Symbol">:</a>
    <a id="3344" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="3366" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a> <a id="3404" class="Symbol">→</a>
    <a id="3410" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="3432" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a>
  <a id="3436" href="foundation.base-changes-span-diagrams.html#3286" class="Function">map-codomain-cartesian-hom-base-change-span-diagram</a> <a id="3488" class="Symbol">=</a>
    <a id="3494" href="foundation.morphisms-span-diagrams.html#3087" class="Function">map-codomain-hom-span-diagram</a>
      <a id="3530" class="Symbol">(</a> <a id="3532" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="3569" class="Symbol">)</a>
      <a id="3577" class="Symbol">(</a> <a id="3579" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="3580" class="Symbol">)</a>
      <a id="3588" class="Symbol">(</a> <a id="3590" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="3632" class="Symbol">)</a>

  <a id="3637" href="foundation.base-changes-span-diagrams.html#3637" class="Function">spanning-map-cartesian-hom-base-change-span-diagram</a> <a id="3689" class="Symbol">:</a>
    <a id="3695" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="3722" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a> <a id="3760" class="Symbol">→</a>
    <a id="3766" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="3793" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a>
  <a id="3797" href="foundation.base-changes-span-diagrams.html#3637" class="Function">spanning-map-cartesian-hom-base-change-span-diagram</a> <a id="3849" class="Symbol">=</a>
    <a id="3855" href="foundation.morphisms-span-diagrams.html#3469" class="Function">spanning-map-hom-span-diagram</a>
      <a id="3891" class="Symbol">(</a> <a id="3893" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="3930" class="Symbol">)</a>
      <a id="3938" class="Symbol">(</a> <a id="3940" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="3941" class="Symbol">)</a>
      <a id="3949" class="Symbol">(</a> <a id="3951" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="3993" class="Symbol">)</a>

  <a id="3998" href="foundation.base-changes-span-diagrams.html#3998" class="Function">left-square-cartesian-hom-base-change-span-diagram</a> <a id="4049" class="Symbol">:</a>
    <a id="4055" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="4083" class="Symbol">(</a> <a id="4085" href="foundation.base-changes-span-diagrams.html#3637" class="Function">spanning-map-cartesian-hom-base-change-span-diagram</a><a id="4136" class="Symbol">)</a>
      <a id="4144" class="Symbol">(</a> <a id="4146" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="4168" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="4205" class="Symbol">)</a>
      <a id="4213" class="Symbol">(</a> <a id="4215" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="4237" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="4238" class="Symbol">)</a>
      <a id="4246" class="Symbol">(</a> <a id="4248" href="foundation.base-changes-span-diagrams.html#2945" class="Function">map-domain-cartesian-hom-base-change-span-diagram</a><a id="4297" class="Symbol">)</a>
  <a id="4301" href="foundation.base-changes-span-diagrams.html#3998" class="Function">left-square-cartesian-hom-base-change-span-diagram</a> <a id="4352" class="Symbol">=</a>
    <a id="4358" href="foundation.morphisms-span-diagrams.html#3815" class="Function">left-square-hom-span-diagram</a>
      <a id="4393" class="Symbol">(</a> <a id="4395" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="4432" class="Symbol">)</a>
      <a id="4440" class="Symbol">(</a> <a id="4442" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="4443" class="Symbol">)</a>
      <a id="4451" class="Symbol">(</a> <a id="4453" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="4495" class="Symbol">)</a>

  <a id="4500" href="foundation.base-changes-span-diagrams.html#4500" class="Function">left-hom-arrow-cartesian-hom-base-change-span-diagram</a> <a id="4554" class="Symbol">:</a>
    <a id="4560" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a>
      <a id="4576" class="Symbol">(</a> <a id="4578" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="4600" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="4637" class="Symbol">)</a>
      <a id="4645" class="Symbol">(</a> <a id="4647" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="4669" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="4670" class="Symbol">)</a>
  <a id="4674" href="foundation.base-changes-span-diagrams.html#4500" class="Function">left-hom-arrow-cartesian-hom-base-change-span-diagram</a> <a id="4728" class="Symbol">=</a>
    <a id="4734" href="foundation.morphisms-span-diagrams.html#4273" class="Function">left-hom-arrow-hom-span-diagram</a>
      <a id="4772" class="Symbol">(</a> <a id="4774" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="4811" class="Symbol">)</a>
      <a id="4819" class="Symbol">(</a> <a id="4821" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="4822" class="Symbol">)</a>
      <a id="4830" class="Symbol">(</a> <a id="4832" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="4874" class="Symbol">)</a>

  <a id="4879" href="foundation.base-changes-span-diagrams.html#4879" class="Function">right-square-cartesian-hom-base-change-span-diagram</a> <a id="4931" class="Symbol">:</a>
    <a id="4937" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="4965" class="Symbol">(</a> <a id="4967" href="foundation.base-changes-span-diagrams.html#3637" class="Function">spanning-map-cartesian-hom-base-change-span-diagram</a><a id="5018" class="Symbol">)</a>
      <a id="5026" class="Symbol">(</a> <a id="5028" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="5051" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="5088" class="Symbol">)</a>
      <a id="5096" class="Symbol">(</a> <a id="5098" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="5121" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="5122" class="Symbol">)</a>
      <a id="5130" class="Symbol">(</a> <a id="5132" href="foundation.base-changes-span-diagrams.html#3286" class="Function">map-codomain-cartesian-hom-base-change-span-diagram</a><a id="5183" class="Symbol">)</a>
  <a id="5187" href="foundation.base-changes-span-diagrams.html#4879" class="Function">right-square-cartesian-hom-base-change-span-diagram</a> <a id="5239" class="Symbol">=</a>
    <a id="5245" href="foundation.morphisms-span-diagrams.html#4607" class="Function">right-square-hom-span-diagram</a>
      <a id="5281" class="Symbol">(</a> <a id="5283" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="5320" class="Symbol">)</a>
      <a id="5328" class="Symbol">(</a> <a id="5330" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="5331" class="Symbol">)</a>
      <a id="5339" class="Symbol">(</a> <a id="5341" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="5383" class="Symbol">)</a>

  <a id="5388" href="foundation.base-changes-span-diagrams.html#5388" class="Function">right-hom-arrow-cartesian-hom-base-change-span-diagram</a> <a id="5443" class="Symbol">:</a>
    <a id="5449" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a>
      <a id="5465" class="Symbol">(</a> <a id="5467" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="5490" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="5527" class="Symbol">)</a>
      <a id="5535" class="Symbol">(</a> <a id="5537" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="5560" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="5561" class="Symbol">)</a>
  <a id="5565" href="foundation.base-changes-span-diagrams.html#5388" class="Function">right-hom-arrow-cartesian-hom-base-change-span-diagram</a> <a id="5620" class="Symbol">=</a>
    <a id="5626" href="foundation.morphisms-span-diagrams.html#5072" class="Function">right-hom-arrow-hom-span-diagram</a>
      <a id="5665" class="Symbol">(</a> <a id="5667" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="5704" class="Symbol">)</a>
      <a id="5712" class="Symbol">(</a> <a id="5714" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="5715" class="Symbol">)</a>
      <a id="5723" class="Symbol">(</a> <a id="5725" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="5767" class="Symbol">)</a>

  <a id="5772" href="foundation.base-changes-span-diagrams.html#5772" class="Function">is-cartesian-cartesian-hom-base-change-span-diagram</a> <a id="5824" class="Symbol">:</a>
    <a id="5830" href="foundation.cartesian-morphisms-span-diagrams.html#7624" class="Function">is-cartesian-hom-span-diagram</a>
      <a id="5866" class="Symbol">(</a> <a id="5868" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="5905" class="Symbol">)</a>
      <a id="5913" class="Symbol">(</a> <a id="5915" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="5916" class="Symbol">)</a>
      <a id="5924" class="Symbol">(</a> <a id="5926" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="5968" class="Symbol">)</a>
  <a id="5972" href="foundation.base-changes-span-diagrams.html#5772" class="Function">is-cartesian-cartesian-hom-base-change-span-diagram</a> <a id="6024" class="Symbol">=</a>
    <a id="6030" href="foundation.cartesian-morphisms-span-diagrams.html#10169" class="Function">is-cartesian-cartesian-hom-span-diagram</a>
      <a id="6076" class="Symbol">(</a> <a id="6078" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="6115" class="Symbol">)</a>
      <a id="6123" class="Symbol">(</a> <a id="6125" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="6126" class="Symbol">)</a>
      <a id="6134" class="Symbol">(</a> <a id="6136" href="foundation.base-changes-span-diagrams.html#2484" class="Function">cartesian-hom-base-change-span-diagram</a><a id="6174" class="Symbol">)</a>

  <a id="6179" href="foundation.base-changes-span-diagrams.html#6179" class="Function">is-left-cartesian-cartesian-hom-base-change-span-diagram</a> <a id="6236" class="Symbol">:</a>
    <a id="6242" href="foundation.cartesian-morphisms-span-diagrams.html#1242" class="Function">is-left-cartesian-hom-span-diagram</a>
      <a id="6283" class="Symbol">(</a> <a id="6285" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="6322" class="Symbol">)</a>
      <a id="6330" class="Symbol">(</a> <a id="6332" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="6333" class="Symbol">)</a>
      <a id="6341" class="Symbol">(</a> <a id="6343" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="6385" class="Symbol">)</a>
  <a id="6389" href="foundation.base-changes-span-diagrams.html#6179" class="Function">is-left-cartesian-cartesian-hom-base-change-span-diagram</a> <a id="6446" class="Symbol">=</a>
    <a id="6452" href="foundation.cartesian-morphisms-span-diagrams.html#10339" class="Function">is-left-cartesian-cartesian-hom-span-diagram</a>
      <a id="6503" class="Symbol">(</a> <a id="6505" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="6542" class="Symbol">)</a>
      <a id="6550" class="Symbol">(</a> <a id="6552" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="6553" class="Symbol">)</a>
      <a id="6561" class="Symbol">(</a> <a id="6563" href="foundation.base-changes-span-diagrams.html#2484" class="Function">cartesian-hom-base-change-span-diagram</a><a id="6601" class="Symbol">)</a>

  <a id="6606" href="foundation.base-changes-span-diagrams.html#6606" class="Function">left-cartesian-hom-arrow-cartesian-hom-base-change-span-diagram</a> <a id="6670" class="Symbol">:</a>
    <a id="6676" href="foundation.cartesian-morphisms-arrows.html#3071" class="Function">cartesian-hom-arrow</a>
      <a id="6702" class="Symbol">(</a> <a id="6704" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="6726" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="6763" class="Symbol">)</a>
      <a id="6771" class="Symbol">(</a> <a id="6773" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="6795" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="6796" class="Symbol">)</a>
  <a id="6800" href="foundation.base-changes-span-diagrams.html#6606" class="Function">left-cartesian-hom-arrow-cartesian-hom-base-change-span-diagram</a> <a id="6864" class="Symbol">=</a>
    <a id="6870" href="foundation.cartesian-morphisms-span-diagrams.html#10568" class="Function">left-cartesian-hom-arrow-cartesian-hom-span-diagram</a>
      <a id="6928" class="Symbol">(</a> <a id="6930" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="6967" class="Symbol">)</a>
      <a id="6975" class="Symbol">(</a> <a id="6977" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="6978" class="Symbol">)</a>
      <a id="6986" class="Symbol">(</a> <a id="6988" href="foundation.base-changes-span-diagrams.html#2484" class="Function">cartesian-hom-base-change-span-diagram</a><a id="7026" class="Symbol">)</a>

  <a id="7031" href="foundation.base-changes-span-diagrams.html#7031" class="Function">is-right-cartesian-cartesian-hom-base-change-span-diagram</a> <a id="7089" class="Symbol">:</a>
    <a id="7095" href="foundation.cartesian-morphisms-span-diagrams.html#4409" class="Function">is-right-cartesian-hom-span-diagram</a>
      <a id="7137" class="Symbol">(</a> <a id="7139" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="7176" class="Symbol">)</a>
      <a id="7184" class="Symbol">(</a> <a id="7186" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="7187" class="Symbol">)</a>
      <a id="7195" class="Symbol">(</a> <a id="7197" href="foundation.base-changes-span-diagrams.html#2648" class="Function">hom-cartesian-hom-base-change-span-diagram</a><a id="7239" class="Symbol">)</a>
  <a id="7243" href="foundation.base-changes-span-diagrams.html#7031" class="Function">is-right-cartesian-cartesian-hom-base-change-span-diagram</a> <a id="7301" class="Symbol">=</a>
    <a id="7307" href="foundation.cartesian-morphisms-span-diagrams.html#10946" class="Function">is-right-cartesian-cartesian-hom-span-diagram</a>
      <a id="7359" class="Symbol">(</a> <a id="7361" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="7398" class="Symbol">)</a>
      <a id="7406" class="Symbol">(</a> <a id="7408" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="7409" class="Symbol">)</a>
      <a id="7417" class="Symbol">(</a> <a id="7419" href="foundation.base-changes-span-diagrams.html#2484" class="Function">cartesian-hom-base-change-span-diagram</a><a id="7457" class="Symbol">)</a>

  <a id="7462" href="foundation.base-changes-span-diagrams.html#7462" class="Function">right-cartesian-hom-arrow-cartesian-hom-base-change-span-diagram</a> <a id="7527" class="Symbol">:</a>
    <a id="7533" href="foundation.cartesian-morphisms-arrows.html#3071" class="Function">cartesian-hom-arrow</a>
      <a id="7559" class="Symbol">(</a> <a id="7561" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="7584" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="7621" class="Symbol">)</a>
      <a id="7629" class="Symbol">(</a> <a id="7631" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="7654" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="7655" class="Symbol">)</a>
  <a id="7659" href="foundation.base-changes-span-diagrams.html#7462" class="Function">right-cartesian-hom-arrow-cartesian-hom-base-change-span-diagram</a> <a id="7724" class="Symbol">=</a>
    <a id="7730" href="foundation.cartesian-morphisms-span-diagrams.html#11178" class="Function">right-cartesian-hom-arrow-cartesian-hom-span-diagram</a>
      <a id="7789" class="Symbol">(</a> <a id="7791" href="foundation.base-changes-span-diagrams.html#1290" class="Function">span-diagram-base-change-span-diagram</a><a id="7828" class="Symbol">)</a>
      <a id="7836" class="Symbol">(</a> <a id="7838" href="foundation.base-changes-span-diagrams.html#1208" class="Bound">𝒮</a><a id="7839" class="Symbol">)</a>
      <a id="7847" class="Symbol">(</a> <a id="7849" href="foundation.base-changes-span-diagrams.html#2484" class="Function">cartesian-hom-base-change-span-diagram</a><a id="7887" class="Symbol">)</a>
</pre>