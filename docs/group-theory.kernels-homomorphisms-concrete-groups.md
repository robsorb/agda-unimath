# Kernels of homomorphisms of concrete groups

<pre class="Agda"><a id="56" class="Keyword">module</a> <a id="63" href="group-theory.kernels-homomorphisms-concrete-groups.html" class="Module">group-theory.kernels-homomorphisms-concrete-groups</a> <a id="114" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="foundation.0-connected-types.html" class="Module">foundation.0-connected-types</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.1-types.html" class="Module">foundation.1-types</a>
<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="foundation.connected-components.html" class="Module">foundation.connected-components</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="368" class="Keyword">open</a> <a id="373" class="Keyword">import</a> <a id="380" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="396" class="Keyword">open</a> <a id="401" class="Keyword">import</a> <a id="408" href="foundation.truncated-maps.html" class="Module">foundation.truncated-maps</a>
<a id="434" class="Keyword">open</a> <a id="439" class="Keyword">import</a> <a id="446" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="475" class="Keyword">open</a> <a id="480" class="Keyword">import</a> <a id="487" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="515" class="Keyword">open</a> <a id="520" class="Keyword">import</a> <a id="527" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="556" class="Keyword">open</a> <a id="561" class="Keyword">import</a> <a id="568" href="group-theory.homomorphisms-concrete-groups.html" class="Module">group-theory.homomorphisms-concrete-groups</a>

<a id="612" class="Keyword">open</a> <a id="617" class="Keyword">import</a> <a id="624" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>

<a id="659" class="Keyword">open</a> <a id="664" class="Keyword">import</a> <a id="671" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The kernel of a concrete group homomorphism `Bf : BG →∗ BH` is the connected
component at the base point of the fiber of `Bf`.

## Definition

<pre class="Agda"><a id="879" class="Keyword">module</a> <a id="886" href="group-theory.kernels-homomorphisms-concrete-groups.html#886" class="Module">_</a>
  <a id="890" class="Symbol">{</a><a id="891" href="group-theory.kernels-homomorphisms-concrete-groups.html#891" class="Bound">l1</a> <a id="894" href="group-theory.kernels-homomorphisms-concrete-groups.html#894" class="Bound">l2</a> <a id="897" class="Symbol">:</a> <a id="899" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="904" class="Symbol">}</a> <a id="906" class="Symbol">(</a><a id="907" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a> <a id="909" class="Symbol">:</a> <a id="911" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="926" href="group-theory.kernels-homomorphisms-concrete-groups.html#891" class="Bound">l1</a><a id="928" class="Symbol">)</a> <a id="930" class="Symbol">(</a><a id="931" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a> <a id="933" class="Symbol">:</a> <a id="935" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="950" href="group-theory.kernels-homomorphisms-concrete-groups.html#894" class="Bound">l2</a><a id="952" class="Symbol">)</a>
  <a id="956" class="Symbol">(</a><a id="957" href="group-theory.kernels-homomorphisms-concrete-groups.html#957" class="Bound">f</a> <a id="959" class="Symbol">:</a> <a id="961" href="group-theory.homomorphisms-concrete-groups.html#678" class="Function">hom-Concrete-Group</a> <a id="980" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a> <a id="982" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a><a id="983" class="Symbol">)</a>
  <a id="987" class="Keyword">where</a>

  <a id="996" href="group-theory.kernels-homomorphisms-concrete-groups.html#996" class="Function">classifying-type-kernel-hom-Concrete-Group</a> <a id="1039" class="Symbol">:</a> <a id="1041" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1044" class="Symbol">(</a><a id="1045" href="group-theory.kernels-homomorphisms-concrete-groups.html#891" class="Bound">l1</a> <a id="1048" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1050" href="group-theory.kernels-homomorphisms-concrete-groups.html#894" class="Bound">l2</a><a id="1052" class="Symbol">)</a>
  <a id="1056" href="group-theory.kernels-homomorphisms-concrete-groups.html#996" class="Function">classifying-type-kernel-hom-Concrete-Group</a> <a id="1099" class="Symbol">=</a>
    <a id="1105" href="foundation.connected-components.html#1754" class="Function">connected-component</a>
      <a id="1131" class="Symbol">(</a> <a id="1133" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a>
        <a id="1147" class="Symbol">(</a> <a id="1149" href="group-theory.homomorphisms-concrete-groups.html#1274" class="Function">classifying-map-hom-Concrete-Group</a> <a id="1184" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a> <a id="1186" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a> <a id="1188" href="group-theory.kernels-homomorphisms-concrete-groups.html#957" class="Bound">f</a><a id="1189" class="Symbol">)</a>
        <a id="1199" class="Symbol">(</a> <a id="1201" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="1222" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a><a id="1223" class="Symbol">))</a>
      <a id="1232" class="Symbol">(</a> <a id="1234" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a>
        <a id="1247" class="Symbol">(</a> <a id="1249" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="1270" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a><a id="1271" class="Symbol">)</a>
        <a id="1281" class="Symbol">(</a> <a id="1283" href="group-theory.homomorphisms-concrete-groups.html#1552" class="Function">preserves-point-classifying-map-hom-Concrete-Group</a> <a id="1334" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a> <a id="1336" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a> <a id="1338" href="group-theory.kernels-homomorphisms-concrete-groups.html#957" class="Bound">f</a><a id="1339" class="Symbol">))</a>

  <a id="1345" href="group-theory.kernels-homomorphisms-concrete-groups.html#1345" class="Function">shape-kernel-hom-Concrete-Group</a> <a id="1377" class="Symbol">:</a>
    <a id="1383" href="group-theory.kernels-homomorphisms-concrete-groups.html#996" class="Function">classifying-type-kernel-hom-Concrete-Group</a>
  <a id="1428" href="group-theory.kernels-homomorphisms-concrete-groups.html#1345" class="Function">shape-kernel-hom-Concrete-Group</a> <a id="1460" class="Symbol">=</a>
    <a id="1466" href="foundation.connected-components.html#1832" class="Function">point-connected-component</a>
      <a id="1498" class="Symbol">(</a> <a id="1500" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a>
        <a id="1514" class="Symbol">(</a> <a id="1516" href="group-theory.homomorphisms-concrete-groups.html#1274" class="Function">classifying-map-hom-Concrete-Group</a> <a id="1551" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a> <a id="1553" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a> <a id="1555" href="group-theory.kernels-homomorphisms-concrete-groups.html#957" class="Bound">f</a><a id="1556" class="Symbol">)</a>
        <a id="1566" class="Symbol">(</a> <a id="1568" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="1589" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a><a id="1590" class="Symbol">))</a>
      <a id="1599" class="Symbol">(</a> <a id="1601" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="1622" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a>
        <a id="1632" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1634" href="group-theory.homomorphisms-concrete-groups.html#1552" class="Function">preserves-point-classifying-map-hom-Concrete-Group</a> <a id="1685" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a> <a id="1687" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a> <a id="1689" href="group-theory.kernels-homomorphisms-concrete-groups.html#957" class="Bound">f</a><a id="1690" class="Symbol">)</a>

  <a id="1695" href="group-theory.kernels-homomorphisms-concrete-groups.html#1695" class="Function">classifying-pointed-type-kernel-hom-Concrete-Group</a> <a id="1746" class="Symbol">:</a> <a id="1748" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1761" class="Symbol">(</a><a id="1762" href="group-theory.kernels-homomorphisms-concrete-groups.html#891" class="Bound">l1</a> <a id="1765" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1767" href="group-theory.kernels-homomorphisms-concrete-groups.html#894" class="Bound">l2</a><a id="1769" class="Symbol">)</a>
  <a id="1773" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1777" href="group-theory.kernels-homomorphisms-concrete-groups.html#1695" class="Function">classifying-pointed-type-kernel-hom-Concrete-Group</a> <a id="1828" class="Symbol">=</a>
    <a id="1834" href="group-theory.kernels-homomorphisms-concrete-groups.html#996" class="Function">classifying-type-kernel-hom-Concrete-Group</a>
  <a id="1879" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1883" href="group-theory.kernels-homomorphisms-concrete-groups.html#1695" class="Function">classifying-pointed-type-kernel-hom-Concrete-Group</a> <a id="1934" class="Symbol">=</a>
    <a id="1940" href="group-theory.kernels-homomorphisms-concrete-groups.html#1345" class="Function">shape-kernel-hom-Concrete-Group</a>

  <a id="1975" href="group-theory.kernels-homomorphisms-concrete-groups.html#1975" class="Function">is-0-connected-classifying-type-kernel-hom-Concrete-Group</a> <a id="2033" class="Symbol">:</a>
    <a id="2039" href="foundation.0-connected-types.html#1548" class="Function">is-0-connected</a> <a id="2054" href="group-theory.kernels-homomorphisms-concrete-groups.html#996" class="Function">classifying-type-kernel-hom-Concrete-Group</a>
  <a id="2099" href="group-theory.kernels-homomorphisms-concrete-groups.html#1975" class="Function">is-0-connected-classifying-type-kernel-hom-Concrete-Group</a> <a id="2157" class="Symbol">=</a>
    <a id="2163" href="foundation.connected-components.html#2500" class="Function">is-0-connected-connected-component</a> <a id="2198" class="Symbol">_</a> <a id="2200" class="Symbol">_</a>

  <a id="2205" href="group-theory.kernels-homomorphisms-concrete-groups.html#2205" class="Function">is-1-type-classifying-type-kernel-hom-Concrete-Group</a> <a id="2258" class="Symbol">:</a>
    <a id="2264" href="foundation-core.1-types.html#559" class="Function">is-1-type</a> <a id="2274" href="group-theory.kernels-homomorphisms-concrete-groups.html#996" class="Function">classifying-type-kernel-hom-Concrete-Group</a>
  <a id="2319" href="group-theory.kernels-homomorphisms-concrete-groups.html#2205" class="Function">is-1-type-classifying-type-kernel-hom-Concrete-Group</a> <a id="2372" class="Symbol">=</a>
    <a id="2378" href="foundation.connected-components.html#3345" class="Function">is-trunc-connected-component</a> <a id="2407" class="Symbol">_</a> <a id="2409" class="Symbol">_</a>
      <a id="2417" class="Symbol">(</a> <a id="2419" href="foundation-core.truncated-maps.html#5078" class="Function">is-trunc-map-is-trunc-domain-codomain</a>
        <a id="2465" class="Symbol">(</a> <a id="2467" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a><a id="2472" class="Symbol">)</a>
        <a id="2482" class="Symbol">(</a> <a id="2484" href="group-theory.concrete-groups.html#2840" class="Function">is-1-type-classifying-type-Concrete-Group</a> <a id="2526" href="group-theory.kernels-homomorphisms-concrete-groups.html#907" class="Bound">G</a><a id="2527" class="Symbol">)</a>
        <a id="2537" class="Symbol">(</a> <a id="2539" href="group-theory.concrete-groups.html#2840" class="Function">is-1-type-classifying-type-Concrete-Group</a> <a id="2581" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a><a id="2582" class="Symbol">)</a>
        <a id="2592" class="Symbol">(</a> <a id="2594" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="2615" href="group-theory.kernels-homomorphisms-concrete-groups.html#931" class="Bound">H</a><a id="2616" class="Symbol">))</a>

  <a id="2622" href="group-theory.kernels-homomorphisms-concrete-groups.html#2622" class="Function">∞-group-kernel-hom-Concrete-Group</a> <a id="2656" class="Symbol">:</a> <a id="2658" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="2666" class="Symbol">(</a><a id="2667" href="group-theory.kernels-homomorphisms-concrete-groups.html#891" class="Bound">l1</a> <a id="2670" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2672" href="group-theory.kernels-homomorphisms-concrete-groups.html#894" class="Bound">l2</a><a id="2674" class="Symbol">)</a>
  <a id="2678" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2682" href="group-theory.kernels-homomorphisms-concrete-groups.html#2622" class="Function">∞-group-kernel-hom-Concrete-Group</a> <a id="2716" class="Symbol">=</a>
    <a id="2722" href="group-theory.kernels-homomorphisms-concrete-groups.html#1695" class="Function">classifying-pointed-type-kernel-hom-Concrete-Group</a>
  <a id="2775" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2779" href="group-theory.kernels-homomorphisms-concrete-groups.html#2622" class="Function">∞-group-kernel-hom-Concrete-Group</a> <a id="2813" class="Symbol">=</a>
    <a id="2819" href="group-theory.kernels-homomorphisms-concrete-groups.html#1975" class="Function">is-0-connected-classifying-type-kernel-hom-Concrete-Group</a>

  <a id="2880" href="group-theory.kernels-homomorphisms-concrete-groups.html#2880" class="Function">type-kernel-hom-Concrete-Group</a> <a id="2911" class="Symbol">:</a> <a id="2913" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2916" class="Symbol">(</a><a id="2917" href="group-theory.kernels-homomorphisms-concrete-groups.html#891" class="Bound">l1</a> <a id="2920" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2922" href="group-theory.kernels-homomorphisms-concrete-groups.html#894" class="Bound">l2</a><a id="2924" class="Symbol">)</a>
  <a id="2928" href="group-theory.kernels-homomorphisms-concrete-groups.html#2880" class="Function">type-kernel-hom-Concrete-Group</a> <a id="2959" class="Symbol">=</a>
    <a id="2965" href="higher-group-theory.higher-groups.html#3080" class="Function">type-∞-Group</a> <a id="2978" href="group-theory.kernels-homomorphisms-concrete-groups.html#2622" class="Function">∞-group-kernel-hom-Concrete-Group</a>

  <a id="3015" href="group-theory.kernels-homomorphisms-concrete-groups.html#3015" class="Function">is-set-type-kernel-hom-Concrete-Group</a> <a id="3053" class="Symbol">:</a>
    <a id="3059" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="3066" href="group-theory.kernels-homomorphisms-concrete-groups.html#2880" class="Function">type-kernel-hom-Concrete-Group</a>
  <a id="3099" href="group-theory.kernels-homomorphisms-concrete-groups.html#3015" class="Function">is-set-type-kernel-hom-Concrete-Group</a> <a id="3137" class="Symbol">=</a>
    <a id="3143" href="group-theory.kernels-homomorphisms-concrete-groups.html#2205" class="Function">is-1-type-classifying-type-kernel-hom-Concrete-Group</a>
      <a id="3202" href="group-theory.kernels-homomorphisms-concrete-groups.html#1345" class="Function">shape-kernel-hom-Concrete-Group</a>
      <a id="3240" href="group-theory.kernels-homomorphisms-concrete-groups.html#1345" class="Function">shape-kernel-hom-Concrete-Group</a>

  <a id="3275" href="group-theory.kernels-homomorphisms-concrete-groups.html#3275" class="Function">concrete-group-kernel-hom-Concrete-Group</a> <a id="3316" class="Symbol">:</a> <a id="3318" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="3333" class="Symbol">(</a><a id="3334" href="group-theory.kernels-homomorphisms-concrete-groups.html#891" class="Bound">l1</a> <a id="3337" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3339" href="group-theory.kernels-homomorphisms-concrete-groups.html#894" class="Bound">l2</a><a id="3341" class="Symbol">)</a>
  <a id="3345" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3349" href="group-theory.kernels-homomorphisms-concrete-groups.html#3275" class="Function">concrete-group-kernel-hom-Concrete-Group</a> <a id="3390" class="Symbol">=</a>
    <a id="3396" href="group-theory.kernels-homomorphisms-concrete-groups.html#2622" class="Function">∞-group-kernel-hom-Concrete-Group</a>
  <a id="3432" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3436" href="group-theory.kernels-homomorphisms-concrete-groups.html#3275" class="Function">concrete-group-kernel-hom-Concrete-Group</a> <a id="3477" class="Symbol">=</a>
    <a id="3483" href="group-theory.kernels-homomorphisms-concrete-groups.html#3015" class="Function">is-set-type-kernel-hom-Concrete-Group</a>
</pre>