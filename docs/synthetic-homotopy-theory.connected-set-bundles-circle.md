# Connected set bundles over the circle

<pre class="Agda"><a id="50" class="Keyword">module</a> <a id="57" href="synthetic-homotopy-theory.connected-set-bundles-circle.html" class="Module">synthetic-homotopy-theory.connected-set-bundles-circle</a> <a id="112" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.0-connected-types.html" class="Module">foundation.0-connected-types</a>
<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="402" class="Keyword">open</a> <a id="407" class="Keyword">import</a> <a id="414" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="441" class="Keyword">open</a> <a id="446" class="Keyword">import</a> <a id="453" href="foundation.mere-equality.html" class="Module">foundation.mere-equality</a>
<a id="478" class="Keyword">open</a> <a id="483" class="Keyword">import</a> <a id="490" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="514" class="Keyword">open</a> <a id="519" class="Keyword">import</a> <a id="526" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="542" class="Keyword">open</a> <a id="547" class="Keyword">import</a> <a id="554" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="574" class="Keyword">open</a> <a id="579" class="Keyword">import</a> <a id="586" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="613" class="Keyword">open</a> <a id="618" class="Keyword">import</a> <a id="625" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="668" class="Keyword">open</a> <a id="673" class="Keyword">import</a> <a id="680" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="708" class="Keyword">open</a> <a id="713" class="Keyword">import</a> <a id="720" href="higher-group-theory.transitive-higher-group-actions.html" class="Module">higher-group-theory.transitive-higher-group-actions</a>

<a id="773" class="Keyword">open</a> <a id="778" class="Keyword">import</a> <a id="785" href="structured-types.sets-equipped-with-automorphisms.html" class="Module">structured-types.sets-equipped-with-automorphisms</a>

<a id="836" class="Keyword">open</a> <a id="841" class="Keyword">import</a> <a id="848" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
</pre>
</details>

## Idea

A **connected set bundle** over the
[circle](synthetic-homotopy-theory.circle.md) is a family of sets `X : 𝕊¹ → Set`
such that the total space `Σ 𝕊¹ (type-Set ∘ X)` is
[connected](foundation.connected-types.md). The connected set bundles over the
circle form a [large category](category-theory.large-categories.md), which can
be thought of as the categorification of the [poset](order-theory.posets.md) of
[natural numbers ordered by divisibility](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).

## Definitions

### The predicate of being a connected set bundle over the circle

<pre class="Agda"><a id="is-connected-prop-set-bundle-𝕊¹"></a><a id="1526" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1526" class="Function">is-connected-prop-set-bundle-𝕊¹</a> <a id="1558" class="Symbol">:</a>
  <a id="1562" class="Symbol">{</a><a id="1563" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1563" class="Bound">l</a> <a id="1565" class="Symbol">:</a> <a id="1567" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1572" class="Symbol">}</a> <a id="1574" class="Symbol">→</a> <a id="1576" class="Symbol">(</a><a id="1577" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a> <a id="1580" class="Symbol">→</a> <a id="1582" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1586" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1563" class="Bound">l</a><a id="1587" class="Symbol">)</a> <a id="1589" class="Symbol">→</a> <a id="1591" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1596" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1563" class="Bound">l</a>
<a id="1598" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1526" class="Function">is-connected-prop-set-bundle-𝕊¹</a> <a id="1630" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1630" class="Bound">X</a> <a id="1632" class="Symbol">=</a>
  <a id="1636" href="foundation.0-connected-types.html#1440" class="Function">is-0-connected-Prop</a> <a id="1656" class="Symbol">(</a><a id="1657" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1659" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a> <a id="1662" class="Symbol">(</a><a id="1663" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1672" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1674" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1630" class="Bound">X</a><a id="1675" class="Symbol">))</a>

<a id="is-connected-set-bundle-𝕊¹"></a><a id="1679" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1679" class="Function">is-connected-set-bundle-𝕊¹</a> <a id="1706" class="Symbol">:</a> <a id="1708" class="Symbol">{</a><a id="1709" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1709" class="Bound">l</a> <a id="1711" class="Symbol">:</a> <a id="1713" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1718" class="Symbol">}</a> <a id="1720" class="Symbol">(</a><a id="1721" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1721" class="Bound">X</a> <a id="1723" class="Symbol">:</a> <a id="1725" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a> <a id="1728" class="Symbol">→</a> <a id="1730" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1734" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1709" class="Bound">l</a><a id="1735" class="Symbol">)</a> <a id="1737" class="Symbol">→</a> <a id="1739" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1742" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1709" class="Bound">l</a>
<a id="1744" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1679" class="Function">is-connected-set-bundle-𝕊¹</a> <a id="1771" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1771" class="Bound">X</a> <a id="1773" class="Symbol">=</a>
  <a id="1777" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1787" class="Symbol">(</a><a id="1788" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1526" class="Function">is-connected-prop-set-bundle-𝕊¹</a> <a id="1820" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1771" class="Bound">X</a><a id="1821" class="Symbol">)</a>

<a id="is-prop-is-connected-set-bundle-𝕊¹"></a><a id="1824" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1824" class="Function">is-prop-is-connected-set-bundle-𝕊¹</a> <a id="1859" class="Symbol">:</a>
  <a id="1863" class="Symbol">{</a><a id="1864" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1864" class="Bound">l</a> <a id="1866" class="Symbol">:</a> <a id="1868" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1873" class="Symbol">}</a> <a id="1875" class="Symbol">(</a><a id="1876" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1876" class="Bound">X</a> <a id="1878" class="Symbol">:</a> <a id="1880" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a> <a id="1883" class="Symbol">→</a> <a id="1885" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1889" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1864" class="Bound">l</a><a id="1890" class="Symbol">)</a> <a id="1892" class="Symbol">→</a> <a id="1894" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1902" class="Symbol">(</a><a id="1903" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1679" class="Function">is-connected-set-bundle-𝕊¹</a> <a id="1930" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1876" class="Bound">X</a><a id="1931" class="Symbol">)</a>
<a id="1933" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1824" class="Function">is-prop-is-connected-set-bundle-𝕊¹</a> <a id="1968" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1968" class="Bound">X</a> <a id="1970" class="Symbol">=</a>
  <a id="1974" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1992" class="Symbol">(</a><a id="1993" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1526" class="Function">is-connected-prop-set-bundle-𝕊¹</a> <a id="2025" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1968" class="Bound">X</a><a id="2026" class="Symbol">)</a>
</pre>
### Connected set bundles over the circle

<pre class="Agda"><a id="connected-set-bundle-𝕊¹"></a><a id="2084" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2084" class="Function">connected-set-bundle-𝕊¹</a> <a id="2108" class="Symbol">:</a> <a id="2110" class="Symbol">(</a><a id="2111" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2111" class="Bound">l</a> <a id="2113" class="Symbol">:</a> <a id="2115" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2120" class="Symbol">)</a> <a id="2122" class="Symbol">→</a> <a id="2124" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2127" class="Symbol">(</a><a id="2128" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2133" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2111" class="Bound">l</a><a id="2134" class="Symbol">)</a>
<a id="2136" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2084" class="Function">connected-set-bundle-𝕊¹</a> <a id="2160" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2160" class="Bound">l</a> <a id="2162" class="Symbol">=</a> <a id="2164" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="2177" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1526" class="Function">is-connected-prop-set-bundle-𝕊¹</a>

<a id="2210" class="Keyword">module</a> <a id="2217" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2217" class="Module">_</a>
  <a id="2221" class="Symbol">{</a><a id="2222" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a> <a id="2224" class="Symbol">:</a> <a id="2226" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2231" class="Symbol">}</a> <a id="2233" class="Symbol">(</a><a id="2234" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2234" class="Bound">X</a> <a id="2236" class="Symbol">:</a> <a id="2238" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2084" class="Function">connected-set-bundle-𝕊¹</a> <a id="2262" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a><a id="2263" class="Symbol">)</a>
  <a id="2267" class="Keyword">where</a>

  <a id="2276" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2276" class="Function">set-bundle-connected-set-bundle-𝕊¹</a> <a id="2311" class="Symbol">:</a> <a id="2313" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a> <a id="2316" class="Symbol">→</a> <a id="2318" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="2322" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a>
  <a id="2326" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2276" class="Function">set-bundle-connected-set-bundle-𝕊¹</a> <a id="2361" class="Symbol">=</a> <a id="2363" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2367" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2234" class="Bound">X</a>

  <a id="2372" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2372" class="Function">bundle-connected-set-bundle-𝕊¹</a> <a id="2403" class="Symbol">:</a> <a id="2405" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a> <a id="2408" class="Symbol">→</a> <a id="2410" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2413" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a>
  <a id="2417" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2372" class="Function">bundle-connected-set-bundle-𝕊¹</a> <a id="2448" class="Symbol">=</a>
    <a id="2454" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="2463" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2465" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2276" class="Function">set-bundle-connected-set-bundle-𝕊¹</a>

  <a id="2503" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2503" class="Function">set-connected-set-bundle-𝕊¹</a> <a id="2531" class="Symbol">:</a> <a id="2533" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="2537" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a>
  <a id="2541" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2503" class="Function">set-connected-set-bundle-𝕊¹</a> <a id="2569" class="Symbol">=</a>
    <a id="2575" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2276" class="Function">set-bundle-connected-set-bundle-𝕊¹</a> <a id="2610" href="synthetic-homotopy-theory.circle.html#1854" class="Postulate">base-𝕊¹</a>

  <a id="2621" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2621" class="Function">type-connected-set-bundle-𝕊¹</a> <a id="2650" class="Symbol">:</a> <a id="2652" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2655" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a>
  <a id="2659" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2621" class="Function">type-connected-set-bundle-𝕊¹</a> <a id="2688" class="Symbol">=</a> <a id="2690" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="2699" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2503" class="Function">set-connected-set-bundle-𝕊¹</a>

  <a id="2730" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2730" class="Function">total-space-connected-set-bundle-𝕊¹</a> <a id="2766" class="Symbol">:</a> <a id="2768" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2771" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a>
  <a id="2775" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2730" class="Function">total-space-connected-set-bundle-𝕊¹</a> <a id="2811" class="Symbol">=</a> <a id="2813" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2815" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a> <a id="2818" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2372" class="Function">bundle-connected-set-bundle-𝕊¹</a>

  <a id="2852" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2852" class="Function">is-connected-connected-set-bundle-𝕊¹</a> <a id="2889" class="Symbol">:</a>
    <a id="2895" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#1679" class="Function">is-connected-set-bundle-𝕊¹</a> <a id="2922" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2276" class="Function">set-bundle-connected-set-bundle-𝕊¹</a>
  <a id="2959" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2852" class="Function">is-connected-connected-set-bundle-𝕊¹</a> <a id="2996" class="Symbol">=</a> <a id="2998" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3002" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2234" class="Bound">X</a>

  <a id="3007" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3007" class="Function">mere-eq-total-space-connected-set-bundle-𝕊¹</a> <a id="3051" class="Symbol">:</a>
    <a id="3057" class="Symbol">(</a><a id="3058" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3058" class="Bound">x</a> <a id="3060" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3060" class="Bound">y</a> <a id="3062" class="Symbol">:</a> <a id="3064" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2730" class="Function">total-space-connected-set-bundle-𝕊¹</a><a id="3099" class="Symbol">)</a> <a id="3101" class="Symbol">→</a>
    <a id="3107" href="foundation.mere-equality.html#1412" class="Function">mere-eq</a> <a id="3115" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3058" class="Bound">x</a> <a id="3117" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3060" class="Bound">y</a>
  <a id="3121" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3007" class="Function">mere-eq-total-space-connected-set-bundle-𝕊¹</a> <a id="3165" class="Symbol">=</a>
    <a id="3171" href="foundation.0-connected-types.html#2066" class="Function">mere-eq-is-0-connected</a> <a id="3194" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2852" class="Function">is-connected-connected-set-bundle-𝕊¹</a>

  <a id="3234" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3234" class="Function">transitive-action-connected-set-bundle-𝕊¹</a> <a id="3276" class="Symbol">:</a>
    <a id="3282" href="higher-group-theory.transitive-higher-group-actions.html#3652" class="Function">transitive-action-∞-Group</a> <a id="3308" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a> <a id="3310" href="synthetic-homotopy-theory.circle.html#6018" class="Function">𝕊¹-∞-Group</a>
  <a id="3323" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3327" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3234" class="Function">transitive-action-connected-set-bundle-𝕊¹</a> <a id="3369" class="Symbol">=</a>
    <a id="3375" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2372" class="Function">bundle-connected-set-bundle-𝕊¹</a>
  <a id="3408" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3412" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3234" class="Function">transitive-action-connected-set-bundle-𝕊¹</a> <a id="3454" class="Symbol">=</a>
    <a id="3460" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2852" class="Function">is-connected-connected-set-bundle-𝕊¹</a>

  <a id="3500" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3500" class="Function">is-abstractly-transitive-action-connected-set-bundle-𝕊¹</a> <a id="3556" class="Symbol">:</a>
    <a id="3562" href="higher-group-theory.transitive-higher-group-actions.html#3220" class="Function">is-abstractly-transitive-action-∞-Group</a>
      <a id="3608" class="Symbol">(</a> <a id="3610" href="synthetic-homotopy-theory.circle.html#6018" class="Function">𝕊¹-∞-Group</a><a id="3620" class="Symbol">)</a>
      <a id="3628" class="Symbol">(</a> <a id="3630" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2372" class="Function">bundle-connected-set-bundle-𝕊¹</a><a id="3660" class="Symbol">)</a>
  <a id="3664" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3500" class="Function">is-abstractly-transitive-action-connected-set-bundle-𝕊¹</a> <a id="3720" class="Symbol">=</a>
    <a id="3726" href="higher-group-theory.transitive-higher-group-actions.html#8556" class="Function">is-abstractly-transitive-transitive-action-∞-Group</a>
      <a id="3783" class="Symbol">(</a> <a id="3785" href="synthetic-homotopy-theory.circle.html#6018" class="Function">𝕊¹-∞-Group</a><a id="3795" class="Symbol">)</a>
      <a id="3803" class="Symbol">(</a> <a id="3805" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3234" class="Function">transitive-action-connected-set-bundle-𝕊¹</a><a id="3846" class="Symbol">)</a>

  <a id="3851" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3851" class="Function">is-inhabited-connected-set-bundle-𝕊¹</a> <a id="3888" class="Symbol">:</a>
    <a id="3894" href="foundation.inhabited-types.html#1345" class="Function">is-inhabited</a> <a id="3907" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2621" class="Function">type-connected-set-bundle-𝕊¹</a>
  <a id="3938" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3851" class="Function">is-inhabited-connected-set-bundle-𝕊¹</a> <a id="3975" class="Symbol">=</a>
    <a id="3981" href="higher-group-theory.transitive-higher-group-actions.html#8020" class="Function">is-inhabited-transitive-action-∞-Group</a>
      <a id="4026" class="Symbol">(</a> <a id="4028" href="synthetic-homotopy-theory.circle.html#6018" class="Function">𝕊¹-∞-Group</a><a id="4038" class="Symbol">)</a>
      <a id="4046" class="Symbol">(</a> <a id="4048" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3234" class="Function">transitive-action-connected-set-bundle-𝕊¹</a><a id="4089" class="Symbol">)</a>

  <a id="4094" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4094" class="Function">is-surjective-tr-connected-set-bundle-𝕊¹</a> <a id="4135" class="Symbol">:</a>
    <a id="4141" class="Symbol">(</a><a id="4142" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4142" class="Bound">t</a> <a id="4144" class="Symbol">:</a> <a id="4146" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a><a id="4148" class="Symbol">)</a> <a id="4150" class="Symbol">(</a><a id="4151" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4151" class="Bound">x</a> <a id="4153" class="Symbol">:</a> <a id="4155" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2621" class="Function">type-connected-set-bundle-𝕊¹</a><a id="4183" class="Symbol">)</a> <a id="4185" class="Symbol">→</a>
    <a id="4191" href="foundation.surjective-maps.html#2524" class="Function">is-surjective</a> <a id="4205" class="Symbol">(λ</a> <a id="4208" class="Symbol">(</a><a id="4209" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4209" class="Bound">p</a> <a id="4211" class="Symbol">:</a> <a id="4213" href="synthetic-homotopy-theory.circle.html#1854" class="Postulate">base-𝕊¹</a> <a id="4221" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="4223" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4142" class="Bound">t</a><a id="4224" class="Symbol">)</a> <a id="4226" class="Symbol">→</a> <a id="4228" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a> <a id="4231" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2372" class="Function">bundle-connected-set-bundle-𝕊¹</a> <a id="4262" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4209" class="Bound">p</a> <a id="4264" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4151" class="Bound">x</a><a id="4265" class="Symbol">)</a>
  <a id="4269" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4094" class="Function">is-surjective-tr-connected-set-bundle-𝕊¹</a> <a id="4310" class="Symbol">=</a>
    <a id="4316" href="higher-group-theory.transitive-higher-group-actions.html#5351" class="Function">is-surjective-tr-is-abstractly-transitive-action-∞-Group</a>
      <a id="4379" class="Symbol">(</a> <a id="4381" href="synthetic-homotopy-theory.circle.html#6018" class="Function">𝕊¹-∞-Group</a><a id="4391" class="Symbol">)</a>
      <a id="4399" class="Symbol">(</a> <a id="4401" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2372" class="Function">bundle-connected-set-bundle-𝕊¹</a><a id="4431" class="Symbol">)</a>
      <a id="4439" class="Symbol">(</a> <a id="4441" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3500" class="Function">is-abstractly-transitive-action-connected-set-bundle-𝕊¹</a><a id="4496" class="Symbol">)</a>

  <a id="4501" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4501" class="Function">inhabited-type-connected-set-bundle-𝕊¹</a> <a id="4540" class="Symbol">:</a> <a id="4542" href="foundation.inhabited-types.html#1583" class="Function">Inhabited-Type</a> <a id="4557" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a>
  <a id="4561" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4501" class="Function">inhabited-type-connected-set-bundle-𝕊¹</a> <a id="4600" class="Symbol">=</a>
    <a id="4606" href="higher-group-theory.transitive-higher-group-actions.html#8308" class="Function">inhabited-type-transitive-action-∞-Group</a>
      <a id="4653" class="Symbol">(</a> <a id="4655" href="synthetic-homotopy-theory.circle.html#6018" class="Function">𝕊¹-∞-Group</a><a id="4665" class="Symbol">)</a>
      <a id="4673" class="Symbol">(</a> <a id="4675" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#3234" class="Function">transitive-action-connected-set-bundle-𝕊¹</a><a id="4716" class="Symbol">)</a>

  <a id="4721" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4721" class="Function">aut-connected-set-bundle-𝕊¹</a> <a id="4749" class="Symbol">:</a> <a id="4751" href="foundation.automorphisms.html#538" class="Function">Aut</a> <a id="4755" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2621" class="Function">type-connected-set-bundle-𝕊¹</a>
  <a id="4786" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4721" class="Function">aut-connected-set-bundle-𝕊¹</a> <a id="4814" class="Symbol">=</a>
    <a id="4820" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="4829" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2372" class="Function">bundle-connected-set-bundle-𝕊¹</a> <a id="4860" href="synthetic-homotopy-theory.circle.html#1880" class="Postulate">loop-𝕊¹</a>

  <a id="4871" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4871" class="Function">map-aut-connected-set-bundle-𝕊¹</a> <a id="4903" class="Symbol">:</a>
    <a id="4909" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2621" class="Function">type-connected-set-bundle-𝕊¹</a> <a id="4938" class="Symbol">→</a> <a id="4940" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2621" class="Function">type-connected-set-bundle-𝕊¹</a>
  <a id="4971" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4871" class="Function">map-aut-connected-set-bundle-𝕊¹</a> <a id="5003" class="Symbol">=</a>
    <a id="5009" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="5019" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4721" class="Function">aut-connected-set-bundle-𝕊¹</a>

  <a id="5050" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#5050" class="Function">set-with-automorphism-connected-set-bundle-𝕊¹</a> <a id="5096" class="Symbol">:</a> <a id="5098" href="structured-types.sets-equipped-with-automorphisms.html#632" class="Function">Set-With-Automorphism</a> <a id="5120" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2222" class="Bound">l</a>
  <a id="5124" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5128" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#5050" class="Function">set-with-automorphism-connected-set-bundle-𝕊¹</a> <a id="5174" class="Symbol">=</a>
    <a id="5180" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#2503" class="Function">set-connected-set-bundle-𝕊¹</a>
  <a id="5210" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5214" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#5050" class="Function">set-with-automorphism-connected-set-bundle-𝕊¹</a> <a id="5260" class="Symbol">=</a>
    <a id="5266" href="synthetic-homotopy-theory.connected-set-bundles-circle.html#4721" class="Function">aut-connected-set-bundle-𝕊¹</a>
</pre>
## Properties

### Connected set bundles over the circle are cyclic sets

#### The set equipped with an automorphism obtained from a connected set bundle over the circle is a cyclic set

This remains to be shown.

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
