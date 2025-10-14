# Free concrete group actions

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="group-theory.free-concrete-group-actions.html" class="Module">group-theory.free-concrete-group-actions</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>

<a id="420" class="Keyword">open</a> <a id="425" class="Keyword">import</a> <a id="432" href="higher-group-theory.free-higher-group-actions.html" class="Module">higher-group-theory.free-higher-group-actions</a>
</pre>
</details>

## Idea

Consider a [concrete group](group-theory.concrete-groups.md) `G` and a
[concrete group action](group-theory.concrete-group-actions.md) of `G` on `X`.
We say that `X` is **free** if its type of
[orbits](group-theory.orbits-concrete-group-actions.md) is a
[set](foundation.sets.md).

[Equivalently](foundation.logical-equivalences.md), we say that `X` is
**abstractly free** if for any element `x : X (sh G)` of the underlying type of
`X` the action map

```text
  g ↦ mul-action-Concrete-Group G X g x
```

is an [embedding](foundation.embeddings.md).

## Definition

### The predicate of being a free concrete group action

<pre class="Agda"><a id="1136" class="Keyword">module</a> <a id="1143" href="group-theory.free-concrete-group-actions.html#1143" class="Module">_</a>
  <a id="1147" class="Symbol">{</a><a id="1148" href="group-theory.free-concrete-group-actions.html#1148" class="Bound">l1</a> <a id="1151" href="group-theory.free-concrete-group-actions.html#1151" class="Bound">l2</a> <a id="1154" class="Symbol">:</a> <a id="1156" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1161" class="Symbol">}</a> <a id="1163" class="Symbol">(</a><a id="1164" href="group-theory.free-concrete-group-actions.html#1164" class="Bound">G</a> <a id="1166" class="Symbol">:</a> <a id="1168" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="1183" href="group-theory.free-concrete-group-actions.html#1148" class="Bound">l1</a><a id="1185" class="Symbol">)</a> <a id="1187" class="Symbol">(</a><a id="1188" href="group-theory.free-concrete-group-actions.html#1188" class="Bound">X</a> <a id="1190" class="Symbol">:</a> <a id="1192" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="1214" href="group-theory.free-concrete-group-actions.html#1151" class="Bound">l2</a> <a id="1217" href="group-theory.free-concrete-group-actions.html#1164" class="Bound">G</a><a id="1218" class="Symbol">)</a>
  <a id="1222" class="Keyword">where</a>

  <a id="1231" href="group-theory.free-concrete-group-actions.html#1231" class="Function">is-free-prop-action-Concrete-Group</a> <a id="1266" class="Symbol">:</a> <a id="1268" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1273" class="Symbol">(</a><a id="1274" href="group-theory.free-concrete-group-actions.html#1148" class="Bound">l1</a> <a id="1277" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1279" href="group-theory.free-concrete-group-actions.html#1151" class="Bound">l2</a><a id="1281" class="Symbol">)</a>
  <a id="1285" href="group-theory.free-concrete-group-actions.html#1231" class="Function">is-free-prop-action-Concrete-Group</a> <a id="1320" class="Symbol">=</a>
    <a id="1326" href="higher-group-theory.free-higher-group-actions.html#1715" class="Function">is-free-prop-action-∞-Group</a> <a id="1354" class="Symbol">(</a><a id="1355" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="1378" href="group-theory.free-concrete-group-actions.html#1164" class="Bound">G</a><a id="1379" class="Symbol">)</a> <a id="1381" class="Symbol">(</a><a id="1382" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1391" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1393" href="group-theory.free-concrete-group-actions.html#1188" class="Bound">X</a><a id="1394" class="Symbol">)</a>

  <a id="1399" href="group-theory.free-concrete-group-actions.html#1399" class="Function">is-free-action-Concrete-Group</a> <a id="1429" class="Symbol">:</a> <a id="1431" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1434" class="Symbol">(</a><a id="1435" href="group-theory.free-concrete-group-actions.html#1148" class="Bound">l1</a> <a id="1438" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1440" href="group-theory.free-concrete-group-actions.html#1151" class="Bound">l2</a><a id="1442" class="Symbol">)</a>
  <a id="1446" href="group-theory.free-concrete-group-actions.html#1399" class="Function">is-free-action-Concrete-Group</a> <a id="1476" class="Symbol">=</a>
    <a id="1482" href="higher-group-theory.free-higher-group-actions.html#1834" class="Function">is-free-action-∞-Group</a> <a id="1505" class="Symbol">(</a><a id="1506" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="1529" href="group-theory.free-concrete-group-actions.html#1164" class="Bound">G</a><a id="1530" class="Symbol">)</a> <a id="1532" class="Symbol">(</a><a id="1533" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1542" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1544" href="group-theory.free-concrete-group-actions.html#1188" class="Bound">X</a><a id="1545" class="Symbol">)</a>

  <a id="1550" href="group-theory.free-concrete-group-actions.html#1550" class="Function">is-prop-is-free-action-Concrete-Group</a> <a id="1588" class="Symbol">:</a> <a id="1590" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1598" href="group-theory.free-concrete-group-actions.html#1399" class="Function">is-free-action-Concrete-Group</a>
  <a id="1630" href="group-theory.free-concrete-group-actions.html#1550" class="Function">is-prop-is-free-action-Concrete-Group</a> <a id="1668" class="Symbol">=</a>
    <a id="1674" href="higher-group-theory.free-higher-group-actions.html#1940" class="Function">is-prop-is-free-action-∞-Group</a> <a id="1705" class="Symbol">(</a><a id="1706" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="1729" href="group-theory.free-concrete-group-actions.html#1164" class="Bound">G</a><a id="1730" class="Symbol">)</a> <a id="1732" class="Symbol">(</a><a id="1733" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1742" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1744" href="group-theory.free-concrete-group-actions.html#1188" class="Bound">X</a><a id="1745" class="Symbol">)</a>
</pre>
### The predicate of being an abstractly free concrete group action

<pre class="Agda"><a id="1829" class="Keyword">module</a> <a id="1836" href="group-theory.free-concrete-group-actions.html#1836" class="Module">_</a>
  <a id="1840" class="Symbol">{</a><a id="1841" href="group-theory.free-concrete-group-actions.html#1841" class="Bound">l1</a> <a id="1844" href="group-theory.free-concrete-group-actions.html#1844" class="Bound">l2</a> <a id="1847" class="Symbol">:</a> <a id="1849" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1854" class="Symbol">}</a> <a id="1856" class="Symbol">(</a><a id="1857" href="group-theory.free-concrete-group-actions.html#1857" class="Bound">G</a> <a id="1859" class="Symbol">:</a> <a id="1861" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="1876" href="group-theory.free-concrete-group-actions.html#1841" class="Bound">l1</a><a id="1878" class="Symbol">)</a> <a id="1880" class="Symbol">(</a><a id="1881" href="group-theory.free-concrete-group-actions.html#1881" class="Bound">X</a> <a id="1883" class="Symbol">:</a> <a id="1885" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="1907" href="group-theory.free-concrete-group-actions.html#1844" class="Bound">l2</a> <a id="1910" href="group-theory.free-concrete-group-actions.html#1857" class="Bound">G</a><a id="1911" class="Symbol">)</a>
  <a id="1915" class="Keyword">where</a>

  <a id="1924" href="group-theory.free-concrete-group-actions.html#1924" class="Function">is-abstractly-free-prop-action-Concrete-Group</a> <a id="1970" class="Symbol">:</a> <a id="1972" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1977" class="Symbol">(</a><a id="1978" href="group-theory.free-concrete-group-actions.html#1841" class="Bound">l1</a> <a id="1981" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1983" href="group-theory.free-concrete-group-actions.html#1844" class="Bound">l2</a><a id="1985" class="Symbol">)</a>
  <a id="1989" href="group-theory.free-concrete-group-actions.html#1924" class="Function">is-abstractly-free-prop-action-Concrete-Group</a> <a id="2035" class="Symbol">=</a>
    <a id="2041" href="higher-group-theory.free-higher-group-actions.html#2241" class="Function">is-abstractly-free-prop-action-∞-Group</a>
      <a id="2086" class="Symbol">(</a> <a id="2088" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="2111" href="group-theory.free-concrete-group-actions.html#1857" class="Bound">G</a><a id="2112" class="Symbol">)</a>
      <a id="2120" class="Symbol">(</a> <a id="2122" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="2131" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2133" href="group-theory.free-concrete-group-actions.html#1881" class="Bound">X</a><a id="2134" class="Symbol">)</a>

  <a id="2139" href="group-theory.free-concrete-group-actions.html#2139" class="Function">is-abstractly-free-action-Concrete-Group</a> <a id="2180" class="Symbol">:</a> <a id="2182" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2185" class="Symbol">(</a><a id="2186" href="group-theory.free-concrete-group-actions.html#1841" class="Bound">l1</a> <a id="2189" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2191" href="group-theory.free-concrete-group-actions.html#1844" class="Bound">l2</a><a id="2193" class="Symbol">)</a>
  <a id="2197" href="group-theory.free-concrete-group-actions.html#2139" class="Function">is-abstractly-free-action-Concrete-Group</a> <a id="2238" class="Symbol">=</a>
    <a id="2244" href="higher-group-theory.free-higher-group-actions.html#2449" class="Function">is-abstractly-free-action-∞-Group</a>
      <a id="2284" class="Symbol">(</a> <a id="2286" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="2309" href="group-theory.free-concrete-group-actions.html#1857" class="Bound">G</a><a id="2310" class="Symbol">)</a>
      <a id="2318" class="Symbol">(</a> <a id="2320" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="2329" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2331" href="group-theory.free-concrete-group-actions.html#1881" class="Bound">X</a><a id="2332" class="Symbol">)</a>

  <a id="2337" href="group-theory.free-concrete-group-actions.html#2337" class="Function">is-prop-is-abstractly-free-action-Concrete-Group</a> <a id="2386" class="Symbol">:</a>
    <a id="2392" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2400" href="group-theory.free-concrete-group-actions.html#2139" class="Function">is-abstractly-free-action-Concrete-Group</a>
  <a id="2443" href="group-theory.free-concrete-group-actions.html#2337" class="Function">is-prop-is-abstractly-free-action-Concrete-Group</a> <a id="2492" class="Symbol">=</a>
    <a id="2498" href="higher-group-theory.free-higher-group-actions.html#2592" class="Function">is-prop-is-abstractly-free-action-∞-Group</a>
      <a id="2546" class="Symbol">(</a> <a id="2548" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="2571" href="group-theory.free-concrete-group-actions.html#1857" class="Bound">G</a><a id="2572" class="Symbol">)</a>
      <a id="2580" class="Symbol">(</a> <a id="2582" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="2591" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2593" href="group-theory.free-concrete-group-actions.html#1881" class="Bound">X</a><a id="2594" class="Symbol">)</a>
</pre>
### Free concrete group actions

<pre class="Agda"><a id="free-action-Concrete-Group"></a><a id="2642" href="group-theory.free-concrete-group-actions.html#2642" class="Function">free-action-Concrete-Group</a> <a id="2669" class="Symbol">:</a>
  <a id="2673" class="Symbol">{</a><a id="2674" href="group-theory.free-concrete-group-actions.html#2674" class="Bound">l1</a> <a id="2677" class="Symbol">:</a> <a id="2679" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2684" class="Symbol">}</a> <a id="2686" class="Symbol">(</a><a id="2687" href="group-theory.free-concrete-group-actions.html#2687" class="Bound">l2</a> <a id="2690" class="Symbol">:</a> <a id="2692" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2697" class="Symbol">)</a> <a id="2699" class="Symbol">→</a> <a id="2701" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="2716" href="group-theory.free-concrete-group-actions.html#2674" class="Bound">l1</a> <a id="2719" class="Symbol">→</a> <a id="2721" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2724" class="Symbol">(</a><a id="2725" href="group-theory.free-concrete-group-actions.html#2674" class="Bound">l1</a> <a id="2728" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2730" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2735" href="group-theory.free-concrete-group-actions.html#2687" class="Bound">l2</a><a id="2737" class="Symbol">)</a>
<a id="2739" href="group-theory.free-concrete-group-actions.html#2642" class="Function">free-action-Concrete-Group</a> <a id="2766" href="group-theory.free-concrete-group-actions.html#2766" class="Bound">l2</a> <a id="2769" href="group-theory.free-concrete-group-actions.html#2769" class="Bound">G</a> <a id="2771" class="Symbol">=</a>
  <a id="2775" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2777" class="Symbol">(</a><a id="2778" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="2800" href="group-theory.free-concrete-group-actions.html#2766" class="Bound">l2</a> <a id="2803" href="group-theory.free-concrete-group-actions.html#2769" class="Bound">G</a><a id="2804" class="Symbol">)</a> <a id="2806" class="Symbol">(</a><a id="2807" href="group-theory.free-concrete-group-actions.html#1399" class="Function">is-free-action-Concrete-Group</a> <a id="2837" href="group-theory.free-concrete-group-actions.html#2769" class="Bound">G</a><a id="2838" class="Symbol">)</a>
</pre>
## Properties

### A concrete group action is free if and only if it is abstractly free

<pre class="Agda"><a id="2942" class="Keyword">module</a> <a id="2949" href="group-theory.free-concrete-group-actions.html#2949" class="Module">_</a>
  <a id="2953" class="Symbol">{</a><a id="2954" href="group-theory.free-concrete-group-actions.html#2954" class="Bound">l1</a> <a id="2957" href="group-theory.free-concrete-group-actions.html#2957" class="Bound">l2</a> <a id="2960" class="Symbol">:</a> <a id="2962" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2967" class="Symbol">}</a> <a id="2969" class="Symbol">(</a><a id="2970" href="group-theory.free-concrete-group-actions.html#2970" class="Bound">G</a> <a id="2972" class="Symbol">:</a> <a id="2974" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="2989" href="group-theory.free-concrete-group-actions.html#2954" class="Bound">l1</a><a id="2991" class="Symbol">)</a> <a id="2993" class="Symbol">(</a><a id="2994" href="group-theory.free-concrete-group-actions.html#2994" class="Bound">X</a> <a id="2996" class="Symbol">:</a> <a id="2998" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="3020" href="group-theory.free-concrete-group-actions.html#2957" class="Bound">l2</a> <a id="3023" href="group-theory.free-concrete-group-actions.html#2970" class="Bound">G</a><a id="3024" class="Symbol">)</a>
  <a id="3028" class="Keyword">where</a>

  <a id="3037" href="group-theory.free-concrete-group-actions.html#3037" class="Function">is-abstractly-free-is-free-action-Concrete-Group</a> <a id="3086" class="Symbol">:</a>
    <a id="3092" href="group-theory.free-concrete-group-actions.html#1399" class="Function">is-free-action-Concrete-Group</a> <a id="3122" href="group-theory.free-concrete-group-actions.html#2970" class="Bound">G</a> <a id="3124" href="group-theory.free-concrete-group-actions.html#2994" class="Bound">X</a> <a id="3126" class="Symbol">→</a>
    <a id="3132" href="group-theory.free-concrete-group-actions.html#2139" class="Function">is-abstractly-free-action-Concrete-Group</a> <a id="3173" href="group-theory.free-concrete-group-actions.html#2970" class="Bound">G</a> <a id="3175" href="group-theory.free-concrete-group-actions.html#2994" class="Bound">X</a>
  <a id="3179" href="group-theory.free-concrete-group-actions.html#3037" class="Function">is-abstractly-free-is-free-action-Concrete-Group</a> <a id="3228" class="Symbol">=</a>
    <a id="3234" href="higher-group-theory.free-higher-group-actions.html#4436" class="Function">is-abstractly-free-is-free-action-∞-Group</a>
      <a id="3282" class="Symbol">(</a> <a id="3284" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="3307" href="group-theory.free-concrete-group-actions.html#2970" class="Bound">G</a><a id="3308" class="Symbol">)</a>
      <a id="3316" class="Symbol">(</a> <a id="3318" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="3327" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3329" href="group-theory.free-concrete-group-actions.html#2994" class="Bound">X</a><a id="3330" class="Symbol">)</a>

  <a id="3335" href="group-theory.free-concrete-group-actions.html#3335" class="Function">is-free-is-abstractly-free-action-Concrete-Group</a> <a id="3384" class="Symbol">:</a>
    <a id="3390" href="group-theory.free-concrete-group-actions.html#2139" class="Function">is-abstractly-free-action-Concrete-Group</a> <a id="3431" href="group-theory.free-concrete-group-actions.html#2970" class="Bound">G</a> <a id="3433" href="group-theory.free-concrete-group-actions.html#2994" class="Bound">X</a> <a id="3435" class="Symbol">→</a>
    <a id="3441" href="group-theory.free-concrete-group-actions.html#1399" class="Function">is-free-action-Concrete-Group</a> <a id="3471" href="group-theory.free-concrete-group-actions.html#2970" class="Bound">G</a> <a id="3473" href="group-theory.free-concrete-group-actions.html#2994" class="Bound">X</a>
  <a id="3477" href="group-theory.free-concrete-group-actions.html#3335" class="Function">is-free-is-abstractly-free-action-Concrete-Group</a> <a id="3526" class="Symbol">=</a>
    <a id="3532" href="higher-group-theory.free-higher-group-actions.html#3824" class="Function">is-free-is-abstractly-free-action-∞-Group</a>
      <a id="3580" class="Symbol">(</a> <a id="3582" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="3605" href="group-theory.free-concrete-group-actions.html#2970" class="Bound">G</a><a id="3606" class="Symbol">)</a>
      <a id="3614" class="Symbol">(</a> <a id="3616" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="3625" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3627" href="group-theory.free-concrete-group-actions.html#2994" class="Bound">X</a><a id="3628" class="Symbol">)</a>
</pre>