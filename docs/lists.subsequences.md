# Subsequences

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="lists.subsequences.html" class="Module">lists.subsequences</a> <a id="51" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="107" class="Keyword">open</a> <a id="112" class="Keyword">import</a> <a id="119" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a>

<a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="474" class="Keyword">open</a> <a id="479" class="Keyword">import</a> <a id="486" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="563" class="Keyword">open</a> <a id="568" class="Keyword">import</a> <a id="575" href="lists.sequences.html" class="Module">lists.sequences</a>

<a id="592" class="Keyword">open</a> <a id="597" class="Keyword">import</a> <a id="604" href="order-theory.strict-order-preserving-maps.html" class="Module">order-theory.strict-order-preserving-maps</a>
<a id="646" class="Keyword">open</a> <a id="651" class="Keyword">import</a> <a id="658" href="order-theory.strictly-increasing-sequences-strictly-preordered-sets.html" class="Module">order-theory.strictly-increasing-sequences-strictly-preordered-sets</a>
</pre>
</details>

## Idea

A {{concept "subsequence" Agda=subsequence}} of a [sequence](lists.sequences.md)
`u : ℕ → A` is a sequence `u ∘ f` for some
[strictly increasing](order-theory.strict-order-preserving-maps.md) sequence
`f : ℕ → ℕ`.

## Definitions

### Subsequences of a sequence

<pre class="Agda"><a id="1023" class="Keyword">module</a> <a id="1030" href="lists.subsequences.html#1030" class="Module">_</a>
  <a id="1034" class="Symbol">{</a><a id="1035" href="lists.subsequences.html#1035" class="Bound">l</a> <a id="1037" class="Symbol">:</a> <a id="1039" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1044" class="Symbol">}</a> <a id="1046" class="Symbol">{</a><a id="1047" href="lists.subsequences.html#1047" class="Bound">A</a> <a id="1049" class="Symbol">:</a> <a id="1051" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1054" href="lists.subsequences.html#1035" class="Bound">l</a><a id="1055" class="Symbol">}</a> <a id="1057" class="Symbol">(</a><a id="1058" href="lists.subsequences.html#1058" class="Bound">u</a> <a id="1060" class="Symbol">:</a> <a id="1062" href="lists.sequences.html#682" class="Function">sequence</a> <a id="1071" href="lists.subsequences.html#1047" class="Bound">A</a><a id="1072" class="Symbol">)</a>
  <a id="1076" class="Keyword">where</a>

  <a id="1085" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="1097" class="Symbol">:</a> <a id="1099" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1102" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="1110" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="1122" class="Symbol">=</a>
    <a id="1128" href="order-theory.strict-order-preserving-maps.html#4117" class="Function">hom-Strictly-Preordered-Set</a>
      <a id="1162" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>
      <a id="1194" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>

  <a id="1223" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="1243" class="Symbol">:</a> <a id="1245" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="1257" class="Symbol">→</a> <a id="1259" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1261" class="Symbol">→</a> <a id="1263" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
  <a id="1267" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="1287" class="Symbol">=</a>
    <a id="1293" href="order-theory.strict-order-preserving-maps.html#4440" class="Function">map-hom-Strictly-Preordered-Set</a>
      <a id="1331" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>
      <a id="1363" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>

  <a id="1392" href="lists.subsequences.html#1392" class="Function">is-strictly-increasing-extract-subsequence</a> <a id="1435" class="Symbol">:</a>
    <a id="1441" class="Symbol">(</a><a id="1442" href="lists.subsequences.html#1442" class="Bound">f</a> <a id="1444" class="Symbol">:</a> <a id="1446" href="lists.subsequences.html#1085" class="Function">subsequence</a><a id="1457" class="Symbol">)</a> <a id="1459" class="Symbol">→</a>
    <a id="1465" href="order-theory.strict-order-preserving-maps.html#3259" class="Function">preserves-strict-order-map-Strictly-Preordered-Set</a>
      <a id="1522" class="Symbol">(</a> <a id="1524" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a><a id="1549" class="Symbol">)</a>
      <a id="1557" class="Symbol">(</a> <a id="1559" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a><a id="1584" class="Symbol">)</a>
      <a id="1592" class="Symbol">(</a> <a id="1594" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="1614" href="lists.subsequences.html#1442" class="Bound">f</a><a id="1615" class="Symbol">)</a>
  <a id="1619" href="lists.subsequences.html#1392" class="Function">is-strictly-increasing-extract-subsequence</a> <a id="1662" class="Symbol">=</a>
    <a id="1668" href="order-theory.strict-order-preserving-maps.html#4591" class="Function">preserves-strict-order-hom-Strictly-Preordered-Set</a>
      <a id="1725" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>
      <a id="1757" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>

  <a id="1786" href="lists.subsequences.html#1786" class="Function">seq-subsequence</a> <a id="1802" class="Symbol">:</a> <a id="1804" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="1816" class="Symbol">→</a> <a id="1818" href="lists.sequences.html#682" class="Function">sequence</a> <a id="1827" href="lists.subsequences.html#1047" class="Bound">A</a>
  <a id="1831" href="lists.subsequences.html#1786" class="Function">seq-subsequence</a> <a id="1847" href="lists.subsequences.html#1847" class="Bound">f</a> <a id="1849" href="lists.subsequences.html#1849" class="Bound">n</a> <a id="1851" class="Symbol">=</a> <a id="1853" href="lists.subsequences.html#1058" class="Bound">u</a> <a id="1855" class="Symbol">(</a><a id="1856" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="1876" href="lists.subsequences.html#1847" class="Bound">f</a> <a id="1878" href="lists.subsequences.html#1849" class="Bound">n</a><a id="1879" class="Symbol">)</a>
</pre>
## Properties

### Any sequence is a subsequence of itself

<pre class="Agda"><a id="1954" class="Keyword">module</a> <a id="1961" href="lists.subsequences.html#1961" class="Module">_</a>
  <a id="1965" class="Symbol">{</a><a id="1966" href="lists.subsequences.html#1966" class="Bound">l</a> <a id="1968" class="Symbol">:</a> <a id="1970" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1975" class="Symbol">}</a> <a id="1977" class="Symbol">{</a><a id="1978" href="lists.subsequences.html#1978" class="Bound">A</a> <a id="1980" class="Symbol">:</a> <a id="1982" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1985" href="lists.subsequences.html#1966" class="Bound">l</a><a id="1986" class="Symbol">}</a> <a id="1988" class="Symbol">(</a><a id="1989" href="lists.subsequences.html#1989" class="Bound">u</a> <a id="1991" class="Symbol">:</a> <a id="1993" href="lists.sequences.html#682" class="Function">sequence</a> <a id="2002" href="lists.subsequences.html#1978" class="Bound">A</a><a id="2003" class="Symbol">)</a>
  <a id="2007" class="Keyword">where</a>

  <a id="2016" href="lists.subsequences.html#2016" class="Function">refl-subsequence</a> <a id="2033" class="Symbol">:</a> <a id="2035" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="2047" href="lists.subsequences.html#1989" class="Bound">u</a>
  <a id="2051" href="lists.subsequences.html#2016" class="Function">refl-subsequence</a> <a id="2068" class="Symbol">=</a> <a id="2070" href="order-theory.strict-order-preserving-maps.html#4970" class="Function">id-hom-Strictly-Preordered-Set</a> <a id="2101" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>
</pre>
### A subsequence of a subsequence is a subsequence of the original sequence

<pre class="Agda"><a id="2218" class="Keyword">module</a> <a id="2225" href="lists.subsequences.html#2225" class="Module">_</a>
  <a id="2229" class="Symbol">{</a><a id="2230" href="lists.subsequences.html#2230" class="Bound">l</a> <a id="2232" class="Symbol">:</a> <a id="2234" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2239" class="Symbol">}</a> <a id="2241" class="Symbol">{</a><a id="2242" href="lists.subsequences.html#2242" class="Bound">A</a> <a id="2244" class="Symbol">:</a> <a id="2246" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2249" href="lists.subsequences.html#2230" class="Bound">l</a><a id="2250" class="Symbol">}</a> <a id="2252" class="Symbol">(</a><a id="2253" href="lists.subsequences.html#2253" class="Bound">u</a> <a id="2255" class="Symbol">:</a> <a id="2257" href="lists.sequences.html#682" class="Function">sequence</a> <a id="2266" href="lists.subsequences.html#2242" class="Bound">A</a><a id="2267" class="Symbol">)</a>
  <a id="2271" class="Keyword">where</a>

  <a id="2280" href="lists.subsequences.html#2280" class="Function">sub-subsequence</a> <a id="2296" class="Symbol">:</a>
    <a id="2302" class="Symbol">(</a><a id="2303" href="lists.subsequences.html#2303" class="Bound">v</a> <a id="2305" class="Symbol">:</a> <a id="2307" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="2319" href="lists.subsequences.html#2253" class="Bound">u</a><a id="2320" class="Symbol">)</a> <a id="2322" class="Symbol">→</a>
    <a id="2328" class="Symbol">(</a><a id="2329" href="lists.subsequences.html#2329" class="Bound">w</a> <a id="2331" class="Symbol">:</a> <a id="2333" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="2345" class="Symbol">(</a><a id="2346" href="lists.subsequences.html#1786" class="Function">seq-subsequence</a> <a id="2362" href="lists.subsequences.html#2253" class="Bound">u</a> <a id="2364" href="lists.subsequences.html#2303" class="Bound">v</a><a id="2365" class="Symbol">))</a> <a id="2368" class="Symbol">→</a>
    <a id="2374" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="2386" href="lists.subsequences.html#2253" class="Bound">u</a>
  <a id="2390" href="lists.subsequences.html#2280" class="Function">sub-subsequence</a> <a id="2406" class="Symbol">=</a>
    <a id="2412" href="order-theory.strict-order-preserving-maps.html#6916" class="Function">comp-hom-Strictly-Preordered-Set</a>
      <a id="2451" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>
      <a id="2483" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>
      <a id="2515" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a>
</pre>
### The extraction sequence of a subsequence is superlinear

<pre class="Agda"><a id="2615" class="Keyword">module</a> <a id="2622" href="lists.subsequences.html#2622" class="Module">_</a>
  <a id="2626" class="Symbol">{</a><a id="2627" href="lists.subsequences.html#2627" class="Bound">l</a> <a id="2629" class="Symbol">:</a> <a id="2631" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2636" class="Symbol">}</a> <a id="2638" class="Symbol">{</a><a id="2639" href="lists.subsequences.html#2639" class="Bound">A</a> <a id="2641" class="Symbol">:</a> <a id="2643" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2646" href="lists.subsequences.html#2627" class="Bound">l</a><a id="2647" class="Symbol">}</a> <a id="2649" class="Symbol">(</a><a id="2650" href="lists.subsequences.html#2650" class="Bound">u</a> <a id="2652" class="Symbol">:</a> <a id="2654" href="lists.sequences.html#682" class="Function">sequence</a> <a id="2663" href="lists.subsequences.html#2639" class="Bound">A</a><a id="2664" class="Symbol">)</a> <a id="2666" class="Symbol">(</a><a id="2667" href="lists.subsequences.html#2667" class="Bound">v</a> <a id="2669" class="Symbol">:</a> <a id="2671" href="lists.subsequences.html#1085" class="Function">subsequence</a> <a id="2683" href="lists.subsequences.html#2650" class="Bound">u</a><a id="2684" class="Symbol">)</a>
  <a id="2688" class="Keyword">where</a>

  <a id="2697" class="Keyword">abstract</a>
    <a id="2710" href="lists.subsequences.html#2710" class="Function">is-superlinear-extract-subsequence</a> <a id="2745" class="Symbol">:</a>
      <a id="2753" class="Symbol">(</a><a id="2754" href="lists.subsequences.html#2754" class="Bound">n</a> <a id="2756" class="Symbol">:</a> <a id="2758" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2759" class="Symbol">)</a> <a id="2761" class="Symbol">→</a> <a id="2763" href="elementary-number-theory.inequality-natural-numbers.html#1276" class="Function">leq-ℕ</a> <a id="2769" href="lists.subsequences.html#2754" class="Bound">n</a> <a id="2771" class="Symbol">(</a><a id="2772" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="2792" href="lists.subsequences.html#2650" class="Bound">u</a> <a id="2794" href="lists.subsequences.html#2667" class="Bound">v</a> <a id="2796" href="lists.subsequences.html#2754" class="Bound">n</a><a id="2797" class="Symbol">)</a>
    <a id="2803" href="lists.subsequences.html#2710" class="Function">is-superlinear-extract-subsequence</a> <a id="2838" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="2845" class="Symbol">=</a>
      <a id="2853" href="elementary-number-theory.inequality-natural-numbers.html#5682" class="Function">leq-zero-ℕ</a> <a id="2864" class="Symbol">(</a><a id="2865" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="2885" href="lists.subsequences.html#2650" class="Bound">u</a> <a id="2887" href="lists.subsequences.html#2667" class="Bound">v</a> <a id="2889" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="2895" class="Symbol">)</a>
    <a id="2901" href="lists.subsequences.html#2710" class="Function">is-superlinear-extract-subsequence</a> <a id="2936" class="Symbol">(</a><a id="2937" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2944" href="lists.subsequences.html#2944" class="Bound">n</a><a id="2945" class="Symbol">)</a> <a id="2947" class="Symbol">=</a>
      <a id="2955" href="elementary-number-theory.strict-inequality-natural-numbers.html#8897" class="Function">leq-succ-le-ℕ</a>
        <a id="2977" class="Symbol">(</a> <a id="2979" href="lists.subsequences.html#2944" class="Bound">n</a><a id="2980" class="Symbol">)</a>
        <a id="2990" class="Symbol">(</a> <a id="2992" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="3012" href="lists.subsequences.html#2650" class="Bound">u</a> <a id="3014" href="lists.subsequences.html#2667" class="Bound">v</a> <a id="3016" class="Symbol">(</a><a id="3017" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="3024" href="lists.subsequences.html#2944" class="Bound">n</a><a id="3025" class="Symbol">))</a>
        <a id="3036" class="Symbol">(</a> <a id="3038" href="elementary-number-theory.strict-inequality-natural-numbers.html#7019" class="Function">concatenate-leq-le-ℕ</a>
          <a id="3069" class="Symbol">{</a> <a id="3071" href="lists.subsequences.html#2944" class="Bound">n</a><a id="3072" class="Symbol">}</a>
          <a id="3084" class="Symbol">{</a> <a id="3086" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="3106" href="lists.subsequences.html#2650" class="Bound">u</a> <a id="3108" href="lists.subsequences.html#2667" class="Bound">v</a> <a id="3110" href="lists.subsequences.html#2944" class="Bound">n</a><a id="3111" class="Symbol">}</a>
          <a id="3123" class="Symbol">{</a> <a id="3125" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="3145" href="lists.subsequences.html#2650" class="Bound">u</a> <a id="3147" href="lists.subsequences.html#2667" class="Bound">v</a> <a id="3149" class="Symbol">(</a><a id="3150" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="3157" href="lists.subsequences.html#2944" class="Bound">n</a><a id="3158" class="Symbol">)}</a>
          <a id="3171" class="Symbol">(</a> <a id="3173" href="lists.subsequences.html#2710" class="Function">is-superlinear-extract-subsequence</a> <a id="3208" href="lists.subsequences.html#2944" class="Bound">n</a><a id="3209" class="Symbol">)</a>
          <a id="3221" class="Symbol">(</a> <a id="3223" href="order-theory.strictly-increasing-sequences-strictly-preordered-sets.html#3496" class="Function">le-succ-is-strictly-increasing-sequence-Strictly-Preordered-Set</a>
            <a id="3299" class="Symbol">(</a> <a id="3301" href="elementary-number-theory.strict-inequality-natural-numbers.html#4716" class="Function">strictly-preordered-set-ℕ</a><a id="3326" class="Symbol">)</a>
            <a id="3340" class="Symbol">(</a> <a id="3342" href="lists.subsequences.html#1223" class="Function">extract-subsequence</a> <a id="3362" href="lists.subsequences.html#2650" class="Bound">u</a> <a id="3364" href="lists.subsequences.html#2667" class="Bound">v</a><a id="3365" class="Symbol">)</a>
            <a id="3379" class="Symbol">(</a> <a id="3381" href="lists.subsequences.html#1392" class="Function">is-strictly-increasing-extract-subsequence</a> <a id="3424" href="lists.subsequences.html#2650" class="Bound">u</a> <a id="3426" href="lists.subsequences.html#2667" class="Bound">v</a><a id="3427" class="Symbol">)</a>
            <a id="3441" class="Symbol">(</a> <a id="3443" href="lists.subsequences.html#2944" class="Bound">n</a><a id="3444" class="Symbol">)))</a>
</pre>