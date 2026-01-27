# Operations on spans

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="foundation.operations-spans.html" class="Module">foundation.operations-spans</a> <a id="67" class="Keyword">where</a>

<a id="74" class="Keyword">open</a> <a id="79" class="Keyword">import</a> <a id="86" href="foundation-core.operations-spans.html" class="Module">foundation-core.operations-spans</a> <a id="119" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="foundation.equivalences-arrows.html" class="Module">foundation.equivalences-arrows</a>
<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

This file contains some further operations on [spans](foundation.spans.md) that
produce new spans from given spans and possibly other data. Previous operations
on spans were defined in
[`foundation-core.operations-spans`](foundation-core.operations-spans.md).

## Definitions

### Concatenating spans and equivalences of arrows on the left

Consider a span `s` given by

```text
       f       g
  A <----- S -----> B
```

and an [equivalence of arrows](foundation.equivalences-arrows.md)
`h : equiv-arrow f' f` as indicated in the diagram

```text
          f'
     A' <---- S'
     |        |
  h₀ | ≃    ≃ | h₁
     ∨        ∨
     A <----- S -----> B.
          f       g
```

Then we obtain a span `A' <- S' -> B`.

<pre class="Agda"><a id="1170" class="Keyword">module</a> <a id="1177" href="foundation.operations-spans.html#1177" class="Module">_</a>
  <a id="1181" class="Symbol">{</a><a id="1182" href="foundation.operations-spans.html#1182" class="Bound">l1</a> <a id="1185" href="foundation.operations-spans.html#1185" class="Bound">l2</a> <a id="1188" href="foundation.operations-spans.html#1188" class="Bound">l3</a> <a id="1191" href="foundation.operations-spans.html#1191" class="Bound">l4</a> <a id="1194" href="foundation.operations-spans.html#1194" class="Bound">l5</a> <a id="1197" class="Symbol">:</a> <a id="1199" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1204" class="Symbol">}</a> <a id="1206" class="Symbol">{</a><a id="1207" href="foundation.operations-spans.html#1207" class="Bound">A</a> <a id="1209" class="Symbol">:</a> <a id="1211" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1214" href="foundation.operations-spans.html#1182" class="Bound">l1</a><a id="1216" class="Symbol">}</a> <a id="1218" class="Symbol">{</a><a id="1219" href="foundation.operations-spans.html#1219" class="Bound">B</a> <a id="1221" class="Symbol">:</a> <a id="1223" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1226" href="foundation.operations-spans.html#1185" class="Bound">l2</a><a id="1228" class="Symbol">}</a>
  <a id="1232" class="Symbol">(</a><a id="1233" href="foundation.operations-spans.html#1233" class="Bound">s</a> <a id="1235" class="Symbol">:</a> <a id="1237" href="foundation.spans.html#1830" class="Function">span</a> <a id="1242" href="foundation.operations-spans.html#1188" class="Bound">l3</a> <a id="1245" href="foundation.operations-spans.html#1207" class="Bound">A</a> <a id="1247" href="foundation.operations-spans.html#1219" class="Bound">B</a><a id="1248" class="Symbol">)</a>
  <a id="1252" class="Symbol">{</a><a id="1253" href="foundation.operations-spans.html#1253" class="Bound">S&#39;</a> <a id="1256" class="Symbol">:</a> <a id="1258" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1261" href="foundation.operations-spans.html#1191" class="Bound">l4</a><a id="1263" class="Symbol">}</a> <a id="1265" class="Symbol">{</a><a id="1266" href="foundation.operations-spans.html#1266" class="Bound">A&#39;</a> <a id="1269" class="Symbol">:</a> <a id="1271" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1274" href="foundation.operations-spans.html#1194" class="Bound">l5</a><a id="1276" class="Symbol">}</a> <a id="1278" class="Symbol">(</a><a id="1279" href="foundation.operations-spans.html#1279" class="Bound">f&#39;</a> <a id="1282" class="Symbol">:</a> <a id="1284" href="foundation.operations-spans.html#1253" class="Bound">S&#39;</a> <a id="1287" class="Symbol">→</a> <a id="1289" href="foundation.operations-spans.html#1266" class="Bound">A&#39;</a><a id="1291" class="Symbol">)</a>
  <a id="1295" class="Symbol">(</a><a id="1296" href="foundation.operations-spans.html#1296" class="Bound">h</a> <a id="1298" class="Symbol">:</a> <a id="1300" href="foundation.equivalences-arrows.html#2283" class="Function">equiv-arrow</a> <a id="1312" href="foundation.operations-spans.html#1279" class="Bound">f&#39;</a> <a id="1315" class="Symbol">(</a><a id="1316" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="1330" href="foundation.operations-spans.html#1233" class="Bound">s</a><a id="1331" class="Symbol">))</a>
  <a id="1336" class="Keyword">where</a>

  <a id="1345" href="foundation.operations-spans.html#1345" class="Function">spanning-type-left-concat-equiv-arrow-span</a> <a id="1388" class="Symbol">:</a> <a id="1390" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1393" href="foundation.operations-spans.html#1191" class="Bound">l4</a>
  <a id="1398" href="foundation.operations-spans.html#1345" class="Function">spanning-type-left-concat-equiv-arrow-span</a> <a id="1441" class="Symbol">=</a> <a id="1443" href="foundation.operations-spans.html#1253" class="Bound">S&#39;</a>

  <a id="1449" href="foundation.operations-spans.html#1449" class="Function">left-map-left-concat-equiv-arrow-span</a> <a id="1487" class="Symbol">:</a>
    <a id="1493" href="foundation.operations-spans.html#1345" class="Function">spanning-type-left-concat-equiv-arrow-span</a> <a id="1536" class="Symbol">→</a> <a id="1538" href="foundation.operations-spans.html#1266" class="Bound">A&#39;</a>
  <a id="1543" href="foundation.operations-spans.html#1449" class="Function">left-map-left-concat-equiv-arrow-span</a> <a id="1581" class="Symbol">=</a> <a id="1583" href="foundation.operations-spans.html#1279" class="Bound">f&#39;</a>

  <a id="1589" href="foundation.operations-spans.html#1589" class="Function">right-map-left-concat-equiv-arrow-span</a> <a id="1628" class="Symbol">:</a>
    <a id="1634" href="foundation.operations-spans.html#1345" class="Function">spanning-type-left-concat-equiv-arrow-span</a> <a id="1677" class="Symbol">→</a> <a id="1679" href="foundation.operations-spans.html#1219" class="Bound">B</a>
  <a id="1683" href="foundation.operations-spans.html#1589" class="Function">right-map-left-concat-equiv-arrow-span</a> <a id="1722" class="Symbol">=</a>
    <a id="1728" class="Symbol">(</a> <a id="1730" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="1745" href="foundation.operations-spans.html#1233" class="Bound">s</a><a id="1746" class="Symbol">)</a> <a id="1748" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
    <a id="1754" class="Symbol">(</a> <a id="1756" href="foundation.equivalences-arrows.html#2514" class="Function">map-domain-equiv-arrow</a> <a id="1779" href="foundation.operations-spans.html#1279" class="Bound">f&#39;</a> <a id="1782" class="Symbol">(</a><a id="1783" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="1797" href="foundation.operations-spans.html#1233" class="Bound">s</a><a id="1798" class="Symbol">)</a> <a id="1800" href="foundation.operations-spans.html#1296" class="Bound">h</a><a id="1801" class="Symbol">)</a>

  <a id="1806" href="foundation.operations-spans.html#1806" class="Function">left-concat-equiv-arrow-span</a> <a id="1835" class="Symbol">:</a>
    <a id="1841" href="foundation.spans.html#1830" class="Function">span</a> <a id="1846" href="foundation.operations-spans.html#1191" class="Bound">l4</a> <a id="1849" href="foundation.operations-spans.html#1266" class="Bound">A&#39;</a> <a id="1852" href="foundation.operations-spans.html#1219" class="Bound">B</a>
  <a id="1856" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1860" href="foundation.operations-spans.html#1806" class="Function">left-concat-equiv-arrow-span</a> <a id="1889" class="Symbol">=</a>
    <a id="1895" href="foundation.operations-spans.html#1345" class="Function">spanning-type-left-concat-equiv-arrow-span</a>
  <a id="1940" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1944" class="Symbol">(</a><a id="1945" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1949" href="foundation.operations-spans.html#1806" class="Function">left-concat-equiv-arrow-span</a><a id="1977" class="Symbol">)</a> <a id="1979" class="Symbol">=</a>
    <a id="1985" href="foundation.operations-spans.html#1449" class="Function">left-map-left-concat-equiv-arrow-span</a>
  <a id="2025" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2029" class="Symbol">(</a><a id="2030" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2034" href="foundation.operations-spans.html#1806" class="Function">left-concat-equiv-arrow-span</a><a id="2062" class="Symbol">)</a> <a id="2064" class="Symbol">=</a>
    <a id="2070" href="foundation.operations-spans.html#1589" class="Function">right-map-left-concat-equiv-arrow-span</a>
</pre>
### Concatenating spans and equivalences of arrows on the right

Consider a span `s` given by

```text
       f       g
  A <----- S -----> B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow g' g`
as indicated in the diagram

```text
               g'
           S' ----> B'
           |        |
        h₀ | ≃    ≃ | h₁
           ∨        ∨
  A <----- S -----> B.
       f       g
```

Then we obtain a span `A <- S' -> B'`.

<pre class="Agda"><a id="2581" class="Keyword">module</a> <a id="2588" href="foundation.operations-spans.html#2588" class="Module">_</a>
  <a id="2592" class="Symbol">{</a><a id="2593" href="foundation.operations-spans.html#2593" class="Bound">l1</a> <a id="2596" href="foundation.operations-spans.html#2596" class="Bound">l2</a> <a id="2599" href="foundation.operations-spans.html#2599" class="Bound">l3</a> <a id="2602" href="foundation.operations-spans.html#2602" class="Bound">l4</a> <a id="2605" href="foundation.operations-spans.html#2605" class="Bound">l5</a> <a id="2608" class="Symbol">:</a> <a id="2610" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2615" class="Symbol">}</a> <a id="2617" class="Symbol">{</a><a id="2618" href="foundation.operations-spans.html#2618" class="Bound">A</a> <a id="2620" class="Symbol">:</a> <a id="2622" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2625" href="foundation.operations-spans.html#2593" class="Bound">l1</a><a id="2627" class="Symbol">}</a> <a id="2629" class="Symbol">{</a><a id="2630" href="foundation.operations-spans.html#2630" class="Bound">B</a> <a id="2632" class="Symbol">:</a> <a id="2634" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2637" href="foundation.operations-spans.html#2596" class="Bound">l2</a><a id="2639" class="Symbol">}</a>
  <a id="2643" class="Symbol">(</a><a id="2644" href="foundation.operations-spans.html#2644" class="Bound">s</a> <a id="2646" class="Symbol">:</a> <a id="2648" href="foundation.spans.html#1830" class="Function">span</a> <a id="2653" href="foundation.operations-spans.html#2599" class="Bound">l3</a> <a id="2656" href="foundation.operations-spans.html#2618" class="Bound">A</a> <a id="2658" href="foundation.operations-spans.html#2630" class="Bound">B</a><a id="2659" class="Symbol">)</a>
  <a id="2663" class="Symbol">{</a><a id="2664" href="foundation.operations-spans.html#2664" class="Bound">S&#39;</a> <a id="2667" class="Symbol">:</a> <a id="2669" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2672" href="foundation.operations-spans.html#2602" class="Bound">l4</a><a id="2674" class="Symbol">}</a> <a id="2676" class="Symbol">{</a><a id="2677" href="foundation.operations-spans.html#2677" class="Bound">B&#39;</a> <a id="2680" class="Symbol">:</a> <a id="2682" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2685" href="foundation.operations-spans.html#2605" class="Bound">l5</a><a id="2687" class="Symbol">}</a> <a id="2689" class="Symbol">(</a><a id="2690" href="foundation.operations-spans.html#2690" class="Bound">g&#39;</a> <a id="2693" class="Symbol">:</a> <a id="2695" href="foundation.operations-spans.html#2664" class="Bound">S&#39;</a> <a id="2698" class="Symbol">→</a> <a id="2700" href="foundation.operations-spans.html#2677" class="Bound">B&#39;</a><a id="2702" class="Symbol">)</a>
  <a id="2706" class="Symbol">(</a><a id="2707" href="foundation.operations-spans.html#2707" class="Bound">h</a> <a id="2709" class="Symbol">:</a> <a id="2711" href="foundation.equivalences-arrows.html#2283" class="Function">equiv-arrow</a> <a id="2723" href="foundation.operations-spans.html#2690" class="Bound">g&#39;</a> <a id="2726" class="Symbol">(</a><a id="2727" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="2742" href="foundation.operations-spans.html#2644" class="Bound">s</a><a id="2743" class="Symbol">))</a>
  <a id="2748" class="Keyword">where</a>

  <a id="2757" href="foundation.operations-spans.html#2757" class="Function">spanning-type-right-concat-equiv-arrow-span</a> <a id="2801" class="Symbol">:</a> <a id="2803" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2806" href="foundation.operations-spans.html#2602" class="Bound">l4</a>
  <a id="2811" href="foundation.operations-spans.html#2757" class="Function">spanning-type-right-concat-equiv-arrow-span</a> <a id="2855" class="Symbol">=</a> <a id="2857" href="foundation.operations-spans.html#2664" class="Bound">S&#39;</a>

  <a id="2863" href="foundation.operations-spans.html#2863" class="Function">left-map-right-concat-equiv-arrow-span</a> <a id="2902" class="Symbol">:</a>
    <a id="2908" href="foundation.operations-spans.html#2757" class="Function">spanning-type-right-concat-equiv-arrow-span</a> <a id="2952" class="Symbol">→</a> <a id="2954" href="foundation.operations-spans.html#2618" class="Bound">A</a>
  <a id="2958" href="foundation.operations-spans.html#2863" class="Function">left-map-right-concat-equiv-arrow-span</a> <a id="2997" class="Symbol">=</a>
    <a id="3003" class="Symbol">(</a> <a id="3005" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="3019" href="foundation.operations-spans.html#2644" class="Bound">s</a><a id="3020" class="Symbol">)</a> <a id="3022" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
    <a id="3028" class="Symbol">(</a> <a id="3030" href="foundation.equivalences-arrows.html#2514" class="Function">map-domain-equiv-arrow</a> <a id="3053" href="foundation.operations-spans.html#2690" class="Bound">g&#39;</a> <a id="3056" class="Symbol">(</a><a id="3057" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="3072" href="foundation.operations-spans.html#2644" class="Bound">s</a><a id="3073" class="Symbol">)</a> <a id="3075" href="foundation.operations-spans.html#2707" class="Bound">h</a><a id="3076" class="Symbol">)</a>

  <a id="3081" href="foundation.operations-spans.html#3081" class="Function">right-map-right-concat-equiv-arrow-span</a> <a id="3121" class="Symbol">:</a>
    <a id="3127" href="foundation.operations-spans.html#2757" class="Function">spanning-type-right-concat-equiv-arrow-span</a> <a id="3171" class="Symbol">→</a> <a id="3173" href="foundation.operations-spans.html#2677" class="Bound">B&#39;</a>
  <a id="3178" href="foundation.operations-spans.html#3081" class="Function">right-map-right-concat-equiv-arrow-span</a> <a id="3218" class="Symbol">=</a> <a id="3220" href="foundation.operations-spans.html#2690" class="Bound">g&#39;</a>

  <a id="3226" href="foundation.operations-spans.html#3226" class="Function">right-concat-equiv-arrow-span</a> <a id="3256" class="Symbol">:</a>
    <a id="3262" href="foundation.spans.html#1830" class="Function">span</a> <a id="3267" href="foundation.operations-spans.html#2602" class="Bound">l4</a> <a id="3270" href="foundation.operations-spans.html#2618" class="Bound">A</a> <a id="3272" href="foundation.operations-spans.html#2677" class="Bound">B&#39;</a>
  <a id="3277" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3281" href="foundation.operations-spans.html#3226" class="Function">right-concat-equiv-arrow-span</a> <a id="3311" class="Symbol">=</a>
    <a id="3317" href="foundation.operations-spans.html#2757" class="Function">spanning-type-right-concat-equiv-arrow-span</a>
  <a id="3363" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3367" class="Symbol">(</a><a id="3368" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3372" href="foundation.operations-spans.html#3226" class="Function">right-concat-equiv-arrow-span</a><a id="3401" class="Symbol">)</a> <a id="3403" class="Symbol">=</a>
    <a id="3409" href="foundation.operations-spans.html#2863" class="Function">left-map-right-concat-equiv-arrow-span</a>
  <a id="3450" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3454" class="Symbol">(</a><a id="3455" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3459" href="foundation.operations-spans.html#3226" class="Function">right-concat-equiv-arrow-span</a><a id="3488" class="Symbol">)</a> <a id="3490" class="Symbol">=</a>
    <a id="3496" href="foundation.operations-spans.html#3081" class="Function">right-map-right-concat-equiv-arrow-span</a>
</pre>
## See also

- [Composition of spans](foundation.composition-spans.md)
- [Opposite spans](foundation.opposite-spans.md)
