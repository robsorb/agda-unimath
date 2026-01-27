# Operations on spans

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="foundation-core.operations-spans.html" class="Module">foundation-core.operations-spans</a> <a id="72" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

This file contains some operations on [spans](foundation.spans.md) that produce
new spans from given spans and possibly other data.

## Definitions

### Concatenating spans and maps on both sides

Consider a [span](foundation.spans.md) `s` given by

```text
       f       g
  A <----- S -----> B
```

and maps `i : A → A'` and `j : B → B'`. The
{{#concept "concatenation span" Disambiguation="span" Agda=concat-span}} of `i`,
`s`, and `j` is the span

```text
       i ∘ f     j ∘ g
  A' <------- S -------> B.
```

<pre class="Agda"><a id="875" class="Keyword">module</a> <a id="882" href="foundation-core.operations-spans.html#882" class="Module">_</a>
  <a id="886" class="Symbol">{</a><a id="887" href="foundation-core.operations-spans.html#887" class="Bound">l1</a> <a id="890" href="foundation-core.operations-spans.html#890" class="Bound">l2</a> <a id="893" href="foundation-core.operations-spans.html#893" class="Bound">l3</a> <a id="896" href="foundation-core.operations-spans.html#896" class="Bound">l4</a> <a id="899" href="foundation-core.operations-spans.html#899" class="Bound">l5</a> <a id="902" class="Symbol">:</a> <a id="904" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="909" class="Symbol">}</a>
  <a id="913" class="Symbol">{</a><a id="914" href="foundation-core.operations-spans.html#914" class="Bound">A</a> <a id="916" class="Symbol">:</a> <a id="918" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="921" href="foundation-core.operations-spans.html#887" class="Bound">l1</a><a id="923" class="Symbol">}</a> <a id="925" class="Symbol">{</a><a id="926" href="foundation-core.operations-spans.html#926" class="Bound">A&#39;</a> <a id="929" class="Symbol">:</a> <a id="931" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="934" href="foundation-core.operations-spans.html#890" class="Bound">l2</a><a id="936" class="Symbol">}</a>
  <a id="940" class="Symbol">{</a><a id="941" href="foundation-core.operations-spans.html#941" class="Bound">B</a> <a id="943" class="Symbol">:</a> <a id="945" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="948" href="foundation-core.operations-spans.html#893" class="Bound">l3</a><a id="950" class="Symbol">}</a> <a id="952" class="Symbol">{</a><a id="953" href="foundation-core.operations-spans.html#953" class="Bound">B&#39;</a> <a id="956" class="Symbol">:</a> <a id="958" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="961" href="foundation-core.operations-spans.html#896" class="Bound">l4</a><a id="963" class="Symbol">}</a>
  <a id="967" class="Keyword">where</a>

  <a id="976" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a> <a id="988" class="Symbol">:</a> <a id="990" href="foundation.spans.html#1830" class="Function">span</a> <a id="995" href="foundation-core.operations-spans.html#899" class="Bound">l5</a> <a id="998" href="foundation-core.operations-spans.html#914" class="Bound">A</a> <a id="1000" href="foundation-core.operations-spans.html#941" class="Bound">B</a> <a id="1002" class="Symbol">→</a> <a id="1004" class="Symbol">(</a><a id="1005" href="foundation-core.operations-spans.html#914" class="Bound">A</a> <a id="1007" class="Symbol">→</a> <a id="1009" href="foundation-core.operations-spans.html#926" class="Bound">A&#39;</a><a id="1011" class="Symbol">)</a> <a id="1013" class="Symbol">→</a> <a id="1015" class="Symbol">(</a><a id="1016" href="foundation-core.operations-spans.html#941" class="Bound">B</a> <a id="1018" class="Symbol">→</a> <a id="1020" href="foundation-core.operations-spans.html#953" class="Bound">B&#39;</a><a id="1022" class="Symbol">)</a> <a id="1024" class="Symbol">→</a> <a id="1026" href="foundation.spans.html#1830" class="Function">span</a> <a id="1031" href="foundation-core.operations-spans.html#899" class="Bound">l5</a> <a id="1034" href="foundation-core.operations-spans.html#926" class="Bound">A&#39;</a> <a id="1037" href="foundation-core.operations-spans.html#953" class="Bound">B&#39;</a>
  <a id="1042" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1046" class="Symbol">(</a><a id="1047" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a> <a id="1059" href="foundation-core.operations-spans.html#1059" class="Bound">s</a> <a id="1061" href="foundation-core.operations-spans.html#1061" class="Bound">i</a> <a id="1063" href="foundation-core.operations-spans.html#1063" class="Bound">j</a><a id="1064" class="Symbol">)</a> <a id="1066" class="Symbol">=</a> <a id="1068" href="foundation.spans.html#2049" class="Function">spanning-type-span</a> <a id="1087" href="foundation-core.operations-spans.html#1059" class="Bound">s</a>
  <a id="1091" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1095" class="Symbol">(</a><a id="1096" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1100" class="Symbol">(</a><a id="1101" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a> <a id="1113" href="foundation-core.operations-spans.html#1113" class="Bound">s</a> <a id="1115" href="foundation-core.operations-spans.html#1115" class="Bound">i</a> <a id="1117" href="foundation-core.operations-spans.html#1117" class="Bound">j</a><a id="1118" class="Symbol">))</a> <a id="1121" class="Symbol">=</a> <a id="1123" href="foundation-core.operations-spans.html#1115" class="Bound">i</a> <a id="1125" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1127" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="1141" href="foundation-core.operations-spans.html#1113" class="Bound">s</a>
  <a id="1145" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1149" class="Symbol">(</a><a id="1150" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1154" class="Symbol">(</a><a id="1155" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a> <a id="1167" href="foundation-core.operations-spans.html#1167" class="Bound">s</a> <a id="1169" href="foundation-core.operations-spans.html#1169" class="Bound">i</a> <a id="1171" href="foundation-core.operations-spans.html#1171" class="Bound">j</a><a id="1172" class="Symbol">))</a> <a id="1175" class="Symbol">=</a> <a id="1177" href="foundation-core.operations-spans.html#1171" class="Bound">j</a> <a id="1179" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1181" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="1196" href="foundation-core.operations-spans.html#1167" class="Bound">s</a>
</pre>
### Concatenating spans and maps on the left

Consider a [span](foundation.spans.md) `s` given by

```text
       f       g
  A <----- S -----> B
```

and a map `i : A → A'`. The
{{#concept "left concatenation" Disambiguation="span" Agda=left-concat-span}} of
`s` by `i` is the span

```text
       i ∘ f      g
  A' <------- S -----> B.
```

<pre class="Agda"><a id="1554" class="Keyword">module</a> <a id="1561" href="foundation-core.operations-spans.html#1561" class="Module">_</a>
  <a id="1565" class="Symbol">{</a><a id="1566" href="foundation-core.operations-spans.html#1566" class="Bound">l1</a> <a id="1569" href="foundation-core.operations-spans.html#1569" class="Bound">l2</a> <a id="1572" href="foundation-core.operations-spans.html#1572" class="Bound">l3</a> <a id="1575" href="foundation-core.operations-spans.html#1575" class="Bound">l4</a> <a id="1578" class="Symbol">:</a> <a id="1580" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1585" class="Symbol">}</a>
  <a id="1589" class="Symbol">{</a><a id="1590" href="foundation-core.operations-spans.html#1590" class="Bound">A</a> <a id="1592" class="Symbol">:</a> <a id="1594" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1597" href="foundation-core.operations-spans.html#1566" class="Bound">l1</a><a id="1599" class="Symbol">}</a> <a id="1601" class="Symbol">{</a><a id="1602" href="foundation-core.operations-spans.html#1602" class="Bound">A&#39;</a> <a id="1605" class="Symbol">:</a> <a id="1607" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1610" href="foundation-core.operations-spans.html#1569" class="Bound">l2</a><a id="1612" class="Symbol">}</a>
  <a id="1616" class="Symbol">{</a><a id="1617" href="foundation-core.operations-spans.html#1617" class="Bound">B</a> <a id="1619" class="Symbol">:</a> <a id="1621" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1624" href="foundation-core.operations-spans.html#1572" class="Bound">l3</a><a id="1626" class="Symbol">}</a>
  <a id="1630" class="Keyword">where</a>

  <a id="1639" href="foundation-core.operations-spans.html#1639" class="Function">left-concat-span</a> <a id="1656" class="Symbol">:</a> <a id="1658" href="foundation.spans.html#1830" class="Function">span</a> <a id="1663" href="foundation-core.operations-spans.html#1575" class="Bound">l4</a> <a id="1666" href="foundation-core.operations-spans.html#1590" class="Bound">A</a> <a id="1668" href="foundation-core.operations-spans.html#1617" class="Bound">B</a> <a id="1670" class="Symbol">→</a> <a id="1672" class="Symbol">(</a><a id="1673" href="foundation-core.operations-spans.html#1590" class="Bound">A</a> <a id="1675" class="Symbol">→</a> <a id="1677" href="foundation-core.operations-spans.html#1602" class="Bound">A&#39;</a><a id="1679" class="Symbol">)</a> <a id="1681" class="Symbol">→</a> <a id="1683" href="foundation.spans.html#1830" class="Function">span</a> <a id="1688" href="foundation-core.operations-spans.html#1575" class="Bound">l4</a> <a id="1691" href="foundation-core.operations-spans.html#1602" class="Bound">A&#39;</a> <a id="1694" href="foundation-core.operations-spans.html#1617" class="Bound">B</a>
  <a id="1698" href="foundation-core.operations-spans.html#1639" class="Function">left-concat-span</a> <a id="1715" href="foundation-core.operations-spans.html#1715" class="Bound">s</a> <a id="1717" href="foundation-core.operations-spans.html#1717" class="Bound">f</a> <a id="1719" class="Symbol">=</a> <a id="1721" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a> <a id="1733" href="foundation-core.operations-spans.html#1715" class="Bound">s</a> <a id="1735" href="foundation-core.operations-spans.html#1717" class="Bound">f</a> <a id="1737" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>
### Concatenating spans and maps on the right

Consider a [span](foundation.spans.md) `s` given by

```text
       f       g
  A <----- S -----> B
```

and a map `j : B → B'`. The
{{#concept "right concatenation" Disambiguation="span" Agda=right-concat-span}}
of `s` by `j` is the span

```text
        f      j ∘ g
  A' <----- S -------> B.
```

<pre class="Agda"><a id="2100" class="Keyword">module</a> <a id="2107" href="foundation-core.operations-spans.html#2107" class="Module">_</a>
  <a id="2111" class="Symbol">{</a><a id="2112" href="foundation-core.operations-spans.html#2112" class="Bound">l1</a> <a id="2115" href="foundation-core.operations-spans.html#2115" class="Bound">l2</a> <a id="2118" href="foundation-core.operations-spans.html#2118" class="Bound">l3</a> <a id="2121" href="foundation-core.operations-spans.html#2121" class="Bound">l4</a> <a id="2124" class="Symbol">:</a> <a id="2126" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2131" class="Symbol">}</a>
  <a id="2135" class="Symbol">{</a><a id="2136" href="foundation-core.operations-spans.html#2136" class="Bound">A</a> <a id="2138" class="Symbol">:</a> <a id="2140" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2143" href="foundation-core.operations-spans.html#2112" class="Bound">l1</a><a id="2145" class="Symbol">}</a>
  <a id="2149" class="Symbol">{</a><a id="2150" href="foundation-core.operations-spans.html#2150" class="Bound">B</a> <a id="2152" class="Symbol">:</a> <a id="2154" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2157" href="foundation-core.operations-spans.html#2118" class="Bound">l3</a><a id="2159" class="Symbol">}</a> <a id="2161" class="Symbol">{</a><a id="2162" href="foundation-core.operations-spans.html#2162" class="Bound">B&#39;</a> <a id="2165" class="Symbol">:</a> <a id="2167" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2170" href="foundation-core.operations-spans.html#2121" class="Bound">l4</a><a id="2172" class="Symbol">}</a>
  <a id="2176" class="Keyword">where</a>

  <a id="2185" href="foundation-core.operations-spans.html#2185" class="Function">right-concat-span</a> <a id="2203" class="Symbol">:</a> <a id="2205" href="foundation.spans.html#1830" class="Function">span</a> <a id="2210" href="foundation-core.operations-spans.html#2121" class="Bound">l4</a> <a id="2213" href="foundation-core.operations-spans.html#2136" class="Bound">A</a> <a id="2215" href="foundation-core.operations-spans.html#2150" class="Bound">B</a> <a id="2217" class="Symbol">→</a> <a id="2219" class="Symbol">(</a><a id="2220" href="foundation-core.operations-spans.html#2150" class="Bound">B</a> <a id="2222" class="Symbol">→</a> <a id="2224" href="foundation-core.operations-spans.html#2162" class="Bound">B&#39;</a><a id="2226" class="Symbol">)</a> <a id="2228" class="Symbol">→</a> <a id="2230" href="foundation.spans.html#1830" class="Function">span</a> <a id="2235" href="foundation-core.operations-spans.html#2121" class="Bound">l4</a> <a id="2238" href="foundation-core.operations-spans.html#2136" class="Bound">A</a> <a id="2240" href="foundation-core.operations-spans.html#2162" class="Bound">B&#39;</a>
  <a id="2245" href="foundation-core.operations-spans.html#2185" class="Function">right-concat-span</a> <a id="2263" href="foundation-core.operations-spans.html#2263" class="Bound">s</a> <a id="2265" href="foundation-core.operations-spans.html#2265" class="Bound">g</a> <a id="2267" class="Symbol">=</a> <a id="2269" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a> <a id="2281" href="foundation-core.operations-spans.html#2263" class="Bound">s</a> <a id="2283" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2286" href="foundation-core.operations-spans.html#2265" class="Bound">g</a>
</pre>
### Concatenating spans and morphisms of arrows on the left

Consider a span `s` given by

```text
       f       g
  A <----- S -----> B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f`
as indicated in the diagram

```text
          f'
     A' <---- S'
     |        |
  h₀ |        | h₁
     ∨        ∨
     A <----- S -----> B.
          f       g
```

Then we obtain a span `A' <- S' -> B`.

<pre class="Agda"><a id="2733" class="Keyword">module</a> <a id="2740" href="foundation-core.operations-spans.html#2740" class="Module">_</a>
  <a id="2744" class="Symbol">{</a><a id="2745" href="foundation-core.operations-spans.html#2745" class="Bound">l1</a> <a id="2748" href="foundation-core.operations-spans.html#2748" class="Bound">l2</a> <a id="2751" href="foundation-core.operations-spans.html#2751" class="Bound">l3</a> <a id="2754" href="foundation-core.operations-spans.html#2754" class="Bound">l4</a> <a id="2757" href="foundation-core.operations-spans.html#2757" class="Bound">l5</a> <a id="2760" class="Symbol">:</a> <a id="2762" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2767" class="Symbol">}</a> <a id="2769" class="Symbol">{</a><a id="2770" href="foundation-core.operations-spans.html#2770" class="Bound">A</a> <a id="2772" class="Symbol">:</a> <a id="2774" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2777" href="foundation-core.operations-spans.html#2745" class="Bound">l1</a><a id="2779" class="Symbol">}</a> <a id="2781" class="Symbol">{</a><a id="2782" href="foundation-core.operations-spans.html#2782" class="Bound">B</a> <a id="2784" class="Symbol">:</a> <a id="2786" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2789" href="foundation-core.operations-spans.html#2748" class="Bound">l2</a><a id="2791" class="Symbol">}</a> <a id="2793" class="Symbol">(</a><a id="2794" href="foundation-core.operations-spans.html#2794" class="Bound">s</a> <a id="2796" class="Symbol">:</a> <a id="2798" href="foundation.spans.html#1830" class="Function">span</a> <a id="2803" href="foundation-core.operations-spans.html#2751" class="Bound">l3</a> <a id="2806" href="foundation-core.operations-spans.html#2770" class="Bound">A</a> <a id="2808" href="foundation-core.operations-spans.html#2782" class="Bound">B</a><a id="2809" class="Symbol">)</a>
  <a id="2813" class="Symbol">{</a><a id="2814" href="foundation-core.operations-spans.html#2814" class="Bound">S&#39;</a> <a id="2817" class="Symbol">:</a> <a id="2819" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2822" href="foundation-core.operations-spans.html#2754" class="Bound">l4</a><a id="2824" class="Symbol">}</a> <a id="2826" class="Symbol">{</a><a id="2827" href="foundation-core.operations-spans.html#2827" class="Bound">A&#39;</a> <a id="2830" class="Symbol">:</a> <a id="2832" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2835" href="foundation-core.operations-spans.html#2757" class="Bound">l5</a><a id="2837" class="Symbol">}</a> <a id="2839" class="Symbol">(</a><a id="2840" href="foundation-core.operations-spans.html#2840" class="Bound">f&#39;</a> <a id="2843" class="Symbol">:</a> <a id="2845" href="foundation-core.operations-spans.html#2814" class="Bound">S&#39;</a> <a id="2848" class="Symbol">→</a> <a id="2850" href="foundation-core.operations-spans.html#2827" class="Bound">A&#39;</a><a id="2852" class="Symbol">)</a> <a id="2854" class="Symbol">(</a><a id="2855" href="foundation-core.operations-spans.html#2855" class="Bound">h</a> <a id="2857" class="Symbol">:</a> <a id="2859" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="2869" href="foundation-core.operations-spans.html#2840" class="Bound">f&#39;</a> <a id="2872" class="Symbol">(</a><a id="2873" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="2887" href="foundation-core.operations-spans.html#2794" class="Bound">s</a><a id="2888" class="Symbol">))</a>
  <a id="2893" class="Keyword">where</a>

  <a id="2902" href="foundation-core.operations-spans.html#2902" class="Function">spanning-type-left-concat-hom-arrow-span</a> <a id="2943" class="Symbol">:</a> <a id="2945" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2948" href="foundation-core.operations-spans.html#2754" class="Bound">l4</a>
  <a id="2953" href="foundation-core.operations-spans.html#2902" class="Function">spanning-type-left-concat-hom-arrow-span</a> <a id="2994" class="Symbol">=</a> <a id="2996" href="foundation-core.operations-spans.html#2814" class="Bound">S&#39;</a>

  <a id="3002" href="foundation-core.operations-spans.html#3002" class="Function">left-map-left-concat-hom-arrow-span</a> <a id="3038" class="Symbol">:</a>
    <a id="3044" href="foundation-core.operations-spans.html#2902" class="Function">spanning-type-left-concat-hom-arrow-span</a> <a id="3085" class="Symbol">→</a> <a id="3087" href="foundation-core.operations-spans.html#2827" class="Bound">A&#39;</a>
  <a id="3092" href="foundation-core.operations-spans.html#3002" class="Function">left-map-left-concat-hom-arrow-span</a> <a id="3128" class="Symbol">=</a> <a id="3130" href="foundation-core.operations-spans.html#2840" class="Bound">f&#39;</a>

  <a id="3136" href="foundation-core.operations-spans.html#3136" class="Function">right-map-left-concat-hom-arrow-span</a> <a id="3173" class="Symbol">:</a>
    <a id="3179" href="foundation-core.operations-spans.html#2902" class="Function">spanning-type-left-concat-hom-arrow-span</a> <a id="3220" class="Symbol">→</a> <a id="3222" href="foundation-core.operations-spans.html#2782" class="Bound">B</a>
  <a id="3226" href="foundation-core.operations-spans.html#3136" class="Function">right-map-left-concat-hom-arrow-span</a> <a id="3263" class="Symbol">=</a>
    <a id="3269" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="3284" href="foundation-core.operations-spans.html#2794" class="Bound">s</a> <a id="3286" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3288" href="foundation.morphisms-arrows.html#1743" class="Function">map-domain-hom-arrow</a> <a id="3309" href="foundation-core.operations-spans.html#2840" class="Bound">f&#39;</a> <a id="3312" class="Symbol">(</a><a id="3313" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="3327" href="foundation-core.operations-spans.html#2794" class="Bound">s</a><a id="3328" class="Symbol">)</a> <a id="3330" href="foundation-core.operations-spans.html#2855" class="Bound">h</a>

  <a id="3335" href="foundation-core.operations-spans.html#3335" class="Function">left-concat-hom-arrow-span</a> <a id="3362" class="Symbol">:</a> <a id="3364" href="foundation.spans.html#1830" class="Function">span</a> <a id="3369" href="foundation-core.operations-spans.html#2754" class="Bound">l4</a> <a id="3372" href="foundation-core.operations-spans.html#2827" class="Bound">A&#39;</a> <a id="3375" href="foundation-core.operations-spans.html#2782" class="Bound">B</a>
  <a id="3379" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3383" href="foundation-core.operations-spans.html#3335" class="Function">left-concat-hom-arrow-span</a> <a id="3410" class="Symbol">=</a> <a id="3412" href="foundation-core.operations-spans.html#2902" class="Function">spanning-type-left-concat-hom-arrow-span</a>
  <a id="3455" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3459" class="Symbol">(</a><a id="3460" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3464" href="foundation-core.operations-spans.html#3335" class="Function">left-concat-hom-arrow-span</a><a id="3490" class="Symbol">)</a> <a id="3492" class="Symbol">=</a> <a id="3494" href="foundation-core.operations-spans.html#3002" class="Function">left-map-left-concat-hom-arrow-span</a>
  <a id="3532" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3536" class="Symbol">(</a><a id="3537" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3541" href="foundation-core.operations-spans.html#3335" class="Function">left-concat-hom-arrow-span</a><a id="3567" class="Symbol">)</a> <a id="3569" class="Symbol">=</a> <a id="3571" href="foundation-core.operations-spans.html#3136" class="Function">right-map-left-concat-hom-arrow-span</a>
</pre>
### Concatenating spans and morphisms of arrows on the right

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
        h₀ |        | h₁
           ∨        ∨
  A <----- S -----> B.
       f       g
```

Then we obtain a span `A <- S' -> B'`.

<pre class="Agda"><a id="4077" class="Keyword">module</a> <a id="4084" href="foundation-core.operations-spans.html#4084" class="Module">_</a>
  <a id="4088" class="Symbol">{</a><a id="4089" href="foundation-core.operations-spans.html#4089" class="Bound">l1</a> <a id="4092" href="foundation-core.operations-spans.html#4092" class="Bound">l2</a> <a id="4095" href="foundation-core.operations-spans.html#4095" class="Bound">l3</a> <a id="4098" href="foundation-core.operations-spans.html#4098" class="Bound">l4</a> <a id="4101" href="foundation-core.operations-spans.html#4101" class="Bound">l5</a> <a id="4104" class="Symbol">:</a> <a id="4106" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4111" class="Symbol">}</a> <a id="4113" class="Symbol">{</a><a id="4114" href="foundation-core.operations-spans.html#4114" class="Bound">A</a> <a id="4116" class="Symbol">:</a> <a id="4118" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4121" href="foundation-core.operations-spans.html#4089" class="Bound">l1</a><a id="4123" class="Symbol">}</a> <a id="4125" class="Symbol">{</a><a id="4126" href="foundation-core.operations-spans.html#4126" class="Bound">B</a> <a id="4128" class="Symbol">:</a> <a id="4130" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4133" href="foundation-core.operations-spans.html#4092" class="Bound">l2</a><a id="4135" class="Symbol">}</a>
  <a id="4139" class="Symbol">(</a><a id="4140" href="foundation-core.operations-spans.html#4140" class="Bound">s</a> <a id="4142" class="Symbol">:</a> <a id="4144" href="foundation.spans.html#1830" class="Function">span</a> <a id="4149" href="foundation-core.operations-spans.html#4095" class="Bound">l3</a> <a id="4152" href="foundation-core.operations-spans.html#4114" class="Bound">A</a> <a id="4154" href="foundation-core.operations-spans.html#4126" class="Bound">B</a><a id="4155" class="Symbol">)</a>
  <a id="4159" class="Symbol">{</a><a id="4160" href="foundation-core.operations-spans.html#4160" class="Bound">S&#39;</a> <a id="4163" class="Symbol">:</a> <a id="4165" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4168" href="foundation-core.operations-spans.html#4098" class="Bound">l4</a><a id="4170" class="Symbol">}</a> <a id="4172" class="Symbol">{</a><a id="4173" href="foundation-core.operations-spans.html#4173" class="Bound">B&#39;</a> <a id="4176" class="Symbol">:</a> <a id="4178" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4181" href="foundation-core.operations-spans.html#4101" class="Bound">l5</a><a id="4183" class="Symbol">}</a> <a id="4185" class="Symbol">(</a><a id="4186" href="foundation-core.operations-spans.html#4186" class="Bound">g&#39;</a> <a id="4189" class="Symbol">:</a> <a id="4191" href="foundation-core.operations-spans.html#4160" class="Bound">S&#39;</a> <a id="4194" class="Symbol">→</a> <a id="4196" href="foundation-core.operations-spans.html#4173" class="Bound">B&#39;</a><a id="4198" class="Symbol">)</a>
  <a id="4202" class="Symbol">(</a><a id="4203" href="foundation-core.operations-spans.html#4203" class="Bound">h</a> <a id="4205" class="Symbol">:</a> <a id="4207" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="4217" href="foundation-core.operations-spans.html#4186" class="Bound">g&#39;</a> <a id="4220" class="Symbol">(</a><a id="4221" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="4236" href="foundation-core.operations-spans.html#4140" class="Bound">s</a><a id="4237" class="Symbol">))</a>
  <a id="4242" class="Keyword">where</a>

  <a id="4251" href="foundation-core.operations-spans.html#4251" class="Function">spanning-type-right-concat-hom-arrow-span</a> <a id="4293" class="Symbol">:</a> <a id="4295" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4298" href="foundation-core.operations-spans.html#4098" class="Bound">l4</a>
  <a id="4303" href="foundation-core.operations-spans.html#4251" class="Function">spanning-type-right-concat-hom-arrow-span</a> <a id="4345" class="Symbol">=</a> <a id="4347" href="foundation-core.operations-spans.html#4160" class="Bound">S&#39;</a>

  <a id="4353" href="foundation-core.operations-spans.html#4353" class="Function">left-map-right-concat-hom-arrow-span</a> <a id="4390" class="Symbol">:</a>
    <a id="4396" href="foundation-core.operations-spans.html#4251" class="Function">spanning-type-right-concat-hom-arrow-span</a> <a id="4438" class="Symbol">→</a> <a id="4440" href="foundation-core.operations-spans.html#4114" class="Bound">A</a>
  <a id="4444" href="foundation-core.operations-spans.html#4353" class="Function">left-map-right-concat-hom-arrow-span</a> <a id="4481" class="Symbol">=</a>
    <a id="4487" href="foundation.spans.html#2108" class="Function">left-map-span</a> <a id="4501" href="foundation-core.operations-spans.html#4140" class="Bound">s</a> <a id="4503" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4505" href="foundation.morphisms-arrows.html#1743" class="Function">map-domain-hom-arrow</a> <a id="4526" href="foundation-core.operations-spans.html#4186" class="Bound">g&#39;</a> <a id="4529" class="Symbol">(</a><a id="4530" href="foundation.spans.html#2180" class="Function">right-map-span</a> <a id="4545" href="foundation-core.operations-spans.html#4140" class="Bound">s</a><a id="4546" class="Symbol">)</a> <a id="4548" href="foundation-core.operations-spans.html#4203" class="Bound">h</a>

  <a id="4553" href="foundation-core.operations-spans.html#4553" class="Function">right-map-right-concat-hom-arrow-span</a> <a id="4591" class="Symbol">:</a>
    <a id="4597" href="foundation-core.operations-spans.html#4251" class="Function">spanning-type-right-concat-hom-arrow-span</a> <a id="4639" class="Symbol">→</a> <a id="4641" href="foundation-core.operations-spans.html#4173" class="Bound">B&#39;</a>
  <a id="4646" href="foundation-core.operations-spans.html#4553" class="Function">right-map-right-concat-hom-arrow-span</a> <a id="4684" class="Symbol">=</a> <a id="4686" href="foundation-core.operations-spans.html#4186" class="Bound">g&#39;</a>

  <a id="4692" href="foundation-core.operations-spans.html#4692" class="Function">right-concat-hom-arrow-span</a> <a id="4720" class="Symbol">:</a> <a id="4722" href="foundation.spans.html#1830" class="Function">span</a> <a id="4727" href="foundation-core.operations-spans.html#4098" class="Bound">l4</a> <a id="4730" href="foundation-core.operations-spans.html#4114" class="Bound">A</a> <a id="4732" href="foundation-core.operations-spans.html#4173" class="Bound">B&#39;</a>
  <a id="4737" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4741" href="foundation-core.operations-spans.html#4692" class="Function">right-concat-hom-arrow-span</a> <a id="4769" class="Symbol">=</a> <a id="4771" href="foundation-core.operations-spans.html#4251" class="Function">spanning-type-right-concat-hom-arrow-span</a>
  <a id="4815" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4819" class="Symbol">(</a><a id="4820" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4824" href="foundation-core.operations-spans.html#4692" class="Function">right-concat-hom-arrow-span</a><a id="4851" class="Symbol">)</a> <a id="4853" class="Symbol">=</a> <a id="4855" href="foundation-core.operations-spans.html#4353" class="Function">left-map-right-concat-hom-arrow-span</a>
  <a id="4894" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4898" class="Symbol">(</a><a id="4899" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4903" href="foundation-core.operations-spans.html#4692" class="Function">right-concat-hom-arrow-span</a><a id="4930" class="Symbol">)</a> <a id="4932" class="Symbol">=</a> <a id="4934" href="foundation-core.operations-spans.html#4553" class="Function">right-map-right-concat-hom-arrow-span</a>
</pre>