# Operations on span diagrams

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="foundation-core.operations-span-diagrams.html" class="Module">foundation-core.operations-span-diagrams</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation.operations-spans.html" class="Module">foundation.operations-spans</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="334" class="Keyword">open</a> <a id="339" class="Keyword">import</a> <a id="346" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

This file contains some operations on
[span diagrams](foundation.span-diagrams.md) that produce new span diagrams from
given span diagrams and possibly other data.

## Definitions

### Concatenating span diagrams and maps on both sides

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and maps `i : A → A'` and `j : B → B'`. The
{{#concept "concatenation-span-diagram" Disambiguation="span diagram" Agda=concat-span-diagram}}
of `𝒮`, `i`, and `j` is the span diagram

```text
       i ∘ f     j ∘ g
  A' <------- S -------> B'.
```

<pre class="Agda"><a id="1057" class="Keyword">module</a> <a id="1064" href="foundation-core.operations-span-diagrams.html#1064" class="Module">_</a>
  <a id="1068" class="Symbol">{</a><a id="1069" href="foundation-core.operations-span-diagrams.html#1069" class="Bound">l1</a> <a id="1072" href="foundation-core.operations-span-diagrams.html#1072" class="Bound">l2</a> <a id="1075" href="foundation-core.operations-span-diagrams.html#1075" class="Bound">l3</a> <a id="1078" href="foundation-core.operations-span-diagrams.html#1078" class="Bound">l4</a> <a id="1081" href="foundation-core.operations-span-diagrams.html#1081" class="Bound">l5</a> <a id="1084" class="Symbol">:</a> <a id="1086" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1091" class="Symbol">}</a>
  <a id="1095" class="Keyword">where</a>

  <a id="1104" href="foundation-core.operations-span-diagrams.html#1104" class="Function">concat-span-diagram</a> <a id="1124" class="Symbol">:</a>
    <a id="1130" class="Symbol">(</a><a id="1131" href="foundation-core.operations-span-diagrams.html#1131" class="Bound">𝒮</a> <a id="1133" class="Symbol">:</a> <a id="1135" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1148" href="foundation-core.operations-span-diagrams.html#1069" class="Bound">l1</a> <a id="1151" href="foundation-core.operations-span-diagrams.html#1072" class="Bound">l2</a> <a id="1154" href="foundation-core.operations-span-diagrams.html#1075" class="Bound">l3</a><a id="1156" class="Symbol">)</a>
    <a id="1162" class="Symbol">{</a><a id="1163" href="foundation-core.operations-span-diagrams.html#1163" class="Bound">A&#39;</a> <a id="1166" class="Symbol">:</a> <a id="1168" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1171" href="foundation-core.operations-span-diagrams.html#1078" class="Bound">l4</a><a id="1173" class="Symbol">}</a> <a id="1175" class="Symbol">(</a><a id="1176" href="foundation-core.operations-span-diagrams.html#1176" class="Bound">f</a> <a id="1178" class="Symbol">:</a> <a id="1180" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="1200" href="foundation-core.operations-span-diagrams.html#1131" class="Bound">𝒮</a> <a id="1202" class="Symbol">→</a> <a id="1204" href="foundation-core.operations-span-diagrams.html#1163" class="Bound">A&#39;</a><a id="1206" class="Symbol">)</a>
    <a id="1212" class="Symbol">{</a><a id="1213" href="foundation-core.operations-span-diagrams.html#1213" class="Bound">B&#39;</a> <a id="1216" class="Symbol">:</a> <a id="1218" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1221" href="foundation-core.operations-span-diagrams.html#1081" class="Bound">l5</a><a id="1223" class="Symbol">}</a> <a id="1225" class="Symbol">(</a><a id="1226" href="foundation-core.operations-span-diagrams.html#1226" class="Bound">g</a> <a id="1228" class="Symbol">:</a> <a id="1230" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="1252" href="foundation-core.operations-span-diagrams.html#1131" class="Bound">𝒮</a> <a id="1254" class="Symbol">→</a> <a id="1256" href="foundation-core.operations-span-diagrams.html#1213" class="Bound">B&#39;</a><a id="1258" class="Symbol">)</a> <a id="1260" class="Symbol">→</a>
    <a id="1266" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1279" href="foundation-core.operations-span-diagrams.html#1078" class="Bound">l4</a> <a id="1282" href="foundation-core.operations-span-diagrams.html#1081" class="Bound">l5</a> <a id="1285" href="foundation-core.operations-span-diagrams.html#1075" class="Bound">l3</a>
  <a id="1290" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1294" class="Symbol">(</a><a id="1295" href="foundation-core.operations-span-diagrams.html#1104" class="Function">concat-span-diagram</a> <a id="1315" href="foundation-core.operations-span-diagrams.html#1315" class="Bound">𝒮</a> <a id="1317" class="Symbol">{</a><a id="1318" href="foundation-core.operations-span-diagrams.html#1318" class="Bound">A&#39;</a><a id="1320" class="Symbol">}</a> <a id="1322" href="foundation-core.operations-span-diagrams.html#1322" class="Bound">f</a> <a id="1324" class="Symbol">{</a><a id="1325" href="foundation-core.operations-span-diagrams.html#1325" class="Bound">B&#39;</a><a id="1327" class="Symbol">}</a> <a id="1329" href="foundation-core.operations-span-diagrams.html#1329" class="Bound">g</a><a id="1330" class="Symbol">)</a> <a id="1332" class="Symbol">=</a>
    <a id="1338" href="foundation-core.operations-span-diagrams.html#1318" class="Bound">A&#39;</a>
  <a id="1343" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1347" class="Symbol">(</a><a id="1348" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1352" class="Symbol">(</a><a id="1353" href="foundation-core.operations-span-diagrams.html#1104" class="Function">concat-span-diagram</a> <a id="1373" href="foundation-core.operations-span-diagrams.html#1373" class="Bound">𝒮</a> <a id="1375" class="Symbol">{</a><a id="1376" href="foundation-core.operations-span-diagrams.html#1376" class="Bound">A&#39;</a><a id="1378" class="Symbol">}</a> <a id="1380" href="foundation-core.operations-span-diagrams.html#1380" class="Bound">f</a> <a id="1382" class="Symbol">{</a><a id="1383" href="foundation-core.operations-span-diagrams.html#1383" class="Bound">B&#39;</a><a id="1385" class="Symbol">}</a> <a id="1387" href="foundation-core.operations-span-diagrams.html#1387" class="Bound">g</a><a id="1388" class="Symbol">))</a> <a id="1391" class="Symbol">=</a>
    <a id="1397" href="foundation-core.operations-span-diagrams.html#1383" class="Bound">B&#39;</a>
  <a id="1402" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1406" class="Symbol">(</a><a id="1407" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1411" class="Symbol">(</a><a id="1412" href="foundation-core.operations-span-diagrams.html#1104" class="Function">concat-span-diagram</a> <a id="1432" href="foundation-core.operations-span-diagrams.html#1432" class="Bound">𝒮</a> <a id="1434" class="Symbol">{</a><a id="1435" href="foundation-core.operations-span-diagrams.html#1435" class="Bound">A&#39;</a><a id="1437" class="Symbol">}</a> <a id="1439" href="foundation-core.operations-span-diagrams.html#1439" class="Bound">f</a> <a id="1441" class="Symbol">{</a><a id="1442" href="foundation-core.operations-span-diagrams.html#1442" class="Bound">B&#39;</a><a id="1444" class="Symbol">}</a> <a id="1446" href="foundation-core.operations-span-diagrams.html#1446" class="Bound">g</a><a id="1447" class="Symbol">))</a> <a id="1450" class="Symbol">=</a>
    <a id="1456" href="foundation-core.operations-spans.html#976" class="Function">concat-span</a> <a id="1468" class="Symbol">(</a><a id="1469" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="1487" href="foundation-core.operations-span-diagrams.html#1432" class="Bound">𝒮</a><a id="1488" class="Symbol">)</a> <a id="1490" href="foundation-core.operations-span-diagrams.html#1439" class="Bound">f</a> <a id="1492" href="foundation-core.operations-span-diagrams.html#1446" class="Bound">g</a>
</pre>
### Concatenating span diagrams and maps on the left

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a map `i : A → A'`. The
{{#concept "left concatenation" Disambiguation="span diagram" Agda=left-concat-span-diagram}}
of `𝒮` and `i` is the span diagram

```text
       i ∘ f      g
  A' <------- S -----> B.
```

<pre class="Agda"><a id="1899" class="Keyword">module</a> <a id="1906" href="foundation-core.operations-span-diagrams.html#1906" class="Module">_</a>
  <a id="1910" class="Symbol">{</a><a id="1911" href="foundation-core.operations-span-diagrams.html#1911" class="Bound">l1</a> <a id="1914" href="foundation-core.operations-span-diagrams.html#1914" class="Bound">l2</a> <a id="1917" href="foundation-core.operations-span-diagrams.html#1917" class="Bound">l3</a> <a id="1920" href="foundation-core.operations-span-diagrams.html#1920" class="Bound">l4</a> <a id="1923" class="Symbol">:</a> <a id="1925" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1930" class="Symbol">}</a>
  <a id="1934" class="Keyword">where</a>

  <a id="1943" href="foundation-core.operations-span-diagrams.html#1943" class="Function">left-concat-span-diagram</a> <a id="1968" class="Symbol">:</a>
    <a id="1974" class="Symbol">(</a><a id="1975" href="foundation-core.operations-span-diagrams.html#1975" class="Bound">𝒮</a> <a id="1977" class="Symbol">:</a> <a id="1979" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1992" href="foundation-core.operations-span-diagrams.html#1911" class="Bound">l1</a> <a id="1995" href="foundation-core.operations-span-diagrams.html#1914" class="Bound">l2</a> <a id="1998" href="foundation-core.operations-span-diagrams.html#1917" class="Bound">l3</a><a id="2000" class="Symbol">)</a> <a id="2002" class="Symbol">{</a><a id="2003" href="foundation-core.operations-span-diagrams.html#2003" class="Bound">A&#39;</a> <a id="2006" class="Symbol">:</a> <a id="2008" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2011" href="foundation-core.operations-span-diagrams.html#1920" class="Bound">l4</a><a id="2013" class="Symbol">}</a> <a id="2015" class="Symbol">→</a>
    <a id="2021" class="Symbol">(</a><a id="2022" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="2042" href="foundation-core.operations-span-diagrams.html#1975" class="Bound">𝒮</a> <a id="2044" class="Symbol">→</a> <a id="2046" href="foundation-core.operations-span-diagrams.html#2003" class="Bound">A&#39;</a><a id="2048" class="Symbol">)</a> <a id="2050" class="Symbol">→</a> <a id="2052" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2065" href="foundation-core.operations-span-diagrams.html#1920" class="Bound">l4</a> <a id="2068" href="foundation-core.operations-span-diagrams.html#1914" class="Bound">l2</a> <a id="2071" href="foundation-core.operations-span-diagrams.html#1917" class="Bound">l3</a>
  <a id="2076" href="foundation-core.operations-span-diagrams.html#1943" class="Function">left-concat-span-diagram</a> <a id="2101" href="foundation-core.operations-span-diagrams.html#2101" class="Bound">𝒮</a> <a id="2103" href="foundation-core.operations-span-diagrams.html#2103" class="Bound">f</a> <a id="2105" class="Symbol">=</a> <a id="2107" href="foundation-core.operations-span-diagrams.html#1104" class="Function">concat-span-diagram</a> <a id="2127" href="foundation-core.operations-span-diagrams.html#2101" class="Bound">𝒮</a> <a id="2129" href="foundation-core.operations-span-diagrams.html#2103" class="Bound">f</a> <a id="2131" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>
### Concatenating span diagrams and maps on the right

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a map `j : B → B'`. The
{{#concept "right concatenation" Disambiguation="span diagram" Agda=right-concat-span-diagram}}
of `𝒮` by `j` is the span diagram

```text
        f      j ∘ g
  A' <----- S -------> B'.
```

<pre class="Agda"><a id="2543" class="Keyword">module</a> <a id="2550" href="foundation-core.operations-span-diagrams.html#2550" class="Module">_</a>
  <a id="2554" class="Symbol">{</a><a id="2555" href="foundation-core.operations-span-diagrams.html#2555" class="Bound">l1</a> <a id="2558" href="foundation-core.operations-span-diagrams.html#2558" class="Bound">l2</a> <a id="2561" href="foundation-core.operations-span-diagrams.html#2561" class="Bound">l3</a> <a id="2564" href="foundation-core.operations-span-diagrams.html#2564" class="Bound">l4</a> <a id="2567" class="Symbol">:</a> <a id="2569" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2574" class="Symbol">}</a>
  <a id="2578" class="Keyword">where</a>

  <a id="2587" href="foundation-core.operations-span-diagrams.html#2587" class="Function">right-concat-span-diagram</a> <a id="2613" class="Symbol">:</a>
    <a id="2619" class="Symbol">(</a><a id="2620" href="foundation-core.operations-span-diagrams.html#2620" class="Bound">𝒮</a> <a id="2622" class="Symbol">:</a> <a id="2624" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2637" href="foundation-core.operations-span-diagrams.html#2555" class="Bound">l1</a> <a id="2640" href="foundation-core.operations-span-diagrams.html#2558" class="Bound">l2</a> <a id="2643" href="foundation-core.operations-span-diagrams.html#2561" class="Bound">l3</a><a id="2645" class="Symbol">)</a> <a id="2647" class="Symbol">{</a><a id="2648" href="foundation-core.operations-span-diagrams.html#2648" class="Bound">B&#39;</a> <a id="2651" class="Symbol">:</a> <a id="2653" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2656" href="foundation-core.operations-span-diagrams.html#2564" class="Bound">l4</a><a id="2658" class="Symbol">}</a> <a id="2660" class="Symbol">→</a>
    <a id="2666" class="Symbol">(</a><a id="2667" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="2689" href="foundation-core.operations-span-diagrams.html#2620" class="Bound">𝒮</a> <a id="2691" class="Symbol">→</a> <a id="2693" href="foundation-core.operations-span-diagrams.html#2648" class="Bound">B&#39;</a><a id="2695" class="Symbol">)</a> <a id="2697" class="Symbol">→</a> <a id="2699" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="2712" href="foundation-core.operations-span-diagrams.html#2555" class="Bound">l1</a> <a id="2715" href="foundation-core.operations-span-diagrams.html#2564" class="Bound">l4</a> <a id="2718" href="foundation-core.operations-span-diagrams.html#2561" class="Bound">l3</a>
  <a id="2723" href="foundation-core.operations-span-diagrams.html#2587" class="Function">right-concat-span-diagram</a> <a id="2749" href="foundation-core.operations-span-diagrams.html#2749" class="Bound">𝒮</a> <a id="2751" href="foundation-core.operations-span-diagrams.html#2751" class="Bound">g</a> <a id="2753" class="Symbol">=</a> <a id="2755" href="foundation-core.operations-span-diagrams.html#1104" class="Function">concat-span-diagram</a> <a id="2775" href="foundation-core.operations-span-diagrams.html#2749" class="Bound">𝒮</a> <a id="2777" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2780" href="foundation-core.operations-span-diagrams.html#2751" class="Bound">g</a>
</pre>
### Concatenation of span diagrams and morphisms of arrows on the left

Consider a span diagram `𝒮` given by

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

Then we obtain a span diagram `A' <- S' -> B`.

<pre class="Agda"><a id="3254" class="Keyword">module</a> <a id="3261" href="foundation-core.operations-span-diagrams.html#3261" class="Module">_</a>
  <a id="3265" class="Symbol">{</a><a id="3266" href="foundation-core.operations-span-diagrams.html#3266" class="Bound">l1</a> <a id="3269" href="foundation-core.operations-span-diagrams.html#3269" class="Bound">l2</a> <a id="3272" href="foundation-core.operations-span-diagrams.html#3272" class="Bound">l3</a> <a id="3275" href="foundation-core.operations-span-diagrams.html#3275" class="Bound">l4</a> <a id="3278" href="foundation-core.operations-span-diagrams.html#3278" class="Bound">l5</a> <a id="3281" class="Symbol">:</a> <a id="3283" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3288" class="Symbol">}</a> <a id="3290" class="Symbol">(</a><a id="3291" href="foundation-core.operations-span-diagrams.html#3291" class="Bound">𝒮</a> <a id="3293" class="Symbol">:</a> <a id="3295" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="3308" href="foundation-core.operations-span-diagrams.html#3266" class="Bound">l1</a> <a id="3311" href="foundation-core.operations-span-diagrams.html#3269" class="Bound">l2</a> <a id="3314" href="foundation-core.operations-span-diagrams.html#3272" class="Bound">l3</a><a id="3316" class="Symbol">)</a>
  <a id="3320" class="Symbol">{</a><a id="3321" href="foundation-core.operations-span-diagrams.html#3321" class="Bound">S&#39;</a> <a id="3324" class="Symbol">:</a> <a id="3326" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3329" href="foundation-core.operations-span-diagrams.html#3275" class="Bound">l4</a><a id="3331" class="Symbol">}</a> <a id="3333" class="Symbol">{</a><a id="3334" href="foundation-core.operations-span-diagrams.html#3334" class="Bound">A&#39;</a> <a id="3337" class="Symbol">:</a> <a id="3339" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3342" href="foundation-core.operations-span-diagrams.html#3278" class="Bound">l5</a><a id="3344" class="Symbol">}</a> <a id="3346" class="Symbol">(</a><a id="3347" href="foundation-core.operations-span-diagrams.html#3347" class="Bound">f&#39;</a> <a id="3350" class="Symbol">:</a> <a id="3352" href="foundation-core.operations-span-diagrams.html#3321" class="Bound">S&#39;</a> <a id="3355" class="Symbol">→</a> <a id="3357" href="foundation-core.operations-span-diagrams.html#3334" class="Bound">A&#39;</a><a id="3359" class="Symbol">)</a>
  <a id="3363" class="Symbol">(</a><a id="3364" href="foundation-core.operations-span-diagrams.html#3364" class="Bound">h</a> <a id="3366" class="Symbol">:</a> <a id="3368" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="3378" href="foundation-core.operations-span-diagrams.html#3347" class="Bound">f&#39;</a> <a id="3381" class="Symbol">(</a><a id="3382" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="3404" href="foundation-core.operations-span-diagrams.html#3291" class="Bound">𝒮</a><a id="3405" class="Symbol">))</a>
  <a id="3410" class="Keyword">where</a>

  <a id="3419" href="foundation-core.operations-span-diagrams.html#3419" class="Function">domain-left-concat-hom-arrow-span-diagram</a> <a id="3461" class="Symbol">:</a> <a id="3463" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3466" href="foundation-core.operations-span-diagrams.html#3278" class="Bound">l5</a>
  <a id="3471" href="foundation-core.operations-span-diagrams.html#3419" class="Function">domain-left-concat-hom-arrow-span-diagram</a> <a id="3513" class="Symbol">=</a> <a id="3515" href="foundation-core.operations-span-diagrams.html#3334" class="Bound">A&#39;</a>

  <a id="3521" href="foundation-core.operations-span-diagrams.html#3521" class="Function">codomain-left-concat-hom-arrow-span-diagram</a> <a id="3565" class="Symbol">:</a> <a id="3567" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3570" href="foundation-core.operations-span-diagrams.html#3269" class="Bound">l2</a>
  <a id="3575" href="foundation-core.operations-span-diagrams.html#3521" class="Function">codomain-left-concat-hom-arrow-span-diagram</a> <a id="3619" class="Symbol">=</a> <a id="3621" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="3643" href="foundation-core.operations-span-diagrams.html#3291" class="Bound">𝒮</a>

  <a id="3648" href="foundation-core.operations-span-diagrams.html#3648" class="Function">span-left-concat-hom-arrow-span-diagram</a> <a id="3688" class="Symbol">:</a>
    <a id="3694" href="foundation.spans.html#1830" class="Function">span</a> <a id="3699" href="foundation-core.operations-span-diagrams.html#3275" class="Bound">l4</a>
      <a id="3708" class="Symbol">(</a> <a id="3710" href="foundation-core.operations-span-diagrams.html#3419" class="Function">domain-left-concat-hom-arrow-span-diagram</a><a id="3751" class="Symbol">)</a>
      <a id="3759" class="Symbol">(</a> <a id="3761" href="foundation-core.operations-span-diagrams.html#3521" class="Function">codomain-left-concat-hom-arrow-span-diagram</a><a id="3804" class="Symbol">)</a>
  <a id="3808" href="foundation-core.operations-span-diagrams.html#3648" class="Function">span-left-concat-hom-arrow-span-diagram</a> <a id="3848" class="Symbol">=</a>
    <a id="3854" href="foundation-core.operations-spans.html#3335" class="Function">left-concat-hom-arrow-span</a>
      <a id="3887" class="Symbol">(</a> <a id="3889" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="3907" href="foundation-core.operations-span-diagrams.html#3291" class="Bound">𝒮</a><a id="3908" class="Symbol">)</a>
      <a id="3916" class="Symbol">(</a> <a id="3918" href="foundation-core.operations-span-diagrams.html#3347" class="Bound">f&#39;</a><a id="3920" class="Symbol">)</a>
      <a id="3928" class="Symbol">(</a> <a id="3930" href="foundation-core.operations-span-diagrams.html#3364" class="Bound">h</a><a id="3931" class="Symbol">)</a>

  <a id="3936" href="foundation-core.operations-span-diagrams.html#3936" class="Function">left-concat-hom-arrow-span-diagram</a> <a id="3971" class="Symbol">:</a> <a id="3973" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="3986" href="foundation-core.operations-span-diagrams.html#3278" class="Bound">l5</a> <a id="3989" href="foundation-core.operations-span-diagrams.html#3269" class="Bound">l2</a> <a id="3992" href="foundation-core.operations-span-diagrams.html#3275" class="Bound">l4</a>
  <a id="3997" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4001" href="foundation-core.operations-span-diagrams.html#3936" class="Function">left-concat-hom-arrow-span-diagram</a> <a id="4036" class="Symbol">=</a>
    <a id="4042" href="foundation-core.operations-span-diagrams.html#3419" class="Function">domain-left-concat-hom-arrow-span-diagram</a>
  <a id="4086" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4090" class="Symbol">(</a><a id="4091" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4095" href="foundation-core.operations-span-diagrams.html#3936" class="Function">left-concat-hom-arrow-span-diagram</a><a id="4129" class="Symbol">)</a> <a id="4131" class="Symbol">=</a>
    <a id="4137" href="foundation-core.operations-span-diagrams.html#3521" class="Function">codomain-left-concat-hom-arrow-span-diagram</a>
  <a id="4183" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4187" class="Symbol">(</a><a id="4188" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4192" href="foundation-core.operations-span-diagrams.html#3936" class="Function">left-concat-hom-arrow-span-diagram</a><a id="4226" class="Symbol">)</a> <a id="4228" class="Symbol">=</a>
    <a id="4234" href="foundation-core.operations-span-diagrams.html#3648" class="Function">span-left-concat-hom-arrow-span-diagram</a>

  <a id="4277" href="foundation-core.operations-span-diagrams.html#4277" class="Function">spanning-type-left-concat-hom-arrow-span-diagram</a> <a id="4326" class="Symbol">:</a> <a id="4328" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4331" href="foundation-core.operations-span-diagrams.html#3275" class="Bound">l4</a>
  <a id="4336" href="foundation-core.operations-span-diagrams.html#4277" class="Function">spanning-type-left-concat-hom-arrow-span-diagram</a> <a id="4385" class="Symbol">=</a>
    <a id="4391" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="4418" href="foundation-core.operations-span-diagrams.html#3936" class="Function">left-concat-hom-arrow-span-diagram</a>

  <a id="4456" href="foundation-core.operations-span-diagrams.html#4456" class="Function">left-map-left-concat-hom-arrow-span-diagram</a> <a id="4500" class="Symbol">:</a>
    <a id="4506" href="foundation-core.operations-span-diagrams.html#4277" class="Function">spanning-type-left-concat-hom-arrow-span-diagram</a> <a id="4555" class="Symbol">→</a>
    <a id="4561" href="foundation-core.operations-span-diagrams.html#3419" class="Function">domain-left-concat-hom-arrow-span-diagram</a>
  <a id="4605" href="foundation-core.operations-span-diagrams.html#4456" class="Function">left-map-left-concat-hom-arrow-span-diagram</a> <a id="4649" class="Symbol">=</a>
    <a id="4655" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="4677" href="foundation-core.operations-span-diagrams.html#3936" class="Function">left-concat-hom-arrow-span-diagram</a>

  <a id="4715" href="foundation-core.operations-span-diagrams.html#4715" class="Function">right-map-left-concat-hom-arrow-span-diagram</a> <a id="4760" class="Symbol">:</a>
    <a id="4766" href="foundation-core.operations-span-diagrams.html#4277" class="Function">spanning-type-left-concat-hom-arrow-span-diagram</a> <a id="4815" class="Symbol">→</a>
    <a id="4821" href="foundation-core.operations-span-diagrams.html#3521" class="Function">codomain-left-concat-hom-arrow-span-diagram</a>
  <a id="4867" href="foundation-core.operations-span-diagrams.html#4715" class="Function">right-map-left-concat-hom-arrow-span-diagram</a> <a id="4912" class="Symbol">=</a>
    <a id="4918" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="4941" href="foundation-core.operations-span-diagrams.html#3936" class="Function">left-concat-hom-arrow-span-diagram</a>
</pre>
### Concatenation of span diagrams and morphisms of arrows on the right

Consider a span diagram `𝒮` given by

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

Then we obtain a span diagram `A <- S' -> B'`.

<pre class="Agda"><a id="5472" class="Keyword">module</a> <a id="5479" href="foundation-core.operations-span-diagrams.html#5479" class="Module">_</a>
  <a id="5483" class="Symbol">{</a><a id="5484" href="foundation-core.operations-span-diagrams.html#5484" class="Bound">l1</a> <a id="5487" href="foundation-core.operations-span-diagrams.html#5487" class="Bound">l2</a> <a id="5490" href="foundation-core.operations-span-diagrams.html#5490" class="Bound">l3</a> <a id="5493" href="foundation-core.operations-span-diagrams.html#5493" class="Bound">l4</a> <a id="5496" href="foundation-core.operations-span-diagrams.html#5496" class="Bound">l5</a> <a id="5499" class="Symbol">:</a> <a id="5501" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5506" class="Symbol">}</a> <a id="5508" class="Symbol">(</a><a id="5509" href="foundation-core.operations-span-diagrams.html#5509" class="Bound">𝒮</a> <a id="5511" class="Symbol">:</a> <a id="5513" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="5526" href="foundation-core.operations-span-diagrams.html#5484" class="Bound">l1</a> <a id="5529" href="foundation-core.operations-span-diagrams.html#5487" class="Bound">l2</a> <a id="5532" href="foundation-core.operations-span-diagrams.html#5490" class="Bound">l3</a><a id="5534" class="Symbol">)</a>
  <a id="5538" class="Symbol">{</a><a id="5539" href="foundation-core.operations-span-diagrams.html#5539" class="Bound">S&#39;</a> <a id="5542" class="Symbol">:</a> <a id="5544" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5547" href="foundation-core.operations-span-diagrams.html#5493" class="Bound">l4</a><a id="5549" class="Symbol">}</a> <a id="5551" class="Symbol">{</a><a id="5552" href="foundation-core.operations-span-diagrams.html#5552" class="Bound">B&#39;</a> <a id="5555" class="Symbol">:</a> <a id="5557" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5560" href="foundation-core.operations-span-diagrams.html#5496" class="Bound">l5</a><a id="5562" class="Symbol">}</a> <a id="5564" class="Symbol">(</a><a id="5565" href="foundation-core.operations-span-diagrams.html#5565" class="Bound">g&#39;</a> <a id="5568" class="Symbol">:</a> <a id="5570" href="foundation-core.operations-span-diagrams.html#5539" class="Bound">S&#39;</a> <a id="5573" class="Symbol">→</a> <a id="5575" href="foundation-core.operations-span-diagrams.html#5552" class="Bound">B&#39;</a><a id="5577" class="Symbol">)</a>
  <a id="5581" class="Symbol">(</a><a id="5582" href="foundation-core.operations-span-diagrams.html#5582" class="Bound">h</a> <a id="5584" class="Symbol">:</a> <a id="5586" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="5596" href="foundation-core.operations-span-diagrams.html#5565" class="Bound">g&#39;</a> <a id="5599" class="Symbol">(</a><a id="5600" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="5623" href="foundation-core.operations-span-diagrams.html#5509" class="Bound">𝒮</a><a id="5624" class="Symbol">))</a>
  <a id="5629" class="Keyword">where</a>

  <a id="5638" href="foundation-core.operations-span-diagrams.html#5638" class="Function">domain-right-concat-hom-arrow-span-diagram</a> <a id="5681" class="Symbol">:</a> <a id="5683" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5686" href="foundation-core.operations-span-diagrams.html#5484" class="Bound">l1</a>
  <a id="5691" href="foundation-core.operations-span-diagrams.html#5638" class="Function">domain-right-concat-hom-arrow-span-diagram</a> <a id="5734" class="Symbol">=</a> <a id="5736" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="5756" href="foundation-core.operations-span-diagrams.html#5509" class="Bound">𝒮</a>

  <a id="5761" href="foundation-core.operations-span-diagrams.html#5761" class="Function">codomain-right-concat-hom-arrow-span-diagram</a> <a id="5806" class="Symbol">:</a> <a id="5808" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5811" href="foundation-core.operations-span-diagrams.html#5496" class="Bound">l5</a>
  <a id="5816" href="foundation-core.operations-span-diagrams.html#5761" class="Function">codomain-right-concat-hom-arrow-span-diagram</a> <a id="5861" class="Symbol">=</a> <a id="5863" href="foundation-core.operations-span-diagrams.html#5552" class="Bound">B&#39;</a>

  <a id="5869" href="foundation-core.operations-span-diagrams.html#5869" class="Function">span-right-concat-hom-arrow-span-diagram</a> <a id="5910" class="Symbol">:</a>
    <a id="5916" href="foundation.spans.html#1830" class="Function">span</a> <a id="5921" href="foundation-core.operations-span-diagrams.html#5493" class="Bound">l4</a>
      <a id="5930" class="Symbol">(</a> <a id="5932" href="foundation-core.operations-span-diagrams.html#5638" class="Function">domain-right-concat-hom-arrow-span-diagram</a><a id="5974" class="Symbol">)</a>
      <a id="5982" class="Symbol">(</a> <a id="5984" href="foundation-core.operations-span-diagrams.html#5761" class="Function">codomain-right-concat-hom-arrow-span-diagram</a><a id="6028" class="Symbol">)</a>
  <a id="6032" href="foundation-core.operations-span-diagrams.html#5869" class="Function">span-right-concat-hom-arrow-span-diagram</a> <a id="6073" class="Symbol">=</a>
    <a id="6079" href="foundation-core.operations-spans.html#4692" class="Function">right-concat-hom-arrow-span</a>
      <a id="6113" class="Symbol">(</a> <a id="6115" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="6133" href="foundation-core.operations-span-diagrams.html#5509" class="Bound">𝒮</a><a id="6134" class="Symbol">)</a>
      <a id="6142" class="Symbol">(</a> <a id="6144" href="foundation-core.operations-span-diagrams.html#5565" class="Bound">g&#39;</a><a id="6146" class="Symbol">)</a>
      <a id="6154" class="Symbol">(</a> <a id="6156" href="foundation-core.operations-span-diagrams.html#5582" class="Bound">h</a><a id="6157" class="Symbol">)</a>

  <a id="6162" href="foundation-core.operations-span-diagrams.html#6162" class="Function">right-concat-hom-arrow-span-diagram</a> <a id="6198" class="Symbol">:</a> <a id="6200" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="6213" href="foundation-core.operations-span-diagrams.html#5484" class="Bound">l1</a> <a id="6216" href="foundation-core.operations-span-diagrams.html#5496" class="Bound">l5</a> <a id="6219" href="foundation-core.operations-span-diagrams.html#5493" class="Bound">l4</a>
  <a id="6224" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="6228" href="foundation-core.operations-span-diagrams.html#6162" class="Function">right-concat-hom-arrow-span-diagram</a> <a id="6264" class="Symbol">=</a>
    <a id="6270" href="foundation-core.operations-span-diagrams.html#5638" class="Function">domain-right-concat-hom-arrow-span-diagram</a>
  <a id="6315" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="6319" class="Symbol">(</a><a id="6320" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="6324" href="foundation-core.operations-span-diagrams.html#6162" class="Function">right-concat-hom-arrow-span-diagram</a><a id="6359" class="Symbol">)</a> <a id="6361" class="Symbol">=</a>
    <a id="6367" href="foundation-core.operations-span-diagrams.html#5761" class="Function">codomain-right-concat-hom-arrow-span-diagram</a>
  <a id="6414" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="6418" class="Symbol">(</a><a id="6419" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="6423" href="foundation-core.operations-span-diagrams.html#6162" class="Function">right-concat-hom-arrow-span-diagram</a><a id="6458" class="Symbol">)</a> <a id="6460" class="Symbol">=</a>
    <a id="6466" href="foundation-core.operations-span-diagrams.html#5869" class="Function">span-right-concat-hom-arrow-span-diagram</a>

  <a id="6510" href="foundation-core.operations-span-diagrams.html#6510" class="Function">spanning-type-right-concat-hom-arrow-span-diagram</a> <a id="6560" class="Symbol">:</a> <a id="6562" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6565" href="foundation-core.operations-span-diagrams.html#5493" class="Bound">l4</a>
  <a id="6570" href="foundation-core.operations-span-diagrams.html#6510" class="Function">spanning-type-right-concat-hom-arrow-span-diagram</a> <a id="6620" class="Symbol">=</a>
    <a id="6626" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="6653" href="foundation-core.operations-span-diagrams.html#6162" class="Function">right-concat-hom-arrow-span-diagram</a>

  <a id="6692" href="foundation-core.operations-span-diagrams.html#6692" class="Function">left-map-right-concat-hom-arrow-span-diagram</a> <a id="6737" class="Symbol">:</a>
    <a id="6743" href="foundation-core.operations-span-diagrams.html#6510" class="Function">spanning-type-right-concat-hom-arrow-span-diagram</a> <a id="6793" class="Symbol">→</a>
    <a id="6799" href="foundation-core.operations-span-diagrams.html#5638" class="Function">domain-right-concat-hom-arrow-span-diagram</a>
  <a id="6844" href="foundation-core.operations-span-diagrams.html#6692" class="Function">left-map-right-concat-hom-arrow-span-diagram</a> <a id="6889" class="Symbol">=</a>
    <a id="6895" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="6917" href="foundation-core.operations-span-diagrams.html#6162" class="Function">right-concat-hom-arrow-span-diagram</a>

  <a id="6956" href="foundation-core.operations-span-diagrams.html#6956" class="Function">right-map-right-concat-hom-arrow-span-diagram</a> <a id="7002" class="Symbol">:</a>
    <a id="7008" href="foundation-core.operations-span-diagrams.html#6510" class="Function">spanning-type-right-concat-hom-arrow-span-diagram</a> <a id="7058" class="Symbol">→</a>
    <a id="7064" href="foundation-core.operations-span-diagrams.html#5761" class="Function">codomain-right-concat-hom-arrow-span-diagram</a>
  <a id="7111" href="foundation-core.operations-span-diagrams.html#6956" class="Function">right-map-right-concat-hom-arrow-span-diagram</a> <a id="7157" class="Symbol">=</a>
    <a id="7163" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="7186" href="foundation-core.operations-span-diagrams.html#6162" class="Function">right-concat-hom-arrow-span-diagram</a>
</pre>