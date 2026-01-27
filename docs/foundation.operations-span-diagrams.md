# Operations on span diagrams

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="foundation.operations-span-diagrams.html" class="Module">foundation.operations-span-diagrams</a> <a id="83" class="Keyword">where</a>

<a id="90" class="Keyword">open</a> <a id="95" class="Keyword">import</a> <a id="102" href="foundation-core.operations-span-diagrams.html" class="Module">foundation-core.operations-span-diagrams</a> <a id="143" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.equivalences-arrows.html" class="Module">foundation.equivalences-arrows</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation.operations-spans.html" class="Module">foundation.operations-spans</a>
<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.spans.html" class="Module">foundation.spans</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

This file contains some further operations on
[span diagrams](foundation.span-diagrams.md) that produce new span diagrams from
given span diagrams and possibly other data. Previous operations on span
diagrams were defined in
[`foundation-core.operations-span-diagrams`](foundation-core.operations-span-diagrams.md).

## Definitions

### Concatenating span diagrams and equivalences of arrows on the left

Consider a span diagram `𝒮` given by

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

Then we obtain a span diagram `A' <- S' -> B`.

<pre class="Agda"><a id="1267" class="Keyword">module</a> <a id="1274" href="foundation.operations-span-diagrams.html#1274" class="Module">_</a>
  <a id="1278" class="Symbol">{</a><a id="1279" href="foundation.operations-span-diagrams.html#1279" class="Bound">l1</a> <a id="1282" href="foundation.operations-span-diagrams.html#1282" class="Bound">l2</a> <a id="1285" href="foundation.operations-span-diagrams.html#1285" class="Bound">l3</a> <a id="1288" href="foundation.operations-span-diagrams.html#1288" class="Bound">l4</a> <a id="1291" href="foundation.operations-span-diagrams.html#1291" class="Bound">l5</a> <a id="1294" class="Symbol">:</a> <a id="1296" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1301" class="Symbol">}</a> <a id="1303" class="Symbol">(</a><a id="1304" href="foundation.operations-span-diagrams.html#1304" class="Bound">𝒮</a> <a id="1306" class="Symbol">:</a> <a id="1308" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1321" href="foundation.operations-span-diagrams.html#1279" class="Bound">l1</a> <a id="1324" href="foundation.operations-span-diagrams.html#1282" class="Bound">l2</a> <a id="1327" href="foundation.operations-span-diagrams.html#1285" class="Bound">l3</a><a id="1329" class="Symbol">)</a>
  <a id="1333" class="Symbol">{</a><a id="1334" href="foundation.operations-span-diagrams.html#1334" class="Bound">S&#39;</a> <a id="1337" class="Symbol">:</a> <a id="1339" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1342" href="foundation.operations-span-diagrams.html#1288" class="Bound">l4</a><a id="1344" class="Symbol">}</a> <a id="1346" class="Symbol">{</a><a id="1347" href="foundation.operations-span-diagrams.html#1347" class="Bound">A&#39;</a> <a id="1350" class="Symbol">:</a> <a id="1352" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1355" href="foundation.operations-span-diagrams.html#1291" class="Bound">l5</a><a id="1357" class="Symbol">}</a> <a id="1359" class="Symbol">(</a><a id="1360" href="foundation.operations-span-diagrams.html#1360" class="Bound">f&#39;</a> <a id="1363" class="Symbol">:</a> <a id="1365" href="foundation.operations-span-diagrams.html#1334" class="Bound">S&#39;</a> <a id="1368" class="Symbol">→</a> <a id="1370" href="foundation.operations-span-diagrams.html#1347" class="Bound">A&#39;</a><a id="1372" class="Symbol">)</a>
  <a id="1376" class="Symbol">(</a><a id="1377" href="foundation.operations-span-diagrams.html#1377" class="Bound">h</a> <a id="1379" class="Symbol">:</a> <a id="1381" href="foundation.equivalences-arrows.html#2283" class="Function">equiv-arrow</a> <a id="1393" href="foundation.operations-span-diagrams.html#1360" class="Bound">f&#39;</a> <a id="1396" class="Symbol">(</a><a id="1397" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="1419" href="foundation.operations-span-diagrams.html#1304" class="Bound">𝒮</a><a id="1420" class="Symbol">))</a>
  <a id="1425" class="Keyword">where</a>

  <a id="1434" href="foundation.operations-span-diagrams.html#1434" class="Function">domain-left-concat-equiv-arrow-span-diagram</a> <a id="1478" class="Symbol">:</a> <a id="1480" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1483" href="foundation.operations-span-diagrams.html#1291" class="Bound">l5</a>
  <a id="1488" href="foundation.operations-span-diagrams.html#1434" class="Function">domain-left-concat-equiv-arrow-span-diagram</a> <a id="1532" class="Symbol">=</a> <a id="1534" href="foundation.operations-span-diagrams.html#1347" class="Bound">A&#39;</a>

  <a id="1540" href="foundation.operations-span-diagrams.html#1540" class="Function">codomain-left-concat-equiv-arrow-span-diagram</a> <a id="1586" class="Symbol">:</a> <a id="1588" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1591" href="foundation.operations-span-diagrams.html#1282" class="Bound">l2</a>
  <a id="1596" href="foundation.operations-span-diagrams.html#1540" class="Function">codomain-left-concat-equiv-arrow-span-diagram</a> <a id="1642" class="Symbol">=</a> <a id="1644" href="foundation.span-diagrams.html#2147" class="Function">codomain-span-diagram</a> <a id="1666" href="foundation.operations-span-diagrams.html#1304" class="Bound">𝒮</a>

  <a id="1671" href="foundation.operations-span-diagrams.html#1671" class="Function">span-left-concat-equiv-arrow-span-diagram</a> <a id="1713" class="Symbol">:</a>
    <a id="1719" href="foundation.spans.html#1830" class="Function">span</a> <a id="1724" href="foundation.operations-span-diagrams.html#1288" class="Bound">l4</a>
      <a id="1733" class="Symbol">(</a> <a id="1735" href="foundation.operations-span-diagrams.html#1434" class="Function">domain-left-concat-equiv-arrow-span-diagram</a><a id="1778" class="Symbol">)</a>
      <a id="1786" class="Symbol">(</a> <a id="1788" href="foundation.operations-span-diagrams.html#1540" class="Function">codomain-left-concat-equiv-arrow-span-diagram</a><a id="1833" class="Symbol">)</a>
  <a id="1837" href="foundation.operations-span-diagrams.html#1671" class="Function">span-left-concat-equiv-arrow-span-diagram</a> <a id="1879" class="Symbol">=</a>
    <a id="1885" href="foundation.operations-spans.html#1806" class="Function">left-concat-equiv-arrow-span</a> <a id="1914" class="Symbol">(</a><a id="1915" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="1933" href="foundation.operations-span-diagrams.html#1304" class="Bound">𝒮</a><a id="1934" class="Symbol">)</a> <a id="1936" href="foundation.operations-span-diagrams.html#1360" class="Bound">f&#39;</a> <a id="1939" href="foundation.operations-span-diagrams.html#1377" class="Bound">h</a>

  <a id="1944" href="foundation.operations-span-diagrams.html#1944" class="Function">left-concat-equiv-arrow-span-diagram</a> <a id="1981" class="Symbol">:</a> <a id="1983" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="1996" href="foundation.operations-span-diagrams.html#1291" class="Bound">l5</a> <a id="1999" href="foundation.operations-span-diagrams.html#1282" class="Bound">l2</a> <a id="2002" href="foundation.operations-span-diagrams.html#1288" class="Bound">l4</a>
  <a id="2007" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2011" href="foundation.operations-span-diagrams.html#1944" class="Function">left-concat-equiv-arrow-span-diagram</a> <a id="2048" class="Symbol">=</a>
    <a id="2054" href="foundation.operations-span-diagrams.html#1434" class="Function">domain-left-concat-equiv-arrow-span-diagram</a>
  <a id="2100" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2104" class="Symbol">(</a><a id="2105" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2109" href="foundation.operations-span-diagrams.html#1944" class="Function">left-concat-equiv-arrow-span-diagram</a><a id="2145" class="Symbol">)</a> <a id="2147" class="Symbol">=</a>
    <a id="2153" href="foundation.operations-span-diagrams.html#1540" class="Function">codomain-left-concat-equiv-arrow-span-diagram</a>
  <a id="2201" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2205" class="Symbol">(</a><a id="2206" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2210" href="foundation.operations-span-diagrams.html#1944" class="Function">left-concat-equiv-arrow-span-diagram</a><a id="2246" class="Symbol">)</a> <a id="2248" class="Symbol">=</a>
    <a id="2254" href="foundation.operations-span-diagrams.html#1671" class="Function">span-left-concat-equiv-arrow-span-diagram</a>

  <a id="2299" href="foundation.operations-span-diagrams.html#2299" class="Function">spanning-type-left-concat-equiv-arrow-span-diagram</a> <a id="2350" class="Symbol">:</a> <a id="2352" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2355" href="foundation.operations-span-diagrams.html#1288" class="Bound">l4</a>
  <a id="2360" href="foundation.operations-span-diagrams.html#2299" class="Function">spanning-type-left-concat-equiv-arrow-span-diagram</a> <a id="2411" class="Symbol">=</a>
    <a id="2417" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="2444" href="foundation.operations-span-diagrams.html#1944" class="Function">left-concat-equiv-arrow-span-diagram</a>

  <a id="2484" href="foundation.operations-span-diagrams.html#2484" class="Function">left-map-left-concat-equiv-arrow-span-diagram</a> <a id="2530" class="Symbol">:</a>
    <a id="2536" href="foundation.operations-span-diagrams.html#2299" class="Function">spanning-type-left-concat-equiv-arrow-span-diagram</a> <a id="2587" class="Symbol">→</a>
    <a id="2593" href="foundation.operations-span-diagrams.html#1434" class="Function">domain-left-concat-equiv-arrow-span-diagram</a>
  <a id="2639" href="foundation.operations-span-diagrams.html#2484" class="Function">left-map-left-concat-equiv-arrow-span-diagram</a> <a id="2685" class="Symbol">=</a>
    <a id="2691" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="2713" href="foundation.operations-span-diagrams.html#1944" class="Function">left-concat-equiv-arrow-span-diagram</a>

  <a id="2753" href="foundation.operations-span-diagrams.html#2753" class="Function">right-map-left-concat-equiv-arrow-span-diagram</a> <a id="2800" class="Symbol">:</a>
    <a id="2806" href="foundation.operations-span-diagrams.html#2299" class="Function">spanning-type-left-concat-equiv-arrow-span-diagram</a> <a id="2857" class="Symbol">→</a>
    <a id="2863" href="foundation.operations-span-diagrams.html#1540" class="Function">codomain-left-concat-equiv-arrow-span-diagram</a>
  <a id="2911" href="foundation.operations-span-diagrams.html#2753" class="Function">right-map-left-concat-equiv-arrow-span-diagram</a> <a id="2958" class="Symbol">=</a>
    <a id="2964" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="2987" href="foundation.operations-span-diagrams.html#1944" class="Function">left-concat-equiv-arrow-span-diagram</a>
</pre>
### Concatenating span diagrams and equivalences of arrows on the right

Consider a span diagram `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a [equivalence of arrows](foundation.equivalences-arrows.md)
`h : equiv-arrow g' g` as indicated in the diagram

```text
               g'
           S' ----> B'
           |        |
        h₀ | ≃    ≃ | h₁
           ∨        ∨
  A <----- S -----> B.
       f       g
```

Then we obtain a span diagram `A <- S' -> B'`.

<pre class="Agda"><a id="3528" class="Keyword">module</a> <a id="3535" href="foundation.operations-span-diagrams.html#3535" class="Module">_</a>
  <a id="3539" class="Symbol">{</a><a id="3540" href="foundation.operations-span-diagrams.html#3540" class="Bound">l1</a> <a id="3543" href="foundation.operations-span-diagrams.html#3543" class="Bound">l2</a> <a id="3546" href="foundation.operations-span-diagrams.html#3546" class="Bound">l3</a> <a id="3549" href="foundation.operations-span-diagrams.html#3549" class="Bound">l4</a> <a id="3552" href="foundation.operations-span-diagrams.html#3552" class="Bound">l5</a> <a id="3555" class="Symbol">:</a> <a id="3557" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3562" class="Symbol">}</a> <a id="3564" class="Symbol">(</a><a id="3565" href="foundation.operations-span-diagrams.html#3565" class="Bound">𝒮</a> <a id="3567" class="Symbol">:</a> <a id="3569" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="3582" href="foundation.operations-span-diagrams.html#3540" class="Bound">l1</a> <a id="3585" href="foundation.operations-span-diagrams.html#3543" class="Bound">l2</a> <a id="3588" href="foundation.operations-span-diagrams.html#3546" class="Bound">l3</a><a id="3590" class="Symbol">)</a>
  <a id="3594" class="Symbol">{</a><a id="3595" href="foundation.operations-span-diagrams.html#3595" class="Bound">S&#39;</a> <a id="3598" class="Symbol">:</a> <a id="3600" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3603" href="foundation.operations-span-diagrams.html#3549" class="Bound">l4</a><a id="3605" class="Symbol">}</a> <a id="3607" class="Symbol">{</a><a id="3608" href="foundation.operations-span-diagrams.html#3608" class="Bound">B&#39;</a> <a id="3611" class="Symbol">:</a> <a id="3613" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3616" href="foundation.operations-span-diagrams.html#3552" class="Bound">l5</a><a id="3618" class="Symbol">}</a> <a id="3620" class="Symbol">(</a><a id="3621" href="foundation.operations-span-diagrams.html#3621" class="Bound">g&#39;</a> <a id="3624" class="Symbol">:</a> <a id="3626" href="foundation.operations-span-diagrams.html#3595" class="Bound">S&#39;</a> <a id="3629" class="Symbol">→</a> <a id="3631" href="foundation.operations-span-diagrams.html#3608" class="Bound">B&#39;</a><a id="3633" class="Symbol">)</a>
  <a id="3637" class="Symbol">(</a><a id="3638" href="foundation.operations-span-diagrams.html#3638" class="Bound">h</a> <a id="3640" class="Symbol">:</a> <a id="3642" href="foundation.equivalences-arrows.html#2283" class="Function">equiv-arrow</a> <a id="3654" href="foundation.operations-span-diagrams.html#3621" class="Bound">g&#39;</a> <a id="3657" class="Symbol">(</a><a id="3658" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="3681" href="foundation.operations-span-diagrams.html#3565" class="Bound">𝒮</a><a id="3682" class="Symbol">))</a>
  <a id="3687" class="Keyword">where</a>

  <a id="3696" href="foundation.operations-span-diagrams.html#3696" class="Function">domain-right-concat-equiv-arrow-span-diagram</a> <a id="3741" class="Symbol">:</a> <a id="3743" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3746" href="foundation.operations-span-diagrams.html#3540" class="Bound">l1</a>
  <a id="3751" href="foundation.operations-span-diagrams.html#3696" class="Function">domain-right-concat-equiv-arrow-span-diagram</a> <a id="3796" class="Symbol">=</a> <a id="3798" href="foundation.span-diagrams.html#2086" class="Function">domain-span-diagram</a> <a id="3818" href="foundation.operations-span-diagrams.html#3565" class="Bound">𝒮</a>

  <a id="3823" href="foundation.operations-span-diagrams.html#3823" class="Function">codomain-right-concat-equiv-arrow-span-diagram</a> <a id="3870" class="Symbol">:</a> <a id="3872" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3875" href="foundation.operations-span-diagrams.html#3552" class="Bound">l5</a>
  <a id="3880" href="foundation.operations-span-diagrams.html#3823" class="Function">codomain-right-concat-equiv-arrow-span-diagram</a> <a id="3927" class="Symbol">=</a> <a id="3929" href="foundation.operations-span-diagrams.html#3608" class="Bound">B&#39;</a>

  <a id="3935" href="foundation.operations-span-diagrams.html#3935" class="Function">span-right-concat-equiv-arrow-span-diagram</a> <a id="3978" class="Symbol">:</a>
    <a id="3984" href="foundation.spans.html#1830" class="Function">span</a> <a id="3989" href="foundation.operations-span-diagrams.html#3549" class="Bound">l4</a>
      <a id="3998" class="Symbol">(</a> <a id="4000" href="foundation.operations-span-diagrams.html#3696" class="Function">domain-right-concat-equiv-arrow-span-diagram</a><a id="4044" class="Symbol">)</a>
      <a id="4052" class="Symbol">(</a> <a id="4054" href="foundation.operations-span-diagrams.html#3823" class="Function">codomain-right-concat-equiv-arrow-span-diagram</a><a id="4100" class="Symbol">)</a>
  <a id="4104" href="foundation.operations-span-diagrams.html#3935" class="Function">span-right-concat-equiv-arrow-span-diagram</a> <a id="4147" class="Symbol">=</a>
    <a id="4153" href="foundation.operations-spans.html#3226" class="Function">right-concat-equiv-arrow-span</a> <a id="4183" class="Symbol">(</a><a id="4184" href="foundation.span-diagrams.html#2218" class="Function">span-span-diagram</a> <a id="4202" href="foundation.operations-span-diagrams.html#3565" class="Bound">𝒮</a><a id="4203" class="Symbol">)</a> <a id="4205" href="foundation.operations-span-diagrams.html#3621" class="Bound">g&#39;</a> <a id="4208" href="foundation.operations-span-diagrams.html#3638" class="Bound">h</a>

  <a id="4213" href="foundation.operations-span-diagrams.html#4213" class="Function">right-concat-equiv-arrow-span-diagram</a> <a id="4251" class="Symbol">:</a> <a id="4253" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="4266" href="foundation.operations-span-diagrams.html#3540" class="Bound">l1</a> <a id="4269" href="foundation.operations-span-diagrams.html#3552" class="Bound">l5</a> <a id="4272" href="foundation.operations-span-diagrams.html#3549" class="Bound">l4</a>
  <a id="4277" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4281" href="foundation.operations-span-diagrams.html#4213" class="Function">right-concat-equiv-arrow-span-diagram</a> <a id="4319" class="Symbol">=</a>
    <a id="4325" href="foundation.operations-span-diagrams.html#3696" class="Function">domain-right-concat-equiv-arrow-span-diagram</a>
  <a id="4372" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4376" class="Symbol">(</a><a id="4377" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4381" href="foundation.operations-span-diagrams.html#4213" class="Function">right-concat-equiv-arrow-span-diagram</a><a id="4418" class="Symbol">)</a> <a id="4420" class="Symbol">=</a>
    <a id="4426" href="foundation.operations-span-diagrams.html#3823" class="Function">codomain-right-concat-equiv-arrow-span-diagram</a>
  <a id="4475" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4479" class="Symbol">(</a><a id="4480" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4484" href="foundation.operations-span-diagrams.html#4213" class="Function">right-concat-equiv-arrow-span-diagram</a><a id="4521" class="Symbol">)</a> <a id="4523" class="Symbol">=</a>
    <a id="4529" href="foundation.operations-span-diagrams.html#3935" class="Function">span-right-concat-equiv-arrow-span-diagram</a>

  <a id="4575" href="foundation.operations-span-diagrams.html#4575" class="Function">spanning-type-right-concat-equiv-arrow-span-diagram</a> <a id="4627" class="Symbol">:</a> <a id="4629" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4632" href="foundation.operations-span-diagrams.html#3549" class="Bound">l4</a>
  <a id="4637" href="foundation.operations-span-diagrams.html#4575" class="Function">spanning-type-right-concat-equiv-arrow-span-diagram</a> <a id="4689" class="Symbol">=</a>
    <a id="4695" href="foundation.span-diagrams.html#2329" class="Function">spanning-type-span-diagram</a> <a id="4722" href="foundation.operations-span-diagrams.html#4213" class="Function">right-concat-equiv-arrow-span-diagram</a>

  <a id="4763" href="foundation.operations-span-diagrams.html#4763" class="Function">left-map-right-concat-equiv-arrow-span-diagram</a> <a id="4810" class="Symbol">:</a>
    <a id="4816" href="foundation.operations-span-diagrams.html#4575" class="Function">spanning-type-right-concat-equiv-arrow-span-diagram</a> <a id="4868" class="Symbol">→</a>
    <a id="4874" href="foundation.operations-span-diagrams.html#3696" class="Function">domain-right-concat-equiv-arrow-span-diagram</a>
  <a id="4921" href="foundation.operations-span-diagrams.html#4763" class="Function">left-map-right-concat-equiv-arrow-span-diagram</a> <a id="4968" class="Symbol">=</a>
    <a id="4974" href="foundation.span-diagrams.html#2439" class="Function">left-map-span-diagram</a> <a id="4996" href="foundation.operations-span-diagrams.html#4213" class="Function">right-concat-equiv-arrow-span-diagram</a>

  <a id="5037" href="foundation.operations-span-diagrams.html#5037" class="Function">right-map-right-concat-equiv-arrow-span-diagram</a> <a id="5085" class="Symbol">:</a>
    <a id="5091" href="foundation.operations-span-diagrams.html#4575" class="Function">spanning-type-right-concat-equiv-arrow-span-diagram</a> <a id="5143" class="Symbol">→</a>
    <a id="5149" href="foundation.operations-span-diagrams.html#3823" class="Function">codomain-right-concat-equiv-arrow-span-diagram</a>
  <a id="5198" href="foundation.operations-span-diagrams.html#5037" class="Function">right-map-right-concat-equiv-arrow-span-diagram</a> <a id="5246" class="Symbol">=</a>
    <a id="5252" href="foundation.span-diagrams.html#2577" class="Function">right-map-span-diagram</a> <a id="5275" href="foundation.operations-span-diagrams.html#4213" class="Function">right-concat-equiv-arrow-span-diagram</a>
</pre>