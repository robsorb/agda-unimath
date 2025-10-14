# Inverse sequential diagrams of types

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="foundation.inverse-sequential-diagrams.html" class="Module">foundation.inverse-sequential-diagrams</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.iterating-functions.html" class="Module">foundation.iterating-functions</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An
{{#concept "inverse sequential diagram" Disambiguation="types" Agda=inverse-sequential-diagram}}
of types `A` is a [sequence](lists.sequences.md) of types together with maps
between every two consecutive types

```text
  fₙ : Aₙ₊₁ → Aₙ
```

giving a sequential diagram of maps that extend infinitely to the left:

```text
     f₃      f₂      f₁      f₀
  ⋯ ---> A₃ ---> A₂ ---> A₁ ---> A₀.
```

This is in contrast to the notion of
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md), which
extend infinitely to the right, hence is the formal dual to inverse sequential
diagrams.

## Definitions

### Inverse sequential diagrams of types

<pre class="Agda"><a id="sequence-map-inverse-sequential-diagram"></a><a id="1060" href="foundation.inverse-sequential-diagrams.html#1060" class="Function">sequence-map-inverse-sequential-diagram</a> <a id="1100" class="Symbol">:</a> <a id="1102" class="Symbol">{</a><a id="1103" href="foundation.inverse-sequential-diagrams.html#1103" class="Bound">l</a> <a id="1105" class="Symbol">:</a> <a id="1107" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1112" class="Symbol">}</a> <a id="1114" class="Symbol">→</a> <a id="1116" class="Symbol">(</a><a id="1117" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1119" class="Symbol">→</a> <a id="1121" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1124" href="foundation.inverse-sequential-diagrams.html#1103" class="Bound">l</a><a id="1125" class="Symbol">)</a> <a id="1127" class="Symbol">→</a> <a id="1129" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1132" href="foundation.inverse-sequential-diagrams.html#1103" class="Bound">l</a>
<a id="1134" href="foundation.inverse-sequential-diagrams.html#1060" class="Function">sequence-map-inverse-sequential-diagram</a> <a id="1174" href="foundation.inverse-sequential-diagrams.html#1174" class="Bound">A</a> <a id="1176" class="Symbol">=</a> <a id="1178" class="Symbol">(</a><a id="1179" href="foundation.inverse-sequential-diagrams.html#1179" class="Bound">n</a> <a id="1181" class="Symbol">:</a> <a id="1183" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1184" class="Symbol">)</a> <a id="1186" class="Symbol">→</a> <a id="1188" href="foundation.inverse-sequential-diagrams.html#1174" class="Bound">A</a> <a id="1190" class="Symbol">(</a><a id="1191" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1198" href="foundation.inverse-sequential-diagrams.html#1179" class="Bound">n</a><a id="1199" class="Symbol">)</a> <a id="1201" class="Symbol">→</a> <a id="1203" href="foundation.inverse-sequential-diagrams.html#1174" class="Bound">A</a> <a id="1205" href="foundation.inverse-sequential-diagrams.html#1179" class="Bound">n</a>

<a id="inverse-sequential-diagram"></a><a id="1208" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="1235" class="Symbol">:</a> <a id="1237" class="Symbol">(</a><a id="1238" href="foundation.inverse-sequential-diagrams.html#1238" class="Bound">l</a> <a id="1240" class="Symbol">:</a> <a id="1242" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1247" class="Symbol">)</a> <a id="1249" class="Symbol">→</a> <a id="1251" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1254" class="Symbol">(</a><a id="1255" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1260" href="foundation.inverse-sequential-diagrams.html#1238" class="Bound">l</a><a id="1261" class="Symbol">)</a>
<a id="1263" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="1290" href="foundation.inverse-sequential-diagrams.html#1290" class="Bound">l</a> <a id="1292" class="Symbol">=</a>
  <a id="1296" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1298" class="Symbol">(</a><a id="1299" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1301" class="Symbol">→</a> <a id="1303" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1306" href="foundation.inverse-sequential-diagrams.html#1290" class="Bound">l</a><a id="1307" class="Symbol">)</a> <a id="1309" class="Symbol">(</a><a id="1310" href="foundation.inverse-sequential-diagrams.html#1060" class="Function">sequence-map-inverse-sequential-diagram</a><a id="1349" class="Symbol">)</a>

<a id="family-inverse-sequential-diagram"></a><a id="1352" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="1386" class="Symbol">:</a>
  <a id="1390" class="Symbol">{</a><a id="1391" href="foundation.inverse-sequential-diagrams.html#1391" class="Bound">l</a> <a id="1393" class="Symbol">:</a> <a id="1395" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1400" class="Symbol">}</a> <a id="1402" class="Symbol">→</a> <a id="1404" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="1431" href="foundation.inverse-sequential-diagrams.html#1391" class="Bound">l</a> <a id="1433" class="Symbol">→</a> <a id="1435" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1437" class="Symbol">→</a> <a id="1439" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1442" href="foundation.inverse-sequential-diagrams.html#1391" class="Bound">l</a>
<a id="1444" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="1478" class="Symbol">=</a> <a id="1480" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

<a id="map-inverse-sequential-diagram"></a><a id="1485" href="foundation.inverse-sequential-diagrams.html#1485" class="Function">map-inverse-sequential-diagram</a> <a id="1516" class="Symbol">:</a>
  <a id="1520" class="Symbol">{</a><a id="1521" href="foundation.inverse-sequential-diagrams.html#1521" class="Bound">l</a> <a id="1523" class="Symbol">:</a> <a id="1525" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1530" class="Symbol">}</a> <a id="1532" class="Symbol">(</a><a id="1533" href="foundation.inverse-sequential-diagrams.html#1533" class="Bound">A</a> <a id="1535" class="Symbol">:</a> <a id="1537" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="1564" href="foundation.inverse-sequential-diagrams.html#1521" class="Bound">l</a><a id="1565" class="Symbol">)</a> <a id="1567" class="Symbol">(</a><a id="1568" href="foundation.inverse-sequential-diagrams.html#1568" class="Bound">n</a> <a id="1570" class="Symbol">:</a> <a id="1572" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1573" class="Symbol">)</a> <a id="1575" class="Symbol">→</a>
  <a id="1579" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="1613" href="foundation.inverse-sequential-diagrams.html#1533" class="Bound">A</a> <a id="1615" class="Symbol">(</a><a id="1616" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1623" href="foundation.inverse-sequential-diagrams.html#1568" class="Bound">n</a><a id="1624" class="Symbol">)</a> <a id="1626" class="Symbol">→</a>
  <a id="1630" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="1664" href="foundation.inverse-sequential-diagrams.html#1533" class="Bound">A</a> <a id="1666" href="foundation.inverse-sequential-diagrams.html#1568" class="Bound">n</a>
<a id="1668" href="foundation.inverse-sequential-diagrams.html#1485" class="Function">map-inverse-sequential-diagram</a> <a id="1699" class="Symbol">=</a> <a id="1701" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>
## Operations

### Right shifting an inverse sequential diagram

We can **right shift** an inverse sequential diagram of types by forgetting the
first terms.

<pre class="Agda"><a id="right-shift-inverse-sequential-diagram"></a><a id="1877" href="foundation.inverse-sequential-diagrams.html#1877" class="Function">right-shift-inverse-sequential-diagram</a> <a id="1916" class="Symbol">:</a>
  <a id="1920" class="Symbol">{</a><a id="1921" href="foundation.inverse-sequential-diagrams.html#1921" class="Bound">l</a> <a id="1923" class="Symbol">:</a> <a id="1925" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1930" class="Symbol">}</a> <a id="1932" class="Symbol">→</a> <a id="1934" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="1961" href="foundation.inverse-sequential-diagrams.html#1921" class="Bound">l</a> <a id="1963" class="Symbol">→</a> <a id="1965" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="1992" href="foundation.inverse-sequential-diagrams.html#1921" class="Bound">l</a>
<a id="1994" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1998" class="Symbol">(</a><a id="1999" href="foundation.inverse-sequential-diagrams.html#1877" class="Function">right-shift-inverse-sequential-diagram</a> <a id="2038" href="foundation.inverse-sequential-diagrams.html#2038" class="Bound">A</a><a id="2039" class="Symbol">)</a> <a id="2041" href="foundation.inverse-sequential-diagrams.html#2041" class="Bound">n</a> <a id="2043" class="Symbol">=</a>
  <a id="2047" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="2081" href="foundation.inverse-sequential-diagrams.html#2038" class="Bound">A</a> <a id="2083" class="Symbol">(</a><a id="2084" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2091" href="foundation.inverse-sequential-diagrams.html#2041" class="Bound">n</a><a id="2092" class="Symbol">)</a>
<a id="2094" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2098" class="Symbol">(</a><a id="2099" href="foundation.inverse-sequential-diagrams.html#1877" class="Function">right-shift-inverse-sequential-diagram</a> <a id="2138" href="foundation.inverse-sequential-diagrams.html#2138" class="Bound">A</a><a id="2139" class="Symbol">)</a> <a id="2141" href="foundation.inverse-sequential-diagrams.html#2141" class="Bound">n</a> <a id="2143" class="Symbol">=</a>
  <a id="2147" href="foundation.inverse-sequential-diagrams.html#1485" class="Function">map-inverse-sequential-diagram</a> <a id="2178" href="foundation.inverse-sequential-diagrams.html#2138" class="Bound">A</a> <a id="2180" class="Symbol">(</a><a id="2181" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2188" href="foundation.inverse-sequential-diagrams.html#2141" class="Bound">n</a><a id="2189" class="Symbol">)</a>

<a id="iterated-right-shift-inverse-sequential-diagram"></a><a id="2192" href="foundation.inverse-sequential-diagrams.html#2192" class="Function">iterated-right-shift-inverse-sequential-diagram</a> <a id="2240" class="Symbol">:</a>
  <a id="2244" class="Symbol">{</a><a id="2245" href="foundation.inverse-sequential-diagrams.html#2245" class="Bound">l</a> <a id="2247" class="Symbol">:</a> <a id="2249" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2254" class="Symbol">}</a> <a id="2256" class="Symbol">→</a> <a id="2258" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2260" class="Symbol">→</a> <a id="2262" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="2289" href="foundation.inverse-sequential-diagrams.html#2245" class="Bound">l</a> <a id="2291" class="Symbol">→</a> <a id="2293" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="2320" href="foundation.inverse-sequential-diagrams.html#2245" class="Bound">l</a>
<a id="2322" href="foundation.inverse-sequential-diagrams.html#2192" class="Function">iterated-right-shift-inverse-sequential-diagram</a> <a id="2370" href="foundation.inverse-sequential-diagrams.html#2370" class="Bound">n</a> <a id="2372" class="Symbol">=</a>
  <a id="2376" href="foundation-core.iterating-functions.html#724" class="Function">iterate</a> <a id="2384" href="foundation.inverse-sequential-diagrams.html#2370" class="Bound">n</a> <a id="2386" href="foundation.inverse-sequential-diagrams.html#1877" class="Function">right-shift-inverse-sequential-diagram</a>
</pre>
### Left shifting an inverse sequential diagram

We can **left shift** an inverse sequential diagram of types by padding it with
the [terminal type](foundation.unit-type.md) `unit`.

<pre class="Agda"><a id="left-shift-inverse-sequential-diagram"></a><a id="2621" href="foundation.inverse-sequential-diagrams.html#2621" class="Function">left-shift-inverse-sequential-diagram</a> <a id="2659" class="Symbol">:</a>
  <a id="2663" class="Symbol">{</a><a id="2664" href="foundation.inverse-sequential-diagrams.html#2664" class="Bound">l</a> <a id="2666" class="Symbol">:</a> <a id="2668" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2673" class="Symbol">}</a> <a id="2675" class="Symbol">→</a> <a id="2677" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="2704" href="foundation.inverse-sequential-diagrams.html#2664" class="Bound">l</a> <a id="2706" class="Symbol">→</a> <a id="2708" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="2735" href="foundation.inverse-sequential-diagrams.html#2664" class="Bound">l</a>
<a id="2737" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2741" class="Symbol">(</a><a id="2742" href="foundation.inverse-sequential-diagrams.html#2621" class="Function">left-shift-inverse-sequential-diagram</a> <a id="2780" class="Symbol">{</a><a id="2781" href="foundation.inverse-sequential-diagrams.html#2781" class="Bound">l</a><a id="2782" class="Symbol">}</a> <a id="2784" href="foundation.inverse-sequential-diagrams.html#2784" class="Bound">A</a><a id="2785" class="Symbol">)</a> <a id="2787" class="Number">0</a> <a id="2789" class="Symbol">=</a> <a id="2791" href="foundation.unit-type.html#1545" class="Function">raise-unit</a> <a id="2802" href="foundation.inverse-sequential-diagrams.html#2781" class="Bound">l</a>
<a id="2804" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2808" class="Symbol">(</a><a id="2809" href="foundation.inverse-sequential-diagrams.html#2621" class="Function">left-shift-inverse-sequential-diagram</a> <a id="2847" href="foundation.inverse-sequential-diagrams.html#2847" class="Bound">A</a><a id="2848" class="Symbol">)</a> <a id="2850" class="Symbol">(</a><a id="2851" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2858" href="foundation.inverse-sequential-diagrams.html#2858" class="Bound">n</a><a id="2859" class="Symbol">)</a> <a id="2861" class="Symbol">=</a>
  <a id="2865" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="2899" href="foundation.inverse-sequential-diagrams.html#2847" class="Bound">A</a> <a id="2901" href="foundation.inverse-sequential-diagrams.html#2858" class="Bound">n</a>
<a id="2903" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2907" class="Symbol">(</a><a id="2908" href="foundation.inverse-sequential-diagrams.html#2621" class="Function">left-shift-inverse-sequential-diagram</a> <a id="2946" href="foundation.inverse-sequential-diagrams.html#2946" class="Bound">A</a><a id="2947" class="Symbol">)</a> <a id="2949" class="Number">0</a> <a id="2951" class="Symbol">=</a>
  <a id="2955" href="foundation.unit-type.html#1675" class="Function">raise-terminal-map</a> <a id="2974" class="Symbol">(</a><a id="2975" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="3009" href="foundation.inverse-sequential-diagrams.html#2946" class="Bound">A</a> <a id="3011" class="Number">0</a><a id="3012" class="Symbol">)</a>
<a id="3014" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3018" class="Symbol">(</a><a id="3019" href="foundation.inverse-sequential-diagrams.html#2621" class="Function">left-shift-inverse-sequential-diagram</a> <a id="3057" href="foundation.inverse-sequential-diagrams.html#3057" class="Bound">A</a><a id="3058" class="Symbol">)</a> <a id="3060" class="Symbol">(</a><a id="3061" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="3068" href="foundation.inverse-sequential-diagrams.html#3068" class="Bound">n</a><a id="3069" class="Symbol">)</a> <a id="3071" class="Symbol">=</a>
  <a id="3075" href="foundation.inverse-sequential-diagrams.html#1485" class="Function">map-inverse-sequential-diagram</a> <a id="3106" href="foundation.inverse-sequential-diagrams.html#3057" class="Bound">A</a> <a id="3108" href="foundation.inverse-sequential-diagrams.html#3068" class="Bound">n</a>

<a id="iterated-left-shift-inverse-sequential-diagram"></a><a id="3111" href="foundation.inverse-sequential-diagrams.html#3111" class="Function">iterated-left-shift-inverse-sequential-diagram</a> <a id="3158" class="Symbol">:</a>
  <a id="3162" class="Symbol">{</a><a id="3163" href="foundation.inverse-sequential-diagrams.html#3163" class="Bound">l</a> <a id="3165" class="Symbol">:</a> <a id="3167" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3172" class="Symbol">}</a> <a id="3174" class="Symbol">(</a><a id="3175" href="foundation.inverse-sequential-diagrams.html#3175" class="Bound">n</a> <a id="3177" class="Symbol">:</a> <a id="3179" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="3180" class="Symbol">)</a> <a id="3182" class="Symbol">→</a>
  <a id="3186" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="3213" href="foundation.inverse-sequential-diagrams.html#3163" class="Bound">l</a> <a id="3215" class="Symbol">→</a> <a id="3217" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="3244" href="foundation.inverse-sequential-diagrams.html#3163" class="Bound">l</a>
<a id="3246" href="foundation.inverse-sequential-diagrams.html#3111" class="Function">iterated-left-shift-inverse-sequential-diagram</a> <a id="3293" href="foundation.inverse-sequential-diagrams.html#3293" class="Bound">n</a> <a id="3295" class="Symbol">=</a>
  <a id="3299" href="foundation-core.iterating-functions.html#724" class="Function">iterate</a> <a id="3307" href="foundation.inverse-sequential-diagrams.html#3293" class="Bound">n</a> <a id="3309" href="foundation.inverse-sequential-diagrams.html#2621" class="Function">left-shift-inverse-sequential-diagram</a>
</pre>
### Postcomposition inverse sequential diagrams

Given an inverse sequential diagram `A` and a type `X` there is an inverse
sequential diagram `X → A` defined by levelwise postcomposition

```text
                    (f₂ ∘ -)          (f₁ ∘ -)          (f₀ ∘ -)
  ⋯ -----> (X → A₃) -------> (X → A₂) -------> (X → A₁) -------> (X → A₀).
```

<pre class="Agda"><a id="3702" class="Keyword">module</a> <a id="3709" href="foundation.inverse-sequential-diagrams.html#3709" class="Module">_</a>
  <a id="3713" class="Symbol">{</a><a id="3714" href="foundation.inverse-sequential-diagrams.html#3714" class="Bound">l1</a> <a id="3717" href="foundation.inverse-sequential-diagrams.html#3717" class="Bound">l2</a> <a id="3720" class="Symbol">:</a> <a id="3722" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3727" class="Symbol">}</a> <a id="3729" class="Symbol">(</a><a id="3730" href="foundation.inverse-sequential-diagrams.html#3730" class="Bound">X</a> <a id="3732" class="Symbol">:</a> <a id="3734" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3737" href="foundation.inverse-sequential-diagrams.html#3714" class="Bound">l1</a><a id="3739" class="Symbol">)</a> <a id="3741" class="Symbol">(</a><a id="3742" href="foundation.inverse-sequential-diagrams.html#3742" class="Bound">A</a> <a id="3744" class="Symbol">:</a> <a id="3746" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="3773" href="foundation.inverse-sequential-diagrams.html#3717" class="Bound">l2</a><a id="3775" class="Symbol">)</a>
  <a id="3779" class="Keyword">where</a>

  <a id="3788" href="foundation.inverse-sequential-diagrams.html#3788" class="Function">postcomp-inverse-sequential-diagram</a> <a id="3824" class="Symbol">:</a> <a id="3826" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a> <a id="3853" class="Symbol">(</a><a id="3854" href="foundation.inverse-sequential-diagrams.html#3714" class="Bound">l1</a> <a id="3857" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3859" href="foundation.inverse-sequential-diagrams.html#3717" class="Bound">l2</a><a id="3861" class="Symbol">)</a>
  <a id="3865" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3869" href="foundation.inverse-sequential-diagrams.html#3788" class="Function">postcomp-inverse-sequential-diagram</a> <a id="3905" href="foundation.inverse-sequential-diagrams.html#3905" class="Bound">n</a> <a id="3907" class="Symbol">=</a>
    <a id="3913" href="foundation.inverse-sequential-diagrams.html#3730" class="Bound">X</a> <a id="3915" class="Symbol">→</a> <a id="3917" href="foundation.inverse-sequential-diagrams.html#1352" class="Function">family-inverse-sequential-diagram</a> <a id="3951" href="foundation.inverse-sequential-diagrams.html#3742" class="Bound">A</a> <a id="3953" href="foundation.inverse-sequential-diagrams.html#3905" class="Bound">n</a>
  <a id="3957" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3961" href="foundation.inverse-sequential-diagrams.html#3788" class="Function">postcomp-inverse-sequential-diagram</a> <a id="3997" href="foundation.inverse-sequential-diagrams.html#3997" class="Bound">n</a> <a id="3999" href="foundation.inverse-sequential-diagrams.html#3999" class="Bound">g</a> <a id="4001" href="foundation.inverse-sequential-diagrams.html#4001" class="Bound">x</a> <a id="4003" class="Symbol">=</a>
    <a id="4009" href="foundation.inverse-sequential-diagrams.html#1485" class="Function">map-inverse-sequential-diagram</a> <a id="4040" href="foundation.inverse-sequential-diagrams.html#3742" class="Bound">A</a> <a id="4042" href="foundation.inverse-sequential-diagrams.html#3997" class="Bound">n</a> <a id="4044" class="Symbol">(</a><a id="4045" href="foundation.inverse-sequential-diagrams.html#3999" class="Bound">g</a> <a id="4047" href="foundation.inverse-sequential-diagrams.html#4001" class="Bound">x</a><a id="4048" class="Symbol">)</a>
</pre>
## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
