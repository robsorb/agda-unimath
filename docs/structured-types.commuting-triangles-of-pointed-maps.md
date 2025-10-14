# Commuting triangles of pointed maps

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="structured-types.commuting-triangles-of-pointed-maps.html" class="Module">structured-types.commuting-triangles-of-pointed-maps</a> <a id="108" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="164" class="Keyword">open</a> <a id="169" class="Keyword">import</a> <a id="176" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="structured-types.whiskering-pointed-homotopies-composition.html" class="Module">structured-types.whiskering-pointed-homotopies-composition</a>
</pre>
</details>

## Idea

Consider a triangle of [pointed maps](structured-types.pointed-maps.md)

```text
           top
       A ------> B
        \       /
    left \     / right
          \   /
           ∨ ∨
            C
```

Such a triangle is said to be a
{{#concept "commuting triangle of pointed maps" Agda=coherence-triangle-pointed-maps}}
if there is a [pointed homotopy](structured-types.pointed-homotopies.md)

```text
  left ~∗ right ∘∗ top.
```

Such a homotopy is referred to as the
{{#concept "coherence" Disambiguation="commuting triangles of pointed maps" Agda=coherence-triangle-pointed-maps}}
of the commuting triangle of pointed maps.

## Definitions

### Coherences of commuting triangles of pointed maps

<pre class="Agda"><a id="1146" class="Keyword">module</a> <a id="1153" href="structured-types.commuting-triangles-of-pointed-maps.html#1153" class="Module">_</a>
  <a id="1157" class="Symbol">{</a><a id="1158" href="structured-types.commuting-triangles-of-pointed-maps.html#1158" class="Bound">l1</a> <a id="1161" href="structured-types.commuting-triangles-of-pointed-maps.html#1161" class="Bound">l2</a> <a id="1164" href="structured-types.commuting-triangles-of-pointed-maps.html#1164" class="Bound">l3</a> <a id="1167" class="Symbol">:</a> <a id="1169" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1174" class="Symbol">}</a>
  <a id="1178" class="Symbol">{</a><a id="1179" href="structured-types.commuting-triangles-of-pointed-maps.html#1179" class="Bound">A</a> <a id="1181" class="Symbol">:</a> <a id="1183" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1196" href="structured-types.commuting-triangles-of-pointed-maps.html#1158" class="Bound">l1</a><a id="1198" class="Symbol">}</a> <a id="1200" class="Symbol">{</a><a id="1201" href="structured-types.commuting-triangles-of-pointed-maps.html#1201" class="Bound">B</a> <a id="1203" class="Symbol">:</a> <a id="1205" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1218" href="structured-types.commuting-triangles-of-pointed-maps.html#1161" class="Bound">l2</a><a id="1220" class="Symbol">}</a> <a id="1222" class="Symbol">{</a><a id="1223" href="structured-types.commuting-triangles-of-pointed-maps.html#1223" class="Bound">C</a> <a id="1225" class="Symbol">:</a> <a id="1227" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1240" href="structured-types.commuting-triangles-of-pointed-maps.html#1164" class="Bound">l3</a><a id="1242" class="Symbol">}</a>
  <a id="1246" class="Symbol">(</a><a id="1247" href="structured-types.commuting-triangles-of-pointed-maps.html#1247" class="Bound">left</a> <a id="1252" class="Symbol">:</a> <a id="1254" href="structured-types.commuting-triangles-of-pointed-maps.html#1179" class="Bound">A</a> <a id="1256" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1259" href="structured-types.commuting-triangles-of-pointed-maps.html#1223" class="Bound">C</a><a id="1260" class="Symbol">)</a> <a id="1262" class="Symbol">(</a><a id="1263" href="structured-types.commuting-triangles-of-pointed-maps.html#1263" class="Bound">right</a> <a id="1269" class="Symbol">:</a> <a id="1271" href="structured-types.commuting-triangles-of-pointed-maps.html#1201" class="Bound">B</a> <a id="1273" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1276" href="structured-types.commuting-triangles-of-pointed-maps.html#1223" class="Bound">C</a><a id="1277" class="Symbol">)</a> <a id="1279" class="Symbol">(</a><a id="1280" href="structured-types.commuting-triangles-of-pointed-maps.html#1280" class="Bound">top</a> <a id="1284" class="Symbol">:</a> <a id="1286" href="structured-types.commuting-triangles-of-pointed-maps.html#1179" class="Bound">A</a> <a id="1288" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1291" href="structured-types.commuting-triangles-of-pointed-maps.html#1201" class="Bound">B</a><a id="1292" class="Symbol">)</a>
  <a id="1296" class="Keyword">where</a>

  <a id="1305" href="structured-types.commuting-triangles-of-pointed-maps.html#1305" class="Function">coherence-triangle-pointed-maps</a> <a id="1337" class="Symbol">:</a> <a id="1339" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1342" class="Symbol">(</a><a id="1343" href="structured-types.commuting-triangles-of-pointed-maps.html#1158" class="Bound">l1</a> <a id="1346" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1348" href="structured-types.commuting-triangles-of-pointed-maps.html#1164" class="Bound">l3</a><a id="1350" class="Symbol">)</a>
  <a id="1354" href="structured-types.commuting-triangles-of-pointed-maps.html#1305" class="Function">coherence-triangle-pointed-maps</a> <a id="1386" class="Symbol">=</a>
    <a id="1392" href="structured-types.commuting-triangles-of-pointed-maps.html#1247" class="Bound">left</a> <a id="1397" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1400" href="structured-types.commuting-triangles-of-pointed-maps.html#1263" class="Bound">right</a> <a id="1406" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="1409" href="structured-types.commuting-triangles-of-pointed-maps.html#1280" class="Bound">top</a>

  <a id="1416" href="structured-types.commuting-triangles-of-pointed-maps.html#1416" class="Function">coherence-triangle-pointed-maps&#39;</a> <a id="1449" class="Symbol">:</a> <a id="1451" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1454" class="Symbol">(</a><a id="1455" href="structured-types.commuting-triangles-of-pointed-maps.html#1158" class="Bound">l1</a> <a id="1458" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1460" href="structured-types.commuting-triangles-of-pointed-maps.html#1164" class="Bound">l3</a><a id="1462" class="Symbol">)</a>
  <a id="1466" href="structured-types.commuting-triangles-of-pointed-maps.html#1416" class="Function">coherence-triangle-pointed-maps&#39;</a> <a id="1499" class="Symbol">=</a>
    <a id="1505" href="structured-types.commuting-triangles-of-pointed-maps.html#1263" class="Bound">right</a> <a id="1511" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="1514" href="structured-types.commuting-triangles-of-pointed-maps.html#1280" class="Bound">top</a> <a id="1518" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1521" href="structured-types.commuting-triangles-of-pointed-maps.html#1247" class="Bound">left</a>
</pre>
## Properties

### Left whiskering of coherences of commuting triangles of pointed maps

Consider a commuting triangle of pointed maps

```text
           top
       A ------> B
        \       /
    left \     / right
          \   /
           ∨ ∨
            C
```

and consider a pointed map `f : C →∗ X`. The
{{#concept "left whiskering" Disambiguation="commuting triangles of pointed maps" Agda=left-whisker-coherence-triangle-pointed-maps}}
is a coherence of the triangle of pointed maps

```text
              top
          A ------> B
           \       /
  f ∘∗ left \     / f ∘∗ right
             \   /
              ∨ ∨
               X
```

In other words, left whiskering of coherences of commuting triangles of pointed
maps is an operation

```text
  (left ~∗ right ∘∗ top) → (f ∘∗ left ~∗ (f ∘∗ right) ∘∗ top).
```

<pre class="Agda"><a id="2372" class="Keyword">module</a> <a id="2379" href="structured-types.commuting-triangles-of-pointed-maps.html#2379" class="Module">_</a>
  <a id="2383" class="Symbol">{</a><a id="2384" href="structured-types.commuting-triangles-of-pointed-maps.html#2384" class="Bound">l1</a> <a id="2387" href="structured-types.commuting-triangles-of-pointed-maps.html#2387" class="Bound">l2</a> <a id="2390" href="structured-types.commuting-triangles-of-pointed-maps.html#2390" class="Bound">l3</a> <a id="2393" href="structured-types.commuting-triangles-of-pointed-maps.html#2393" class="Bound">l4</a> <a id="2396" class="Symbol">:</a> <a id="2398" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2403" class="Symbol">}</a>
  <a id="2407" class="Symbol">{</a><a id="2408" href="structured-types.commuting-triangles-of-pointed-maps.html#2408" class="Bound">A</a> <a id="2410" class="Symbol">:</a> <a id="2412" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2425" href="structured-types.commuting-triangles-of-pointed-maps.html#2384" class="Bound">l1</a><a id="2427" class="Symbol">}</a> <a id="2429" class="Symbol">{</a><a id="2430" href="structured-types.commuting-triangles-of-pointed-maps.html#2430" class="Bound">B</a> <a id="2432" class="Symbol">:</a> <a id="2434" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2447" href="structured-types.commuting-triangles-of-pointed-maps.html#2387" class="Bound">l2</a><a id="2449" class="Symbol">}</a> <a id="2451" class="Symbol">{</a><a id="2452" href="structured-types.commuting-triangles-of-pointed-maps.html#2452" class="Bound">C</a> <a id="2454" class="Symbol">:</a> <a id="2456" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2469" href="structured-types.commuting-triangles-of-pointed-maps.html#2390" class="Bound">l3</a><a id="2471" class="Symbol">}</a>
  <a id="2475" class="Symbol">{</a><a id="2476" href="structured-types.commuting-triangles-of-pointed-maps.html#2476" class="Bound">X</a> <a id="2478" class="Symbol">:</a> <a id="2480" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2493" href="structured-types.commuting-triangles-of-pointed-maps.html#2393" class="Bound">l4</a><a id="2495" class="Symbol">}</a> <a id="2497" class="Symbol">(</a><a id="2498" href="structured-types.commuting-triangles-of-pointed-maps.html#2498" class="Bound">f</a> <a id="2500" class="Symbol">:</a> <a id="2502" href="structured-types.commuting-triangles-of-pointed-maps.html#2452" class="Bound">C</a> <a id="2504" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2507" href="structured-types.commuting-triangles-of-pointed-maps.html#2476" class="Bound">X</a><a id="2508" class="Symbol">)</a>
  <a id="2512" class="Symbol">(</a><a id="2513" href="structured-types.commuting-triangles-of-pointed-maps.html#2513" class="Bound">left</a> <a id="2518" class="Symbol">:</a> <a id="2520" href="structured-types.commuting-triangles-of-pointed-maps.html#2408" class="Bound">A</a> <a id="2522" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2525" href="structured-types.commuting-triangles-of-pointed-maps.html#2452" class="Bound">C</a><a id="2526" class="Symbol">)</a> <a id="2528" class="Symbol">(</a><a id="2529" href="structured-types.commuting-triangles-of-pointed-maps.html#2529" class="Bound">right</a> <a id="2535" class="Symbol">:</a> <a id="2537" href="structured-types.commuting-triangles-of-pointed-maps.html#2430" class="Bound">B</a> <a id="2539" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2542" href="structured-types.commuting-triangles-of-pointed-maps.html#2452" class="Bound">C</a><a id="2543" class="Symbol">)</a> <a id="2545" class="Symbol">(</a><a id="2546" href="structured-types.commuting-triangles-of-pointed-maps.html#2546" class="Bound">top</a> <a id="2550" class="Symbol">:</a> <a id="2552" href="structured-types.commuting-triangles-of-pointed-maps.html#2408" class="Bound">A</a> <a id="2554" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2557" href="structured-types.commuting-triangles-of-pointed-maps.html#2430" class="Bound">B</a><a id="2558" class="Symbol">)</a>
  <a id="2562" class="Keyword">where</a>

  <a id="2571" href="structured-types.commuting-triangles-of-pointed-maps.html#2571" class="Function">left-whisker-coherence-triangle-pointed-maps</a> <a id="2616" class="Symbol">:</a>
    <a id="2622" href="structured-types.commuting-triangles-of-pointed-maps.html#1305" class="Function">coherence-triangle-pointed-maps</a> <a id="2654" href="structured-types.commuting-triangles-of-pointed-maps.html#2513" class="Bound">left</a> <a id="2659" href="structured-types.commuting-triangles-of-pointed-maps.html#2529" class="Bound">right</a> <a id="2665" href="structured-types.commuting-triangles-of-pointed-maps.html#2546" class="Bound">top</a> <a id="2669" class="Symbol">→</a>
    <a id="2675" href="structured-types.commuting-triangles-of-pointed-maps.html#1305" class="Function">coherence-triangle-pointed-maps</a> <a id="2707" class="Symbol">(</a><a id="2708" href="structured-types.commuting-triangles-of-pointed-maps.html#2498" class="Bound">f</a> <a id="2710" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="2713" href="structured-types.commuting-triangles-of-pointed-maps.html#2513" class="Bound">left</a><a id="2717" class="Symbol">)</a> <a id="2719" class="Symbol">(</a><a id="2720" href="structured-types.commuting-triangles-of-pointed-maps.html#2498" class="Bound">f</a> <a id="2722" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="2725" href="structured-types.commuting-triangles-of-pointed-maps.html#2529" class="Bound">right</a><a id="2730" class="Symbol">)</a> <a id="2732" href="structured-types.commuting-triangles-of-pointed-maps.html#2546" class="Bound">top</a>
  <a id="2738" href="structured-types.commuting-triangles-of-pointed-maps.html#2571" class="Function">left-whisker-coherence-triangle-pointed-maps</a> <a id="2783" href="structured-types.commuting-triangles-of-pointed-maps.html#2783" class="Bound">H</a> <a id="2785" class="Symbol">=</a>
    <a id="2791" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
      <a id="2817" class="Symbol">(</a> <a id="2819" href="structured-types.whiskering-pointed-homotopies-composition.html#4822" class="Function">left-whisker-comp-pointed-htpy</a> <a id="2850" href="structured-types.commuting-triangles-of-pointed-maps.html#2498" class="Bound">f</a> <a id="2852" href="structured-types.commuting-triangles-of-pointed-maps.html#2513" class="Bound">left</a> <a id="2857" class="Symbol">(</a><a id="2858" href="structured-types.commuting-triangles-of-pointed-maps.html#2529" class="Bound">right</a> <a id="2864" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="2867" href="structured-types.commuting-triangles-of-pointed-maps.html#2546" class="Bound">top</a><a id="2870" class="Symbol">)</a> <a id="2872" href="structured-types.commuting-triangles-of-pointed-maps.html#2783" class="Bound">H</a><a id="2873" class="Symbol">)</a>
      <a id="2881" class="Symbol">(</a> <a id="2883" href="structured-types.pointed-homotopies.html#9643" class="Function">inv-pointed-htpy</a>
        <a id="2908" class="Symbol">(</a> <a id="2910" href="structured-types.pointed-homotopies.html#13283" class="Function">associative-comp-pointed-map</a> <a id="2939" href="structured-types.commuting-triangles-of-pointed-maps.html#2498" class="Bound">f</a> <a id="2941" href="structured-types.commuting-triangles-of-pointed-maps.html#2529" class="Bound">right</a> <a id="2947" href="structured-types.commuting-triangles-of-pointed-maps.html#2546" class="Bound">top</a><a id="2950" class="Symbol">))</a>
</pre>