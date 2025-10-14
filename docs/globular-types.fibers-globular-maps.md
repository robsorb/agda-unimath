# Fibers of globular maps

<pre class="Agda"><a id="36" class="Symbol">{-#</a> <a id="40" class="Keyword">OPTIONS</a> <a id="48" class="Pragma">--guardedness</a> <a id="62" class="Symbol">#-}</a>

<a id="67" class="Keyword">module</a> <a id="74" href="globular-types.fibers-globular-maps.html" class="Module">globular-types.fibers-globular-maps</a> <a id="110" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="globular-types.dependent-globular-types.html" class="Module">globular-types.dependent-globular-types</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="globular-types.globular-maps.html" class="Module">globular-types.globular-maps</a>
<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

Consider a [globular map](globular-types.globular-maps.md) `f : H → G` between
two [globular types](globular-types.globular-types.md) `H` and `G`. The
{{#concept "fiber" Disambiguation="globular map" Agda=fiber-globular-map}} of
`f` is a [dependent globular type](globular-types.dependent-globular-types.md)
`fib_f` given by

```text
  (fib_f)₀ x := fib f₀ x
  (fib_f)' (y , refl) (y' , refl) := fib_f'.
```

## Definitions

### The fiber of a globular map

<pre class="Agda"><a id="fiber-globular-map"></a><a id="953" href="globular-types.fibers-globular-maps.html#953" class="Function">fiber-globular-map</a> <a id="972" class="Symbol">:</a>
  <a id="976" class="Symbol">{</a><a id="977" href="globular-types.fibers-globular-maps.html#977" class="Bound">l1</a> <a id="980" href="globular-types.fibers-globular-maps.html#980" class="Bound">l2</a> <a id="983" href="globular-types.fibers-globular-maps.html#983" class="Bound">l3</a> <a id="986" href="globular-types.fibers-globular-maps.html#986" class="Bound">l4</a> <a id="989" class="Symbol">:</a> <a id="991" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="996" class="Symbol">}</a>
  <a id="1000" class="Symbol">(</a><a id="1001" href="globular-types.fibers-globular-maps.html#1001" class="Bound">H</a> <a id="1003" class="Symbol">:</a> <a id="1005" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1019" href="globular-types.fibers-globular-maps.html#977" class="Bound">l1</a> <a id="1022" href="globular-types.fibers-globular-maps.html#980" class="Bound">l2</a><a id="1024" class="Symbol">)</a> <a id="1026" class="Symbol">(</a><a id="1027" href="globular-types.fibers-globular-maps.html#1027" class="Bound">G</a> <a id="1029" class="Symbol">:</a> <a id="1031" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1045" href="globular-types.fibers-globular-maps.html#983" class="Bound">l3</a> <a id="1048" href="globular-types.fibers-globular-maps.html#986" class="Bound">l4</a><a id="1050" class="Symbol">)</a>
  <a id="1054" class="Symbol">(</a><a id="1055" href="globular-types.fibers-globular-maps.html#1055" class="Bound">f</a> <a id="1057" class="Symbol">:</a> <a id="1059" href="globular-types.globular-maps.html#774" class="Record">globular-map</a> <a id="1072" href="globular-types.fibers-globular-maps.html#1001" class="Bound">H</a> <a id="1074" href="globular-types.fibers-globular-maps.html#1027" class="Bound">G</a><a id="1075" class="Symbol">)</a> <a id="1077" class="Symbol">→</a>
  <a id="1081" href="globular-types.dependent-globular-types.html#778" class="Record">Dependent-Globular-Type</a> <a id="1105" class="Symbol">(</a><a id="1106" href="globular-types.fibers-globular-maps.html#977" class="Bound">l1</a> <a id="1109" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1111" href="globular-types.fibers-globular-maps.html#983" class="Bound">l3</a><a id="1113" class="Symbol">)</a> <a id="1115" class="Symbol">(</a><a id="1116" href="globular-types.fibers-globular-maps.html#980" class="Bound">l2</a> <a id="1119" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1121" href="globular-types.fibers-globular-maps.html#986" class="Bound">l4</a><a id="1123" class="Symbol">)</a> <a id="1125" href="globular-types.fibers-globular-maps.html#1027" class="Bound">G</a>
<a id="1127" href="globular-types.dependent-globular-types.html#937" class="Field">0-cell-Dependent-Globular-Type</a>
  <a id="1160" class="Symbol">(</a> <a id="1162" href="globular-types.fibers-globular-maps.html#953" class="Function">fiber-globular-map</a> <a id="1181" href="globular-types.fibers-globular-maps.html#1181" class="Bound">H</a> <a id="1183" href="globular-types.fibers-globular-maps.html#1183" class="Bound">G</a> <a id="1185" href="globular-types.fibers-globular-maps.html#1185" class="Bound">f</a><a id="1186" class="Symbol">)</a> <a id="1188" class="Symbol">=</a>
  <a id="1192" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="1198" class="Symbol">(</a><a id="1199" href="globular-types.globular-maps.html#928" class="Field">0-cell-globular-map</a> <a id="1219" href="globular-types.fibers-globular-maps.html#1185" class="Bound">f</a><a id="1220" class="Symbol">)</a>
<a id="1222" href="globular-types.dependent-globular-types.html#1011" class="Field">1-cell-dependent-globular-type-Dependent-Globular-Type</a>
  <a id="1279" class="Symbol">(</a> <a id="1281" href="globular-types.fibers-globular-maps.html#953" class="Function">fiber-globular-map</a> <a id="1300" href="globular-types.fibers-globular-maps.html#1300" class="Bound">H</a> <a id="1302" href="globular-types.fibers-globular-maps.html#1302" class="Bound">G</a> <a id="1304" href="globular-types.fibers-globular-maps.html#1304" class="Bound">f</a><a id="1305" class="Symbol">)</a> <a id="1307" class="Symbol">{</a><a id="1308" href="globular-types.fibers-globular-maps.html#1308" class="Bound">x</a><a id="1309" class="Symbol">}</a> <a id="1311" class="Symbol">{</a><a id="1312" href="globular-types.fibers-globular-maps.html#1312" class="Bound">x&#39;</a><a id="1314" class="Symbol">}</a> <a id="1316" class="Symbol">(</a><a id="1317" href="globular-types.fibers-globular-maps.html#1317" class="Bound">y</a> <a id="1319" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1321" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1325" class="Symbol">)</a> <a id="1327" class="Symbol">(</a><a id="1328" href="globular-types.fibers-globular-maps.html#1328" class="Bound">y&#39;</a> <a id="1331" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1333" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1337" class="Symbol">)</a> <a id="1339" class="Symbol">=</a>
  <a id="1343" href="globular-types.fibers-globular-maps.html#953" class="Function">fiber-globular-map</a>
    <a id="1366" class="Symbol">(</a> <a id="1368" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1403" href="globular-types.fibers-globular-maps.html#1300" class="Bound">H</a> <a id="1405" href="globular-types.fibers-globular-maps.html#1317" class="Bound">y</a> <a id="1407" href="globular-types.fibers-globular-maps.html#1328" class="Bound">y&#39;</a><a id="1409" class="Symbol">)</a>
    <a id="1415" class="Symbol">(</a> <a id="1417" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="1452" href="globular-types.fibers-globular-maps.html#1302" class="Bound">G</a> <a id="1454" class="Symbol">_</a> <a id="1456" class="Symbol">_)</a>
    <a id="1463" class="Symbol">(</a> <a id="1465" href="globular-types.globular-maps.html#1009" class="Field">1-cell-globular-map-globular-map</a> <a id="1498" href="globular-types.fibers-globular-maps.html#1304" class="Bound">f</a><a id="1499" class="Symbol">)</a>
</pre>