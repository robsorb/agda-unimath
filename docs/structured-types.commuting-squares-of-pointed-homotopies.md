# Commuting squares of pointed homotopies

<pre class="Agda"><a id="52" class="Keyword">module</a> <a id="59" href="structured-types.commuting-squares-of-pointed-homotopies.html" class="Module">structured-types.commuting-squares-of-pointed-homotopies</a> <a id="116" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="structured-types.pointed-2-homotopies.html" class="Module">structured-types.pointed-2-homotopies</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="structured-types.pointed-dependent-functions.html" class="Module">structured-types.pointed-dependent-functions</a>
<a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="structured-types.pointed-families-of-types.html" class="Module">structured-types.pointed-families-of-types</a>
<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="422" class="Keyword">open</a> <a id="427" class="Keyword">import</a> <a id="434" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

A square of [pointed homotopies](structured-types.pointed-homotopies.md)

```text
          top
      f ------> g
      |         |
 left |         | right
      ∨         ∨
      h ------> i
        bottom
```

is said to be a
{{#concept "commuting square" Disambiguation="pointed homotopies" Agda=coherence-square-pointed-homotopies}}
of pointed homotopies if there is a pointed homotopy
`left ∙h bottom ~∗ top ∙h right `. Such a pointed homotopy is called a
{{#concept "coherence" Disambiguation="commuting square of homotopies" Agda=coherence-square-pointed-homotopies}}
of the square.

## Definitions

### Commuting squares of pointed homotopies

<pre class="Agda"><a id="1151" class="Keyword">module</a> <a id="1158" href="structured-types.commuting-squares-of-pointed-homotopies.html#1158" class="Module">_</a>
  <a id="1162" class="Symbol">{</a><a id="1163" href="structured-types.commuting-squares-of-pointed-homotopies.html#1163" class="Bound">l1</a> <a id="1166" href="structured-types.commuting-squares-of-pointed-homotopies.html#1166" class="Bound">l2</a> <a id="1169" class="Symbol">:</a> <a id="1171" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1176" class="Symbol">}</a>
  <a id="1180" class="Symbol">{</a><a id="1181" href="structured-types.commuting-squares-of-pointed-homotopies.html#1181" class="Bound">A</a> <a id="1183" class="Symbol">:</a> <a id="1185" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1198" href="structured-types.commuting-squares-of-pointed-homotopies.html#1163" class="Bound">l1</a><a id="1200" class="Symbol">}</a> <a id="1202" class="Symbol">{</a><a id="1203" href="structured-types.commuting-squares-of-pointed-homotopies.html#1203" class="Bound">B</a> <a id="1205" class="Symbol">:</a> <a id="1207" href="structured-types.pointed-families-of-types.html#583" class="Function">Pointed-Fam</a> <a id="1219" href="structured-types.commuting-squares-of-pointed-homotopies.html#1166" class="Bound">l2</a> <a id="1222" href="structured-types.commuting-squares-of-pointed-homotopies.html#1181" class="Bound">A</a><a id="1223" class="Symbol">}</a> <a id="1225" class="Symbol">{</a><a id="1226" href="structured-types.commuting-squares-of-pointed-homotopies.html#1226" class="Bound">f</a> <a id="1228" href="structured-types.commuting-squares-of-pointed-homotopies.html#1228" class="Bound">g</a> <a id="1230" href="structured-types.commuting-squares-of-pointed-homotopies.html#1230" class="Bound">h</a> <a id="1232" href="structured-types.commuting-squares-of-pointed-homotopies.html#1232" class="Bound">i</a> <a id="1234" class="Symbol">:</a> <a id="1236" href="structured-types.pointed-dependent-functions.html#728" class="Function">pointed-Π</a> <a id="1246" href="structured-types.commuting-squares-of-pointed-homotopies.html#1181" class="Bound">A</a> <a id="1248" href="structured-types.commuting-squares-of-pointed-homotopies.html#1203" class="Bound">B</a><a id="1249" class="Symbol">}</a>
  <a id="1253" class="Symbol">(</a><a id="1254" href="structured-types.commuting-squares-of-pointed-homotopies.html#1254" class="Bound">top</a> <a id="1258" class="Symbol">:</a> <a id="1260" href="structured-types.commuting-squares-of-pointed-homotopies.html#1226" class="Bound">f</a> <a id="1262" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1265" href="structured-types.commuting-squares-of-pointed-homotopies.html#1228" class="Bound">g</a><a id="1266" class="Symbol">)</a> <a id="1268" class="Symbol">(</a><a id="1269" href="structured-types.commuting-squares-of-pointed-homotopies.html#1269" class="Bound">left</a> <a id="1274" class="Symbol">:</a> <a id="1276" href="structured-types.commuting-squares-of-pointed-homotopies.html#1226" class="Bound">f</a> <a id="1278" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1281" href="structured-types.commuting-squares-of-pointed-homotopies.html#1230" class="Bound">h</a><a id="1282" class="Symbol">)</a> <a id="1284" class="Symbol">(</a><a id="1285" href="structured-types.commuting-squares-of-pointed-homotopies.html#1285" class="Bound">right</a> <a id="1291" class="Symbol">:</a> <a id="1293" href="structured-types.commuting-squares-of-pointed-homotopies.html#1228" class="Bound">g</a> <a id="1295" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1298" href="structured-types.commuting-squares-of-pointed-homotopies.html#1232" class="Bound">i</a><a id="1299" class="Symbol">)</a> <a id="1301" class="Symbol">(</a><a id="1302" href="structured-types.commuting-squares-of-pointed-homotopies.html#1302" class="Bound">bottom</a> <a id="1309" class="Symbol">:</a> <a id="1311" href="structured-types.commuting-squares-of-pointed-homotopies.html#1230" class="Bound">h</a> <a id="1313" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1316" href="structured-types.commuting-squares-of-pointed-homotopies.html#1232" class="Bound">i</a><a id="1317" class="Symbol">)</a>
  <a id="1321" class="Keyword">where</a>

  <a id="1330" href="structured-types.commuting-squares-of-pointed-homotopies.html#1330" class="Function">coherence-square-pointed-homotopies</a> <a id="1366" class="Symbol">:</a> <a id="1368" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1371" class="Symbol">(</a><a id="1372" href="structured-types.commuting-squares-of-pointed-homotopies.html#1163" class="Bound">l1</a> <a id="1375" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1377" href="structured-types.commuting-squares-of-pointed-homotopies.html#1166" class="Bound">l2</a><a id="1379" class="Symbol">)</a>
  <a id="1383" href="structured-types.commuting-squares-of-pointed-homotopies.html#1330" class="Function">coherence-square-pointed-homotopies</a> <a id="1419" class="Symbol">=</a>
    <a id="1425" href="structured-types.pointed-2-homotopies.html#4028" class="Function">pointed-2-htpy</a>
      <a id="1446" class="Symbol">(</a> <a id="1448" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="1468" href="structured-types.commuting-squares-of-pointed-homotopies.html#1269" class="Bound">left</a> <a id="1473" href="structured-types.commuting-squares-of-pointed-homotopies.html#1302" class="Bound">bottom</a><a id="1479" class="Symbol">)</a>
      <a id="1487" class="Symbol">(</a> <a id="1489" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="1509" href="structured-types.commuting-squares-of-pointed-homotopies.html#1254" class="Bound">top</a> <a id="1513" href="structured-types.commuting-squares-of-pointed-homotopies.html#1285" class="Bound">right</a><a id="1518" class="Symbol">)</a>

  <a id="1523" href="structured-types.commuting-squares-of-pointed-homotopies.html#1523" class="Function">coherence-square-pointed-homotopies&#39;</a> <a id="1560" class="Symbol">:</a> <a id="1562" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1565" class="Symbol">(</a><a id="1566" href="structured-types.commuting-squares-of-pointed-homotopies.html#1163" class="Bound">l1</a> <a id="1569" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1571" href="structured-types.commuting-squares-of-pointed-homotopies.html#1166" class="Bound">l2</a><a id="1573" class="Symbol">)</a>
  <a id="1577" href="structured-types.commuting-squares-of-pointed-homotopies.html#1523" class="Function">coherence-square-pointed-homotopies&#39;</a> <a id="1614" class="Symbol">=</a>
    <a id="1620" href="structured-types.pointed-2-homotopies.html#4028" class="Function">pointed-2-htpy</a>
      <a id="1641" class="Symbol">(</a> <a id="1643" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="1663" href="structured-types.commuting-squares-of-pointed-homotopies.html#1254" class="Bound">top</a> <a id="1667" href="structured-types.commuting-squares-of-pointed-homotopies.html#1285" class="Bound">right</a><a id="1672" class="Symbol">)</a>
      <a id="1680" class="Symbol">(</a> <a id="1682" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a> <a id="1702" href="structured-types.commuting-squares-of-pointed-homotopies.html#1269" class="Bound">left</a> <a id="1707" href="structured-types.commuting-squares-of-pointed-homotopies.html#1302" class="Bound">bottom</a><a id="1713" class="Symbol">)</a>
</pre>