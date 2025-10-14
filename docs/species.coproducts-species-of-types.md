# Coproducts of species of types

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="species.coproducts-species-of-types.html" class="Module">species.coproducts-species-of-types</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="foundation.functoriality-dependent-function-types.html" class="Module">foundation.functoriality-dependent-function-types</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="foundation.type-theoretic-principle-of-choice.html" class="Module">foundation.type-theoretic-principle-of-choice</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="foundation.universal-property-coproduct-types.html" class="Module">foundation.universal-property-coproduct-types</a>
<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="species.morphisms-species-of-types.html" class="Module">species.morphisms-species-of-types</a>
<a id="529" class="Keyword">open</a> <a id="534" class="Keyword">import</a> <a id="541" href="species.species-of-types.html" class="Module">species.species-of-types</a>
</pre>
</details>

## Idea

The
{{#concept "coproduct" Disambiguation="of species of types" Agda=coproduct-species-types}}
of two [species of types](species.species-of-types.md) `F` and `G` is the
pointwise [coproduct](foundation.coproduct-types.md).

## Definition

### Coproduct on objects

<pre class="Agda"><a id="coproduct-species-types"></a><a id="865" href="species.coproducts-species-of-types.html#865" class="Function">coproduct-species-types</a> <a id="889" class="Symbol">:</a>
  <a id="893" class="Symbol">{</a><a id="894" href="species.coproducts-species-of-types.html#894" class="Bound">l1</a> <a id="897" href="species.coproducts-species-of-types.html#897" class="Bound">l2</a> <a id="900" href="species.coproducts-species-of-types.html#900" class="Bound">l3</a> <a id="903" class="Symbol">:</a> <a id="905" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="910" class="Symbol">}</a> <a id="912" class="Symbol">(</a><a id="913" href="species.coproducts-species-of-types.html#913" class="Bound">F</a> <a id="915" class="Symbol">:</a> <a id="917" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="931" href="species.coproducts-species-of-types.html#894" class="Bound">l1</a> <a id="934" href="species.coproducts-species-of-types.html#897" class="Bound">l2</a><a id="936" class="Symbol">)</a> <a id="938" class="Symbol">(</a><a id="939" href="species.coproducts-species-of-types.html#939" class="Bound">G</a> <a id="941" class="Symbol">:</a> <a id="943" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="957" href="species.coproducts-species-of-types.html#894" class="Bound">l1</a> <a id="960" href="species.coproducts-species-of-types.html#900" class="Bound">l3</a><a id="962" class="Symbol">)</a> <a id="964" class="Symbol">→</a>
  <a id="968" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="982" href="species.coproducts-species-of-types.html#894" class="Bound">l1</a> <a id="985" class="Symbol">(</a><a id="986" href="species.coproducts-species-of-types.html#897" class="Bound">l2</a> <a id="989" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="991" href="species.coproducts-species-of-types.html#900" class="Bound">l3</a><a id="993" class="Symbol">)</a>
<a id="995" href="species.coproducts-species-of-types.html#865" class="Function">coproduct-species-types</a> <a id="1019" href="species.coproducts-species-of-types.html#1019" class="Bound">F</a> <a id="1021" href="species.coproducts-species-of-types.html#1021" class="Bound">G</a> <a id="1023" href="species.coproducts-species-of-types.html#1023" class="Bound">X</a> <a id="1025" class="Symbol">=</a> <a id="1027" class="Symbol">(</a><a id="1028" href="species.coproducts-species-of-types.html#1019" class="Bound">F</a> <a id="1030" href="species.coproducts-species-of-types.html#1023" class="Bound">X</a> <a id="1032" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="1034" href="species.coproducts-species-of-types.html#1021" class="Bound">G</a> <a id="1036" href="species.coproducts-species-of-types.html#1023" class="Bound">X</a><a id="1037" class="Symbol">)</a>
</pre>
## Universal properties

Proof of

```text
  (hom-species-types (species-types-coproduct F G) H) ≃
  ((hom-species-types F H) × (hom-species-types G H)).
```

<pre class="Agda"><a id="equiv-universal-property-coproduct-species-types"></a><a id="1211" href="species.coproducts-species-of-types.html#1211" class="Function">equiv-universal-property-coproduct-species-types</a> <a id="1260" class="Symbol">:</a>
  <a id="1264" class="Symbol">{</a><a id="1265" href="species.coproducts-species-of-types.html#1265" class="Bound">l1</a> <a id="1268" href="species.coproducts-species-of-types.html#1268" class="Bound">l2</a> <a id="1271" href="species.coproducts-species-of-types.html#1271" class="Bound">l3</a> <a id="1274" href="species.coproducts-species-of-types.html#1274" class="Bound">l4</a> <a id="1277" class="Symbol">:</a> <a id="1279" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1284" class="Symbol">}</a>
  <a id="1288" class="Symbol">(</a><a id="1289" href="species.coproducts-species-of-types.html#1289" class="Bound">F</a> <a id="1291" class="Symbol">:</a> <a id="1293" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1307" href="species.coproducts-species-of-types.html#1265" class="Bound">l1</a> <a id="1310" href="species.coproducts-species-of-types.html#1268" class="Bound">l2</a><a id="1312" class="Symbol">)</a>
  <a id="1316" class="Symbol">(</a><a id="1317" href="species.coproducts-species-of-types.html#1317" class="Bound">G</a> <a id="1319" class="Symbol">:</a> <a id="1321" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1335" href="species.coproducts-species-of-types.html#1265" class="Bound">l1</a> <a id="1338" href="species.coproducts-species-of-types.html#1271" class="Bound">l3</a><a id="1340" class="Symbol">)</a>
  <a id="1344" class="Symbol">(</a><a id="1345" href="species.coproducts-species-of-types.html#1345" class="Bound">H</a> <a id="1347" class="Symbol">:</a> <a id="1349" href="species.species-of-types.html#525" class="Function">species-types</a> <a id="1363" href="species.coproducts-species-of-types.html#1265" class="Bound">l1</a> <a id="1366" href="species.coproducts-species-of-types.html#1274" class="Bound">l4</a><a id="1368" class="Symbol">)</a> <a id="1370" class="Symbol">→</a>
  <a id="1374" href="species.morphisms-species-of-types.html#834" class="Function">hom-species-types</a> <a id="1392" class="Symbol">(</a><a id="1393" href="species.coproducts-species-of-types.html#865" class="Function">coproduct-species-types</a> <a id="1417" href="species.coproducts-species-of-types.html#1289" class="Bound">F</a> <a id="1419" href="species.coproducts-species-of-types.html#1317" class="Bound">G</a><a id="1420" class="Symbol">)</a> <a id="1422" href="species.coproducts-species-of-types.html#1345" class="Bound">H</a> <a id="1424" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
  <a id="1428" class="Symbol">((</a><a id="1430" href="species.morphisms-species-of-types.html#834" class="Function">hom-species-types</a> <a id="1448" href="species.coproducts-species-of-types.html#1289" class="Bound">F</a> <a id="1450" href="species.coproducts-species-of-types.html#1345" class="Bound">H</a><a id="1451" class="Symbol">)</a> <a id="1453" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1455" class="Symbol">(</a><a id="1456" href="species.morphisms-species-of-types.html#834" class="Function">hom-species-types</a> <a id="1474" href="species.coproducts-species-of-types.html#1317" class="Bound">G</a> <a id="1476" href="species.coproducts-species-of-types.html#1345" class="Bound">H</a><a id="1477" class="Symbol">))</a>
<a id="1480" href="species.coproducts-species-of-types.html#1211" class="Function">equiv-universal-property-coproduct-species-types</a> <a id="1529" href="species.coproducts-species-of-types.html#1529" class="Bound">F</a> <a id="1531" href="species.coproducts-species-of-types.html#1531" class="Bound">G</a> <a id="1533" href="species.coproducts-species-of-types.html#1533" class="Bound">H</a> <a id="1535" class="Symbol">=</a>
  <a id="1539" class="Symbol">(</a> <a id="1541" href="foundation-core.type-theoretic-principle-of-choice.html#2895" class="Function">distributive-Π-Σ</a><a id="1557" class="Symbol">)</a> <a id="1559" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
  <a id="1564" class="Symbol">(</a> <a id="1566" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a> <a id="1587" class="Symbol">(λ</a> <a id="1590" href="species.coproducts-species-of-types.html#1590" class="Bound">X</a> <a id="1592" class="Symbol">→</a> <a id="1594" href="foundation.universal-property-coproduct-types.html#2015" class="Function">equiv-universal-property-coproduct</a> <a id="1629" class="Symbol">(</a><a id="1630" href="species.coproducts-species-of-types.html#1533" class="Bound">H</a> <a id="1632" href="species.coproducts-species-of-types.html#1590" class="Bound">X</a><a id="1633" class="Symbol">)))</a>
</pre>