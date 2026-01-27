# Dedekind finite types

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="univalent-combinatorics.dedekind-finite-types.html" class="Module">univalent-combinatorics.dedekind-finite-types</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="391" class="Keyword">open</a> <a id="396" class="Keyword">import</a> <a id="403" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="429" class="Keyword">open</a> <a id="434" class="Keyword">import</a> <a id="441" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="467" class="Keyword">open</a> <a id="472" class="Keyword">import</a> <a id="479" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="516" class="Keyword">open</a> <a id="521" class="Keyword">import</a> <a id="528" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="552" class="Keyword">open</a> <a id="557" class="Keyword">import</a> <a id="564" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="580" class="Keyword">open</a> <a id="585" class="Keyword">import</a> <a id="592" href="foundation.split-surjective-maps.html" class="Module">foundation.split-surjective-maps</a>
<a id="625" class="Keyword">open</a> <a id="630" class="Keyword">import</a> <a id="637" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="664" class="Keyword">open</a> <a id="669" class="Keyword">import</a> <a id="676" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

{{#concept "Dedekind finite types" Agda=Dedekind-Finite-Type Agda=is-dedekind-finite}}
are types `X` with the [property](foundation-core.propositions.md) that every
self-[embedding](foundation-core.embeddings.md) `X ↪ X` is an
[equivalence](foundation-core.equivalences.md).

## Definitions

### The predicate of being a Dedekind finite type

<pre class="Agda"><a id="is-dedekind-finite-Prop"></a><a id="1080" href="univalent-combinatorics.dedekind-finite-types.html#1080" class="Function">is-dedekind-finite-Prop</a> <a id="1104" class="Symbol">:</a> <a id="1106" class="Symbol">{</a><a id="1107" href="univalent-combinatorics.dedekind-finite-types.html#1107" class="Bound">l</a> <a id="1109" class="Symbol">:</a> <a id="1111" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1116" class="Symbol">}</a> <a id="1118" class="Symbol">→</a> <a id="1120" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1123" href="univalent-combinatorics.dedekind-finite-types.html#1107" class="Bound">l</a> <a id="1125" class="Symbol">→</a> <a id="1127" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1132" href="univalent-combinatorics.dedekind-finite-types.html#1107" class="Bound">l</a>
<a id="1134" href="univalent-combinatorics.dedekind-finite-types.html#1080" class="Function">is-dedekind-finite-Prop</a> <a id="1158" href="univalent-combinatorics.dedekind-finite-types.html#1158" class="Bound">X</a> <a id="1160" class="Symbol">=</a>
  <a id="1164" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
    <a id="1175" class="Symbol">(</a> <a id="1177" href="univalent-combinatorics.dedekind-finite-types.html#1158" class="Bound">X</a> <a id="1179" class="Symbol">→</a> <a id="1181" href="univalent-combinatorics.dedekind-finite-types.html#1158" class="Bound">X</a><a id="1182" class="Symbol">)</a>
    <a id="1188" class="Symbol">(</a> <a id="1190" class="Symbol">λ</a> <a id="1192" href="univalent-combinatorics.dedekind-finite-types.html#1192" class="Bound">f</a> <a id="1194" class="Symbol">→</a> <a id="1196" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a> <a id="1210" class="Symbol">(</a><a id="1211" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="1218" href="univalent-combinatorics.dedekind-finite-types.html#1192" class="Bound">f</a><a id="1219" class="Symbol">)</a> <a id="1221" class="Symbol">(</a><a id="1222" href="foundation.equivalences.html#5072" class="Function">is-equiv-Prop</a> <a id="1236" href="univalent-combinatorics.dedekind-finite-types.html#1192" class="Bound">f</a><a id="1237" class="Symbol">))</a>

<a id="is-dedekind-finite"></a><a id="1241" href="univalent-combinatorics.dedekind-finite-types.html#1241" class="Function">is-dedekind-finite</a> <a id="1260" class="Symbol">:</a> <a id="1262" class="Symbol">{</a><a id="1263" href="univalent-combinatorics.dedekind-finite-types.html#1263" class="Bound">l</a> <a id="1265" class="Symbol">:</a> <a id="1267" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1272" class="Symbol">}</a> <a id="1274" class="Symbol">→</a> <a id="1276" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1279" href="univalent-combinatorics.dedekind-finite-types.html#1263" class="Bound">l</a> <a id="1281" class="Symbol">→</a> <a id="1283" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1286" href="univalent-combinatorics.dedekind-finite-types.html#1263" class="Bound">l</a>
<a id="1288" href="univalent-combinatorics.dedekind-finite-types.html#1241" class="Function">is-dedekind-finite</a> <a id="1307" href="univalent-combinatorics.dedekind-finite-types.html#1307" class="Bound">X</a> <a id="1309" class="Symbol">=</a> <a id="1311" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1321" class="Symbol">(</a><a id="1322" href="univalent-combinatorics.dedekind-finite-types.html#1080" class="Function">is-dedekind-finite-Prop</a> <a id="1346" href="univalent-combinatorics.dedekind-finite-types.html#1307" class="Bound">X</a><a id="1347" class="Symbol">)</a>
</pre>
### The subuniverse of Dedekind finite types

<pre class="Agda"><a id="Dedekind-Finite-Type"></a><a id="1408" href="univalent-combinatorics.dedekind-finite-types.html#1408" class="Function">Dedekind-Finite-Type</a> <a id="1429" class="Symbol">:</a> <a id="1431" class="Symbol">(</a><a id="1432" href="univalent-combinatorics.dedekind-finite-types.html#1432" class="Bound">l</a> <a id="1434" class="Symbol">:</a> <a id="1436" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1441" class="Symbol">)</a> <a id="1443" class="Symbol">→</a> <a id="1445" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1448" class="Symbol">(</a><a id="1449" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1454" href="univalent-combinatorics.dedekind-finite-types.html#1432" class="Bound">l</a><a id="1455" class="Symbol">)</a>
<a id="1457" href="univalent-combinatorics.dedekind-finite-types.html#1408" class="Function">Dedekind-Finite-Type</a> <a id="1478" href="univalent-combinatorics.dedekind-finite-types.html#1478" class="Bound">l</a> <a id="1480" class="Symbol">=</a> <a id="1482" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1484" class="Symbol">(</a><a id="1485" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1488" href="univalent-combinatorics.dedekind-finite-types.html#1478" class="Bound">l</a><a id="1489" class="Symbol">)</a> <a id="1491" href="univalent-combinatorics.dedekind-finite-types.html#1241" class="Function">is-dedekind-finite</a>

<a id="1511" class="Keyword">module</a> <a id="1518" href="univalent-combinatorics.dedekind-finite-types.html#1518" class="Module">_</a>
  <a id="1522" class="Symbol">{</a><a id="1523" href="univalent-combinatorics.dedekind-finite-types.html#1523" class="Bound">l</a> <a id="1525" class="Symbol">:</a> <a id="1527" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1532" class="Symbol">}</a> <a id="1534" class="Symbol">(</a><a id="1535" href="univalent-combinatorics.dedekind-finite-types.html#1535" class="Bound">X</a> <a id="1537" class="Symbol">:</a> <a id="1539" href="univalent-combinatorics.dedekind-finite-types.html#1408" class="Function">Dedekind-Finite-Type</a> <a id="1560" href="univalent-combinatorics.dedekind-finite-types.html#1523" class="Bound">l</a><a id="1561" class="Symbol">)</a>
  <a id="1565" class="Keyword">where</a>

  <a id="1574" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a> <a id="1600" class="Symbol">:</a> <a id="1602" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1605" href="univalent-combinatorics.dedekind-finite-types.html#1523" class="Bound">l</a>
  <a id="1609" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a> <a id="1635" class="Symbol">=</a> <a id="1637" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1641" href="univalent-combinatorics.dedekind-finite-types.html#1535" class="Bound">X</a>

  <a id="1646" href="univalent-combinatorics.dedekind-finite-types.html#1646" class="Function">is-dedekind-finite-Dedekind-Finite-Type</a> <a id="1686" class="Symbol">:</a>
    <a id="1692" href="univalent-combinatorics.dedekind-finite-types.html#1241" class="Function">is-dedekind-finite</a> <a id="1711" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a>
  <a id="1739" href="univalent-combinatorics.dedekind-finite-types.html#1646" class="Function">is-dedekind-finite-Dedekind-Finite-Type</a> <a id="1779" class="Symbol">=</a> <a id="1781" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1785" href="univalent-combinatorics.dedekind-finite-types.html#1535" class="Bound">X</a>
</pre>
## Properties

### If two Dedekind finite types mutually embed, they are equivalent

This can be understood as a constructive
[Cantor–Schröder–Bernstein theorem](foundation.cantor-schroder-bernstein-escardo.md)
for Dedekind finite types.

**Proof.** Given embeddings `f : X ↪ Y` and `g : Y ↪ X`, we have a commuting
diagram

```text
       g ∘ f
    X ------> X
    |       ∧ |
  f |   g /   | f
    |   /     |
    ∨ /       ∨
    Y ------> Y.
       f ∘ g
```

The top and bottom rows are equivalences by Dedekind finiteness, so by the
6-for-2 property of equivalences every edge in this diagram is an equivalence. ∎

<pre class="Agda"><a id="2420" class="Keyword">module</a> <a id="2427" href="univalent-combinatorics.dedekind-finite-types.html#2427" class="Module">_</a>
  <a id="2431" class="Symbol">{</a><a id="2432" href="univalent-combinatorics.dedekind-finite-types.html#2432" class="Bound">l1</a> <a id="2435" href="univalent-combinatorics.dedekind-finite-types.html#2435" class="Bound">l2</a> <a id="2438" class="Symbol">:</a> <a id="2440" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2445" class="Symbol">}</a>
  <a id="2449" class="Symbol">(</a><a id="2450" href="univalent-combinatorics.dedekind-finite-types.html#2450" class="Bound">X</a> <a id="2452" class="Symbol">:</a> <a id="2454" href="univalent-combinatorics.dedekind-finite-types.html#1408" class="Function">Dedekind-Finite-Type</a> <a id="2475" href="univalent-combinatorics.dedekind-finite-types.html#2432" class="Bound">l1</a><a id="2477" class="Symbol">)</a> <a id="2479" class="Symbol">(</a><a id="2480" href="univalent-combinatorics.dedekind-finite-types.html#2480" class="Bound">Y</a> <a id="2482" class="Symbol">:</a> <a id="2484" href="univalent-combinatorics.dedekind-finite-types.html#1408" class="Function">Dedekind-Finite-Type</a> <a id="2505" href="univalent-combinatorics.dedekind-finite-types.html#2435" class="Bound">l2</a><a id="2507" class="Symbol">)</a>
  <a id="2511" class="Symbol">(</a><a id="2512" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a> <a id="2514" class="Symbol">:</a> <a id="2516" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a> <a id="2542" href="univalent-combinatorics.dedekind-finite-types.html#2450" class="Bound">X</a> <a id="2544" href="foundation-core.embeddings.html#1627" class="Function Operator">↪</a> <a id="2546" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a> <a id="2572" href="univalent-combinatorics.dedekind-finite-types.html#2480" class="Bound">Y</a><a id="2573" class="Symbol">)</a>
  <a id="2577" class="Symbol">(</a><a id="2578" href="univalent-combinatorics.dedekind-finite-types.html#2578" class="Bound">g</a> <a id="2580" class="Symbol">:</a> <a id="2582" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a> <a id="2608" href="univalent-combinatorics.dedekind-finite-types.html#2480" class="Bound">Y</a> <a id="2610" href="foundation-core.embeddings.html#1627" class="Function Operator">↪</a> <a id="2612" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a> <a id="2638" href="univalent-combinatorics.dedekind-finite-types.html#2450" class="Bound">X</a><a id="2639" class="Symbol">)</a>
  <a id="2643" class="Keyword">where</a>

  <a id="2652" href="univalent-combinatorics.dedekind-finite-types.html#2652" class="Function">is-equiv-map-Cantor-Schröder-Bernstein-Dedekind-Finite-Type</a> <a id="2712" class="Symbol">:</a>
    <a id="2718" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="2727" class="Symbol">(</a><a id="2728" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="2736" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a><a id="2737" class="Symbol">)</a>
  <a id="2741" href="univalent-combinatorics.dedekind-finite-types.html#2652" class="Function">is-equiv-map-Cantor-Schröder-Bernstein-Dedekind-Finite-Type</a> <a id="2801" class="Symbol">=</a>
    <a id="2807" href="foundation.equivalences.html#12459" class="Function">is-equiv-left-is-equiv-top-is-equiv-bottom-square</a>
      <a id="2863" class="Symbol">(</a> <a id="2865" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="2873" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a><a id="2874" class="Symbol">)</a>
      <a id="2882" class="Symbol">(</a> <a id="2884" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="2892" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a><a id="2893" class="Symbol">)</a>
      <a id="2901" class="Symbol">(</a> <a id="2903" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="2911" href="univalent-combinatorics.dedekind-finite-types.html#2578" class="Bound">g</a><a id="2912" class="Symbol">)</a>
      <a id="2920" class="Symbol">(</a> <a id="2922" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="2931" class="Symbol">)</a>
      <a id="2939" class="Symbol">(</a> <a id="2941" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="2950" class="Symbol">)</a>
      <a id="2958" class="Symbol">(</a> <a id="2960" href="univalent-combinatorics.dedekind-finite-types.html#1646" class="Function">is-dedekind-finite-Dedekind-Finite-Type</a> <a id="3000" href="univalent-combinatorics.dedekind-finite-types.html#2450" class="Bound">X</a>
        <a id="3010" class="Symbol">(</a> <a id="3012" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="3020" href="univalent-combinatorics.dedekind-finite-types.html#2578" class="Bound">g</a> <a id="3022" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3024" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="3032" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a><a id="3033" class="Symbol">)</a>
        <a id="3043" class="Symbol">(</a> <a id="3045" href="foundation.embeddings.html#3647" class="Function">is-emb-map-comp-emb</a> <a id="3065" href="univalent-combinatorics.dedekind-finite-types.html#2578" class="Bound">g</a> <a id="3067" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a><a id="3068" class="Symbol">))</a>
      <a id="3077" class="Symbol">(</a> <a id="3079" href="univalent-combinatorics.dedekind-finite-types.html#1646" class="Function">is-dedekind-finite-Dedekind-Finite-Type</a> <a id="3119" href="univalent-combinatorics.dedekind-finite-types.html#2480" class="Bound">Y</a>
        <a id="3129" class="Symbol">(</a> <a id="3131" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="3139" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a> <a id="3141" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="3143" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="3151" href="univalent-combinatorics.dedekind-finite-types.html#2578" class="Bound">g</a><a id="3152" class="Symbol">)</a>
        <a id="3162" class="Symbol">(</a> <a id="3164" href="foundation.embeddings.html#3647" class="Function">is-emb-map-comp-emb</a> <a id="3184" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a> <a id="3186" href="univalent-combinatorics.dedekind-finite-types.html#2578" class="Bound">g</a><a id="3187" class="Symbol">))</a>

  <a id="3193" href="univalent-combinatorics.dedekind-finite-types.html#3193" class="Function">Cantor-Schröder-Bernstein-Dedekind-Finite-Type</a> <a id="3240" class="Symbol">:</a>
    <a id="3246" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a> <a id="3272" href="univalent-combinatorics.dedekind-finite-types.html#2450" class="Bound">X</a> <a id="3274" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="3276" href="univalent-combinatorics.dedekind-finite-types.html#1574" class="Function">type-Dedekind-Finite-Type</a> <a id="3302" href="univalent-combinatorics.dedekind-finite-types.html#2480" class="Bound">Y</a>
  <a id="3306" href="univalent-combinatorics.dedekind-finite-types.html#3193" class="Function">Cantor-Schröder-Bernstein-Dedekind-Finite-Type</a> <a id="3353" class="Symbol">=</a>
    <a id="3359" class="Symbol">(</a> <a id="3361" href="foundation-core.embeddings.html#1770" class="Function">map-emb</a> <a id="3369" href="univalent-combinatorics.dedekind-finite-types.html#2512" class="Bound">f</a> <a id="3371" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3373" href="univalent-combinatorics.dedekind-finite-types.html#2652" class="Function">is-equiv-map-Cantor-Schröder-Bernstein-Dedekind-Finite-Type</a><a id="3432" class="Symbol">)</a>
</pre>
### If all elements are merely equal, then the type is Dedekind finite

<pre class="Agda"><a id="is-dedekind-finite-all-elements-merely-equal"></a><a id="3519" href="univalent-combinatorics.dedekind-finite-types.html#3519" class="Function">is-dedekind-finite-all-elements-merely-equal</a> <a id="3564" class="Symbol">:</a>
  <a id="3568" class="Symbol">{</a><a id="3569" href="univalent-combinatorics.dedekind-finite-types.html#3569" class="Bound">l</a> <a id="3571" class="Symbol">:</a> <a id="3573" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3578" class="Symbol">}</a> <a id="3580" class="Symbol">{</a><a id="3581" href="univalent-combinatorics.dedekind-finite-types.html#3581" class="Bound">X</a> <a id="3583" class="Symbol">:</a> <a id="3585" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3588" href="univalent-combinatorics.dedekind-finite-types.html#3569" class="Bound">l</a><a id="3589" class="Symbol">}</a> <a id="3591" class="Symbol">→</a> <a id="3593" class="Symbol">((</a><a id="3595" href="univalent-combinatorics.dedekind-finite-types.html#3595" class="Bound">x</a> <a id="3597" href="univalent-combinatorics.dedekind-finite-types.html#3597" class="Bound">y</a> <a id="3599" class="Symbol">:</a> <a id="3601" href="univalent-combinatorics.dedekind-finite-types.html#3581" class="Bound">X</a><a id="3602" class="Symbol">)</a> <a id="3604" class="Symbol">→</a> <a id="3606" href="foundation.propositional-truncations.html#1662" class="Function Operator">║</a> <a id="3608" href="univalent-combinatorics.dedekind-finite-types.html#3595" class="Bound">x</a> <a id="3610" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3612" href="univalent-combinatorics.dedekind-finite-types.html#3597" class="Bound">y</a> <a id="3614" href="foundation.propositional-truncations.html#1662" class="Function Operator">║₋₁</a><a id="3617" class="Symbol">)</a> <a id="3619" class="Symbol">→</a> <a id="3621" href="univalent-combinatorics.dedekind-finite-types.html#1241" class="Function">is-dedekind-finite</a> <a id="3640" href="univalent-combinatorics.dedekind-finite-types.html#3581" class="Bound">X</a>
<a id="3642" href="univalent-combinatorics.dedekind-finite-types.html#3519" class="Function">is-dedekind-finite-all-elements-merely-equal</a> <a id="3687" href="univalent-combinatorics.dedekind-finite-types.html#3687" class="Bound">H</a> <a id="3689" href="univalent-combinatorics.dedekind-finite-types.html#3689" class="Bound">f</a> <a id="3691" class="Symbol">=</a>
  <a id="3695" href="foundation.surjective-maps.html#15104" class="Function">is-equiv-is-emb-is-surjective</a> <a id="3725" class="Symbol">(λ</a> <a id="3728" href="univalent-combinatorics.dedekind-finite-types.html#3728" class="Bound">x</a> <a id="3730" class="Symbol">→</a> <a id="3732" href="foundation.functoriality-propositional-truncation.html#1256" class="Function">map-trunc-Prop</a> <a id="3747" class="Symbol">(</a><a id="3748" href="univalent-combinatorics.dedekind-finite-types.html#3728" class="Bound">x</a> <a id="3750" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,_</a><a id="3752" class="Symbol">)</a> <a id="3754" class="Symbol">(</a><a id="3755" href="univalent-combinatorics.dedekind-finite-types.html#3687" class="Bound">H</a> <a id="3757" class="Symbol">(</a><a id="3758" href="univalent-combinatorics.dedekind-finite-types.html#3689" class="Bound">f</a> <a id="3760" href="univalent-combinatorics.dedekind-finite-types.html#3728" class="Bound">x</a><a id="3761" class="Symbol">)</a> <a id="3763" href="univalent-combinatorics.dedekind-finite-types.html#3728" class="Bound">x</a><a id="3764" class="Symbol">))</a>
</pre>
### Propositions are Dedekind finite

<pre class="Agda"><a id="is-dedekind-finite-is-prop"></a><a id="3818" href="univalent-combinatorics.dedekind-finite-types.html#3818" class="Function">is-dedekind-finite-is-prop</a> <a id="3845" class="Symbol">:</a>
  <a id="3849" class="Symbol">{</a><a id="3850" href="univalent-combinatorics.dedekind-finite-types.html#3850" class="Bound">l</a> <a id="3852" class="Symbol">:</a> <a id="3854" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3859" class="Symbol">}</a> <a id="3861" class="Symbol">{</a><a id="3862" href="univalent-combinatorics.dedekind-finite-types.html#3862" class="Bound">X</a> <a id="3864" class="Symbol">:</a> <a id="3866" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3869" href="univalent-combinatorics.dedekind-finite-types.html#3850" class="Bound">l</a><a id="3870" class="Symbol">}</a> <a id="3872" class="Symbol">→</a> <a id="3874" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3882" href="univalent-combinatorics.dedekind-finite-types.html#3862" class="Bound">X</a> <a id="3884" class="Symbol">→</a> <a id="3886" href="univalent-combinatorics.dedekind-finite-types.html#1241" class="Function">is-dedekind-finite</a> <a id="3905" href="univalent-combinatorics.dedekind-finite-types.html#3862" class="Bound">X</a>
<a id="3907" href="univalent-combinatorics.dedekind-finite-types.html#3818" class="Function">is-dedekind-finite-is-prop</a> <a id="3934" href="univalent-combinatorics.dedekind-finite-types.html#3934" class="Bound">H</a> <a id="3936" href="univalent-combinatorics.dedekind-finite-types.html#3936" class="Bound">f</a> <a id="3938" href="univalent-combinatorics.dedekind-finite-types.html#3938" class="Bound">is-emb-f</a> <a id="3947" class="Symbol">=</a>
  <a id="3951" href="foundation.split-surjective-maps.html#2951" class="Function">is-equiv-is-split-surjective-is-injective</a> <a id="3993" href="univalent-combinatorics.dedekind-finite-types.html#3936" class="Bound">f</a>
    <a id="3999" class="Symbol">(</a> <a id="4001" href="foundation-core.injective-maps.html#3323" class="Function">is-injective-is-emb</a> <a id="4021" href="univalent-combinatorics.dedekind-finite-types.html#3938" class="Bound">is-emb-f</a><a id="4029" class="Symbol">)</a>
    <a id="4035" class="Symbol">(</a> <a id="4037" class="Symbol">λ</a> <a id="4039" href="univalent-combinatorics.dedekind-finite-types.html#4039" class="Bound">x</a> <a id="4041" class="Symbol">→</a> <a id="4043" class="Symbol">(</a><a id="4044" href="univalent-combinatorics.dedekind-finite-types.html#4039" class="Bound">x</a> <a id="4046" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4048" href="foundation-core.propositions.html#2524" class="Function">eq-is-prop</a> <a id="4059" href="univalent-combinatorics.dedekind-finite-types.html#3934" class="Bound">H</a><a id="4060" class="Symbol">))</a>
</pre>
## Comments

It seems to be an open problem whether Dedekind finite types are closed under
coproducts or products. {{#cite Sto87}}

## See also

- [Dual Dedekind finite types](univalent-combinatorics.dual-dedekind-finite-types.md)
- [Finite types](univalent-combinatorics.finite-types.md)
- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)
- [Subfinite types](univalent-combinatorics.subfinite-types.md)
- [Subfinitely enumerable types](univalent-combinatorics.subfinitely-enumerable-types.md)

## References

{{#bibliography}} {{#reference Sto87}}

## External links

- [`Fin.Dedekind`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Dedekind.html)
  at TypeTopology
- [finite object#Dedekind finiteness](https://ncatlab.org/nlab/show/finite+object#dedekind_finiteness)
  at $n$Lab
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
