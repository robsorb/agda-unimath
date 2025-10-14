# Strict preorders

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="order-theory.strict-preorders.html" class="Module">order-theory.strict-preorders</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="320" class="Keyword">open</a> <a id="325" class="Keyword">import</a> <a id="332" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A {{#concept "strict preorder" Agda=Strict-Preorder}} consists of a type $A$, a
[binary relation](foundation.binary-relations.md) $<$ on $A$ valued in the
[propositions](foundation-core.propositions.md), such that the relation $<$ is
irreflexive and transitive:

- For any $x:A$ we have $x ≮ x$.
- For any $x,y,z:A$ we have $(y<z) → (x<y) → (x<z)$.

Note that strict preorders satisfy antisymmetry by irreflexivity and
transitivity, but this is not the correct extensionality principle for strict
preorders. The correct extensionality principle is considered on the page on
[strict orders](order-theory.strict-orders.md).

## Definitions

### The type of strict preorders

<pre class="Agda"><a id="Strict-Preorder"></a><a id="1102" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="1118" class="Symbol">:</a> <a id="1120" class="Symbol">(</a><a id="1121" href="order-theory.strict-preorders.html#1121" class="Bound">l1</a> <a id="1124" href="order-theory.strict-preorders.html#1124" class="Bound">l2</a> <a id="1127" class="Symbol">:</a> <a id="1129" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1134" class="Symbol">)</a> <a id="1136" class="Symbol">→</a> <a id="1138" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1141" class="Symbol">(</a><a id="1142" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1147" href="order-theory.strict-preorders.html#1121" class="Bound">l1</a> <a id="1150" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1152" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1157" href="order-theory.strict-preorders.html#1124" class="Bound">l2</a><a id="1159" class="Symbol">)</a>
<a id="1161" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="1177" href="order-theory.strict-preorders.html#1177" class="Bound">l1</a> <a id="1180" href="order-theory.strict-preorders.html#1180" class="Bound">l2</a> <a id="1183" class="Symbol">=</a>
  <a id="1187" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1189" class="Symbol">(</a> <a id="1191" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1194" href="order-theory.strict-preorders.html#1177" class="Bound">l1</a><a id="1196" class="Symbol">)</a>
    <a id="1202" class="Symbol">(</a> <a id="1204" class="Symbol">λ</a> <a id="1206" href="order-theory.strict-preorders.html#1206" class="Bound">A</a> <a id="1208" class="Symbol">→</a>
      <a id="1216" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1218" class="Symbol">(</a> <a id="1220" href="foundation.binary-relations.html#1511" class="Function">Relation-Prop</a> <a id="1234" href="order-theory.strict-preorders.html#1180" class="Bound">l2</a> <a id="1237" href="order-theory.strict-preorders.html#1206" class="Bound">A</a><a id="1238" class="Symbol">)</a>
        <a id="1248" class="Symbol">(</a> <a id="1250" class="Symbol">λ</a> <a id="1252" href="order-theory.strict-preorders.html#1252" class="Bound">R</a> <a id="1254" class="Symbol">→</a> <a id="1256" href="foundation.binary-relations.html#5708" class="Function">is-irreflexive-Relation-Prop</a> <a id="1285" href="order-theory.strict-preorders.html#1252" class="Bound">R</a> <a id="1287" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1289" href="foundation.binary-relations.html#4937" class="Function">is-transitive-Relation-Prop</a> <a id="1317" href="order-theory.strict-preorders.html#1252" class="Bound">R</a><a id="1318" class="Symbol">))</a>

<a id="1322" class="Keyword">module</a> <a id="1329" href="order-theory.strict-preorders.html#1329" class="Module">_</a>
  <a id="1333" class="Symbol">{</a><a id="1334" href="order-theory.strict-preorders.html#1334" class="Bound">l1</a> <a id="1337" href="order-theory.strict-preorders.html#1337" class="Bound">l2</a> <a id="1340" class="Symbol">:</a> <a id="1342" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1347" class="Symbol">}</a> <a id="1349" class="Symbol">(</a><a id="1350" href="order-theory.strict-preorders.html#1350" class="Bound">A</a> <a id="1352" class="Symbol">:</a> <a id="1354" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="1370" href="order-theory.strict-preorders.html#1334" class="Bound">l1</a> <a id="1373" href="order-theory.strict-preorders.html#1337" class="Bound">l2</a><a id="1375" class="Symbol">)</a>
  <a id="1379" class="Keyword">where</a>

  <a id="1388" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="1409" class="Symbol">:</a>
    <a id="1415" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1418" href="order-theory.strict-preorders.html#1334" class="Bound">l1</a>
  <a id="1423" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="1444" class="Symbol">=</a>
    <a id="1450" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1454" href="order-theory.strict-preorders.html#1350" class="Bound">A</a>

  <a id="1459" href="order-theory.strict-preorders.html#1459" class="Function">le-prop-Strict-Preorder</a> <a id="1483" class="Symbol">:</a>
    <a id="1489" href="foundation.binary-relations.html#1511" class="Function">Relation-Prop</a> <a id="1503" href="order-theory.strict-preorders.html#1337" class="Bound">l2</a> <a id="1506" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a>
  <a id="1529" href="order-theory.strict-preorders.html#1459" class="Function">le-prop-Strict-Preorder</a> <a id="1553" class="Symbol">=</a>
    <a id="1559" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1563" class="Symbol">(</a><a id="1564" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1568" href="order-theory.strict-preorders.html#1350" class="Bound">A</a><a id="1569" class="Symbol">)</a>

  <a id="1574" href="order-theory.strict-preorders.html#1574" class="Function">le-Strict-Preorder</a> <a id="1593" class="Symbol">:</a>
    <a id="1599" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1608" href="order-theory.strict-preorders.html#1337" class="Bound">l2</a> <a id="1611" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a>
  <a id="1634" href="order-theory.strict-preorders.html#1574" class="Function">le-Strict-Preorder</a> <a id="1653" class="Symbol">=</a>
    <a id="1659" href="foundation.binary-relations.html#1621" class="Function">type-Relation-Prop</a> <a id="1678" href="order-theory.strict-preorders.html#1459" class="Function">le-prop-Strict-Preorder</a>

  <a id="1705" href="order-theory.strict-preorders.html#1705" class="Function">is-prop-le-Strict-Preorder</a> <a id="1732" class="Symbol">:</a>
    <a id="1738" class="Symbol">(</a><a id="1739" href="order-theory.strict-preorders.html#1739" class="Bound">x</a> <a id="1741" href="order-theory.strict-preorders.html#1741" class="Bound">y</a> <a id="1743" class="Symbol">:</a> <a id="1745" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a><a id="1765" class="Symbol">)</a> <a id="1767" class="Symbol">→</a>
    <a id="1773" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1781" class="Symbol">(</a><a id="1782" href="order-theory.strict-preorders.html#1574" class="Function">le-Strict-Preorder</a> <a id="1801" href="order-theory.strict-preorders.html#1739" class="Bound">x</a> <a id="1803" href="order-theory.strict-preorders.html#1741" class="Bound">y</a><a id="1804" class="Symbol">)</a>
  <a id="1808" href="order-theory.strict-preorders.html#1705" class="Function">is-prop-le-Strict-Preorder</a> <a id="1835" class="Symbol">=</a>
    <a id="1841" href="foundation.binary-relations.html#1749" class="Function">is-prop-type-Relation-Prop</a> <a id="1868" href="order-theory.strict-preorders.html#1459" class="Function">le-prop-Strict-Preorder</a>

  <a id="1895" href="order-theory.strict-preorders.html#1895" class="Function">is-irreflexive-le-Strict-Preorder</a> <a id="1929" class="Symbol">:</a>
    <a id="1935" href="foundation.binary-relations.html#5565" class="Function">is-irreflexive</a> <a id="1950" href="order-theory.strict-preorders.html#1574" class="Function">le-Strict-Preorder</a>
  <a id="1971" href="order-theory.strict-preorders.html#1895" class="Function">is-irreflexive-le-Strict-Preorder</a> <a id="2005" class="Symbol">=</a>
    <a id="2011" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2015" class="Symbol">(</a><a id="2016" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2020" class="Symbol">(</a><a id="2021" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2025" href="order-theory.strict-preorders.html#1350" class="Bound">A</a><a id="2026" class="Symbol">))</a>

  <a id="2032" href="order-theory.strict-preorders.html#2032" class="Function">is-transitive-le-Strict-Preorder</a> <a id="2065" class="Symbol">:</a>
    <a id="2071" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2085" href="order-theory.strict-preorders.html#1574" class="Function">le-Strict-Preorder</a>
  <a id="2106" href="order-theory.strict-preorders.html#2032" class="Function">is-transitive-le-Strict-Preorder</a> <a id="2139" class="Symbol">=</a>
    <a id="2145" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2149" class="Symbol">(</a><a id="2150" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2154" class="Symbol">(</a><a id="2155" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2159" href="order-theory.strict-preorders.html#1350" class="Bound">A</a><a id="2160" class="Symbol">))</a>
</pre>
## Properties

### The ordering of a strict preorder is antisymmetric

<pre class="Agda"><a id="2247" class="Keyword">module</a> <a id="2254" href="order-theory.strict-preorders.html#2254" class="Module">_</a>
  <a id="2258" class="Symbol">{</a><a id="2259" href="order-theory.strict-preorders.html#2259" class="Bound">l1</a> <a id="2262" href="order-theory.strict-preorders.html#2262" class="Bound">l2</a> <a id="2265" class="Symbol">:</a> <a id="2267" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2272" class="Symbol">}</a> <a id="2274" class="Symbol">(</a><a id="2275" href="order-theory.strict-preorders.html#2275" class="Bound">A</a> <a id="2277" class="Symbol">:</a> <a id="2279" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="2295" href="order-theory.strict-preorders.html#2259" class="Bound">l1</a> <a id="2298" href="order-theory.strict-preorders.html#2262" class="Bound">l2</a><a id="2300" class="Symbol">)</a>
  <a id="2304" class="Keyword">where</a>

  <a id="2313" href="order-theory.strict-preorders.html#2313" class="Function">is-antisymmetric-le-Strict-Preorder</a> <a id="2349" class="Symbol">:</a>
    <a id="2355" href="foundation.binary-relations.html#6436" class="Function">is-antisymmetric</a> <a id="2372" class="Symbol">(</a><a id="2373" href="order-theory.strict-preorders.html#1574" class="Function">le-Strict-Preorder</a> <a id="2392" href="order-theory.strict-preorders.html#2275" class="Bound">A</a><a id="2393" class="Symbol">)</a>
  <a id="2397" href="order-theory.strict-preorders.html#2313" class="Function">is-antisymmetric-le-Strict-Preorder</a> <a id="2433" href="order-theory.strict-preorders.html#2433" class="Bound">x</a> <a id="2435" href="order-theory.strict-preorders.html#2435" class="Bound">y</a> <a id="2437" href="order-theory.strict-preorders.html#2437" class="Bound">H</a> <a id="2439" href="order-theory.strict-preorders.html#2439" class="Bound">K</a> <a id="2441" class="Symbol">=</a>
    <a id="2447" href="foundation-core.empty-types.html#904" class="Function">ex-falso</a>
      <a id="2462" class="Symbol">(</a> <a id="2464" href="order-theory.strict-preorders.html#1895" class="Function">is-irreflexive-le-Strict-Preorder</a> <a id="2498" href="order-theory.strict-preorders.html#2275" class="Bound">A</a> <a id="2500" href="order-theory.strict-preorders.html#2433" class="Bound">x</a>
        <a id="2510" class="Symbol">(</a> <a id="2512" href="order-theory.strict-preorders.html#2032" class="Function">is-transitive-le-Strict-Preorder</a> <a id="2545" href="order-theory.strict-preorders.html#2275" class="Bound">A</a> <a id="2547" href="order-theory.strict-preorders.html#2433" class="Bound">x</a> <a id="2549" href="order-theory.strict-preorders.html#2435" class="Bound">y</a> <a id="2551" href="order-theory.strict-preorders.html#2433" class="Bound">x</a> <a id="2553" href="order-theory.strict-preorders.html#2439" class="Bound">K</a> <a id="2555" href="order-theory.strict-preorders.html#2437" class="Bound">H</a><a id="2556" class="Symbol">))</a>
</pre>