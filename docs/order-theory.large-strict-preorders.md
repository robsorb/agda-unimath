# Large strict preorders

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="order-theory.large-strict-preorders.html" class="Module">order-theory.large-strict-preorders</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>

<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.large-binary-relations.html" class="Module">foundation.large-binary-relations</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="foundation.strictly-involutive-identity-types.html" class="Module">foundation.strictly-involutive-identity-types</a>
<a id="433" class="Keyword">open</a> <a id="438" class="Keyword">import</a> <a id="445" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="473" class="Keyword">open</a> <a id="478" class="Keyword">import</a> <a id="485" href="order-theory.strict-preorders.html" class="Module">order-theory.strict-preorders</a>
</pre>
</details>

## Idea

A {{#concept "large strict preorder" Agda=Large-Strict-Preorder}} consists of a
hierarchy of types $A$ indexed by universe levels, a
[large binary relation](foundation.large-binary-relations.md) $<$ on $A$ valued
in the [propositions](foundation-core.propositions.md), such that the relation
$<$ is irreflexive and transitive:

- For any $x:A$ we have $x ≮ x$.
- For any $x,y,z:A$ we have $(y<z) → (x<y) → (x<z)$.

Note that large strict preorders satisfy antisymmetry by irreflexivity and
transitivity, but this is not the correct extensionality principle for strict
preorders. The correct extensionality principle is considered on the page on
[large strict orders](order-theory.large-strict-orders.md).

## Definitions

### Large strict preorders

<pre class="Agda"><a id="1299" class="Keyword">record</a>
  <a id="Large-Strict-Preorder"></a><a id="1308" href="order-theory.large-strict-preorders.html#1308" class="Record">Large-Strict-Preorder</a>
  <a id="1332" class="Symbol">(</a><a id="1333" href="order-theory.large-strict-preorders.html#1333" class="Bound">α</a> <a id="1335" class="Symbol">:</a> <a id="1337" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1343" class="Symbol">→</a> <a id="1345" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1350" class="Symbol">)</a> <a id="1352" class="Symbol">(</a><a id="1353" href="order-theory.large-strict-preorders.html#1353" class="Bound">β</a> <a id="1355" class="Symbol">:</a> <a id="1357" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1363" class="Symbol">→</a> <a id="1365" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1371" class="Symbol">→</a> <a id="1373" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1378" class="Symbol">)</a> <a id="1380" class="Symbol">:</a> <a id="1382" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1388" class="Keyword">where</a>
  <a id="1396" class="Keyword">constructor</a>
    <a id="make-Large-Strict-Preorder"></a><a id="1412" href="order-theory.large-strict-preorders.html#1412" class="InductiveConstructor">make-Large-Strict-Preorder</a>
  <a id="1441" class="Keyword">field</a>
    <a id="Large-Strict-Preorder.type-Large-Strict-Preorder"></a><a id="1451" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a> <a id="1478" class="Symbol">:</a> <a id="1480" class="Symbol">(</a><a id="1481" href="order-theory.large-strict-preorders.html#1481" class="Bound">l</a> <a id="1483" class="Symbol">:</a> <a id="1485" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1490" class="Symbol">)</a> <a id="1492" class="Symbol">→</a> <a id="1494" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1497" class="Symbol">(</a><a id="1498" href="order-theory.large-strict-preorders.html#1333" class="Bound">α</a> <a id="1500" href="order-theory.large-strict-preorders.html#1481" class="Bound">l</a><a id="1501" class="Symbol">)</a>

    <a id="Large-Strict-Preorder.le-prop-Large-Strict-Preorder"></a><a id="1508" href="order-theory.large-strict-preorders.html#1508" class="Field">le-prop-Large-Strict-Preorder</a> <a id="1538" class="Symbol">:</a>
      <a id="1546" href="foundation.large-binary-relations.html#1598" class="Function">Large-Relation-Prop</a> <a id="1566" href="order-theory.large-strict-preorders.html#1353" class="Bound">β</a> <a id="1568" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a>

  <a id="Large-Strict-Preorder.le-Large-Strict-Preorder"></a><a id="1598" href="order-theory.large-strict-preorders.html#1598" class="Function">le-Large-Strict-Preorder</a> <a id="1623" class="Symbol">:</a> <a id="1625" href="foundation.large-binary-relations.html#1089" class="Function">Large-Relation</a> <a id="1640" href="order-theory.large-strict-preorders.html#1353" class="Bound">β</a> <a id="1642" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a>
  <a id="1671" href="order-theory.large-strict-preorders.html#1598" class="Function">le-Large-Strict-Preorder</a> <a id="1696" href="order-theory.large-strict-preorders.html#1696" class="Bound">x</a> <a id="1698" href="order-theory.large-strict-preorders.html#1698" class="Bound">y</a> <a id="1700" class="Symbol">=</a> <a id="1702" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1712" class="Symbol">(</a><a id="1713" href="order-theory.large-strict-preorders.html#1508" class="Field">le-prop-Large-Strict-Preorder</a> <a id="1743" href="order-theory.large-strict-preorders.html#1696" class="Bound">x</a> <a id="1745" href="order-theory.large-strict-preorders.html#1698" class="Bound">y</a><a id="1746" class="Symbol">)</a>

  <a id="Large-Strict-Preorder.is-prop-le-Large-Strict-Preorder"></a><a id="1751" href="order-theory.large-strict-preorders.html#1751" class="Function">is-prop-le-Large-Strict-Preorder</a> <a id="1784" class="Symbol">:</a>
    <a id="1790" class="Symbol">{</a><a id="1791" href="order-theory.large-strict-preorders.html#1791" class="Bound">l1</a> <a id="1794" href="order-theory.large-strict-preorders.html#1794" class="Bound">l2</a> <a id="1797" class="Symbol">:</a> <a id="1799" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1804" class="Symbol">}</a>
    <a id="1810" class="Symbol">(</a><a id="1811" href="order-theory.large-strict-preorders.html#1811" class="Bound">x</a> <a id="1813" class="Symbol">:</a> <a id="1815" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a> <a id="1842" href="order-theory.large-strict-preorders.html#1791" class="Bound">l1</a><a id="1844" class="Symbol">)</a>
    <a id="1850" class="Symbol">(</a><a id="1851" href="order-theory.large-strict-preorders.html#1851" class="Bound">y</a> <a id="1853" class="Symbol">:</a> <a id="1855" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a> <a id="1882" href="order-theory.large-strict-preorders.html#1794" class="Bound">l2</a><a id="1884" class="Symbol">)</a> <a id="1886" class="Symbol">→</a>
    <a id="1892" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1900" class="Symbol">(</a><a id="1901" href="order-theory.large-strict-preorders.html#1598" class="Function">le-Large-Strict-Preorder</a> <a id="1926" href="order-theory.large-strict-preorders.html#1811" class="Bound">x</a> <a id="1928" href="order-theory.large-strict-preorders.html#1851" class="Bound">y</a><a id="1929" class="Symbol">)</a>
  <a id="1933" href="order-theory.large-strict-preorders.html#1751" class="Function">is-prop-le-Large-Strict-Preorder</a> <a id="1966" href="order-theory.large-strict-preorders.html#1966" class="Bound">x</a> <a id="1968" href="order-theory.large-strict-preorders.html#1968" class="Bound">y</a> <a id="1970" class="Symbol">=</a>
    <a id="1976" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1994" class="Symbol">(</a><a id="1995" href="order-theory.large-strict-preorders.html#1508" class="Field">le-prop-Large-Strict-Preorder</a> <a id="2025" href="order-theory.large-strict-preorders.html#1966" class="Bound">x</a> <a id="2027" href="order-theory.large-strict-preorders.html#1968" class="Bound">y</a><a id="2028" class="Symbol">)</a>

  <a id="2033" class="Keyword">field</a>
    <a id="Large-Strict-Preorder.is-irreflexive-le-Large-Strict-Preorder"></a><a id="2043" href="order-theory.large-strict-preorders.html#2043" class="Field">is-irreflexive-le-Large-Strict-Preorder</a> <a id="2083" class="Symbol">:</a>
      <a id="2091" href="foundation.large-binary-relations.html#3776" class="Function">is-antireflexive-Large-Relation</a>
        <a id="2131" class="Symbol">(</a> <a id="2133" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a><a id="2159" class="Symbol">)</a>
        <a id="2169" class="Symbol">(</a> <a id="2171" href="order-theory.large-strict-preorders.html#1598" class="Function">le-Large-Strict-Preorder</a><a id="2195" class="Symbol">)</a>

    <a id="Large-Strict-Preorder.transitive-le-Large-Strict-Preorder"></a><a id="2202" href="order-theory.large-strict-preorders.html#2202" class="Field">transitive-le-Large-Strict-Preorder</a> <a id="2238" class="Symbol">:</a>
      <a id="2246" href="foundation.large-binary-relations.html#3481" class="Function">is-transitive-Large-Relation</a>
        <a id="2283" class="Symbol">(</a> <a id="2285" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a><a id="2311" class="Symbol">)</a>
        <a id="2321" class="Symbol">(</a> <a id="2323" href="order-theory.large-strict-preorders.html#1598" class="Function">le-Large-Strict-Preorder</a><a id="2347" class="Symbol">)</a>

<a id="2350" class="Keyword">open</a> <a id="2355" href="order-theory.large-strict-preorders.html#1308" class="Module">Large-Strict-Preorder</a> <a id="2377" class="Keyword">public</a>
</pre>
### The underlying strict preorder at a universe level

<pre class="Agda"><a id="2453" class="Keyword">module</a> <a id="2460" href="order-theory.large-strict-preorders.html#2460" class="Module">_</a>
  <a id="2464" class="Symbol">{</a><a id="2465" href="order-theory.large-strict-preorders.html#2465" class="Bound">α</a> <a id="2467" class="Symbol">:</a> <a id="2469" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="2475" class="Symbol">→</a> <a id="2477" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2482" class="Symbol">}</a> <a id="2484" class="Symbol">{</a><a id="2485" href="order-theory.large-strict-preorders.html#2485" class="Bound">β</a> <a id="2487" class="Symbol">:</a> <a id="2489" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="2495" class="Symbol">→</a> <a id="2497" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="2503" class="Symbol">→</a> <a id="2505" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2510" class="Symbol">}</a>
  <a id="2514" class="Symbol">(</a><a id="2515" href="order-theory.large-strict-preorders.html#2515" class="Bound">P</a> <a id="2517" class="Symbol">:</a> <a id="2519" href="order-theory.large-strict-preorders.html#1308" class="Record">Large-Strict-Preorder</a> <a id="2541" href="order-theory.large-strict-preorders.html#2465" class="Bound">α</a> <a id="2543" href="order-theory.large-strict-preorders.html#2485" class="Bound">β</a><a id="2544" class="Symbol">)</a>
  <a id="2548" class="Keyword">where</a>

  <a id="2557" href="order-theory.large-strict-preorders.html#2557" class="Function">strict-preorder-Large-Strict-Preorder</a> <a id="2595" class="Symbol">:</a>
    <a id="2601" class="Symbol">(</a><a id="2602" href="order-theory.large-strict-preorders.html#2602" class="Bound">l</a> <a id="2604" class="Symbol">:</a> <a id="2606" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2611" class="Symbol">)</a> <a id="2613" class="Symbol">→</a> <a id="2615" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="2631" class="Symbol">(</a><a id="2632" href="order-theory.large-strict-preorders.html#2465" class="Bound">α</a> <a id="2634" href="order-theory.large-strict-preorders.html#2602" class="Bound">l</a><a id="2635" class="Symbol">)</a> <a id="2637" class="Symbol">(</a><a id="2638" href="order-theory.large-strict-preorders.html#2485" class="Bound">β</a> <a id="2640" href="order-theory.large-strict-preorders.html#2602" class="Bound">l</a> <a id="2642" href="order-theory.large-strict-preorders.html#2602" class="Bound">l</a><a id="2643" class="Symbol">)</a>
  <a id="2647" href="order-theory.large-strict-preorders.html#2557" class="Function">strict-preorder-Large-Strict-Preorder</a> <a id="2685" href="order-theory.large-strict-preorders.html#2685" class="Bound">l</a> <a id="2687" class="Symbol">=</a>
    <a id="2693" class="Symbol">(</a> <a id="2695" href="order-theory.large-strict-preorders.html#1451" class="Field">type-Large-Strict-Preorder</a> <a id="2722" href="order-theory.large-strict-preorders.html#2515" class="Bound">P</a> <a id="2724" href="order-theory.large-strict-preorders.html#2685" class="Bound">l</a> <a id="2726" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="2734" href="order-theory.large-strict-preorders.html#1508" class="Field">le-prop-Large-Strict-Preorder</a> <a id="2764" href="order-theory.large-strict-preorders.html#2515" class="Bound">P</a> <a id="2766" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="2774" href="order-theory.large-strict-preorders.html#2043" class="Field">is-irreflexive-le-Large-Strict-Preorder</a> <a id="2814" href="order-theory.large-strict-preorders.html#2515" class="Bound">P</a> <a id="2816" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="2824" href="order-theory.large-strict-preorders.html#2202" class="Field">transitive-le-Large-Strict-Preorder</a> <a id="2860" href="order-theory.large-strict-preorders.html#2515" class="Bound">P</a><a id="2861" class="Symbol">)</a>
</pre>