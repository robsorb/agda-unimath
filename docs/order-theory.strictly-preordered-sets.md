# Strictly preordered sets

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="order-theory.strictly-preordered-sets.html" class="Module">order-theory.strictly-preordered-sets</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="269" class="Keyword">open</a> <a id="274" class="Keyword">import</a> <a id="281" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="440" class="Keyword">open</a> <a id="445" class="Keyword">import</a> <a id="452" href="order-theory.strict-preorders.html" class="Module">order-theory.strict-preorders</a>
</pre>
</details>

## Idea

A {{#concept "strictly preordered set" Agda=Strictly-Preordered-Set}} is a
[strictly preordered type](order-theory.strict-preorders.md) whose underlying
type is a [set](foundation-core.sets.md). More specifically, a strictly
preordered set consists of a set $A$, a
[binary relation](foundation.binary-relations.md) $<$ on $A$ valued in the
[propositions](foundation-core.propositions.md), such that the relation $<$ is
irreflexive and transitive:

- For any $x:A$ we have $x \nle x$.
- For any $x,y,z:A$ we have $y<z \to x<y \to x<z$.

Strictly preordered sets satisfy antisymmetry by irreflexivity and transitivity.

## Definitions

### The type of strictly preordered sets

<pre class="Agda"><a id="Strictly-Preordered-Set"></a><a id="1192" href="order-theory.strictly-preordered-sets.html#1192" class="Function">Strictly-Preordered-Set</a> <a id="1216" class="Symbol">:</a> <a id="1218" class="Symbol">(</a><a id="1219" href="order-theory.strictly-preordered-sets.html#1219" class="Bound">l1</a> <a id="1222" href="order-theory.strictly-preordered-sets.html#1222" class="Bound">l2</a> <a id="1225" class="Symbol">:</a> <a id="1227" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1232" class="Symbol">)</a> <a id="1234" class="Symbol">→</a> <a id="1236" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1239" class="Symbol">(</a><a id="1240" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1245" href="order-theory.strictly-preordered-sets.html#1219" class="Bound">l1</a> <a id="1248" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1250" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1255" href="order-theory.strictly-preordered-sets.html#1222" class="Bound">l2</a><a id="1257" class="Symbol">)</a>
<a id="1259" href="order-theory.strictly-preordered-sets.html#1192" class="Function">Strictly-Preordered-Set</a> <a id="1283" href="order-theory.strictly-preordered-sets.html#1283" class="Bound">l1</a> <a id="1286" href="order-theory.strictly-preordered-sets.html#1286" class="Bound">l2</a> <a id="1289" class="Symbol">=</a>
  <a id="1293" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1295" class="Symbol">(</a> <a id="1297" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1301" href="order-theory.strictly-preordered-sets.html#1283" class="Bound">l1</a><a id="1303" class="Symbol">)</a>
    <a id="1309" class="Symbol">(</a> <a id="1311" class="Symbol">λ</a> <a id="1313" href="order-theory.strictly-preordered-sets.html#1313" class="Bound">A</a> <a id="1315" class="Symbol">→</a>
      <a id="1323" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1325" class="Symbol">(</a> <a id="1327" href="foundation.binary-relations.html#1511" class="Function">Relation-Prop</a> <a id="1341" href="order-theory.strictly-preordered-sets.html#1286" class="Bound">l2</a> <a id="1344" class="Symbol">(</a><a id="1345" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1354" href="order-theory.strictly-preordered-sets.html#1313" class="Bound">A</a><a id="1355" class="Symbol">))</a>
        <a id="1366" class="Symbol">(</a> <a id="1368" class="Symbol">λ</a> <a id="1370" href="order-theory.strictly-preordered-sets.html#1370" class="Bound">R</a> <a id="1372" class="Symbol">→</a> <a id="1374" href="foundation.binary-relations.html#5708" class="Function">is-irreflexive-Relation-Prop</a> <a id="1403" href="order-theory.strictly-preordered-sets.html#1370" class="Bound">R</a> <a id="1405" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1407" href="foundation.binary-relations.html#4937" class="Function">is-transitive-Relation-Prop</a> <a id="1435" href="order-theory.strictly-preordered-sets.html#1370" class="Bound">R</a><a id="1436" class="Symbol">))</a>

<a id="make-Strictly-Preordered-Set"></a><a id="1440" href="order-theory.strictly-preordered-sets.html#1440" class="Function">make-Strictly-Preordered-Set</a> <a id="1469" class="Symbol">:</a>
  <a id="1473" class="Symbol">{</a><a id="1474" href="order-theory.strictly-preordered-sets.html#1474" class="Bound">l1</a> <a id="1477" href="order-theory.strictly-preordered-sets.html#1477" class="Bound">l2</a> <a id="1480" class="Symbol">:</a> <a id="1482" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1487" class="Symbol">}</a>
  <a id="1491" class="Symbol">(</a><a id="1492" href="order-theory.strictly-preordered-sets.html#1492" class="Bound">P</a> <a id="1494" class="Symbol">:</a> <a id="1496" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="1512" href="order-theory.strictly-preordered-sets.html#1474" class="Bound">l1</a> <a id="1515" href="order-theory.strictly-preordered-sets.html#1477" class="Bound">l2</a><a id="1517" class="Symbol">)</a> <a id="1519" class="Symbol">→</a>
  <a id="1523" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="1530" class="Symbol">(</a><a id="1531" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="1552" href="order-theory.strictly-preordered-sets.html#1492" class="Bound">P</a><a id="1553" class="Symbol">)</a> <a id="1555" class="Symbol">→</a>
  <a id="1559" href="order-theory.strictly-preordered-sets.html#1192" class="Function">Strictly-Preordered-Set</a> <a id="1583" href="order-theory.strictly-preordered-sets.html#1474" class="Bound">l1</a> <a id="1586" href="order-theory.strictly-preordered-sets.html#1477" class="Bound">l2</a>
<a id="1589" href="order-theory.strictly-preordered-sets.html#1440" class="Function">make-Strictly-Preordered-Set</a> <a id="1618" href="order-theory.strictly-preordered-sets.html#1618" class="Bound">P</a> <a id="1620" href="order-theory.strictly-preordered-sets.html#1620" class="Bound">is-set-P</a> <a id="1629" class="Symbol">=</a>
  <a id="1633" class="Symbol">(</a> <a id="1635" class="Symbol">(</a> <a id="1637" href="order-theory.strict-preorders.html#1388" class="Function">type-Strict-Preorder</a> <a id="1658" href="order-theory.strictly-preordered-sets.html#1618" class="Bound">P</a> <a id="1660" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1662" href="order-theory.strictly-preordered-sets.html#1620" class="Bound">is-set-P</a><a id="1670" class="Symbol">)</a> <a id="1672" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1674" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1678" href="order-theory.strictly-preordered-sets.html#1618" class="Bound">P</a><a id="1679" class="Symbol">)</a>

<a id="1682" class="Keyword">module</a> <a id="1689" href="order-theory.strictly-preordered-sets.html#1689" class="Module">_</a>
  <a id="1693" class="Symbol">{</a><a id="1694" href="order-theory.strictly-preordered-sets.html#1694" class="Bound">l1</a> <a id="1697" href="order-theory.strictly-preordered-sets.html#1697" class="Bound">l2</a> <a id="1700" class="Symbol">:</a> <a id="1702" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1707" class="Symbol">}</a> <a id="1709" class="Symbol">(</a><a id="1710" href="order-theory.strictly-preordered-sets.html#1710" class="Bound">A</a> <a id="1712" class="Symbol">:</a> <a id="1714" href="order-theory.strictly-preordered-sets.html#1192" class="Function">Strictly-Preordered-Set</a> <a id="1738" href="order-theory.strictly-preordered-sets.html#1694" class="Bound">l1</a> <a id="1741" href="order-theory.strictly-preordered-sets.html#1697" class="Bound">l2</a><a id="1743" class="Symbol">)</a>
  <a id="1747" class="Keyword">where</a>

  <a id="1756" href="order-theory.strictly-preordered-sets.html#1756" class="Function">set-Strictly-Preordered-Set</a> <a id="1784" class="Symbol">:</a>
    <a id="1790" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1794" href="order-theory.strictly-preordered-sets.html#1694" class="Bound">l1</a>
  <a id="1799" href="order-theory.strictly-preordered-sets.html#1756" class="Function">set-Strictly-Preordered-Set</a> <a id="1827" class="Symbol">=</a>
    <a id="1833" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1837" href="order-theory.strictly-preordered-sets.html#1710" class="Bound">A</a>

  <a id="1842" href="order-theory.strictly-preordered-sets.html#1842" class="Function">type-Strictly-Preordered-Set</a> <a id="1871" class="Symbol">:</a>
    <a id="1877" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1880" href="order-theory.strictly-preordered-sets.html#1694" class="Bound">l1</a>
  <a id="1885" href="order-theory.strictly-preordered-sets.html#1842" class="Function">type-Strictly-Preordered-Set</a> <a id="1914" class="Symbol">=</a>
    <a id="1920" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1929" href="order-theory.strictly-preordered-sets.html#1756" class="Function">set-Strictly-Preordered-Set</a>

  <a id="1960" href="order-theory.strictly-preordered-sets.html#1960" class="Function">is-set-type-Strictly-Preordered-Set</a> <a id="1996" class="Symbol">:</a>
    <a id="2002" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="2009" href="order-theory.strictly-preordered-sets.html#1842" class="Function">type-Strictly-Preordered-Set</a>
  <a id="2040" href="order-theory.strictly-preordered-sets.html#1960" class="Function">is-set-type-Strictly-Preordered-Set</a> <a id="2076" class="Symbol">=</a>
    <a id="2082" href="foundation-core.sets.html#1076" class="Function">is-set-type-Set</a> <a id="2098" href="order-theory.strictly-preordered-sets.html#1756" class="Function">set-Strictly-Preordered-Set</a>

  <a id="2129" href="order-theory.strictly-preordered-sets.html#2129" class="Function">le-prop-Strictly-Preordered-Set</a> <a id="2161" class="Symbol">:</a>
    <a id="2167" href="foundation.binary-relations.html#1511" class="Function">Relation-Prop</a> <a id="2181" href="order-theory.strictly-preordered-sets.html#1697" class="Bound">l2</a> <a id="2184" href="order-theory.strictly-preordered-sets.html#1842" class="Function">type-Strictly-Preordered-Set</a>
  <a id="2215" href="order-theory.strictly-preordered-sets.html#2129" class="Function">le-prop-Strictly-Preordered-Set</a> <a id="2247" class="Symbol">=</a>
    <a id="2253" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2257" class="Symbol">(</a><a id="2258" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2262" href="order-theory.strictly-preordered-sets.html#1710" class="Bound">A</a><a id="2263" class="Symbol">)</a>

  <a id="2268" href="order-theory.strictly-preordered-sets.html#2268" class="Function">le-Strictly-Preordered-Set</a> <a id="2295" class="Symbol">:</a>
    <a id="2301" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="2310" href="order-theory.strictly-preordered-sets.html#1697" class="Bound">l2</a> <a id="2313" href="order-theory.strictly-preordered-sets.html#1842" class="Function">type-Strictly-Preordered-Set</a>
  <a id="2344" href="order-theory.strictly-preordered-sets.html#2268" class="Function">le-Strictly-Preordered-Set</a> <a id="2371" class="Symbol">=</a>
    <a id="2377" href="foundation.binary-relations.html#1621" class="Function">type-Relation-Prop</a> <a id="2396" href="order-theory.strictly-preordered-sets.html#2129" class="Function">le-prop-Strictly-Preordered-Set</a>

  <a id="2431" href="order-theory.strictly-preordered-sets.html#2431" class="Function">is-prop-le-Strictly-Preordered-Set</a> <a id="2466" class="Symbol">:</a>
    <a id="2472" class="Symbol">(</a><a id="2473" href="order-theory.strictly-preordered-sets.html#2473" class="Bound">x</a> <a id="2475" href="order-theory.strictly-preordered-sets.html#2475" class="Bound">y</a> <a id="2477" class="Symbol">:</a> <a id="2479" href="order-theory.strictly-preordered-sets.html#1842" class="Function">type-Strictly-Preordered-Set</a><a id="2507" class="Symbol">)</a> <a id="2509" class="Symbol">→</a>
    <a id="2515" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2523" class="Symbol">(</a><a id="2524" href="order-theory.strictly-preordered-sets.html#2268" class="Function">le-Strictly-Preordered-Set</a> <a id="2551" href="order-theory.strictly-preordered-sets.html#2473" class="Bound">x</a> <a id="2553" href="order-theory.strictly-preordered-sets.html#2475" class="Bound">y</a><a id="2554" class="Symbol">)</a>
  <a id="2558" href="order-theory.strictly-preordered-sets.html#2431" class="Function">is-prop-le-Strictly-Preordered-Set</a> <a id="2593" class="Symbol">=</a>
    <a id="2599" href="foundation.binary-relations.html#1749" class="Function">is-prop-type-Relation-Prop</a> <a id="2626" href="order-theory.strictly-preordered-sets.html#2129" class="Function">le-prop-Strictly-Preordered-Set</a>

  <a id="2661" href="order-theory.strictly-preordered-sets.html#2661" class="Function">is-irreflexive-le-Strictly-Preordered-Set</a> <a id="2703" class="Symbol">:</a>
    <a id="2709" href="foundation.binary-relations.html#5565" class="Function">is-irreflexive</a> <a id="2724" href="order-theory.strictly-preordered-sets.html#2268" class="Function">le-Strictly-Preordered-Set</a>
  <a id="2753" href="order-theory.strictly-preordered-sets.html#2661" class="Function">is-irreflexive-le-Strictly-Preordered-Set</a> <a id="2795" class="Symbol">=</a>
    <a id="2801" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2805" class="Symbol">(</a><a id="2806" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2810" class="Symbol">(</a><a id="2811" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2815" href="order-theory.strictly-preordered-sets.html#1710" class="Bound">A</a><a id="2816" class="Symbol">))</a>

  <a id="2822" href="order-theory.strictly-preordered-sets.html#2822" class="Function">is-transitive-le-Strictly-Preordered-Set</a> <a id="2863" class="Symbol">:</a>
    <a id="2869" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="2883" href="order-theory.strictly-preordered-sets.html#2268" class="Function">le-Strictly-Preordered-Set</a>
  <a id="2912" href="order-theory.strictly-preordered-sets.html#2822" class="Function">is-transitive-le-Strictly-Preordered-Set</a> <a id="2953" class="Symbol">=</a>
    <a id="2959" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2963" class="Symbol">(</a><a id="2964" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2968" class="Symbol">(</a><a id="2969" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2973" href="order-theory.strictly-preordered-sets.html#1710" class="Bound">A</a><a id="2974" class="Symbol">))</a>

  <a id="2980" href="order-theory.strictly-preordered-sets.html#2980" class="Function">strict-preorder-Strictly-Preordered-Set</a> <a id="3020" class="Symbol">:</a>
    <a id="3026" href="order-theory.strict-preorders.html#1102" class="Function">Strict-Preorder</a> <a id="3042" href="order-theory.strictly-preordered-sets.html#1694" class="Bound">l1</a> <a id="3045" href="order-theory.strictly-preordered-sets.html#1697" class="Bound">l2</a>
  <a id="3050" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3054" href="order-theory.strictly-preordered-sets.html#2980" class="Function">strict-preorder-Strictly-Preordered-Set</a> <a id="3094" class="Symbol">=</a>
    <a id="3100" href="order-theory.strictly-preordered-sets.html#1842" class="Function">type-Strictly-Preordered-Set</a>
  <a id="3131" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3135" class="Symbol">(</a><a id="3136" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3140" href="order-theory.strictly-preordered-sets.html#2980" class="Function">strict-preorder-Strictly-Preordered-Set</a><a id="3179" class="Symbol">)</a> <a id="3181" class="Symbol">=</a>
    <a id="3187" href="order-theory.strictly-preordered-sets.html#2129" class="Function">le-prop-Strictly-Preordered-Set</a>
  <a id="3221" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3225" class="Symbol">(</a><a id="3226" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3230" class="Symbol">(</a><a id="3231" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3235" href="order-theory.strictly-preordered-sets.html#2980" class="Function">strict-preorder-Strictly-Preordered-Set</a><a id="3274" class="Symbol">))</a> <a id="3277" class="Symbol">=</a>
    <a id="3283" href="order-theory.strictly-preordered-sets.html#2661" class="Function">is-irreflexive-le-Strictly-Preordered-Set</a>
  <a id="3327" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3331" class="Symbol">(</a><a id="3332" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3336" class="Symbol">(</a><a id="3337" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3341" href="order-theory.strictly-preordered-sets.html#2980" class="Function">strict-preorder-Strictly-Preordered-Set</a><a id="3380" class="Symbol">))</a> <a id="3383" class="Symbol">=</a>
    <a id="3389" href="order-theory.strictly-preordered-sets.html#2822" class="Function">is-transitive-le-Strictly-Preordered-Set</a>
</pre>
## Properties

### The ordering of a strictly preordered set is antisymmetric

<pre class="Agda"><a id="3522" class="Keyword">module</a> <a id="3529" href="order-theory.strictly-preordered-sets.html#3529" class="Module">_</a>
  <a id="3533" class="Symbol">{</a><a id="3534" href="order-theory.strictly-preordered-sets.html#3534" class="Bound">l1</a> <a id="3537" href="order-theory.strictly-preordered-sets.html#3537" class="Bound">l2</a> <a id="3540" class="Symbol">:</a> <a id="3542" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3547" class="Symbol">}</a> <a id="3549" class="Symbol">(</a><a id="3550" href="order-theory.strictly-preordered-sets.html#3550" class="Bound">A</a> <a id="3552" class="Symbol">:</a> <a id="3554" href="order-theory.strictly-preordered-sets.html#1192" class="Function">Strictly-Preordered-Set</a> <a id="3578" href="order-theory.strictly-preordered-sets.html#3534" class="Bound">l1</a> <a id="3581" href="order-theory.strictly-preordered-sets.html#3537" class="Bound">l2</a><a id="3583" class="Symbol">)</a>
  <a id="3587" class="Keyword">where</a>

  <a id="3596" href="order-theory.strictly-preordered-sets.html#3596" class="Function">is-antisymmetric-le-Strictly-Preordered-Set</a> <a id="3640" class="Symbol">:</a>
    <a id="3646" href="foundation.binary-relations.html#6436" class="Function">is-antisymmetric</a> <a id="3663" class="Symbol">(</a><a id="3664" href="order-theory.strictly-preordered-sets.html#2268" class="Function">le-Strictly-Preordered-Set</a> <a id="3691" href="order-theory.strictly-preordered-sets.html#3550" class="Bound">A</a><a id="3692" class="Symbol">)</a>
  <a id="3696" href="order-theory.strictly-preordered-sets.html#3596" class="Function">is-antisymmetric-le-Strictly-Preordered-Set</a> <a id="3740" class="Symbol">=</a>
    <a id="3746" href="order-theory.strict-preorders.html#2313" class="Function">is-antisymmetric-le-Strict-Preorder</a>
      <a id="3788" class="Symbol">(</a> <a id="3790" href="order-theory.strictly-preordered-sets.html#2980" class="Function">strict-preorder-Strictly-Preordered-Set</a> <a id="3830" href="order-theory.strictly-preordered-sets.html#3550" class="Bound">A</a><a id="3831" class="Symbol">)</a>
</pre>
## See also

- [Strict orders](order-theory.strict-orders.md) are strictly preordered sets
  that are _extensional_ with respect to the structure of the underlying strict
  preorder.
