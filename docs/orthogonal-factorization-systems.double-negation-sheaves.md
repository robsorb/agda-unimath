# Double negation sheaves

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="orthogonal-factorization-systems.double-negation-sheaves.html" class="Module">orthogonal-factorization-systems.double-negation-sheaves</a> <a id="100" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="foundation.double-negation-stable-propositions.html" class="Module">foundation.double-negation-stable-propositions</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation.irrefutable-propositions.html" class="Module">foundation.irrefutable-propositions</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="460" class="Keyword">open</a> <a id="465" class="Keyword">import</a> <a id="472" href="foundation.type-arithmetic-cartesian-product-types.html" class="Module">foundation.type-arithmetic-cartesian-product-types</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="foundation.universal-property-coproduct-types.html" class="Module">foundation.universal-property-coproduct-types</a>
<a id="581" class="Keyword">open</a> <a id="586" class="Keyword">import</a> <a id="593" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="621" class="Keyword">open</a> <a id="626" class="Keyword">import</a> <a id="633" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="662" class="Keyword">open</a> <a id="667" class="Keyword">import</a> <a id="674" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="705" class="Keyword">open</a> <a id="710" class="Keyword">import</a> <a id="717" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>

<a id="747" class="Keyword">open</a> <a id="752" class="Keyword">import</a> <a id="759" href="orthogonal-factorization-systems.null-types.html" class="Module">orthogonal-factorization-systems.null-types</a>
</pre>
</details>

## Idea

{{#concept "Double negation sheaves" Agda=is-double-negation-sheaf}} are types
that are [null](orthogonal-factorization-systems.null-types.md) at
[irrefutable propositions](foundation.irrefutable-propositions.md), i.e.,
[propositions](foundation-core.propositions.md) `P` for which the
[double negation](foundation.double-negation.md) `¬¬P` is true.

Double negation sheaves were first introduced in the context of Homotopy Type
Theory in Example 3.41 of {{#cite RSS20}}, and are considered in the restricted
context of [sets](foundation-core.sets.md) in {{#cite Swan24}}.

## Definitions

### The property of being a double negation sheaf

<pre class="Agda"><a id="is-double-negation-sheaf"></a><a id="1478" href="orthogonal-factorization-systems.double-negation-sheaves.html#1478" class="Function">is-double-negation-sheaf</a> <a id="1503" class="Symbol">:</a>
  <a id="1507" class="Symbol">(</a><a id="1508" href="orthogonal-factorization-systems.double-negation-sheaves.html#1508" class="Bound">l1</a> <a id="1511" class="Symbol">:</a> <a id="1513" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1518" class="Symbol">)</a> <a id="1520" class="Symbol">{</a><a id="1521" href="orthogonal-factorization-systems.double-negation-sheaves.html#1521" class="Bound">l2</a> <a id="1524" class="Symbol">:</a> <a id="1526" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1531" class="Symbol">}</a> <a id="1533" class="Symbol">(</a><a id="1534" href="orthogonal-factorization-systems.double-negation-sheaves.html#1534" class="Bound">A</a> <a id="1536" class="Symbol">:</a> <a id="1538" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1541" href="orthogonal-factorization-systems.double-negation-sheaves.html#1521" class="Bound">l2</a><a id="1543" class="Symbol">)</a> <a id="1545" class="Symbol">→</a> <a id="1547" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1550" class="Symbol">(</a><a id="1551" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1556" href="orthogonal-factorization-systems.double-negation-sheaves.html#1508" class="Bound">l1</a> <a id="1559" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1561" href="orthogonal-factorization-systems.double-negation-sheaves.html#1521" class="Bound">l2</a><a id="1563" class="Symbol">)</a>
<a id="1565" href="orthogonal-factorization-systems.double-negation-sheaves.html#1478" class="Function">is-double-negation-sheaf</a> <a id="1590" href="orthogonal-factorization-systems.double-negation-sheaves.html#1590" class="Bound">l1</a> <a id="1593" href="orthogonal-factorization-systems.double-negation-sheaves.html#1593" class="Bound">A</a> <a id="1595" class="Symbol">=</a>
  <a id="1599" class="Symbol">(</a><a id="1600" href="orthogonal-factorization-systems.double-negation-sheaves.html#1600" class="Bound">P</a> <a id="1602" class="Symbol">:</a> <a id="1604" href="foundation.irrefutable-propositions.html#2520" class="Function">Irrefutable-Prop</a> <a id="1621" href="orthogonal-factorization-systems.double-negation-sheaves.html#1590" class="Bound">l1</a><a id="1623" class="Symbol">)</a> <a id="1625" class="Symbol">→</a> <a id="1627" href="orthogonal-factorization-systems.null-types.html#2143" class="Function">is-null</a> <a id="1635" class="Symbol">(</a><a id="1636" href="foundation.irrefutable-propositions.html#2891" class="Function">type-Irrefutable-Prop</a> <a id="1658" href="orthogonal-factorization-systems.double-negation-sheaves.html#1600" class="Bound">P</a><a id="1659" class="Symbol">)</a> <a id="1661" href="orthogonal-factorization-systems.double-negation-sheaves.html#1593" class="Bound">A</a>

<a id="is-prop-is-double-negation-sheaf"></a><a id="1664" href="orthogonal-factorization-systems.double-negation-sheaves.html#1664" class="Function">is-prop-is-double-negation-sheaf</a> <a id="1697" class="Symbol">:</a>
  <a id="1701" class="Symbol">{</a><a id="1702" href="orthogonal-factorization-systems.double-negation-sheaves.html#1702" class="Bound">l1</a> <a id="1705" href="orthogonal-factorization-systems.double-negation-sheaves.html#1705" class="Bound">l2</a> <a id="1708" class="Symbol">:</a> <a id="1710" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1715" class="Symbol">}</a> <a id="1717" class="Symbol">{</a><a id="1718" href="orthogonal-factorization-systems.double-negation-sheaves.html#1718" class="Bound">A</a> <a id="1720" class="Symbol">:</a> <a id="1722" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1725" href="orthogonal-factorization-systems.double-negation-sheaves.html#1705" class="Bound">l2</a><a id="1727" class="Symbol">}</a> <a id="1729" class="Symbol">→</a> <a id="1731" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1739" class="Symbol">(</a><a id="1740" href="orthogonal-factorization-systems.double-negation-sheaves.html#1478" class="Function">is-double-negation-sheaf</a> <a id="1765" href="orthogonal-factorization-systems.double-negation-sheaves.html#1702" class="Bound">l1</a> <a id="1768" href="orthogonal-factorization-systems.double-negation-sheaves.html#1718" class="Bound">A</a><a id="1769" class="Symbol">)</a>
<a id="1771" href="orthogonal-factorization-systems.double-negation-sheaves.html#1664" class="Function">is-prop-is-double-negation-sheaf</a> <a id="1804" class="Symbol">{</a><a id="1805" class="Argument">A</a> <a id="1807" class="Symbol">=</a> <a id="1809" href="orthogonal-factorization-systems.double-negation-sheaves.html#1809" class="Bound">A</a><a id="1810" class="Symbol">}</a> <a id="1812" class="Symbol">=</a>
  <a id="1816" href="foundation-core.propositions.html#6443" class="Function">is-prop-Π</a> <a id="1826" class="Symbol">(λ</a> <a id="1829" href="orthogonal-factorization-systems.double-negation-sheaves.html#1829" class="Bound">P</a> <a id="1831" class="Symbol">→</a> <a id="1833" href="orthogonal-factorization-systems.null-types.html#2217" class="Function">is-prop-is-null</a> <a id="1849" class="Symbol">(</a><a id="1850" href="foundation.irrefutable-propositions.html#2891" class="Function">type-Irrefutable-Prop</a> <a id="1872" href="orthogonal-factorization-systems.double-negation-sheaves.html#1829" class="Bound">P</a><a id="1873" class="Symbol">)</a> <a id="1875" href="orthogonal-factorization-systems.double-negation-sheaves.html#1809" class="Bound">A</a><a id="1876" class="Symbol">)</a>
</pre>
## Properties

### The empty type is a double negation sheaf

<pre class="Agda"><a id="is-double-negation-sheaf-empty"></a><a id="1953" href="orthogonal-factorization-systems.double-negation-sheaves.html#1953" class="Function">is-double-negation-sheaf-empty</a> <a id="1984" class="Symbol">:</a>
  <a id="1988" class="Symbol">{</a><a id="1989" href="orthogonal-factorization-systems.double-negation-sheaves.html#1989" class="Bound">l</a> <a id="1991" class="Symbol">:</a> <a id="1993" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1998" class="Symbol">}</a> <a id="2000" class="Symbol">→</a> <a id="2002" href="orthogonal-factorization-systems.double-negation-sheaves.html#1478" class="Function">is-double-negation-sheaf</a> <a id="2027" href="orthogonal-factorization-systems.double-negation-sheaves.html#1989" class="Bound">l</a> <a id="2029" href="foundation-core.empty-types.html#801" class="Datatype">empty</a>
<a id="2035" href="orthogonal-factorization-systems.double-negation-sheaves.html#1953" class="Function">is-double-negation-sheaf-empty</a> <a id="2066" href="orthogonal-factorization-systems.double-negation-sheaves.html#2066" class="Bound">P</a> <a id="2068" class="Symbol">=</a>
  <a id="2072" href="foundation.logical-equivalences.html#4962" class="Function">is-equiv-has-converse</a> <a id="2094" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a>
    <a id="2109" class="Symbol">(</a> <a id="2111" href="foundation-core.propositions.html#8765" class="Function">hom-Prop</a> <a id="2120" class="Symbol">(</a><a id="2121" href="foundation.irrefutable-propositions.html#3278" class="Function">prop-Irrefutable-Prop</a> <a id="2143" href="orthogonal-factorization-systems.double-negation-sheaves.html#2066" class="Bound">P</a><a id="2144" class="Symbol">)</a> <a id="2146" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a><a id="2156" class="Symbol">)</a>
    <a id="2162" class="Symbol">(</a> <a id="2164" href="foundation.irrefutable-propositions.html#3392" class="Function">is-irrefutable-Irrefutable-Prop</a> <a id="2196" href="orthogonal-factorization-systems.double-negation-sheaves.html#2066" class="Bound">P</a><a id="2197" class="Symbol">)</a>
</pre>
### Contractible types are double negation sheaves

<pre class="Agda"><a id="is-double-negation-sheaf-is-contr"></a><a id="2264" href="orthogonal-factorization-systems.double-negation-sheaves.html#2264" class="Function">is-double-negation-sheaf-is-contr</a> <a id="2298" class="Symbol">:</a>
  <a id="2302" class="Symbol">{</a><a id="2303" href="orthogonal-factorization-systems.double-negation-sheaves.html#2303" class="Bound">l1</a> <a id="2306" href="orthogonal-factorization-systems.double-negation-sheaves.html#2306" class="Bound">l2</a> <a id="2309" class="Symbol">:</a> <a id="2311" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2316" class="Symbol">}</a> <a id="2318" class="Symbol">{</a><a id="2319" href="orthogonal-factorization-systems.double-negation-sheaves.html#2319" class="Bound">A</a> <a id="2321" class="Symbol">:</a> <a id="2323" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2326" href="orthogonal-factorization-systems.double-negation-sheaves.html#2303" class="Bound">l1</a><a id="2328" class="Symbol">}</a> <a id="2330" class="Symbol">→</a> <a id="2332" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2341" href="orthogonal-factorization-systems.double-negation-sheaves.html#2319" class="Bound">A</a> <a id="2343" class="Symbol">→</a> <a id="2345" href="orthogonal-factorization-systems.double-negation-sheaves.html#1478" class="Function">is-double-negation-sheaf</a> <a id="2370" href="orthogonal-factorization-systems.double-negation-sheaves.html#2306" class="Bound">l2</a> <a id="2373" href="orthogonal-factorization-systems.double-negation-sheaves.html#2319" class="Bound">A</a>
<a id="2375" href="orthogonal-factorization-systems.double-negation-sheaves.html#2264" class="Function">is-double-negation-sheaf-is-contr</a> <a id="2409" href="orthogonal-factorization-systems.double-negation-sheaves.html#2409" class="Bound">is-contr-A</a> <a id="2420" href="orthogonal-factorization-systems.double-negation-sheaves.html#2420" class="Bound">P</a> <a id="2422" class="Symbol">=</a>
  <a id="2426" href="orthogonal-factorization-systems.null-types.html#7342" class="Function">is-null-is-contr</a> <a id="2443" class="Symbol">(</a><a id="2444" href="foundation.irrefutable-propositions.html#2891" class="Function">type-Irrefutable-Prop</a> <a id="2466" href="orthogonal-factorization-systems.double-negation-sheaves.html#2420" class="Bound">P</a><a id="2467" class="Symbol">)</a> <a id="2469" href="orthogonal-factorization-systems.double-negation-sheaves.html#2409" class="Bound">is-contr-A</a>
</pre>
### Propositions that are double negation sheaves are double negation stable

<pre class="Agda"><a id="2571" class="Keyword">module</a> <a id="2578" href="orthogonal-factorization-systems.double-negation-sheaves.html#2578" class="Module">_</a>
  <a id="2582" class="Symbol">{</a><a id="2583" href="orthogonal-factorization-systems.double-negation-sheaves.html#2583" class="Bound">l</a> <a id="2585" class="Symbol">:</a> <a id="2587" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2592" class="Symbol">}</a> <a id="2594" class="Symbol">{</a><a id="2595" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a> <a id="2597" class="Symbol">:</a> <a id="2599" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2602" href="orthogonal-factorization-systems.double-negation-sheaves.html#2583" class="Bound">l</a><a id="2603" class="Symbol">}</a>
  <a id="2607" class="Symbol">(</a><a id="2608" href="orthogonal-factorization-systems.double-negation-sheaves.html#2608" class="Bound">is-prop-A</a> <a id="2618" class="Symbol">:</a> <a id="2620" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2628" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a><a id="2629" class="Symbol">)</a>
  <a id="2633" class="Symbol">(</a><a id="2634" href="orthogonal-factorization-systems.double-negation-sheaves.html#2634" class="Bound">is-¬¬sheaf-A</a> <a id="2647" class="Symbol">:</a> <a id="2649" href="orthogonal-factorization-systems.double-negation-sheaves.html#1478" class="Function">is-double-negation-sheaf</a> <a id="2674" href="orthogonal-factorization-systems.double-negation-sheaves.html#2583" class="Bound">l</a> <a id="2676" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a><a id="2677" class="Symbol">)</a>
  <a id="2681" class="Keyword">where</a>

  <a id="2690" href="orthogonal-factorization-systems.double-negation-sheaves.html#2690" class="Function">compute-is-double-negation-sheaf-is-prop</a> <a id="2731" class="Symbol">:</a> <a id="2733" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a> <a id="2735" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="2737" class="Symbol">(</a><a id="2738" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2740" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a> <a id="2742" class="Symbol">→</a> <a id="2744" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a><a id="2745" class="Symbol">)</a>
  <a id="2749" href="orthogonal-factorization-systems.double-negation-sheaves.html#2690" class="Function">compute-is-double-negation-sheaf-is-prop</a> <a id="2790" class="Symbol">=</a>
    <a id="2796" class="Symbol">(</a> <a id="2798" href="foundation.type-arithmetic-cartesian-product-types.html#3602" class="Function">left-unit-law-product-is-contr</a>
      <a id="2835" class="Symbol">(</a> <a id="2837" href="foundation-core.propositions.html#2852" class="Function">is-proof-irrelevant-is-prop</a> <a id="2865" class="Symbol">(</a><a id="2866" href="foundation-core.propositions.html#7883" class="Function">is-prop-function-type</a> <a id="2888" href="orthogonal-factorization-systems.double-negation-sheaves.html#2608" class="Bound">is-prop-A</a><a id="2897" class="Symbol">)</a> <a id="2899" href="foundation-core.function-types.html#307" class="Function">id</a><a id="2901" class="Symbol">))</a> <a id="2904" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
    <a id="2911" class="Symbol">(</a> <a id="2913" href="foundation.universal-property-coproduct-types.html#2015" class="Function">equiv-universal-property-coproduct</a> <a id="2948" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a><a id="2949" class="Symbol">)</a> <a id="2951" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
    <a id="2958" class="Symbol">(</a> <a id="2960" class="Symbol">_</a> <a id="2962" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2964" href="orthogonal-factorization-systems.double-negation-sheaves.html#2634" class="Bound">is-¬¬sheaf-A</a> <a id="2977" class="Symbol">(</a><a id="2978" href="foundation.irrefutable-propositions.html#4086" class="Function">is-decidable-prop-Irrefutable-Prop</a> <a id="3013" class="Symbol">(</a><a id="3014" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a> <a id="3016" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3018" href="orthogonal-factorization-systems.double-negation-sheaves.html#2608" class="Bound">is-prop-A</a><a id="3027" class="Symbol">)))</a>

  <a id="3034" href="orthogonal-factorization-systems.double-negation-sheaves.html#3034" class="Function">is-double-negation-stable-is-double-negation-sheaf-is-prop</a> <a id="3093" class="Symbol">:</a>
    <a id="3099" href="foundation.double-negation-stable-propositions.html#1559" class="Function">is-double-negation-stable</a> <a id="3125" class="Symbol">(</a><a id="3126" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a> <a id="3128" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3130" href="orthogonal-factorization-systems.double-negation-sheaves.html#2608" class="Bound">is-prop-A</a><a id="3139" class="Symbol">)</a>
  <a id="3143" href="orthogonal-factorization-systems.double-negation-sheaves.html#3034" class="Function">is-double-negation-stable-is-double-negation-sheaf-is-prop</a> <a id="3202" href="orthogonal-factorization-systems.double-negation-sheaves.html#3202" class="Bound">¬¬a</a> <a id="3206" class="Symbol">=</a>
    <a id="3212" href="foundation-core.equivalences.html#6985" class="Function">map-inv-is-equiv</a> <a id="3229" class="Symbol">(</a><a id="3230" href="orthogonal-factorization-systems.double-negation-sheaves.html#2634" class="Bound">is-¬¬sheaf-A</a> <a id="3243" class="Symbol">(</a><a id="3244" href="orthogonal-factorization-systems.double-negation-sheaves.html#2595" class="Bound">A</a> <a id="3246" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3248" href="orthogonal-factorization-systems.double-negation-sheaves.html#2608" class="Bound">is-prop-A</a> <a id="3258" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3260" href="orthogonal-factorization-systems.double-negation-sheaves.html#3202" class="Bound">¬¬a</a><a id="3263" class="Symbol">))</a> <a id="3266" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>
### Double negation stable propositions are double negation sheaves

This follows from the fact that a proposition `P` is double negation stable if
and only if it is local at all double negations

```text
  (¬¬A → P) → (A → P),
```

and nullification at irrefutable propositions is a restriction of this.

> This remains to be formalized.

### The negation of a type is a double negation sheaf

This is a corollary of the previous result.

> This remains to be formalized.

## References

{{#bibliography}}
