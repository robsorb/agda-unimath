# The locale of propositions

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="foundation.locale-of-propositions.html" class="Module">foundation.locale-of-propositions</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.large-locale-of-propositions.html" class="Module">foundation.large-locale-of-propositions</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="434" class="Keyword">open</a> <a id="439" class="Keyword">import</a> <a id="446" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>

<a id="478" class="Keyword">open</a> <a id="483" class="Keyword">import</a> <a id="490" href="order-theory.frames.html" class="Module">order-theory.frames</a>
<a id="510" class="Keyword">open</a> <a id="515" class="Keyword">import</a> <a id="522" href="order-theory.greatest-lower-bounds-posets.html" class="Module">order-theory.greatest-lower-bounds-posets</a>
<a id="564" class="Keyword">open</a> <a id="569" class="Keyword">import</a> <a id="576" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>
<a id="602" class="Keyword">open</a> <a id="607" class="Keyword">import</a> <a id="614" href="order-theory.large-preorders.html" class="Module">order-theory.large-preorders</a>
<a id="643" class="Keyword">open</a> <a id="648" class="Keyword">import</a> <a id="655" href="order-theory.meet-semilattices.html" class="Module">order-theory.meet-semilattices</a>
<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="order-theory.meet-suplattices.html" class="Module">order-theory.meet-suplattices</a>
<a id="728" class="Keyword">open</a> <a id="733" class="Keyword">import</a> <a id="740" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="760" class="Keyword">open</a> <a id="765" class="Keyword">import</a> <a id="772" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
<a id="795" class="Keyword">open</a> <a id="800" class="Keyword">import</a> <a id="807" href="order-theory.suplattices.html" class="Module">order-theory.suplattices</a>
<a id="832" class="Keyword">open</a> <a id="837" class="Keyword">import</a> <a id="844" href="order-theory.top-elements-posets.html" class="Module">order-theory.top-elements-posets</a>
</pre>
</details>

## Idea

The [locale](order-theory.locales.md) of
[propositions](foundation-core.propositions.md) consists of all the propositions
of any [universe level](foundation.universe-levels.md) and is ordered by the
implications between them. [Conjunction](foundation.conjunction.md) gives this
[poset](order-theory.posets.md) the structure of a
[meet-semilattice](order-theory.meet-semilattices.md), and
[existential quantification](foundation.existential-quantification.md) gives it
the structure of a [suplattice](order-theory.suplattices.md).

## Definitions

### The preorder of propositions

<pre class="Agda"><a id="Prop-Preorder"></a><a id="1492" href="foundation.locale-of-propositions.html#1492" class="Function">Prop-Preorder</a> <a id="1506" class="Symbol">:</a> <a id="1508" class="Symbol">(</a><a id="1509" href="foundation.locale-of-propositions.html#1509" class="Bound">l</a> <a id="1511" class="Symbol">:</a> <a id="1513" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1518" class="Symbol">)</a> <a id="1520" class="Symbol">→</a> <a id="1522" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="1531" class="Symbol">(</a><a id="1532" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1537" href="foundation.locale-of-propositions.html#1509" class="Bound">l</a><a id="1538" class="Symbol">)</a> <a id="1540" href="foundation.locale-of-propositions.html#1509" class="Bound">l</a>
<a id="1542" href="foundation.locale-of-propositions.html#1492" class="Function">Prop-Preorder</a> <a id="1556" class="Symbol">=</a> <a id="1558" href="order-theory.large-preorders.html#3384" class="Function">preorder-Large-Preorder</a> <a id="1582" href="foundation.large-locale-of-propositions.html#1811" class="Function">Prop-Large-Preorder</a>
</pre>
### The poset of propositions

<pre class="Agda"><a id="Prop-Poset"></a><a id="1646" href="foundation.locale-of-propositions.html#1646" class="Function">Prop-Poset</a> <a id="1657" class="Symbol">:</a> <a id="1659" class="Symbol">(</a><a id="1660" href="foundation.locale-of-propositions.html#1660" class="Bound">l</a> <a id="1662" class="Symbol">:</a> <a id="1664" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1669" class="Symbol">)</a> <a id="1671" class="Symbol">→</a> <a id="1673" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1679" class="Symbol">(</a><a id="1680" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1685" href="foundation.locale-of-propositions.html#1660" class="Bound">l</a><a id="1686" class="Symbol">)</a> <a id="1688" href="foundation.locale-of-propositions.html#1660" class="Bound">l</a>
<a id="1690" href="foundation.locale-of-propositions.html#1646" class="Function">Prop-Poset</a> <a id="1701" class="Symbol">=</a> <a id="1703" href="order-theory.large-posets.html#4790" class="Function">poset-Large-Poset</a> <a id="1721" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a>
</pre>
### The largest element in the poset of propositions

<pre class="Agda"><a id="has-top-element-Prop-Locale"></a><a id="1805" href="foundation.locale-of-propositions.html#1805" class="Function">has-top-element-Prop-Locale</a> <a id="1833" class="Symbol">:</a>
  <a id="1837" class="Symbol">{</a><a id="1838" href="foundation.locale-of-propositions.html#1838" class="Bound">l</a> <a id="1840" class="Symbol">:</a> <a id="1842" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1847" class="Symbol">}</a> <a id="1849" class="Symbol">→</a> <a id="1851" href="order-theory.top-elements-posets.html#1147" class="Function">has-top-element-Poset</a> <a id="1873" class="Symbol">(</a><a id="1874" href="foundation.locale-of-propositions.html#1646" class="Function">Prop-Poset</a> <a id="1885" href="foundation.locale-of-propositions.html#1838" class="Bound">l</a><a id="1886" class="Symbol">)</a>
<a id="1888" href="foundation.locale-of-propositions.html#1805" class="Function">has-top-element-Prop-Locale</a> <a id="1916" class="Symbol">{</a><a id="1917" href="foundation.locale-of-propositions.html#1917" class="Bound">l</a><a id="1918" class="Symbol">}</a> <a id="1920" class="Symbol">=</a> <a id="1922" class="Symbol">(</a><a id="1923" href="foundation.unit-type.html#4828" class="Function">raise-unit-Prop</a> <a id="1939" href="foundation.locale-of-propositions.html#1917" class="Bound">l</a> <a id="1941" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1943" class="Symbol">λ</a> <a id="1945" href="foundation.locale-of-propositions.html#1945" class="Bound">_</a> <a id="1947" href="foundation.locale-of-propositions.html#1947" class="Bound">_</a> <a id="1949" class="Symbol">→</a> <a id="1951" href="foundation.unit-type.html#1606" class="Function">raise-star</a><a id="1961" class="Symbol">)</a>
</pre>
### Meets in the poset of propositions

<pre class="Agda"><a id="is-meet-semilattice-Prop-Locale"></a><a id="2016" href="foundation.locale-of-propositions.html#2016" class="Function">is-meet-semilattice-Prop-Locale</a> <a id="2048" class="Symbol">:</a>
  <a id="2052" class="Symbol">{</a><a id="2053" href="foundation.locale-of-propositions.html#2053" class="Bound">l</a> <a id="2055" class="Symbol">:</a> <a id="2057" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2062" class="Symbol">}</a> <a id="2064" class="Symbol">→</a> <a id="2066" href="order-theory.meet-semilattices.html#9833" class="Function">is-meet-semilattice-Poset</a> <a id="2092" class="Symbol">(</a><a id="2093" href="foundation.locale-of-propositions.html#1646" class="Function">Prop-Poset</a> <a id="2104" href="foundation.locale-of-propositions.html#2053" class="Bound">l</a><a id="2105" class="Symbol">)</a>
<a id="2107" href="foundation.locale-of-propositions.html#2016" class="Function">is-meet-semilattice-Prop-Locale</a> <a id="2139" href="foundation.locale-of-propositions.html#2139" class="Bound">P</a> <a id="2141" href="foundation.locale-of-propositions.html#2141" class="Bound">Q</a> <a id="2143" class="Symbol">=</a>
  <a id="2147" class="Symbol">(</a> <a id="2149" href="foundation.locale-of-propositions.html#2139" class="Bound">P</a> <a id="2151" href="foundation.conjunction.html#2377" class="Function Operator">∧</a> <a id="2153" href="foundation.locale-of-propositions.html#2141" class="Bound">Q</a> <a id="2155" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2157" href="foundation.conjunction.html#5895" class="Function">is-greatest-binary-lower-bound-conjunction-Prop</a> <a id="2205" href="foundation.locale-of-propositions.html#2139" class="Bound">P</a> <a id="2207" href="foundation.locale-of-propositions.html#2141" class="Bound">Q</a><a id="2208" class="Symbol">)</a>

<a id="Prop-Order-Theoretic-Meet-Semilattice"></a><a id="2211" href="foundation.locale-of-propositions.html#2211" class="Function">Prop-Order-Theoretic-Meet-Semilattice</a> <a id="2249" class="Symbol">:</a>
  <a id="2253" class="Symbol">(</a><a id="2254" href="foundation.locale-of-propositions.html#2254" class="Bound">l</a> <a id="2256" class="Symbol">:</a> <a id="2258" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2263" class="Symbol">)</a> <a id="2265" class="Symbol">→</a> <a id="2267" href="order-theory.meet-semilattices.html#10664" class="Function">Order-Theoretic-Meet-Semilattice</a> <a id="2300" class="Symbol">(</a><a id="2301" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2306" href="foundation.locale-of-propositions.html#2254" class="Bound">l</a><a id="2307" class="Symbol">)</a> <a id="2309" href="foundation.locale-of-propositions.html#2254" class="Bound">l</a>
<a id="2311" href="foundation.locale-of-propositions.html#2211" class="Function">Prop-Order-Theoretic-Meet-Semilattice</a> <a id="2349" href="foundation.locale-of-propositions.html#2349" class="Bound">l</a> <a id="2351" class="Symbol">=</a>
  <a id="2355" href="foundation.locale-of-propositions.html#1646" class="Function">Prop-Poset</a> <a id="2366" href="foundation.locale-of-propositions.html#2349" class="Bound">l</a> <a id="2368" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2370" href="foundation.locale-of-propositions.html#2016" class="Function">is-meet-semilattice-Prop-Locale</a>

<a id="Prop-Meet-Semilattice"></a><a id="2403" href="foundation.locale-of-propositions.html#2403" class="Function">Prop-Meet-Semilattice</a> <a id="2425" class="Symbol">:</a>
  <a id="2429" class="Symbol">(</a><a id="2430" href="foundation.locale-of-propositions.html#2430" class="Bound">l</a> <a id="2432" class="Symbol">:</a> <a id="2434" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2439" class="Symbol">)</a> <a id="2441" class="Symbol">→</a> <a id="2443" href="order-theory.meet-semilattices.html#2461" class="Function">Meet-Semilattice</a> <a id="2460" class="Symbol">(</a><a id="2461" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2466" href="foundation.locale-of-propositions.html#2430" class="Bound">l</a><a id="2467" class="Symbol">)</a>
<a id="2469" href="foundation.locale-of-propositions.html#2403" class="Function">Prop-Meet-Semilattice</a> <a id="2491" href="foundation.locale-of-propositions.html#2491" class="Bound">l</a> <a id="2493" class="Symbol">=</a>
  <a id="2497" href="order-theory.meet-semilattices.html#23601" class="Function">meet-semilattice-Order-Theoretic-Meet-Semilattice</a>
    <a id="2551" class="Symbol">(</a> <a id="2553" href="foundation.locale-of-propositions.html#2211" class="Function">Prop-Order-Theoretic-Meet-Semilattice</a> <a id="2591" href="foundation.locale-of-propositions.html#2491" class="Bound">l</a><a id="2592" class="Symbol">)</a>
</pre>
### Suprema in the poset of propositions

<pre class="Agda"><a id="is-suplattice-lzero-Prop-Locale"></a><a id="2649" href="foundation.locale-of-propositions.html#2649" class="Function">is-suplattice-lzero-Prop-Locale</a> <a id="2681" class="Symbol">:</a>
  <a id="2685" class="Symbol">{</a><a id="2686" href="foundation.locale-of-propositions.html#2686" class="Bound">l</a> <a id="2688" class="Symbol">:</a> <a id="2690" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2695" class="Symbol">}</a> <a id="2697" class="Symbol">→</a> <a id="2699" href="order-theory.suplattices.html#1290" class="Function">is-suplattice-Poset</a> <a id="2719" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2725" class="Symbol">(</a><a id="2726" href="foundation.locale-of-propositions.html#1646" class="Function">Prop-Poset</a> <a id="2737" href="foundation.locale-of-propositions.html#2686" class="Bound">l</a><a id="2738" class="Symbol">)</a>
<a id="2740" href="foundation.locale-of-propositions.html#2649" class="Function">is-suplattice-lzero-Prop-Locale</a> <a id="2772" href="foundation.locale-of-propositions.html#2772" class="Bound">I</a> <a id="2774" href="foundation.locale-of-propositions.html#2774" class="Bound">P</a> <a id="2776" class="Symbol">=</a> <a id="2778" class="Symbol">(</a><a id="2779" href="foundation.existential-quantification.html#4308" class="Function">∃</a> <a id="2781" href="foundation.locale-of-propositions.html#2772" class="Bound">I</a> <a id="2783" href="foundation.locale-of-propositions.html#2774" class="Bound">P</a> <a id="2785" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2787" href="foundation.logical-equivalences.html#3309" class="Function">inv-iff</a> <a id="2795" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2797" href="foundation.existential-quantification.html#6825" class="Function">up-exists</a><a id="2806" class="Symbol">)</a>

<a id="is-suplattice-Prop-Locale"></a><a id="2809" href="foundation.locale-of-propositions.html#2809" class="Function">is-suplattice-Prop-Locale</a> <a id="2835" class="Symbol">:</a>
  <a id="2839" class="Symbol">{</a><a id="2840" href="foundation.locale-of-propositions.html#2840" class="Bound">l</a> <a id="2842" class="Symbol">:</a> <a id="2844" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2849" class="Symbol">}</a> <a id="2851" class="Symbol">→</a> <a id="2853" href="order-theory.suplattices.html#1290" class="Function">is-suplattice-Poset</a> <a id="2873" href="foundation.locale-of-propositions.html#2840" class="Bound">l</a> <a id="2875" class="Symbol">(</a><a id="2876" href="foundation.locale-of-propositions.html#1646" class="Function">Prop-Poset</a> <a id="2887" href="foundation.locale-of-propositions.html#2840" class="Bound">l</a><a id="2888" class="Symbol">)</a>
<a id="2890" href="foundation.locale-of-propositions.html#2809" class="Function">is-suplattice-Prop-Locale</a> <a id="2916" href="foundation.locale-of-propositions.html#2916" class="Bound">I</a> <a id="2918" href="foundation.locale-of-propositions.html#2918" class="Bound">P</a> <a id="2920" class="Symbol">=</a> <a id="2922" class="Symbol">(</a><a id="2923" href="foundation.existential-quantification.html#4308" class="Function">∃</a> <a id="2925" href="foundation.locale-of-propositions.html#2916" class="Bound">I</a> <a id="2927" href="foundation.locale-of-propositions.html#2918" class="Bound">P</a> <a id="2929" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2931" href="foundation.logical-equivalences.html#3309" class="Function">inv-iff</a> <a id="2939" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2941" href="foundation.existential-quantification.html#6825" class="Function">up-exists</a><a id="2950" class="Symbol">)</a>

<a id="Prop-Suplattice"></a><a id="2953" href="foundation.locale-of-propositions.html#2953" class="Function">Prop-Suplattice</a> <a id="2969" class="Symbol">:</a>
  <a id="2973" class="Symbol">(</a><a id="2974" href="foundation.locale-of-propositions.html#2974" class="Bound">l</a> <a id="2976" class="Symbol">:</a> <a id="2978" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2983" class="Symbol">)</a> <a id="2985" class="Symbol">→</a> <a id="2987" href="order-theory.suplattices.html#2026" class="Function">Suplattice</a> <a id="2998" class="Symbol">(</a><a id="2999" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3004" href="foundation.locale-of-propositions.html#2974" class="Bound">l</a><a id="3005" class="Symbol">)</a> <a id="3007" href="foundation.locale-of-propositions.html#2974" class="Bound">l</a> <a id="3009" href="foundation.locale-of-propositions.html#2974" class="Bound">l</a>
<a id="3011" href="foundation.locale-of-propositions.html#2953" class="Function">Prop-Suplattice</a> <a id="3027" href="foundation.locale-of-propositions.html#3027" class="Bound">l</a> <a id="3029" class="Symbol">=</a> <a id="3031" href="foundation.locale-of-propositions.html#1646" class="Function">Prop-Poset</a> <a id="3042" href="foundation.locale-of-propositions.html#3027" class="Bound">l</a> <a id="3044" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3046" href="foundation.locale-of-propositions.html#2809" class="Function">is-suplattice-Prop-Locale</a>
</pre>
```text
is-meet-suplattice-Prop-Locale :
  {l : Level} → is-meet-suplattice-Meet-Semilattice l (Prop-Meet-Semilattice l)
is-meet-suplattice-Prop-Locale I P = ？

Prop-Meet-Suplattice :
  (l : Level) → Meet-Suplattice (lsuc l) l
Prop-Meet-Suplattice l =
  Prop-Meet-Semilattice l , is-meet-suplattice-Prop-Locale
```

### The frame of propositions

```text
Prop-Frame : (l : Level) → Frame (lsuc l) l
Prop-Frame l = Prop-Meet-Suplattice l , ？
```

### The locale of propositions

```text
Prop-Locale : Locale lsuc (_⊔_) lzero
Prop-Locale = Prop-Frame
```

## See also

- [Propositional resizing](foundation.propositional-resizing.md)
