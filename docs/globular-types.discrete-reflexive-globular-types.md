# Discrete reflexive globular types

<pre class="Agda"><a id="46" class="Symbol">{-#</a> <a id="50" class="Keyword">OPTIONS</a> <a id="58" class="Pragma">--guardedness</a> <a id="72" class="Symbol">#-}</a>

<a id="77" class="Keyword">module</a> <a id="84" href="globular-types.discrete-reflexive-globular-types.html" class="Module">globular-types.discrete-reflexive-globular-types</a> <a id="133" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="274" class="Keyword">open</a> <a id="279" class="Keyword">import</a> <a id="286" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
<a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="globular-types.symmetric-globular-types.html" class="Module">globular-types.symmetric-globular-types</a>
<a id="460" class="Keyword">open</a> <a id="465" class="Keyword">import</a> <a id="472" href="globular-types.transitive-globular-types.html" class="Module">globular-types.transitive-globular-types</a>
</pre>
</details>

## Idea

A [reflexive globular type](globular-types.reflexive-globular-types.md) is said
to be
{{#concept "discrete" Disambiguation="reflexive globular type" Agda=is-discrete-Reflexive-Globular-Type}}
if:

- For every 0-cell `x` the type family `G₁ x` of 1-cells out of `x` is
  [torsorial](foundation-core.torsorial-type-families.md), and
- For every two 0-cells `x` and `y` the reflexive globular type `G' x y` is
  discrete.

The {{#concept "standard discrete globular type"}} at a type `A` is the
[globular type](globular-types.globular-types.md) obtained from the iterated
[identity types](foundation-core.identity-types.md) on `A`. This globular type
is [reflexive](globular-types.reflexive-globular-types.md),
[transitive](globular-types.transitive-globular-types.md), and indeed
[discrete](globular-types.discrete-reflexive-globular-types.md).

## Definitions

### The predicate of being a discrete reflexive globular type

<pre class="Agda"><a id="1470" class="Keyword">record</a>
  <a id="is-discrete-Reflexive-Globular-Type"></a><a id="1479" href="globular-types.discrete-reflexive-globular-types.html#1479" class="Record">is-discrete-Reflexive-Globular-Type</a>
    <a id="1519" class="Symbol">{</a><a id="1520" href="globular-types.discrete-reflexive-globular-types.html#1520" class="Bound">l1</a> <a id="1523" href="globular-types.discrete-reflexive-globular-types.html#1523" class="Bound">l2</a> <a id="1526" class="Symbol">:</a> <a id="1528" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1533" class="Symbol">}</a> <a id="1535" class="Symbol">(</a><a id="1536" href="globular-types.discrete-reflexive-globular-types.html#1536" class="Bound">G</a> <a id="1538" class="Symbol">:</a> <a id="1540" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="1564" href="globular-types.discrete-reflexive-globular-types.html#1520" class="Bound">l1</a> <a id="1567" href="globular-types.discrete-reflexive-globular-types.html#1523" class="Bound">l2</a><a id="1569" class="Symbol">)</a> <a id="1571" class="Symbol">:</a> <a id="1573" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1576" class="Symbol">(</a><a id="1577" href="globular-types.discrete-reflexive-globular-types.html#1520" class="Bound">l1</a> <a id="1580" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1582" href="globular-types.discrete-reflexive-globular-types.html#1523" class="Bound">l2</a><a id="1584" class="Symbol">)</a>
  <a id="1588" class="Keyword">where</a>
  <a id="1596" class="Keyword">coinductive</a>

  <a id="1611" class="Keyword">field</a>
    <a id="is-discrete-Reflexive-Globular-Type.is-torsorial-1-cell-is-discrete-Reflexive-Globular-Type"></a><a id="1621" href="globular-types.discrete-reflexive-globular-types.html#1621" class="Field">is-torsorial-1-cell-is-discrete-Reflexive-Globular-Type</a> <a id="1677" class="Symbol">:</a>
      <a id="1685" class="Symbol">(</a><a id="1686" href="globular-types.discrete-reflexive-globular-types.html#1686" class="Bound">x</a> <a id="1688" class="Symbol">:</a> <a id="1690" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="1721" href="globular-types.discrete-reflexive-globular-types.html#1536" class="Bound">G</a><a id="1722" class="Symbol">)</a> <a id="1724" class="Symbol">→</a>
      <a id="1732" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="1745" class="Symbol">(</a><a id="1746" href="globular-types.reflexive-globular-types.html#4270" class="Function">1-cell-Reflexive-Globular-Type</a> <a id="1777" href="globular-types.discrete-reflexive-globular-types.html#1536" class="Bound">G</a> <a id="1779" href="globular-types.discrete-reflexive-globular-types.html#1686" class="Bound">x</a><a id="1780" class="Symbol">)</a>

  <a id="1785" class="Keyword">field</a>
    <a id="is-discrete-Reflexive-Globular-Type.is-discrete-1-cell-reflexive-globular-type-is-discrete-Reflexive-Globular-Type"></a><a id="1795" href="globular-types.discrete-reflexive-globular-types.html#1795" class="Field">is-discrete-1-cell-reflexive-globular-type-is-discrete-Reflexive-Globular-Type</a> <a id="1874" class="Symbol">:</a>
      <a id="1882" class="Symbol">(</a><a id="1883" href="globular-types.discrete-reflexive-globular-types.html#1883" class="Bound">x</a> <a id="1885" href="globular-types.discrete-reflexive-globular-types.html#1885" class="Bound">y</a> <a id="1887" class="Symbol">:</a> <a id="1889" href="globular-types.reflexive-globular-types.html#4130" class="Function">0-cell-Reflexive-Globular-Type</a> <a id="1920" href="globular-types.discrete-reflexive-globular-types.html#1536" class="Bound">G</a><a id="1921" class="Symbol">)</a> <a id="1923" class="Symbol">→</a>
      <a id="1931" href="globular-types.discrete-reflexive-globular-types.html#1479" class="Record">is-discrete-Reflexive-Globular-Type</a>
        <a id="1975" class="Symbol">(</a> <a id="1977" href="globular-types.reflexive-globular-types.html#6667" class="Function">1-cell-reflexive-globular-type-Reflexive-Globular-Type</a> <a id="2032" href="globular-types.discrete-reflexive-globular-types.html#1536" class="Bound">G</a> <a id="2034" href="globular-types.discrete-reflexive-globular-types.html#1883" class="Bound">x</a> <a id="2036" href="globular-types.discrete-reflexive-globular-types.html#1885" class="Bound">y</a><a id="2037" class="Symbol">)</a>

<a id="2040" class="Keyword">open</a> <a id="2045" href="globular-types.discrete-reflexive-globular-types.html#1479" class="Module">is-discrete-Reflexive-Globular-Type</a> <a id="2081" class="Keyword">public</a>
</pre>
### Discrete reflexive globular types

<pre class="Agda"><a id="2140" class="Keyword">record</a>
  <a id="Discrete-Reflexive-Globular-Type"></a><a id="2149" href="globular-types.discrete-reflexive-globular-types.html#2149" class="Record">Discrete-Reflexive-Globular-Type</a>
    <a id="2186" class="Symbol">(</a><a id="2187" href="globular-types.discrete-reflexive-globular-types.html#2187" class="Bound">l1</a> <a id="2190" href="globular-types.discrete-reflexive-globular-types.html#2190" class="Bound">l2</a> <a id="2193" class="Symbol">:</a> <a id="2195" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2200" class="Symbol">)</a> <a id="2202" class="Symbol">:</a> <a id="2204" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2207" class="Symbol">(</a><a id="2208" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2213" href="globular-types.discrete-reflexive-globular-types.html#2187" class="Bound">l1</a> <a id="2216" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2218" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2223" href="globular-types.discrete-reflexive-globular-types.html#2190" class="Bound">l2</a><a id="2225" class="Symbol">)</a>
  <a id="2229" class="Keyword">where</a>

  <a id="2238" class="Keyword">field</a>
    <a id="Discrete-Reflexive-Globular-Type.reflexive-globular-type-Discrete-Reflexive-Globular-Type"></a><a id="2248" href="globular-types.discrete-reflexive-globular-types.html#2248" class="Field">reflexive-globular-type-Discrete-Reflexive-Globular-Type</a> <a id="2305" class="Symbol">:</a>
      <a id="2313" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2337" href="globular-types.discrete-reflexive-globular-types.html#2187" class="Bound">l1</a> <a id="2340" href="globular-types.discrete-reflexive-globular-types.html#2190" class="Bound">l2</a>

  <a id="2346" class="Keyword">field</a>
    <a id="Discrete-Reflexive-Globular-Type.is-discrete-Discrete-Reflexive-Globular-Type"></a><a id="2356" href="globular-types.discrete-reflexive-globular-types.html#2356" class="Field">is-discrete-Discrete-Reflexive-Globular-Type</a> <a id="2401" class="Symbol">:</a>
      <a id="2409" href="globular-types.discrete-reflexive-globular-types.html#1479" class="Record">is-discrete-Reflexive-Globular-Type</a>
        <a id="2453" href="globular-types.discrete-reflexive-globular-types.html#2248" class="Field">reflexive-globular-type-Discrete-Reflexive-Globular-Type</a>

<a id="2511" class="Keyword">open</a> <a id="2516" href="globular-types.discrete-reflexive-globular-types.html#2149" class="Module">Discrete-Reflexive-Globular-Type</a> <a id="2549" class="Keyword">public</a>
</pre>
### The standard discrete reflexive globular types

<pre class="Agda"><a id="2621" class="Keyword">module</a> <a id="2628" href="globular-types.discrete-reflexive-globular-types.html#2628" class="Module">_</a>
  <a id="2632" class="Symbol">{</a><a id="2633" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a> <a id="2635" class="Symbol">:</a> <a id="2637" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2642" class="Symbol">}</a>
  <a id="2646" class="Keyword">where</a>

  <a id="2655" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="2702" class="Symbol">:</a> <a id="2704" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2707" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a> <a id="2709" class="Symbol">→</a> <a id="2711" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="2725" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a> <a id="2727" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a>
  <a id="2731" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="2752" class="Symbol">(</a><a id="2753" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="2800" href="globular-types.discrete-reflexive-globular-types.html#2800" class="Bound">A</a><a id="2801" class="Symbol">)</a> <a id="2803" class="Symbol">=</a>
    <a id="2809" href="globular-types.discrete-reflexive-globular-types.html#2800" class="Bound">A</a>
  <a id="2813" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a>
    <a id="2852" class="Symbol">(</a> <a id="2854" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="2901" href="globular-types.discrete-reflexive-globular-types.html#2901" class="Bound">A</a><a id="2902" class="Symbol">)</a>
    <a id="2908" class="Symbol">(</a> <a id="2910" href="globular-types.discrete-reflexive-globular-types.html#2910" class="Bound">x</a><a id="2911" class="Symbol">)</a>
    <a id="2917" class="Symbol">(</a> <a id="2919" href="globular-types.discrete-reflexive-globular-types.html#2919" class="Bound">y</a><a id="2920" class="Symbol">)</a> <a id="2922" class="Symbol">=</a>
    <a id="2928" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="2975" class="Symbol">(</a><a id="2976" href="globular-types.discrete-reflexive-globular-types.html#2910" class="Bound">x</a> <a id="2978" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2980" href="globular-types.discrete-reflexive-globular-types.html#2919" class="Bound">y</a><a id="2981" class="Symbol">)</a>

  <a id="2986" href="globular-types.discrete-reflexive-globular-types.html#2986" class="Function">refl-discrete-Reflexive-Globular-Type</a> <a id="3024" class="Symbol">:</a>
    <a id="3030" class="Symbol">{</a><a id="3031" href="globular-types.discrete-reflexive-globular-types.html#3031" class="Bound">A</a> <a id="3033" class="Symbol">:</a> <a id="3035" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3038" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a><a id="3039" class="Symbol">}</a> <a id="3041" class="Symbol">→</a>
    <a id="3047" href="globular-types.reflexive-globular-types.html#744" class="Record">is-reflexive-Globular-Type</a>
      <a id="3080" class="Symbol">(</a> <a id="3082" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="3129" href="globular-types.discrete-reflexive-globular-types.html#3031" class="Bound">A</a><a id="3130" class="Symbol">)</a>
  <a id="3134" href="globular-types.reflexive-globular-types.html#867" class="Field">is-reflexive-1-cell-is-reflexive-Globular-Type</a>
    <a id="3185" href="globular-types.discrete-reflexive-globular-types.html#2986" class="Function">refl-discrete-Reflexive-Globular-Type</a>
    <a id="3227" href="globular-types.discrete-reflexive-globular-types.html#3227" class="Bound">x</a> <a id="3229" class="Symbol">=</a>
    <a id="3235" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
  <a id="3242" href="globular-types.reflexive-globular-types.html#973" class="Field">is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type</a>
    <a id="3307" href="globular-types.discrete-reflexive-globular-types.html#2986" class="Function">refl-discrete-Reflexive-Globular-Type</a> <a id="3345" class="Symbol">=</a>
    <a id="3351" href="globular-types.discrete-reflexive-globular-types.html#2986" class="Function">refl-discrete-Reflexive-Globular-Type</a>

  <a id="3392" href="globular-types.discrete-reflexive-globular-types.html#3392" class="Function">discrete-Reflexive-Globular-Type</a> <a id="3425" class="Symbol">:</a>
    <a id="3431" class="Symbol">(</a><a id="3432" href="globular-types.discrete-reflexive-globular-types.html#3432" class="Bound">A</a> <a id="3434" class="Symbol">:</a> <a id="3436" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3439" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a><a id="3440" class="Symbol">)</a> <a id="3442" class="Symbol">→</a> <a id="3444" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="3468" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a> <a id="3470" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a>
  <a id="3474" href="globular-types.reflexive-globular-types.html#4067" class="Field">globular-type-Reflexive-Globular-Type</a> <a id="3512" class="Symbol">(</a><a id="3513" href="globular-types.discrete-reflexive-globular-types.html#3392" class="Function">discrete-Reflexive-Globular-Type</a> <a id="3546" href="globular-types.discrete-reflexive-globular-types.html#3546" class="Bound">A</a><a id="3547" class="Symbol">)</a> <a id="3549" class="Symbol">=</a>
    <a id="3555" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="3602" href="globular-types.discrete-reflexive-globular-types.html#3546" class="Bound">A</a>
  <a id="3606" href="globular-types.reflexive-globular-types.html#5323" class="Field">refl-Reflexive-Globular-Type</a> <a id="3635" class="Symbol">(</a><a id="3636" href="globular-types.discrete-reflexive-globular-types.html#3392" class="Function">discrete-Reflexive-Globular-Type</a> <a id="3669" href="globular-types.discrete-reflexive-globular-types.html#3669" class="Bound">A</a><a id="3670" class="Symbol">)</a> <a id="3672" class="Symbol">=</a>
    <a id="3678" href="globular-types.discrete-reflexive-globular-types.html#2986" class="Function">refl-discrete-Reflexive-Globular-Type</a>

  <a id="3719" href="globular-types.discrete-reflexive-globular-types.html#3719" class="Function">is-discrete-standard-Discrete-Reflexive-Globular-Type</a> <a id="3773" class="Symbol">:</a>
    <a id="3779" class="Symbol">{</a><a id="3780" href="globular-types.discrete-reflexive-globular-types.html#3780" class="Bound">A</a> <a id="3782" class="Symbol">:</a> <a id="3784" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3787" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a><a id="3788" class="Symbol">}</a> <a id="3790" class="Symbol">→</a>
    <a id="3796" href="globular-types.discrete-reflexive-globular-types.html#1479" class="Record">is-discrete-Reflexive-Globular-Type</a> <a id="3832" class="Symbol">(</a><a id="3833" href="globular-types.discrete-reflexive-globular-types.html#3392" class="Function">discrete-Reflexive-Globular-Type</a> <a id="3866" href="globular-types.discrete-reflexive-globular-types.html#3780" class="Bound">A</a><a id="3867" class="Symbol">)</a>
  <a id="3871" href="globular-types.discrete-reflexive-globular-types.html#1621" class="Field">is-torsorial-1-cell-is-discrete-Reflexive-Globular-Type</a>
    <a id="3931" href="globular-types.discrete-reflexive-globular-types.html#3719" class="Function">is-discrete-standard-Discrete-Reflexive-Globular-Type</a>
    <a id="3989" href="globular-types.discrete-reflexive-globular-types.html#3989" class="Bound">x</a> <a id="3991" class="Symbol">=</a>
    <a id="3997" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a> <a id="4013" href="globular-types.discrete-reflexive-globular-types.html#3989" class="Bound">x</a>
  <a id="4017" href="globular-types.discrete-reflexive-globular-types.html#1795" class="Field">is-discrete-1-cell-reflexive-globular-type-is-discrete-Reflexive-Globular-Type</a>
    <a id="4100" href="globular-types.discrete-reflexive-globular-types.html#3719" class="Function">is-discrete-standard-Discrete-Reflexive-Globular-Type</a> <a id="4154" href="globular-types.discrete-reflexive-globular-types.html#4154" class="Bound">x</a> <a id="4156" href="globular-types.discrete-reflexive-globular-types.html#4156" class="Bound">y</a> <a id="4158" class="Symbol">=</a>
    <a id="4164" href="globular-types.discrete-reflexive-globular-types.html#3719" class="Function">is-discrete-standard-Discrete-Reflexive-Globular-Type</a>

  <a id="4221" href="globular-types.discrete-reflexive-globular-types.html#4221" class="Function">standard-Discrete-Reflexive-Globular-Type</a> <a id="4263" class="Symbol">:</a>
    <a id="4269" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4272" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a> <a id="4274" class="Symbol">→</a> <a id="4276" href="globular-types.discrete-reflexive-globular-types.html#2149" class="Record">Discrete-Reflexive-Globular-Type</a> <a id="4309" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a> <a id="4311" href="globular-types.discrete-reflexive-globular-types.html#2633" class="Bound">l</a>
  <a id="4315" href="globular-types.discrete-reflexive-globular-types.html#2248" class="Field">reflexive-globular-type-Discrete-Reflexive-Globular-Type</a>
    <a id="4376" class="Symbol">(</a> <a id="4378" href="globular-types.discrete-reflexive-globular-types.html#4221" class="Function">standard-Discrete-Reflexive-Globular-Type</a> <a id="4420" href="globular-types.discrete-reflexive-globular-types.html#4420" class="Bound">A</a><a id="4421" class="Symbol">)</a> <a id="4423" class="Symbol">=</a>
    <a id="4429" href="globular-types.discrete-reflexive-globular-types.html#3392" class="Function">discrete-Reflexive-Globular-Type</a> <a id="4462" href="globular-types.discrete-reflexive-globular-types.html#4420" class="Bound">A</a>
  <a id="4466" href="globular-types.discrete-reflexive-globular-types.html#2356" class="Field">is-discrete-Discrete-Reflexive-Globular-Type</a>
    <a id="4515" class="Symbol">(</a> <a id="4517" href="globular-types.discrete-reflexive-globular-types.html#4221" class="Function">standard-Discrete-Reflexive-Globular-Type</a> <a id="4559" href="globular-types.discrete-reflexive-globular-types.html#4559" class="Bound">A</a><a id="4560" class="Symbol">)</a> <a id="4562" class="Symbol">=</a>
    <a id="4568" href="globular-types.discrete-reflexive-globular-types.html#3719" class="Function">is-discrete-standard-Discrete-Reflexive-Globular-Type</a>
</pre>
## Properties

### The standard discrete reflexive globular types are transitive

<pre class="Agda"><a id="is-transitive-discrete-Reflexive-Globular-Type"></a><a id="4717" href="globular-types.discrete-reflexive-globular-types.html#4717" class="Function">is-transitive-discrete-Reflexive-Globular-Type</a> <a id="4764" class="Symbol">:</a>
  <a id="4768" class="Symbol">{</a><a id="4769" href="globular-types.discrete-reflexive-globular-types.html#4769" class="Bound">l</a> <a id="4771" class="Symbol">:</a> <a id="4773" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4778" class="Symbol">}</a> <a id="4780" class="Symbol">{</a><a id="4781" href="globular-types.discrete-reflexive-globular-types.html#4781" class="Bound">A</a> <a id="4783" class="Symbol">:</a> <a id="4785" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4788" href="globular-types.discrete-reflexive-globular-types.html#4769" class="Bound">l</a><a id="4789" class="Symbol">}</a> <a id="4791" class="Symbol">→</a>
  <a id="4795" href="globular-types.transitive-globular-types.html#876" class="Record">is-transitive-Globular-Type</a> <a id="4823" class="Symbol">(</a><a id="4824" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="4871" href="globular-types.discrete-reflexive-globular-types.html#4781" class="Bound">A</a><a id="4872" class="Symbol">)</a>
<a id="4874" href="globular-types.transitive-globular-types.html#1000" class="Field">comp-1-cell-is-transitive-Globular-Type</a>
  <a id="4916" href="globular-types.discrete-reflexive-globular-types.html#4717" class="Function">is-transitive-discrete-Reflexive-Globular-Type</a> <a id="4963" href="globular-types.discrete-reflexive-globular-types.html#4963" class="Bound">q</a> <a id="4965" href="globular-types.discrete-reflexive-globular-types.html#4965" class="Bound">p</a> <a id="4967" class="Symbol">=</a>
  <a id="4971" href="globular-types.discrete-reflexive-globular-types.html#4965" class="Bound">p</a> <a id="4973" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a> <a id="4975" href="globular-types.discrete-reflexive-globular-types.html#4963" class="Bound">q</a>
<a id="4977" href="globular-types.transitive-globular-types.html#1101" class="Field">is-transitive-1-cell-globular-type-is-transitive-Globular-Type</a>
  <a id="5042" href="globular-types.discrete-reflexive-globular-types.html#4717" class="Function">is-transitive-discrete-Reflexive-Globular-Type</a> <a id="5089" class="Symbol">=</a>
  <a id="5093" href="globular-types.discrete-reflexive-globular-types.html#4717" class="Function">is-transitive-discrete-Reflexive-Globular-Type</a>

<a id="discrete-Transitive-Globular-Type"></a><a id="5141" href="globular-types.discrete-reflexive-globular-types.html#5141" class="Function">discrete-Transitive-Globular-Type</a> <a id="5175" class="Symbol">:</a>
  <a id="5179" class="Symbol">{</a><a id="5180" href="globular-types.discrete-reflexive-globular-types.html#5180" class="Bound">l</a> <a id="5182" class="Symbol">:</a> <a id="5184" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5189" class="Symbol">}</a> <a id="5191" class="Symbol">(</a><a id="5192" href="globular-types.discrete-reflexive-globular-types.html#5192" class="Bound">A</a> <a id="5194" class="Symbol">:</a> <a id="5196" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5199" href="globular-types.discrete-reflexive-globular-types.html#5180" class="Bound">l</a><a id="5200" class="Symbol">)</a> <a id="5202" class="Symbol">→</a> <a id="5204" href="globular-types.transitive-globular-types.html#3131" class="Record">Transitive-Globular-Type</a> <a id="5229" href="globular-types.discrete-reflexive-globular-types.html#5180" class="Bound">l</a> <a id="5231" href="globular-types.discrete-reflexive-globular-types.html#5180" class="Bound">l</a>
<a id="5233" href="globular-types.transitive-globular-types.html#3344" class="Field">globular-type-Transitive-Globular-Type</a> <a id="5272" class="Symbol">(</a><a id="5273" href="globular-types.discrete-reflexive-globular-types.html#5141" class="Function">discrete-Transitive-Globular-Type</a> <a id="5307" href="globular-types.discrete-reflexive-globular-types.html#5307" class="Bound">A</a><a id="5308" class="Symbol">)</a> <a id="5310" class="Symbol">=</a>
  <a id="5314" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="5361" href="globular-types.discrete-reflexive-globular-types.html#5307" class="Bound">A</a>
<a id="5363" href="globular-types.transitive-globular-types.html#5494" class="Field">is-transitive-Transitive-Globular-Type</a> <a id="5402" class="Symbol">(</a><a id="5403" href="globular-types.discrete-reflexive-globular-types.html#5141" class="Function">discrete-Transitive-Globular-Type</a> <a id="5437" href="globular-types.discrete-reflexive-globular-types.html#5437" class="Bound">A</a><a id="5438" class="Symbol">)</a> <a id="5440" class="Symbol">=</a>
  <a id="5444" href="globular-types.discrete-reflexive-globular-types.html#4717" class="Function">is-transitive-discrete-Reflexive-Globular-Type</a>
</pre>
### The standard discrete reflexive globular types are symmetric

<pre class="Agda"><a id="is-symmetric-discrete-Reflexive-Globular-Type"></a><a id="5570" href="globular-types.discrete-reflexive-globular-types.html#5570" class="Function">is-symmetric-discrete-Reflexive-Globular-Type</a> <a id="5616" class="Symbol">:</a>
  <a id="5620" class="Symbol">{</a><a id="5621" href="globular-types.discrete-reflexive-globular-types.html#5621" class="Bound">l</a> <a id="5623" class="Symbol">:</a> <a id="5625" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5630" class="Symbol">}</a> <a id="5632" class="Symbol">{</a><a id="5633" href="globular-types.discrete-reflexive-globular-types.html#5633" class="Bound">A</a> <a id="5635" class="Symbol">:</a> <a id="5637" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5640" href="globular-types.discrete-reflexive-globular-types.html#5621" class="Bound">l</a><a id="5641" class="Symbol">}</a> <a id="5643" class="Symbol">→</a>
  <a id="5647" href="globular-types.symmetric-globular-types.html#756" class="Record">is-symmetric-Globular-Type</a> <a id="5674" class="Symbol">(</a><a id="5675" href="globular-types.discrete-reflexive-globular-types.html#2655" class="Function">globular-type-discrete-Reflexive-Globular-Type</a> <a id="5722" href="globular-types.discrete-reflexive-globular-types.html#5633" class="Bound">A</a><a id="5723" class="Symbol">)</a>
<a id="5725" href="globular-types.symmetric-globular-types.html#879" class="Field">is-symmetric-1-cell-is-symmetric-Globular-Type</a>
  <a id="5774" href="globular-types.discrete-reflexive-globular-types.html#5570" class="Function">is-symmetric-discrete-Reflexive-Globular-Type</a> <a id="5820" href="globular-types.discrete-reflexive-globular-types.html#5820" class="Bound">a</a> <a id="5822" href="globular-types.discrete-reflexive-globular-types.html#5822" class="Bound">b</a> <a id="5824" class="Symbol">=</a>
  <a id="5828" href="foundation-core.identity-types.html#6358" class="Function">inv</a>
<a id="5832" href="globular-types.symmetric-globular-types.html#985" class="Field">is-symmetric-1-cell-globular-type-is-symmetric-Globular-Type</a>
  <a id="5895" href="globular-types.discrete-reflexive-globular-types.html#5570" class="Function">is-symmetric-discrete-Reflexive-Globular-Type</a> <a id="5941" href="globular-types.discrete-reflexive-globular-types.html#5941" class="Bound">x</a> <a id="5943" href="globular-types.discrete-reflexive-globular-types.html#5943" class="Bound">y</a> <a id="5945" class="Symbol">=</a>
  <a id="5949" href="globular-types.discrete-reflexive-globular-types.html#5570" class="Function">is-symmetric-discrete-Reflexive-Globular-Type</a>
</pre>
## See also

- [Discrete dependent reflexive globular types](globular-types.discrete-dependent-reflexive-globular-types.md)
- [Discrete globular types](globular-types.discrete-globular-types.md)
- [Discrete reflexive graphs](graph-theory.discrete-reflexive-graphs.md)
