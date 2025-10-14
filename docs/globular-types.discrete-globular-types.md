# Discrete globular types

<pre class="Agda"><a id="36" class="Symbol">{-#</a> <a id="40" class="Keyword">OPTIONS</a> <a id="48" class="Pragma">--guardedness</a> <a id="62" class="Symbol">#-}</a>

<a id="67" class="Keyword">module</a> <a id="74" href="globular-types.discrete-globular-types.html" class="Module">globular-types.discrete-globular-types</a> <a id="113" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="213" class="Keyword">open</a> <a id="218" class="Keyword">import</a> <a id="225" href="foundation.discrete-binary-relations.html" class="Module">foundation.discrete-binary-relations</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="298" class="Keyword">open</a> <a id="303" class="Keyword">import</a> <a id="310" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="globular-types.empty-globular-types.html" class="Module">globular-types.empty-globular-types</a>
<a id="386" class="Keyword">open</a> <a id="391" class="Keyword">import</a> <a id="398" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

A [globular type](globular-types.globular-types.md) `G` is said to be
{{#concept "discrete" Disambiguation="globular type" Agda=is-discrete-Globular-Type}}
if it has no 1-cells, i.e., if the type `G₁ x y` of 1-cells from `x` to `y` in
`G` is [empty](foundation.empty-types.md) for any two 0-cells `x y : G₀`. In
other words, a globular type is discrete if its
[binary relation](foundation.binary-relations.md) is
[discrete](foundation.discrete-binary-relations.md).

The forgetful functor from globular types to types given by `G ↦ G₀` has a left
adjoint, mapping a type `A` to the globular type with the type `A` as its
0-cells and no edges. The image of this left adjoint is precisely the type of
discrete globular types.

Note that the globular type obtained from a type and its iterated
[identity types](foundation-core.identity-types.md) is the
[standard discrete reflexive globular type](globular-types.discrete-reflexive-globular-types.md).

## Definitions

### The predicate on globular types of being discrete

<pre class="Agda"><a id="1482" class="Keyword">module</a> <a id="1489" href="globular-types.discrete-globular-types.html#1489" class="Module">_</a>
  <a id="1493" class="Symbol">{</a><a id="1494" href="globular-types.discrete-globular-types.html#1494" class="Bound">l1</a> <a id="1497" href="globular-types.discrete-globular-types.html#1497" class="Bound">l2</a> <a id="1500" class="Symbol">:</a> <a id="1502" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1507" class="Symbol">}</a> <a id="1509" class="Symbol">(</a><a id="1510" href="globular-types.discrete-globular-types.html#1510" class="Bound">G</a> <a id="1512" class="Symbol">:</a> <a id="1514" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1528" href="globular-types.discrete-globular-types.html#1494" class="Bound">l1</a> <a id="1531" href="globular-types.discrete-globular-types.html#1497" class="Bound">l2</a><a id="1533" class="Symbol">)</a>
  <a id="1537" class="Keyword">where</a>

  <a id="1546" href="globular-types.discrete-globular-types.html#1546" class="Function">is-discrete-prop-Globular-Type</a> <a id="1577" class="Symbol">:</a> <a id="1579" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1584" class="Symbol">(</a><a id="1585" href="globular-types.discrete-globular-types.html#1494" class="Bound">l1</a> <a id="1588" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1590" href="globular-types.discrete-globular-types.html#1497" class="Bound">l2</a><a id="1592" class="Symbol">)</a>
  <a id="1596" href="globular-types.discrete-globular-types.html#1546" class="Function">is-discrete-prop-Globular-Type</a> <a id="1627" class="Symbol">=</a>
    <a id="1633" href="foundation.discrete-binary-relations.html#1804" class="Function">is-discrete-prop-Relation</a> <a id="1659" class="Symbol">(</a><a id="1660" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="1681" href="globular-types.discrete-globular-types.html#1510" class="Bound">G</a><a id="1682" class="Symbol">)</a>

  <a id="1687" href="globular-types.discrete-globular-types.html#1687" class="Function">is-discrete-Globular-Type</a> <a id="1713" class="Symbol">:</a> <a id="1715" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1718" class="Symbol">(</a><a id="1719" href="globular-types.discrete-globular-types.html#1494" class="Bound">l1</a> <a id="1722" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1724" href="globular-types.discrete-globular-types.html#1497" class="Bound">l2</a><a id="1726" class="Symbol">)</a>
  <a id="1730" href="globular-types.discrete-globular-types.html#1687" class="Function">is-discrete-Globular-Type</a> <a id="1756" class="Symbol">=</a> <a id="1758" href="foundation.discrete-binary-relations.html#1940" class="Function">is-discrete-Relation</a> <a id="1779" class="Symbol">(</a><a id="1780" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="1801" href="globular-types.discrete-globular-types.html#1510" class="Bound">G</a><a id="1802" class="Symbol">)</a>

  <a id="1807" href="globular-types.discrete-globular-types.html#1807" class="Function">is-prop-is-discrete-Globular-Type</a> <a id="1841" class="Symbol">:</a> <a id="1843" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1851" href="globular-types.discrete-globular-types.html#1687" class="Function">is-discrete-Globular-Type</a>
  <a id="1879" href="globular-types.discrete-globular-types.html#1807" class="Function">is-prop-is-discrete-Globular-Type</a> <a id="1913" class="Symbol">=</a>
    <a id="1919" href="foundation.discrete-binary-relations.html#2040" class="Function">is-prop-is-discrete-Relation</a> <a id="1948" class="Symbol">(</a><a id="1949" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="1970" href="globular-types.discrete-globular-types.html#1510" class="Bound">G</a><a id="1971" class="Symbol">)</a>
</pre>
### Discrete globular types

<pre class="Agda"><a id="Discrete-Globular-Type"></a><a id="2015" href="globular-types.discrete-globular-types.html#2015" class="Function">Discrete-Globular-Type</a> <a id="2038" class="Symbol">:</a> <a id="2040" class="Symbol">(</a><a id="2041" href="globular-types.discrete-globular-types.html#2041" class="Bound">l1</a> <a id="2044" href="globular-types.discrete-globular-types.html#2044" class="Bound">l2</a> <a id="2047" class="Symbol">:</a> <a id="2049" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2054" class="Symbol">)</a> <a id="2056" class="Symbol">→</a> <a id="2058" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2061" class="Symbol">(</a><a id="2062" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2067" href="globular-types.discrete-globular-types.html#2041" class="Bound">l1</a> <a id="2070" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2072" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2077" href="globular-types.discrete-globular-types.html#2044" class="Bound">l2</a><a id="2079" class="Symbol">)</a>
<a id="2081" href="globular-types.discrete-globular-types.html#2015" class="Function">Discrete-Globular-Type</a> <a id="2104" href="globular-types.discrete-globular-types.html#2104" class="Bound">l1</a> <a id="2107" href="globular-types.discrete-globular-types.html#2107" class="Bound">l2</a> <a id="2110" class="Symbol">=</a>
  <a id="2114" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2116" class="Symbol">(</a><a id="2117" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="2131" href="globular-types.discrete-globular-types.html#2104" class="Bound">l1</a> <a id="2134" href="globular-types.discrete-globular-types.html#2107" class="Bound">l2</a><a id="2136" class="Symbol">)</a> <a id="2138" href="globular-types.discrete-globular-types.html#1687" class="Function">is-discrete-Globular-Type</a>
</pre>
### The standard discrete globular types

<pre class="Agda"><a id="discrete-Globular-Type"></a><a id="2219" href="globular-types.discrete-globular-types.html#2219" class="Function">discrete-Globular-Type</a> <a id="2242" class="Symbol">:</a>
  <a id="2246" class="Symbol">{</a><a id="2247" href="globular-types.discrete-globular-types.html#2247" class="Bound">l</a> <a id="2249" class="Symbol">:</a> <a id="2251" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2256" class="Symbol">}</a> <a id="2258" class="Symbol">(</a><a id="2259" href="globular-types.discrete-globular-types.html#2259" class="Bound">A</a> <a id="2261" class="Symbol">:</a> <a id="2263" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2266" href="globular-types.discrete-globular-types.html#2247" class="Bound">l</a><a id="2267" class="Symbol">)</a> <a id="2269" class="Symbol">→</a> <a id="2271" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="2285" href="globular-types.discrete-globular-types.html#2247" class="Bound">l</a> <a id="2287" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2293" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="2314" class="Symbol">(</a><a id="2315" href="globular-types.discrete-globular-types.html#2219" class="Function">discrete-Globular-Type</a> <a id="2338" href="globular-types.discrete-globular-types.html#2338" class="Bound">A</a><a id="2339" class="Symbol">)</a> <a id="2341" class="Symbol">=</a>
  <a id="2345" href="globular-types.discrete-globular-types.html#2338" class="Bound">A</a>
<a id="2347" href="globular-types.globular-types.html#4820" class="Field">1-cell-globular-type-Globular-Type</a> <a id="2382" class="Symbol">(</a><a id="2383" href="globular-types.discrete-globular-types.html#2219" class="Function">discrete-Globular-Type</a> <a id="2406" href="globular-types.discrete-globular-types.html#2406" class="Bound">A</a><a id="2407" class="Symbol">)</a> <a id="2409" href="globular-types.discrete-globular-types.html#2409" class="Bound">x</a> <a id="2411" href="globular-types.discrete-globular-types.html#2411" class="Bound">y</a> <a id="2413" class="Symbol">=</a>
  <a id="2417" href="globular-types.empty-globular-types.html#1116" class="Function">empty-Globular-Type</a>
</pre>
## See also

- [Discrete directed graphs](graph-theory.discrete-directed-graphs.md)
- [Discrete reflexive globular types](globular-types.discrete-reflexive-globular-types.md)
