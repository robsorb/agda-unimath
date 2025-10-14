# The large locale of propositions

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="foundation.large-locale-of-propositions.html" class="Module">foundation.large-locale-of-propositions</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="312" class="Keyword">open</a> <a id="317" class="Keyword">import</a> <a id="324" href="foundation.propositional-extensionality.html" class="Module">foundation.propositional-extensionality</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="397" class="Keyword">open</a> <a id="402" class="Keyword">import</a> <a id="409" href="foundation.universal-property-cartesian-product-types.html" class="Module">foundation.universal-property-cartesian-product-types</a>
<a id="463" class="Keyword">open</a> <a id="468" class="Keyword">import</a> <a id="475" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="546" class="Keyword">open</a> <a id="551" class="Keyword">import</a> <a id="558" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>

<a id="588" class="Keyword">open</a> <a id="593" class="Keyword">import</a> <a id="600" href="order-theory.bottom-elements-large-posets.html" class="Module">order-theory.bottom-elements-large-posets</a>
<a id="642" class="Keyword">open</a> <a id="647" class="Keyword">import</a> <a id="654" href="order-theory.large-frames.html" class="Module">order-theory.large-frames</a>
<a id="680" class="Keyword">open</a> <a id="685" class="Keyword">import</a> <a id="692" href="order-theory.large-locales.html" class="Module">order-theory.large-locales</a>
<a id="719" class="Keyword">open</a> <a id="724" class="Keyword">import</a> <a id="731" href="order-theory.large-meet-semilattices.html" class="Module">order-theory.large-meet-semilattices</a>
<a id="768" class="Keyword">open</a> <a id="773" class="Keyword">import</a> <a id="780" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>
<a id="806" class="Keyword">open</a> <a id="811" class="Keyword">import</a> <a id="818" href="order-theory.large-preorders.html" class="Module">order-theory.large-preorders</a>
<a id="847" class="Keyword">open</a> <a id="852" class="Keyword">import</a> <a id="859" href="order-theory.large-suplattices.html" class="Module">order-theory.large-suplattices</a>
<a id="890" class="Keyword">open</a> <a id="895" class="Keyword">import</a> <a id="902" href="order-theory.least-upper-bounds-large-posets.html" class="Module">order-theory.least-upper-bounds-large-posets</a>
<a id="947" class="Keyword">open</a> <a id="952" class="Keyword">import</a> <a id="959" href="order-theory.top-elements-large-posets.html" class="Module">order-theory.top-elements-large-posets</a>
</pre>
</details>

## Idea

The [large locale](order-theory.large-locales.md) of
[propositions](foundation-core.propositions.md) consists of all the propositions
of any [universe level](foundation.universe-levels.md) and is ordered by the
implications between them. [Conjunction](foundation.conjunction.md) gives this
[large poset](order-theory.large-posets.md) the structure of a
[large meet-semilattice](order-theory.large-meet-semilattices.md), and
[existential quantification](foundation.existential-quantification.md) gives it
the structure of a [large suplattice](order-theory.large-suplattices.md).

**Note.** The collection of all propositions is large because we do not assume
[propositional resizing](foundation.propositional-resizing.md).

## Definitions

### The large preorder of propositions

<pre class="Agda"><a id="Prop-Large-Preorder"></a><a id="1811" href="foundation.large-locale-of-propositions.html#1811" class="Function">Prop-Large-Preorder</a> <a id="1831" class="Symbol">:</a> <a id="1833" href="order-theory.large-preorders.html#926" class="Record">Large-Preorder</a> <a id="1848" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1853" class="Symbol">(</a><a id="1854" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1857" class="Symbol">)</a>
<a id="1859" href="order-theory.large-preorders.html#1051" class="Field">type-Large-Preorder</a> <a id="1879" href="foundation.large-locale-of-propositions.html#1811" class="Function">Prop-Large-Preorder</a> <a id="1899" class="Symbol">=</a> <a id="1901" href="foundation-core.propositions.html#1153" class="Function">Prop</a>
<a id="1906" href="order-theory.large-preorders.html#1100" class="Field">leq-prop-Large-Preorder</a> <a id="1930" href="foundation.large-locale-of-propositions.html#1811" class="Function">Prop-Large-Preorder</a> <a id="1950" class="Symbol">=</a> <a id="1952" href="foundation-core.propositions.html#8765" class="Function">hom-Prop</a>
<a id="1961" href="order-theory.large-preorders.html#1172" class="Field">refl-leq-Large-Preorder</a> <a id="1985" href="foundation.large-locale-of-propositions.html#1811" class="Function">Prop-Large-Preorder</a> <a id="2005" href="foundation.large-locale-of-propositions.html#2005" class="Bound">P</a> <a id="2007" class="Symbol">=</a> <a id="2009" href="foundation-core.function-types.html#307" class="Function">id</a>
<a id="2012" href="order-theory.large-preorders.html#1307" class="Field">transitive-leq-Large-Preorder</a> <a id="2042" href="foundation.large-locale-of-propositions.html#1811" class="Function">Prop-Large-Preorder</a> <a id="2062" href="foundation.large-locale-of-propositions.html#2062" class="Bound">P</a> <a id="2064" href="foundation.large-locale-of-propositions.html#2064" class="Bound">Q</a> <a id="2066" href="foundation.large-locale-of-propositions.html#2066" class="Bound">R</a> <a id="2068" href="foundation.large-locale-of-propositions.html#2068" class="Bound">g</a> <a id="2070" href="foundation.large-locale-of-propositions.html#2070" class="Bound">f</a> <a id="2072" class="Symbol">=</a> <a id="2074" href="foundation.large-locale-of-propositions.html#2068" class="Bound">g</a> <a id="2076" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2078" href="foundation.large-locale-of-propositions.html#2070" class="Bound">f</a>
</pre>
### The large poset of propositions

<pre class="Agda"><a id="Prop-Large-Poset"></a><a id="2130" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a> <a id="2147" class="Symbol">:</a> <a id="2149" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="2161" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2166" class="Symbol">(</a><a id="2167" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="2170" class="Symbol">)</a>
<a id="2172" href="order-theory.large-posets.html#1179" class="Field">large-preorder-Large-Poset</a> <a id="2199" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a> <a id="2216" class="Symbol">=</a> <a id="2218" href="foundation.large-locale-of-propositions.html#1811" class="Function">Prop-Large-Preorder</a>
<a id="2238" href="order-theory.large-posets.html#1231" class="Field">antisymmetric-leq-Large-Poset</a> <a id="2268" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a> <a id="2285" href="foundation.large-locale-of-propositions.html#2285" class="Bound">P</a> <a id="2287" href="foundation.large-locale-of-propositions.html#2287" class="Bound">Q</a> <a id="2289" class="Symbol">=</a> <a id="2291" href="foundation.propositional-extensionality.html#2809" class="Function">eq-iff</a>
</pre>
### Meets in the large poset of propositions

<pre class="Agda"><a id="has-meets-Prop-Large-Locale"></a><a id="2357" href="foundation.large-locale-of-propositions.html#2357" class="Function">has-meets-Prop-Large-Locale</a> <a id="2385" class="Symbol">:</a>
  <a id="2389" href="order-theory.large-meet-semilattices.html#852" class="Record">has-meets-Large-Poset</a> <a id="2411" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a>
<a id="2428" href="order-theory.large-meet-semilattices.html#1034" class="Field">meet-has-meets-Large-Poset</a> <a id="2455" href="foundation.large-locale-of-propositions.html#2357" class="Function">has-meets-Prop-Large-Locale</a> <a id="2483" class="Symbol">=</a> <a id="2485" href="foundation.conjunction.html#2065" class="Function">conjunction-Prop</a>
<a id="2502" href="order-theory.large-meet-semilattices.html#1188" class="Field">is-greatest-binary-lower-bound-meet-has-meets-Large-Poset</a>
  <a id="2562" href="foundation.large-locale-of-propositions.html#2357" class="Function">has-meets-Prop-Large-Locale</a> <a id="2590" href="foundation.large-locale-of-propositions.html#2590" class="Bound">P</a> <a id="2592" href="foundation.large-locale-of-propositions.html#2592" class="Bound">Q</a> <a id="2594" href="foundation.large-locale-of-propositions.html#2594" class="Bound">R</a> <a id="2596" class="Symbol">=</a>
  <a id="2600" href="foundation.conjunction.html#5895" class="Function">is-greatest-binary-lower-bound-conjunction-Prop</a> <a id="2648" href="foundation.large-locale-of-propositions.html#2590" class="Bound">P</a> <a id="2650" href="foundation.large-locale-of-propositions.html#2592" class="Bound">Q</a> <a id="2652" href="foundation.large-locale-of-propositions.html#2594" class="Bound">R</a>
</pre>
### The largest element in the large poset of propositions

<pre class="Agda"><a id="has-top-element-Prop-Large-Locale"></a><a id="2727" href="foundation.large-locale-of-propositions.html#2727" class="Function">has-top-element-Prop-Large-Locale</a> <a id="2761" class="Symbol">:</a>
  <a id="2765" href="order-theory.top-elements-large-posets.html#1154" class="Record">has-top-element-Large-Poset</a> <a id="2793" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a>
<a id="2810" href="order-theory.top-elements-large-posets.html#1214" class="Field">top-has-top-element-Large-Poset</a>
  <a id="2844" href="foundation.large-locale-of-propositions.html#2727" class="Function">has-top-element-Prop-Large-Locale</a> <a id="2878" class="Symbol">=</a> <a id="2880" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a>
<a id="2890" href="order-theory.top-elements-large-posets.html#1287" class="Field">is-top-element-top-has-top-element-Large-Poset</a>
  <a id="2939" href="foundation.large-locale-of-propositions.html#2727" class="Function">has-top-element-Prop-Large-Locale</a> <a id="2973" href="foundation.large-locale-of-propositions.html#2973" class="Bound">P</a> <a id="2975" href="foundation.large-locale-of-propositions.html#2975" class="Bound">p</a> <a id="2977" class="Symbol">=</a>
  <a id="2981" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a>
</pre>
### The smallest element in the large poset of propositions

<pre class="Agda"><a id="has-bottom-element-Prop-Large-Locale"></a><a id="3060" href="foundation.large-locale-of-propositions.html#3060" class="Function">has-bottom-element-Prop-Large-Locale</a> <a id="3097" class="Symbol">:</a>
  <a id="3101" href="order-theory.bottom-elements-large-posets.html#1126" class="Record">has-bottom-element-Large-Poset</a> <a id="3132" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a>
<a id="3149" href="order-theory.bottom-elements-large-posets.html#1189" class="Field">bottom-has-bottom-element-Large-Poset</a>
  <a id="3189" href="foundation.large-locale-of-propositions.html#3060" class="Function">has-bottom-element-Prop-Large-Locale</a> <a id="3226" class="Symbol">=</a> <a id="3228" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a>
<a id="3239" href="order-theory.bottom-elements-large-posets.html#1268" class="Field">is-bottom-element-bottom-has-bottom-element-Large-Poset</a>
  <a id="3297" href="foundation.large-locale-of-propositions.html#3060" class="Function">has-bottom-element-Prop-Large-Locale</a> <a id="3334" href="foundation.large-locale-of-propositions.html#3334" class="Bound">P</a> <a id="3336" class="Symbol">=</a> <a id="3338" href="foundation-core.empty-types.html#904" class="Function">ex-falso</a>
</pre>
### The large poset of propositions is a large meet-semilattice

<pre class="Agda"><a id="is-large-meet-semilattice-Prop-Large-Locale"></a><a id="3425" href="foundation.large-locale-of-propositions.html#3425" class="Function">is-large-meet-semilattice-Prop-Large-Locale</a> <a id="3469" class="Symbol">:</a>
  <a id="3473" href="order-theory.large-meet-semilattices.html#1541" class="Record">is-large-meet-semilattice-Large-Poset</a> <a id="3511" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a>
<a id="3528" href="order-theory.large-meet-semilattices.html#1694" class="Field">has-meets-is-large-meet-semilattice-Large-Poset</a>
  <a id="3578" href="foundation.large-locale-of-propositions.html#3425" class="Function">is-large-meet-semilattice-Prop-Large-Locale</a> <a id="3622" class="Symbol">=</a>
  <a id="3626" href="foundation.large-locale-of-propositions.html#2357" class="Function">has-meets-Prop-Large-Locale</a>
<a id="3654" href="order-theory.large-meet-semilattices.html#1778" class="Field">has-top-element-is-large-meet-semilattice-Large-Poset</a>
  <a id="3710" href="foundation.large-locale-of-propositions.html#3425" class="Function">is-large-meet-semilattice-Prop-Large-Locale</a> <a id="3754" class="Symbol">=</a>
  <a id="3758" href="foundation.large-locale-of-propositions.html#2727" class="Function">has-top-element-Prop-Large-Locale</a>

<a id="Prop-Large-Meet-Semilattice"></a><a id="3793" href="foundation.large-locale-of-propositions.html#3793" class="Function">Prop-Large-Meet-Semilattice</a> <a id="3821" class="Symbol">:</a> <a id="3823" href="order-theory.large-meet-semilattices.html#3450" class="Record">Large-Meet-Semilattice</a> <a id="3846" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3851" class="Symbol">(</a><a id="3852" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="3855" class="Symbol">)</a>
<a id="3857" href="foundation.large-locale-of-propositions.html#3793" class="Function">Prop-Large-Meet-Semilattice</a> <a id="3885" class="Symbol">=</a>
  <a id="3889" href="order-theory.large-meet-semilattices.html#3567" class="InductiveConstructor">make-Large-Meet-Semilattice</a>
    <a id="3921" class="Symbol">(</a> <a id="3923" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a><a id="3939" class="Symbol">)</a>
    <a id="3945" class="Symbol">(</a> <a id="3947" href="foundation.large-locale-of-propositions.html#3425" class="Function">is-large-meet-semilattice-Prop-Large-Locale</a><a id="3990" class="Symbol">)</a>
</pre>
### Suprema in the large poset of propositions

<pre class="Agda"><a id="is-large-suplattice-Prop-Large-Locale"></a><a id="4053" href="foundation.large-locale-of-propositions.html#4053" class="Function">is-large-suplattice-Prop-Large-Locale</a> <a id="4091" class="Symbol">:</a>
  <a id="4095" href="order-theory.large-suplattices.html#1258" class="Function">is-large-suplattice-Large-Poset</a> <a id="4127" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="4133" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a>
<a id="4150" href="order-theory.least-upper-bounds-large-posets.html#3523" class="Field">sup-has-least-upper-bound-family-of-elements-Large-Poset</a>
  <a id="4209" class="Symbol">(</a> <a id="4211" href="foundation.large-locale-of-propositions.html#4053" class="Function">is-large-suplattice-Prop-Large-Locale</a> <a id="4249" class="Symbol">{</a><a id="4250" class="Argument">I</a> <a id="4252" class="Symbol">=</a> <a id="4254" href="foundation.large-locale-of-propositions.html#4254" class="Bound">I</a><a id="4255" class="Symbol">}</a> <a id="4257" href="foundation.large-locale-of-propositions.html#4257" class="Bound">P</a><a id="4258" class="Symbol">)</a> <a id="4260" class="Symbol">=</a>
  <a id="4264" href="foundation.existential-quantification.html#4308" class="Function">∃</a> <a id="4266" href="foundation.large-locale-of-propositions.html#4254" class="Bound">I</a> <a id="4268" href="foundation.large-locale-of-propositions.html#4257" class="Bound">P</a>
<a id="4270" href="order-theory.least-upper-bounds-large-posets.html#3629" class="Field">is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset</a>
  <a id="4350" class="Symbol">(</a> <a id="4352" href="foundation.large-locale-of-propositions.html#4053" class="Function">is-large-suplattice-Prop-Large-Locale</a> <a id="4390" class="Symbol">{</a><a id="4391" class="Argument">I</a> <a id="4393" class="Symbol">=</a> <a id="4395" href="foundation.large-locale-of-propositions.html#4395" class="Bound">I</a><a id="4396" class="Symbol">}</a> <a id="4398" href="foundation.large-locale-of-propositions.html#4398" class="Bound">P</a><a id="4399" class="Symbol">)</a> <a id="4401" href="foundation.large-locale-of-propositions.html#4401" class="Bound">R</a> <a id="4403" class="Symbol">=</a>
  <a id="4407" href="foundation.logical-equivalences.html#3309" class="Function">inv-iff</a> <a id="4415" class="Symbol">(</a><a id="4416" href="foundation.existential-quantification.html#6825" class="Function">up-exists</a> <a id="4426" href="foundation.large-locale-of-propositions.html#4401" class="Bound">R</a><a id="4427" class="Symbol">)</a>

<a id="Prop-Large-Suplattice"></a><a id="4430" href="foundation.large-locale-of-propositions.html#4430" class="Function">Prop-Large-Suplattice</a> <a id="4452" class="Symbol">:</a> <a id="4454" href="order-theory.large-suplattices.html#2153" class="Record">Large-Suplattice</a> <a id="4471" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="4476" class="Symbol">(</a><a id="4477" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="4480" class="Symbol">)</a> <a id="4482" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="4488" href="foundation.large-locale-of-propositions.html#4430" class="Function">Prop-Large-Suplattice</a> <a id="4510" class="Symbol">=</a>
  <a id="4514" href="order-theory.large-suplattices.html#2266" class="InductiveConstructor">make-Large-Suplattice</a> <a id="4536" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a> <a id="4553" href="foundation.large-locale-of-propositions.html#4053" class="Function">is-large-suplattice-Prop-Large-Locale</a>
</pre>
### The large frame of propositions

<pre class="Agda"><a id="Prop-Large-Frame"></a><a id="4641" href="foundation.large-locale-of-propositions.html#4641" class="Function">Prop-Large-Frame</a> <a id="4658" class="Symbol">:</a> <a id="4660" href="order-theory.large-frames.html#1062" class="Record">Large-Frame</a> <a id="4672" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="4677" class="Symbol">(</a><a id="4678" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="4681" class="Symbol">)</a> <a id="4683" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="4689" href="order-theory.large-frames.html#1195" class="Field">large-poset-Large-Frame</a> <a id="4713" href="foundation.large-locale-of-propositions.html#4641" class="Function">Prop-Large-Frame</a> <a id="4730" class="Symbol">=</a>
  <a id="4734" href="foundation.large-locale-of-propositions.html#2130" class="Function">Prop-Large-Poset</a>
<a id="4751" href="order-theory.large-frames.html#1247" class="Field">is-large-meet-semilattice-Large-Frame</a> <a id="4789" href="foundation.large-locale-of-propositions.html#4641" class="Function">Prop-Large-Frame</a> <a id="4806" class="Symbol">=</a>
  <a id="4810" href="foundation.large-locale-of-propositions.html#3425" class="Function">is-large-meet-semilattice-Prop-Large-Locale</a>
<a id="4854" href="order-theory.large-frames.html#1359" class="Field">is-large-suplattice-Large-Frame</a> <a id="4886" href="foundation.large-locale-of-propositions.html#4641" class="Function">Prop-Large-Frame</a> <a id="4903" class="Symbol">=</a>
  <a id="4907" href="foundation.large-locale-of-propositions.html#4053" class="Function">is-large-suplattice-Prop-Large-Locale</a>
<a id="4945" href="order-theory.large-frames.html#1461" class="Field">distributive-meet-sup-Large-Frame</a> <a id="4979" href="foundation.large-locale-of-propositions.html#4641" class="Function">Prop-Large-Frame</a> <a id="4996" class="Symbol">=</a>
  <a id="5000" href="foundation.existential-quantification.html#10903" class="Function">eq-distributive-conjunction-exists</a>
</pre>
### The large locale of propositions

<pre class="Agda"><a id="Prop-Large-Locale"></a><a id="5086" href="foundation.large-locale-of-propositions.html#5086" class="Function">Prop-Large-Locale</a> <a id="5104" class="Symbol">:</a> <a id="5106" href="order-theory.large-locales.html#1051" class="Function">Large-Locale</a> <a id="5119" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="5124" class="Symbol">(</a><a id="5125" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="5128" class="Symbol">)</a> <a id="5130" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="5136" href="foundation.large-locale-of-propositions.html#5086" class="Function">Prop-Large-Locale</a> <a id="5154" class="Symbol">=</a> <a id="5156" href="foundation.large-locale-of-propositions.html#4641" class="Function">Prop-Large-Frame</a>
</pre>
## See also

- [Propositional resizing](foundation.propositional-resizing.md)
