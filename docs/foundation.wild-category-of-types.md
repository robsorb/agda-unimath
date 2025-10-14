# The wild category of types

<pre class="Agda"><a id="39" class="Symbol">{-#</a> <a id="43" class="Keyword">OPTIONS</a> <a id="51" class="Pragma">--guardedness</a> <a id="65" class="Symbol">#-}</a>

<a id="70" class="Keyword">module</a> <a id="77" href="foundation.wild-category-of-types.html" class="Module">foundation.wild-category-of-types</a> <a id="111" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="foundation.globular-type-of-functions.html" class="Module">foundation.globular-type-of-functions</a>
<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="foundation.isomorphisms-of-sets.html" class="Module">foundation.isomorphisms-of-sets</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="foundation.strictly-involutive-identity-types.html" class="Module">foundation.strictly-involutive-identity-types</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="526" class="Keyword">open</a> <a id="531" class="Keyword">import</a> <a id="538" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="573" class="Keyword">open</a> <a id="578" class="Keyword">import</a> <a id="585" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="614" class="Keyword">open</a> <a id="619" class="Keyword">import</a> <a id="626" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="657" class="Keyword">open</a> <a id="662" class="Keyword">import</a> <a id="669" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="720" class="Keyword">open</a> <a id="725" class="Keyword">import</a> <a id="732" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>

<a id="764" class="Keyword">open</a> <a id="769" class="Keyword">import</a> <a id="776" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
<a id="806" class="Keyword">open</a> <a id="811" class="Keyword">import</a> <a id="818" href="globular-types.large-globular-types.html" class="Module">globular-types.large-globular-types</a>
<a id="854" class="Keyword">open</a> <a id="859" class="Keyword">import</a> <a id="866" href="globular-types.large-reflexive-globular-types.html" class="Module">globular-types.large-reflexive-globular-types</a>
<a id="912" class="Keyword">open</a> <a id="917" class="Keyword">import</a> <a id="924" href="globular-types.large-transitive-globular-types.html" class="Module">globular-types.large-transitive-globular-types</a>
<a id="971" class="Keyword">open</a> <a id="976" class="Keyword">import</a> <a id="983" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
<a id="1023" class="Keyword">open</a> <a id="1028" class="Keyword">import</a> <a id="1035" href="globular-types.transitive-globular-types.html" class="Module">globular-types.transitive-globular-types</a>

<a id="1077" class="Keyword">open</a> <a id="1082" class="Keyword">import</a> <a id="1089" href="wild-category-theory.noncoherent-large-omega-precategories.html" class="Module">wild-category-theory.noncoherent-large-omega-precategories</a>
<a id="1148" class="Keyword">open</a> <a id="1153" class="Keyword">import</a> <a id="1160" href="wild-category-theory.noncoherent-omega-precategories.html" class="Module">wild-category-theory.noncoherent-omega-precategories</a>
</pre>
</details>

## Idea

The
{{#concept "wild category of types" Agda=Type-Noncoherent-Large-ω-Precategory}}
consists of types and [functions](foundation.dependent-function-types.md) and
[homotopies](foundation-core.homotopies.md).

## Definitions

### The large globular type of types

<pre class="Agda"><a id="Type-Large-Globular-Type"></a><a id="1509" href="foundation.wild-category-of-types.html#1509" class="Function">Type-Large-Globular-Type</a> <a id="1534" class="Symbol">:</a> <a id="1536" href="globular-types.large-globular-types.html#4432" class="Record">Large-Globular-Type</a> <a id="1556" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1561" class="Symbol">(</a><a id="1562" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="1565" class="Symbol">)</a>
<a id="1567" href="globular-types.large-globular-types.html#4526" class="Field">0-cell-Large-Globular-Type</a> <a id="1594" href="foundation.wild-category-of-types.html#1509" class="Function">Type-Large-Globular-Type</a> <a id="1619" href="foundation.wild-category-of-types.html#1619" class="Bound">l</a> <a id="1621" class="Symbol">=</a>
  <a id="1625" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1628" href="foundation.wild-category-of-types.html#1619" class="Bound">l</a>
<a id="1630" href="globular-types.large-globular-types.html#4588" class="Field">1-cell-globular-type-Large-Globular-Type</a> <a id="1671" href="foundation.wild-category-of-types.html#1509" class="Function">Type-Large-Globular-Type</a> <a id="1696" href="foundation.wild-category-of-types.html#1696" class="Bound">A</a> <a id="1698" href="foundation.wild-category-of-types.html#1698" class="Bound">B</a> <a id="1700" class="Symbol">=</a>
  <a id="1704" href="foundation.globular-type-of-functions.html#1425" class="Function">function-type-Globular-Type</a> <a id="1732" href="foundation.wild-category-of-types.html#1696" class="Bound">A</a> <a id="1734" href="foundation.wild-category-of-types.html#1698" class="Bound">B</a>

<a id="is-reflexive-Type-Large-Globular-Type"></a><a id="1737" href="foundation.wild-category-of-types.html#1737" class="Function">is-reflexive-Type-Large-Globular-Type</a> <a id="1775" class="Symbol">:</a>
  <a id="1779" href="globular-types.large-reflexive-globular-types.html#850" class="Record">is-reflexive-Large-Globular-Type</a> <a id="1812" href="foundation.wild-category-of-types.html#1509" class="Function">Type-Large-Globular-Type</a>
<a id="1837" href="globular-types.large-reflexive-globular-types.html#1000" class="Field">refl-1-cell-is-reflexive-Large-Globular-Type</a>
  <a id="1884" href="foundation.wild-category-of-types.html#1737" class="Function">is-reflexive-Type-Large-Globular-Type</a> <a id="1922" href="foundation.wild-category-of-types.html#1922" class="Bound">X</a> <a id="1924" class="Symbol">=</a>
  <a id="1928" href="foundation-core.function-types.html#307" class="Function">id</a>
<a id="1931" href="globular-types.large-reflexive-globular-types.html#1174" class="Field">is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type</a>
  <a id="2000" href="foundation.wild-category-of-types.html#1737" class="Function">is-reflexive-Type-Large-Globular-Type</a> <a id="2038" class="Symbol">=</a>
  <a id="2042" href="foundation.globular-type-of-functions.html#1698" class="Function">is-reflexive-function-type-Globular-Type</a>

<a id="Type-Large-Reflexive-Globular-Type"></a><a id="2084" href="foundation.wild-category-of-types.html#2084" class="Function">Type-Large-Reflexive-Globular-Type</a> <a id="2119" class="Symbol">:</a> <a id="2121" href="globular-types.large-reflexive-globular-types.html#3470" class="Record">Large-Reflexive-Globular-Type</a> <a id="2151" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2156" class="Symbol">(</a><a id="2157" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="2160" class="Symbol">)</a>
<a id="2162" href="globular-types.large-reflexive-globular-types.html#3664" class="Field">large-globular-type-Large-Reflexive-Globular-Type</a>
  <a id="2214" href="foundation.wild-category-of-types.html#2084" class="Function">Type-Large-Reflexive-Globular-Type</a> <a id="2249" class="Symbol">=</a>
  <a id="2253" href="foundation.wild-category-of-types.html#1509" class="Function">Type-Large-Globular-Type</a>
<a id="2278" href="globular-types.large-reflexive-globular-types.html#10809" class="Field">is-reflexive-Large-Reflexive-Globular-Type</a>
  <a id="2323" href="foundation.wild-category-of-types.html#2084" class="Function">Type-Large-Reflexive-Globular-Type</a> <a id="2358" class="Symbol">=</a>
  <a id="2362" href="foundation.wild-category-of-types.html#1737" class="Function">is-reflexive-Type-Large-Globular-Type</a>

<a id="is-transitive-Type-Large-Globular-Type"></a><a id="2401" href="foundation.wild-category-of-types.html#2401" class="Function">is-transitive-Type-Large-Globular-Type</a> <a id="2440" class="Symbol">:</a>
  <a id="2444" href="globular-types.large-transitive-globular-types.html#839" class="Record">is-transitive-Large-Globular-Type</a> <a id="2478" href="foundation.wild-category-of-types.html#1509" class="Function">Type-Large-Globular-Type</a>
<a id="2503" href="globular-types.large-transitive-globular-types.html#986" class="Field">comp-1-cell-is-transitive-Large-Globular-Type</a>
  <a id="2551" href="foundation.wild-category-of-types.html#2401" class="Function">is-transitive-Type-Large-Globular-Type</a> <a id="2590" href="foundation.wild-category-of-types.html#2590" class="Bound">g</a> <a id="2592" href="foundation.wild-category-of-types.html#2592" class="Bound">f</a> <a id="2594" class="Symbol">=</a>
  <a id="2598" href="foundation.wild-category-of-types.html#2590" class="Bound">g</a> <a id="2600" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2602" href="foundation.wild-category-of-types.html#2592" class="Bound">f</a>
<a id="2604" href="globular-types.large-transitive-globular-types.html#1327" class="Field">is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type</a>
  <a id="2675" href="foundation.wild-category-of-types.html#2401" class="Function">is-transitive-Type-Large-Globular-Type</a> <a id="2714" class="Symbol">=</a>
  <a id="2718" href="foundation.globular-type-of-functions.html#2262" class="Function">is-transitive-function-type-Globular-Type</a>

<a id="Type-Large-Transitive-Globular-Type"></a><a id="2761" href="foundation.wild-category-of-types.html#2761" class="Function">Type-Large-Transitive-Globular-Type</a> <a id="2797" class="Symbol">:</a> <a id="2799" href="globular-types.large-transitive-globular-types.html#3994" class="Record">Large-Transitive-Globular-Type</a> <a id="2830" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2835" class="Symbol">(</a><a id="2836" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="2839" class="Symbol">)</a>
<a id="2841" href="globular-types.large-transitive-globular-types.html#4110" class="Field">large-globular-type-Large-Transitive-Globular-Type</a>
  <a id="2894" href="foundation.wild-category-of-types.html#2761" class="Function">Type-Large-Transitive-Globular-Type</a> <a id="2930" class="Symbol">=</a>
  <a id="2934" href="foundation.wild-category-of-types.html#1509" class="Function">Type-Large-Globular-Type</a>
<a id="2959" href="globular-types.large-transitive-globular-types.html#6903" class="Field">is-transitive-Large-Transitive-Globular-Type</a>
  <a id="3006" href="foundation.wild-category-of-types.html#2761" class="Function">Type-Large-Transitive-Globular-Type</a> <a id="3042" class="Symbol">=</a>
  <a id="3046" href="foundation.wild-category-of-types.html#2401" class="Function">is-transitive-Type-Large-Globular-Type</a>
</pre>
### The noncoherent large ω-precategory of types

<pre class="Agda"><a id="Type-Noncoherent-Large-ω-Precategory"></a><a id="3148" href="foundation.wild-category-of-types.html#3148" class="Function">Type-Noncoherent-Large-ω-Precategory</a> <a id="3185" class="Symbol">:</a>
  <a id="3189" href="wild-category-theory.noncoherent-large-omega-precategories.html#2501" class="Record">Noncoherent-Large-ω-Precategory</a> <a id="3221" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3226" class="Symbol">(</a><a id="3227" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="3230" class="Symbol">)</a>
<a id="3232" href="wild-category-theory.noncoherent-large-omega-precategories.html#2699" class="Field">large-globular-type-Noncoherent-Large-ω-Precategory</a>
  <a id="3286" href="foundation.wild-category-of-types.html#3148" class="Function">Type-Noncoherent-Large-ω-Precategory</a> <a id="3323" class="Symbol">=</a>
  <a id="3327" href="foundation.wild-category-of-types.html#1509" class="Function">Type-Large-Globular-Type</a>
<a id="3352" href="wild-category-theory.noncoherent-large-omega-precategories.html#7367" class="Field">id-structure-Noncoherent-Large-ω-Precategory</a>
  <a id="3399" href="foundation.wild-category-of-types.html#3148" class="Function">Type-Noncoherent-Large-ω-Precategory</a> <a id="3436" class="Symbol">=</a>
  <a id="3440" href="foundation.wild-category-of-types.html#1737" class="Function">is-reflexive-Type-Large-Globular-Type</a>
<a id="3478" href="wild-category-theory.noncoherent-large-omega-precategories.html#9263" class="Field">comp-structure-Noncoherent-Large-ω-Precategory</a>
  <a id="3527" href="foundation.wild-category-of-types.html#3148" class="Function">Type-Noncoherent-Large-ω-Precategory</a> <a id="3564" class="Symbol">=</a>
  <a id="3568" href="foundation.wild-category-of-types.html#2401" class="Function">is-transitive-Type-Large-Globular-Type</a>
</pre>