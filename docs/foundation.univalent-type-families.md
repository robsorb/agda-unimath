# Univalent type families

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation.univalent-type-families.html" class="Module">foundation.univalent-type-families</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="foundation.identity-systems.html" class="Module">foundation.identity-systems</a>
<a id="427" class="Keyword">open</a> <a id="432" class="Keyword">import</a> <a id="439" href="foundation.iterated-dependent-product-types.html" class="Module">foundation.iterated-dependent-product-types</a>
<a id="483" class="Keyword">open</a> <a id="488" class="Keyword">import</a> <a id="495" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="519" class="Keyword">open</a> <a id="524" class="Keyword">import</a> <a id="531" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="555" class="Keyword">open</a> <a id="560" class="Keyword">import</a> <a id="567" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="610" class="Keyword">open</a> <a id="615" class="Keyword">import</a> <a id="622" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="644" class="Keyword">open</a> <a id="649" class="Keyword">import</a> <a id="656" href="foundation.universal-property-identity-systems.html" class="Module">foundation.universal-property-identity-systems</a>
<a id="703" class="Keyword">open</a> <a id="708" class="Keyword">import</a> <a id="715" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="743" class="Keyword">open</a> <a id="748" class="Keyword">import</a> <a id="755" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="782" class="Keyword">open</a> <a id="787" class="Keyword">import</a> <a id="794" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="825" class="Keyword">open</a> <a id="830" class="Keyword">import</a> <a id="837" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="868" class="Keyword">open</a> <a id="873" class="Keyword">import</a> <a id="880" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="905" class="Keyword">open</a> <a id="910" class="Keyword">import</a> <a id="917" href="foundation-core.torsorial-type-families.html" class="Module">foundation-core.torsorial-type-families</a>
</pre>
</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "univalent" Disambiguation="type family" Agda=is-univalent}} if the
map

```text
  equiv-tr B : x ＝ y → B x ≃ B y
```

is an [equivalence](foundation-core.equivalences.md) for every `x y : A`. By
[the univalence axiom](foundation-core.univalence.md), this is equivalent to the
type family `B` being an [embedding](foundation-core.embeddings.md) considered
as a map. In other words, that `A` is a
[subuniverse](foundation.subuniverses.md).

## Definition

### The predicate on type families of being univalent

<pre class="Agda"><a id="is-univalent"></a><a id="1553" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="1566" class="Symbol">:</a>
  <a id="1570" class="Symbol">{</a><a id="1571" href="foundation.univalent-type-families.html#1571" class="Bound">l1</a> <a id="1574" href="foundation.univalent-type-families.html#1574" class="Bound">l2</a> <a id="1577" class="Symbol">:</a> <a id="1579" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1584" class="Symbol">}</a> <a id="1586" class="Symbol">{</a><a id="1587" href="foundation.univalent-type-families.html#1587" class="Bound">A</a> <a id="1589" class="Symbol">:</a> <a id="1591" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1594" href="foundation.univalent-type-families.html#1571" class="Bound">l1</a><a id="1596" class="Symbol">}</a> <a id="1598" class="Symbol">→</a> <a id="1600" class="Symbol">(</a><a id="1601" href="foundation.univalent-type-families.html#1587" class="Bound">A</a> <a id="1603" class="Symbol">→</a> <a id="1605" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1608" href="foundation.univalent-type-families.html#1574" class="Bound">l2</a><a id="1610" class="Symbol">)</a> <a id="1612" class="Symbol">→</a> <a id="1614" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1617" class="Symbol">(</a><a id="1618" href="foundation.univalent-type-families.html#1571" class="Bound">l1</a> <a id="1621" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1623" href="foundation.univalent-type-families.html#1574" class="Bound">l2</a><a id="1625" class="Symbol">)</a>
<a id="1627" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="1640" class="Symbol">{</a><a id="1641" class="Argument">A</a> <a id="1643" class="Symbol">=</a> <a id="1645" href="foundation.univalent-type-families.html#1645" class="Bound">A</a><a id="1646" class="Symbol">}</a> <a id="1648" href="foundation.univalent-type-families.html#1648" class="Bound">B</a> <a id="1650" class="Symbol">=</a> <a id="1652" class="Symbol">(</a><a id="1653" href="foundation.univalent-type-families.html#1653" class="Bound">x</a> <a id="1655" href="foundation.univalent-type-families.html#1655" class="Bound">y</a> <a id="1657" class="Symbol">:</a> <a id="1659" href="foundation.univalent-type-families.html#1645" class="Bound">A</a><a id="1660" class="Symbol">)</a> <a id="1662" class="Symbol">→</a> <a id="1664" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1673" class="Symbol">(λ</a> <a id="1676" class="Symbol">(</a><a id="1677" href="foundation.univalent-type-families.html#1677" class="Bound">p</a> <a id="1679" class="Symbol">:</a> <a id="1681" href="foundation.univalent-type-families.html#1653" class="Bound">x</a> <a id="1683" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1685" href="foundation.univalent-type-families.html#1655" class="Bound">y</a><a id="1686" class="Symbol">)</a> <a id="1688" class="Symbol">→</a> <a id="1690" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="1699" href="foundation.univalent-type-families.html#1648" class="Bound">B</a> <a id="1701" href="foundation.univalent-type-families.html#1677" class="Bound">p</a><a id="1702" class="Symbol">)</a>

<a id="1705" class="Keyword">module</a> <a id="1712" href="foundation.univalent-type-families.html#1712" class="Module">_</a>
  <a id="1716" class="Symbol">{</a><a id="1717" href="foundation.univalent-type-families.html#1717" class="Bound">l1</a> <a id="1720" href="foundation.univalent-type-families.html#1720" class="Bound">l2</a> <a id="1723" class="Symbol">:</a> <a id="1725" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1730" class="Symbol">}</a> <a id="1732" class="Symbol">{</a><a id="1733" href="foundation.univalent-type-families.html#1733" class="Bound">A</a> <a id="1735" class="Symbol">:</a> <a id="1737" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1740" href="foundation.univalent-type-families.html#1717" class="Bound">l1</a><a id="1742" class="Symbol">}</a> <a id="1744" class="Symbol">{</a><a id="1745" href="foundation.univalent-type-families.html#1745" class="Bound">B</a> <a id="1747" class="Symbol">:</a> <a id="1749" href="foundation.univalent-type-families.html#1733" class="Bound">A</a> <a id="1751" class="Symbol">→</a> <a id="1753" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1756" href="foundation.univalent-type-families.html#1720" class="Bound">l2</a><a id="1758" class="Symbol">}</a>
  <a id="1762" class="Keyword">where</a>

  <a id="1771" href="foundation.univalent-type-families.html#1771" class="Function">is-prop-is-univalent</a> <a id="1792" class="Symbol">:</a> <a id="1794" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1802" class="Symbol">(</a><a id="1803" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="1816" href="foundation.univalent-type-families.html#1745" class="Bound">B</a><a id="1817" class="Symbol">)</a>
  <a id="1821" href="foundation.univalent-type-families.html#1771" class="Function">is-prop-is-univalent</a> <a id="1842" class="Symbol">=</a>
    <a id="1848" href="foundation.iterated-dependent-product-types.html#5476" class="Function">is-prop-iterated-Π</a> <a id="1867" class="Number">2</a> <a id="1869" class="Symbol">(λ</a> <a id="1872" href="foundation.univalent-type-families.html#1872" class="Bound">x</a> <a id="1874" href="foundation.univalent-type-families.html#1874" class="Bound">y</a> <a id="1876" class="Symbol">→</a> <a id="1878" href="foundation.equivalences.html#4907" class="Function">is-property-is-equiv</a> <a id="1899" class="Symbol">(</a><a id="1900" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="1909" href="foundation.univalent-type-families.html#1745" class="Bound">B</a><a id="1910" class="Symbol">))</a>

  <a id="1916" href="foundation.univalent-type-families.html#1916" class="Function">is-univalent-Prop</a> <a id="1934" class="Symbol">:</a> <a id="1936" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1941" class="Symbol">(</a><a id="1942" href="foundation.univalent-type-families.html#1717" class="Bound">l1</a> <a id="1945" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1947" href="foundation.univalent-type-families.html#1720" class="Bound">l2</a><a id="1949" class="Symbol">)</a>
  <a id="1953" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1957" href="foundation.univalent-type-families.html#1916" class="Function">is-univalent-Prop</a> <a id="1975" class="Symbol">=</a> <a id="1977" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="1990" href="foundation.univalent-type-families.html#1745" class="Bound">B</a>
  <a id="1994" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1998" href="foundation.univalent-type-families.html#1916" class="Function">is-univalent-Prop</a> <a id="2016" class="Symbol">=</a> <a id="2018" href="foundation.univalent-type-families.html#1771" class="Function">is-prop-is-univalent</a>
</pre>
### Univalent type families

<pre class="Agda"><a id="univalent-type-family"></a><a id="2081" href="foundation.univalent-type-families.html#2081" class="Function">univalent-type-family</a> <a id="2103" class="Symbol">:</a>
  <a id="2107" class="Symbol">{</a><a id="2108" href="foundation.univalent-type-families.html#2108" class="Bound">l1</a> <a id="2111" class="Symbol">:</a> <a id="2113" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2118" class="Symbol">}</a> <a id="2120" class="Symbol">(</a><a id="2121" href="foundation.univalent-type-families.html#2121" class="Bound">l2</a> <a id="2124" class="Symbol">:</a> <a id="2126" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2131" class="Symbol">)</a> <a id="2133" class="Symbol">(</a><a id="2134" href="foundation.univalent-type-families.html#2134" class="Bound">A</a> <a id="2136" class="Symbol">:</a> <a id="2138" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2141" href="foundation.univalent-type-families.html#2108" class="Bound">l1</a><a id="2143" class="Symbol">)</a> <a id="2145" class="Symbol">→</a> <a id="2147" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2150" class="Symbol">(</a><a id="2151" href="foundation.univalent-type-families.html#2108" class="Bound">l1</a> <a id="2154" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2156" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2161" href="foundation.univalent-type-families.html#2121" class="Bound">l2</a><a id="2163" class="Symbol">)</a>
<a id="2165" href="foundation.univalent-type-families.html#2081" class="Function">univalent-type-family</a> <a id="2187" href="foundation.univalent-type-families.html#2187" class="Bound">l2</a> <a id="2190" href="foundation.univalent-type-families.html#2190" class="Bound">A</a> <a id="2192" class="Symbol">=</a> <a id="2194" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2196" class="Symbol">(</a><a id="2197" href="foundation.univalent-type-families.html#2190" class="Bound">A</a> <a id="2199" class="Symbol">→</a> <a id="2201" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2204" href="foundation.univalent-type-families.html#2187" class="Bound">l2</a><a id="2206" class="Symbol">)</a> <a id="2208" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a>
</pre>
## Properties

### The univalence axiom states that the identity family `id : 𝒰 → 𝒰` is univalent

<pre class="Agda"><a id="is-univalent-UU"></a><a id="2333" href="foundation.univalent-type-families.html#2333" class="Function">is-univalent-UU</a> <a id="2349" class="Symbol">:</a>
  <a id="2353" class="Symbol">(</a><a id="2354" href="foundation.univalent-type-families.html#2354" class="Bound">l</a> <a id="2356" class="Symbol">:</a> <a id="2358" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2363" class="Symbol">)</a> <a id="2365" class="Symbol">→</a> <a id="2367" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="2380" class="Symbol">(</a><a id="2381" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2384" class="Symbol">{</a><a id="2385" class="Argument">A</a> <a id="2387" class="Symbol">=</a> <a id="2389" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2392" href="foundation.univalent-type-families.html#2354" class="Bound">l</a><a id="2393" class="Symbol">})</a>
<a id="2396" href="foundation.univalent-type-families.html#2333" class="Function">is-univalent-UU</a> <a id="2412" href="foundation.univalent-type-families.html#2412" class="Bound">l</a> <a id="2414" class="Symbol">=</a> <a id="2416" href="foundation.univalence.html#2111" class="Function">univalence</a>
</pre>
### Assuming the univalence axiom, type families are univalent if and only if they are embeddings as maps

**Proof:** We have the
[commuting triangle of maps](foundation-core.commuting-triangles-of-maps.md)

```text
                ap B
       (x ＝ y) -----> (B x ＝ B y)
           \               /
            \             /
  equiv-tr B \           / equiv-eq
              ∨         ∨
              (B x ≃ B y)
```

where the right edge is an equivalence by the univalence axiom. Hence, the top
map is an equivalence if and only if the left map is.

<pre class="Agda"><a id="2995" class="Keyword">module</a> <a id="3002" href="foundation.univalent-type-families.html#3002" class="Module">_</a>
  <a id="3006" class="Symbol">{</a><a id="3007" href="foundation.univalent-type-families.html#3007" class="Bound">l1</a> <a id="3010" href="foundation.univalent-type-families.html#3010" class="Bound">l2</a> <a id="3013" class="Symbol">:</a> <a id="3015" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3020" class="Symbol">}</a> <a id="3022" class="Symbol">{</a><a id="3023" href="foundation.univalent-type-families.html#3023" class="Bound">A</a> <a id="3025" class="Symbol">:</a> <a id="3027" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3030" href="foundation.univalent-type-families.html#3007" class="Bound">l1</a><a id="3032" class="Symbol">}</a> <a id="3034" class="Symbol">{</a><a id="3035" href="foundation.univalent-type-families.html#3035" class="Bound">B</a> <a id="3037" class="Symbol">:</a> <a id="3039" href="foundation.univalent-type-families.html#3023" class="Bound">A</a> <a id="3041" class="Symbol">→</a> <a id="3043" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3046" href="foundation.univalent-type-families.html#3010" class="Bound">l2</a><a id="3048" class="Symbol">}</a>
  <a id="3052" class="Keyword">where</a>

  <a id="3061" class="Keyword">abstract</a>
    <a id="3074" href="foundation.univalent-type-families.html#3074" class="Function">is-emb-is-univalent</a> <a id="3094" class="Symbol">:</a>
      <a id="3102" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="3115" href="foundation.univalent-type-families.html#3035" class="Bound">B</a> <a id="3117" class="Symbol">→</a> <a id="3119" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="3126" href="foundation.univalent-type-families.html#3035" class="Bound">B</a>
    <a id="3132" href="foundation.univalent-type-families.html#3074" class="Function">is-emb-is-univalent</a> <a id="3152" href="foundation.univalent-type-families.html#3152" class="Bound">U</a> <a id="3154" href="foundation.univalent-type-families.html#3154" class="Bound">x</a> <a id="3156" href="foundation.univalent-type-families.html#3156" class="Bound">y</a> <a id="3158" class="Symbol">=</a>
      <a id="3166" href="foundation-core.equivalences.html#12227" class="Function">is-equiv-top-map-triangle</a>
        <a id="3200" class="Symbol">(</a> <a id="3202" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="3211" href="foundation.univalent-type-families.html#3035" class="Bound">B</a><a id="3212" class="Symbol">)</a>
        <a id="3222" class="Symbol">(</a> <a id="3224" href="foundation-core.univalence.html#1454" class="Function">equiv-eq</a><a id="3232" class="Symbol">)</a>
        <a id="3242" class="Symbol">(</a> <a id="3244" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="3247" href="foundation.univalent-type-families.html#3035" class="Bound">B</a><a id="3248" class="Symbol">)</a>
        <a id="3258" class="Symbol">(</a> <a id="3260" class="Symbol">λ</a> <a id="3262" class="Keyword">where</a> <a id="3268" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="3273" class="Symbol">→</a> <a id="3275" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="3279" class="Symbol">)</a>
        <a id="3289" class="Symbol">(</a> <a id="3291" href="foundation.univalence.html#2111" class="Function">univalence</a> <a id="3302" class="Symbol">(</a><a id="3303" href="foundation.univalent-type-families.html#3035" class="Bound">B</a> <a id="3305" href="foundation.univalent-type-families.html#3154" class="Bound">x</a><a id="3306" class="Symbol">)</a> <a id="3308" class="Symbol">(</a><a id="3309" href="foundation.univalent-type-families.html#3035" class="Bound">B</a> <a id="3311" href="foundation.univalent-type-families.html#3156" class="Bound">y</a><a id="3312" class="Symbol">))</a>
        <a id="3323" class="Symbol">(</a> <a id="3325" href="foundation.univalent-type-families.html#3152" class="Bound">U</a> <a id="3327" href="foundation.univalent-type-families.html#3154" class="Bound">x</a> <a id="3329" href="foundation.univalent-type-families.html#3156" class="Bound">y</a><a id="3330" class="Symbol">)</a>

    <a id="3337" href="foundation.univalent-type-families.html#3337" class="Function">is-univalent-is-emb</a> <a id="3357" class="Symbol">:</a>
      <a id="3365" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="3372" href="foundation.univalent-type-families.html#3035" class="Bound">B</a> <a id="3374" class="Symbol">→</a> <a id="3376" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="3389" href="foundation.univalent-type-families.html#3035" class="Bound">B</a>
    <a id="3395" href="foundation.univalent-type-families.html#3337" class="Function">is-univalent-is-emb</a> <a id="3415" href="foundation.univalent-type-families.html#3415" class="Bound">is-emb-B</a> <a id="3424" href="foundation.univalent-type-families.html#3424" class="Bound">x</a> <a id="3426" href="foundation.univalent-type-families.html#3426" class="Bound">y</a> <a id="3428" class="Symbol">=</a>
      <a id="3436" href="foundation-core.equivalences.html#10197" class="Function">is-equiv-left-map-triangle</a>
        <a id="3471" class="Symbol">(</a> <a id="3473" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="3482" href="foundation.univalent-type-families.html#3035" class="Bound">B</a><a id="3483" class="Symbol">)</a>
        <a id="3493" class="Symbol">(</a> <a id="3495" href="foundation-core.univalence.html#1454" class="Function">equiv-eq</a><a id="3503" class="Symbol">)</a>
        <a id="3513" class="Symbol">(</a> <a id="3515" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="3518" href="foundation.univalent-type-families.html#3035" class="Bound">B</a><a id="3519" class="Symbol">)</a>
        <a id="3529" class="Symbol">(</a> <a id="3531" class="Symbol">λ</a> <a id="3533" class="Keyword">where</a> <a id="3539" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="3544" class="Symbol">→</a> <a id="3546" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="3550" class="Symbol">)</a>
        <a id="3560" class="Symbol">(</a> <a id="3562" href="foundation.univalent-type-families.html#3415" class="Bound">is-emb-B</a> <a id="3571" href="foundation.univalent-type-families.html#3424" class="Bound">x</a> <a id="3573" href="foundation.univalent-type-families.html#3426" class="Bound">y</a><a id="3574" class="Symbol">)</a>
        <a id="3584" class="Symbol">(</a> <a id="3586" href="foundation.univalence.html#2111" class="Function">univalence</a> <a id="3597" class="Symbol">(</a><a id="3598" href="foundation.univalent-type-families.html#3035" class="Bound">B</a> <a id="3600" href="foundation.univalent-type-families.html#3424" class="Bound">x</a><a id="3601" class="Symbol">)</a> <a id="3603" class="Symbol">(</a><a id="3604" href="foundation.univalent-type-families.html#3035" class="Bound">B</a> <a id="3606" href="foundation.univalent-type-families.html#3426" class="Bound">y</a><a id="3607" class="Symbol">))</a>
</pre>
### Univalent type families satisfy equivalence induction

<pre class="Agda"><a id="3682" class="Keyword">module</a> <a id="3689" href="foundation.univalent-type-families.html#3689" class="Module">_</a>
  <a id="3693" class="Symbol">{</a><a id="3694" href="foundation.univalent-type-families.html#3694" class="Bound">l1</a> <a id="3697" href="foundation.univalent-type-families.html#3697" class="Bound">l2</a> <a id="3700" class="Symbol">:</a> <a id="3702" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3707" class="Symbol">}</a> <a id="3709" class="Symbol">{</a><a id="3710" href="foundation.univalent-type-families.html#3710" class="Bound">A</a> <a id="3712" class="Symbol">:</a> <a id="3714" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3717" href="foundation.univalent-type-families.html#3694" class="Bound">l1</a><a id="3719" class="Symbol">}</a> <a id="3721" class="Symbol">{</a><a id="3722" href="foundation.univalent-type-families.html#3722" class="Bound">B</a> <a id="3724" class="Symbol">:</a> <a id="3726" href="foundation.univalent-type-families.html#3710" class="Bound">A</a> <a id="3728" class="Symbol">→</a> <a id="3730" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3733" href="foundation.univalent-type-families.html#3697" class="Bound">l2</a><a id="3735" class="Symbol">}</a>
  <a id="3739" class="Symbol">(</a><a id="3740" href="foundation.univalent-type-families.html#3740" class="Bound">U</a> <a id="3742" class="Symbol">:</a> <a id="3744" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="3757" href="foundation.univalent-type-families.html#3722" class="Bound">B</a><a id="3758" class="Symbol">)</a>
  <a id="3762" class="Keyword">where</a>

  <a id="3771" href="foundation.univalent-type-families.html#3771" class="Function">is-torsorial-fam-equiv-is-univalent</a> <a id="3807" class="Symbol">:</a>
    <a id="3813" class="Symbol">{</a><a id="3814" href="foundation.univalent-type-families.html#3814" class="Bound">x</a> <a id="3816" class="Symbol">:</a> <a id="3818" href="foundation.univalent-type-families.html#3710" class="Bound">A</a><a id="3819" class="Symbol">}</a> <a id="3821" class="Symbol">→</a> <a id="3823" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="3836" class="Symbol">(λ</a> <a id="3839" href="foundation.univalent-type-families.html#3839" class="Bound">y</a> <a id="3841" class="Symbol">→</a> <a id="3843" href="foundation.univalent-type-families.html#3722" class="Bound">B</a> <a id="3845" href="foundation.univalent-type-families.html#3814" class="Bound">x</a> <a id="3847" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="3849" href="foundation.univalent-type-families.html#3722" class="Bound">B</a> <a id="3851" href="foundation.univalent-type-families.html#3839" class="Bound">y</a><a id="3852" class="Symbol">)</a>
  <a id="3856" href="foundation.univalent-type-families.html#3771" class="Function">is-torsorial-fam-equiv-is-univalent</a> <a id="3892" class="Symbol">{</a><a id="3893" href="foundation.univalent-type-families.html#3893" class="Bound">x</a><a id="3894" class="Symbol">}</a> <a id="3896" class="Symbol">=</a>
    <a id="3902" href="foundation.fundamental-theorem-of-identity-types.html#2310" class="Function">fundamental-theorem-id&#39;</a> <a id="3926" class="Symbol">(λ</a> <a id="3929" href="foundation.univalent-type-families.html#3929" class="Bound">y</a> <a id="3931" class="Symbol">→</a> <a id="3933" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="3942" href="foundation.univalent-type-families.html#3722" class="Bound">B</a><a id="3943" class="Symbol">)</a> <a id="3945" class="Symbol">(</a><a id="3946" href="foundation.univalent-type-families.html#3740" class="Bound">U</a> <a id="3948" href="foundation.univalent-type-families.html#3893" class="Bound">x</a><a id="3949" class="Symbol">)</a>

  <a id="3954" href="foundation.univalent-type-families.html#3954" class="Function">dependent-universal-property-identity-system-fam-equiv-is-univalent</a> <a id="4022" class="Symbol">:</a>
    <a id="4028" class="Symbol">{</a><a id="4029" href="foundation.univalent-type-families.html#4029" class="Bound">x</a> <a id="4031" class="Symbol">:</a> <a id="4033" href="foundation.univalent-type-families.html#3710" class="Bound">A</a><a id="4034" class="Symbol">}</a> <a id="4036" class="Symbol">→</a>
    <a id="4042" href="foundation.universal-property-identity-systems.html#1112" class="Function">dependent-universal-property-identity-system</a> <a id="4087" class="Symbol">(λ</a> <a id="4090" href="foundation.univalent-type-families.html#4090" class="Bound">y</a> <a id="4092" class="Symbol">→</a> <a id="4094" href="foundation.univalent-type-families.html#3722" class="Bound">B</a> <a id="4096" href="foundation.univalent-type-families.html#4029" class="Bound">x</a> <a id="4098" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="4100" href="foundation.univalent-type-families.html#3722" class="Bound">B</a> <a id="4102" href="foundation.univalent-type-families.html#4090" class="Bound">y</a><a id="4103" class="Symbol">)</a> <a id="4105" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
  <a id="4116" href="foundation.univalent-type-families.html#3954" class="Function">dependent-universal-property-identity-system-fam-equiv-is-univalent</a> <a id="4184" class="Symbol">{</a><a id="4185" href="foundation.univalent-type-families.html#4185" class="Bound">x</a><a id="4186" class="Symbol">}</a> <a id="4188" class="Symbol">=</a>
    <a id="4194" href="foundation.universal-property-identity-systems.html#1605" class="Function">dependent-universal-property-identity-system-is-torsorial</a>
      <a id="4258" class="Symbol">(</a> <a id="4260" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a><a id="4268" class="Symbol">)</a>
      <a id="4276" class="Symbol">(</a> <a id="4278" href="foundation.univalent-type-families.html#3771" class="Function">is-torsorial-fam-equiv-is-univalent</a> <a id="4314" class="Symbol">{</a><a id="4315" href="foundation.univalent-type-families.html#4185" class="Bound">x</a><a id="4316" class="Symbol">})</a>
</pre>
### Inclusions of subuniverses into the universe are univalent

**Note.** This proof relies on essential use of the univalence axiom.

<pre class="Agda"><a id="4467" class="Keyword">module</a> <a id="4474" href="foundation.univalent-type-families.html#4474" class="Module">_</a>
  <a id="4478" class="Symbol">{</a><a id="4479" href="foundation.univalent-type-families.html#4479" class="Bound">l1</a> <a id="4482" href="foundation.univalent-type-families.html#4482" class="Bound">l2</a> <a id="4485" class="Symbol">:</a> <a id="4487" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4492" class="Symbol">}</a> <a id="4494" class="Symbol">(</a><a id="4495" href="foundation.univalent-type-families.html#4495" class="Bound">S</a> <a id="4497" class="Symbol">:</a> <a id="4499" href="foundation.subuniverses.html#1114" class="Function">subuniverse</a> <a id="4511" href="foundation.univalent-type-families.html#4479" class="Bound">l1</a> <a id="4514" href="foundation.univalent-type-families.html#4482" class="Bound">l2</a><a id="4516" class="Symbol">)</a>
  <a id="4520" class="Keyword">where</a>

  <a id="4529" href="foundation.univalent-type-families.html#4529" class="Function">is-univalent-inclusion-subuniverse</a> <a id="4564" class="Symbol">:</a> <a id="4566" href="foundation.univalent-type-families.html#1553" class="Function">is-univalent</a> <a id="4579" class="Symbol">(</a><a id="4580" href="foundation.subuniverses.html#1720" class="Function">inclusion-subuniverse</a> <a id="4602" href="foundation.univalent-type-families.html#4495" class="Bound">S</a><a id="4603" class="Symbol">)</a>
  <a id="4607" href="foundation.univalent-type-families.html#4529" class="Function">is-univalent-inclusion-subuniverse</a> <a id="4642" class="Symbol">=</a>
    <a id="4648" href="foundation.univalent-type-families.html#3337" class="Function">is-univalent-is-emb</a> <a id="4668" class="Symbol">(</a><a id="4669" href="foundation.subuniverses.html#1984" class="Function">is-emb-inclusion-subuniverse</a> <a id="4698" href="foundation.univalent-type-families.html#4495" class="Bound">S</a><a id="4699" class="Symbol">)</a>
</pre>
## See also

- [Preunivalent type families](foundation.preunivalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md):
  By a corollary of
  [the fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
  `equiv-tr B` is a
  [fiberwise equivalence](foundation-core.families-of-equivalences.md) as soon
  as it admits a fiberwise [section](foundation-core.sections.md).
