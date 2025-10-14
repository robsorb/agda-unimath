# Symmetric cores of binary relations

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="foundation.symmetric-cores-binary-relations.html" class="Module">foundation.symmetric-cores-binary-relations</a> <a id="99" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="155" class="Keyword">open</a> <a id="160" class="Keyword">import</a> <a id="167" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="195" class="Keyword">open</a> <a id="200" class="Keyword">import</a> <a id="207" href="foundation.morphisms-binary-relations.html" class="Module">foundation.morphisms-binary-relations</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="foundation.postcomposition-functions.html" class="Module">foundation.postcomposition-functions</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="foundation.symmetric-binary-relations.html" class="Module">foundation.symmetric-binary-relations</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="399" class="Keyword">open</a> <a id="404" class="Keyword">import</a> <a id="411" href="foundation.type-arithmetic-dependent-function-types.html" class="Module">foundation.type-arithmetic-dependent-function-types</a>
<a id="463" class="Keyword">open</a> <a id="468" class="Keyword">import</a> <a id="475" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="502" class="Keyword">open</a> <a id="507" class="Keyword">import</a> <a id="514" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="542" class="Keyword">open</a> <a id="547" class="Keyword">import</a> <a id="554" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="583" class="Keyword">open</a> <a id="588" class="Keyword">import</a> <a id="595" href="foundation-core.functoriality-dependent-function-types.html" class="Module">foundation-core.functoriality-dependent-function-types</a>

<a id="651" class="Keyword">open</a> <a id="656" class="Keyword">import</a> <a id="663" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The **symmetric core** of a [binary relation](foundation.binary-relations.md)
`R : A → A → 𝒰` on a type `A` is a
[symmetric binary relation](foundation.symmetric-binary-relations.md) `core R`
equipped with a counit

```text
  (x y : A) → core R {x , y} → R x y
```

that satisfies the universal property of the symmetric core, i.e., it satisfies
the property that for any symmetric relation `S : unordered-pair A → 𝒰`, the
precomposition function

```text
  hom-Symmetric-Relation S (core R) → hom-Relation (rel S) R
```

is an [equivalence](foundation-core.equivalences.md). The symmetric core of a
binary relation `R` is defined as the relation

```text
  core R (I,a) := (i : I) → R (a i) (a -i)
```

where `-i` is the element of the
[2-element type](univalent-combinatorics.2-element-types.md) obtained by
applying the swap [involution](foundation.involutions.md) to `i`. With this
definition it is easy to see that the universal property of the adjunction
should hold, since we have

```text
  ((I,a) → S (I,a) → core R (I,a)) ≃ ((x y : A) → S {x,y} → R x y).
```

## Definitions

### The symmetric core of a binary relation

<pre class="Agda"><a id="1874" class="Keyword">module</a> <a id="1881" href="foundation.symmetric-cores-binary-relations.html#1881" class="Module">_</a>
  <a id="1885" class="Symbol">{</a><a id="1886" href="foundation.symmetric-cores-binary-relations.html#1886" class="Bound">l1</a> <a id="1889" href="foundation.symmetric-cores-binary-relations.html#1889" class="Bound">l2</a> <a id="1892" class="Symbol">:</a> <a id="1894" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1899" class="Symbol">}</a> <a id="1901" class="Symbol">{</a><a id="1902" href="foundation.symmetric-cores-binary-relations.html#1902" class="Bound">A</a> <a id="1904" class="Symbol">:</a> <a id="1906" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1909" href="foundation.symmetric-cores-binary-relations.html#1886" class="Bound">l1</a><a id="1911" class="Symbol">}</a> <a id="1913" class="Symbol">(</a><a id="1914" href="foundation.symmetric-cores-binary-relations.html#1914" class="Bound">R</a> <a id="1916" class="Symbol">:</a> <a id="1918" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1927" href="foundation.symmetric-cores-binary-relations.html#1889" class="Bound">l2</a> <a id="1930" href="foundation.symmetric-cores-binary-relations.html#1902" class="Bound">A</a><a id="1931" class="Symbol">)</a>
  <a id="1935" class="Keyword">where</a>

  <a id="1944" href="foundation.symmetric-cores-binary-relations.html#1944" class="Function">symmetric-core-Relation</a> <a id="1968" class="Symbol">:</a> <a id="1970" href="foundation.symmetric-binary-relations.html#1503" class="Function">Symmetric-Relation</a> <a id="1989" href="foundation.symmetric-cores-binary-relations.html#1889" class="Bound">l2</a> <a id="1992" href="foundation.symmetric-cores-binary-relations.html#1902" class="Bound">A</a>
  <a id="1996" href="foundation.symmetric-cores-binary-relations.html#1944" class="Function">symmetric-core-Relation</a> <a id="2020" href="foundation.symmetric-cores-binary-relations.html#2020" class="Bound">p</a> <a id="2022" class="Symbol">=</a>
    <a id="2028" class="Symbol">(</a><a id="2029" href="foundation.symmetric-cores-binary-relations.html#2029" class="Bound">i</a> <a id="2031" class="Symbol">:</a> <a id="2033" href="foundation.unordered-pairs.html#2595" class="Function">type-unordered-pair</a> <a id="2053" href="foundation.symmetric-cores-binary-relations.html#2020" class="Bound">p</a><a id="2054" class="Symbol">)</a> <a id="2056" class="Symbol">→</a>
    <a id="2062" href="foundation.symmetric-cores-binary-relations.html#1914" class="Bound">R</a> <a id="2064" class="Symbol">(</a><a id="2065" href="foundation.unordered-pairs.html#3321" class="Function">element-unordered-pair</a> <a id="2088" href="foundation.symmetric-cores-binary-relations.html#2020" class="Bound">p</a> <a id="2090" href="foundation.symmetric-cores-binary-relations.html#2029" class="Bound">i</a><a id="2091" class="Symbol">)</a> <a id="2093" class="Symbol">(</a><a id="2094" href="foundation.unordered-pairs.html#3406" class="Function">other-element-unordered-pair</a> <a id="2123" href="foundation.symmetric-cores-binary-relations.html#2020" class="Bound">p</a> <a id="2125" href="foundation.symmetric-cores-binary-relations.html#2029" class="Bound">i</a><a id="2126" class="Symbol">)</a>

  <a id="2131" href="foundation.symmetric-cores-binary-relations.html#2131" class="Function">counit-symmetric-core-Relation</a> <a id="2162" class="Symbol">:</a>
    <a id="2168" class="Symbol">{</a><a id="2169" href="foundation.symmetric-cores-binary-relations.html#2169" class="Bound">x</a> <a id="2171" href="foundation.symmetric-cores-binary-relations.html#2171" class="Bound">y</a> <a id="2173" class="Symbol">:</a> <a id="2175" href="foundation.symmetric-cores-binary-relations.html#1902" class="Bound">A</a><a id="2176" class="Symbol">}</a> <a id="2178" class="Symbol">→</a>
    <a id="2184" href="foundation.symmetric-binary-relations.html#4237" class="Function">relation-Symmetric-Relation</a> <a id="2212" href="foundation.symmetric-cores-binary-relations.html#1944" class="Function">symmetric-core-Relation</a> <a id="2236" href="foundation.symmetric-cores-binary-relations.html#2169" class="Bound">x</a> <a id="2238" href="foundation.symmetric-cores-binary-relations.html#2171" class="Bound">y</a> <a id="2240" class="Symbol">→</a> <a id="2242" href="foundation.symmetric-cores-binary-relations.html#1914" class="Bound">R</a> <a id="2244" href="foundation.symmetric-cores-binary-relations.html#2169" class="Bound">x</a> <a id="2246" href="foundation.symmetric-cores-binary-relations.html#2171" class="Bound">y</a>
  <a id="2250" href="foundation.symmetric-cores-binary-relations.html#2131" class="Function">counit-symmetric-core-Relation</a> <a id="2281" class="Symbol">{</a><a id="2282" href="foundation.symmetric-cores-binary-relations.html#2282" class="Bound">x</a><a id="2283" class="Symbol">}</a> <a id="2285" class="Symbol">{</a><a id="2286" href="foundation.symmetric-cores-binary-relations.html#2286" class="Bound">y</a><a id="2287" class="Symbol">}</a> <a id="2289" href="foundation.symmetric-cores-binary-relations.html#2289" class="Bound">r</a> <a id="2291" class="Symbol">=</a>
    <a id="2297" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a>
      <a id="2306" class="Symbol">(</a> <a id="2308" href="foundation.symmetric-cores-binary-relations.html#1914" class="Bound">R</a> <a id="2310" href="foundation.symmetric-cores-binary-relations.html#2282" class="Bound">x</a><a id="2311" class="Symbol">)</a>
      <a id="2319" class="Symbol">(</a> <a id="2321" href="foundation.unordered-pairs.html#5171" class="Function">compute-other-element-standard-unordered-pair</a> <a id="2367" href="foundation.symmetric-cores-binary-relations.html#2282" class="Bound">x</a> <a id="2369" href="foundation.symmetric-cores-binary-relations.html#2286" class="Bound">y</a> <a id="2371" class="Symbol">(</a><a id="2372" href="univalent-combinatorics.standard-finite-types.html#5750" class="Function">zero-Fin</a> <a id="2381" class="Number">1</a><a id="2382" class="Symbol">))</a>
      <a id="2391" class="Symbol">(</a> <a id="2393" href="foundation.symmetric-cores-binary-relations.html#2289" class="Bound">r</a> <a id="2395" class="Symbol">(</a><a id="2396" href="univalent-combinatorics.standard-finite-types.html#5750" class="Function">zero-Fin</a> <a id="2405" class="Number">1</a><a id="2406" class="Symbol">))</a>
</pre>
## Properties

### The universal property of the symmetric core of a binary relation

<pre class="Agda"><a id="2508" class="Keyword">module</a> <a id="2515" href="foundation.symmetric-cores-binary-relations.html#2515" class="Module">_</a>
  <a id="2519" class="Symbol">{</a><a id="2520" href="foundation.symmetric-cores-binary-relations.html#2520" class="Bound">l1</a> <a id="2523" href="foundation.symmetric-cores-binary-relations.html#2523" class="Bound">l2</a> <a id="2526" href="foundation.symmetric-cores-binary-relations.html#2526" class="Bound">l3</a> <a id="2529" class="Symbol">:</a> <a id="2531" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2536" class="Symbol">}</a> <a id="2538" class="Symbol">{</a><a id="2539" href="foundation.symmetric-cores-binary-relations.html#2539" class="Bound">A</a> <a id="2541" class="Symbol">:</a> <a id="2543" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2546" href="foundation.symmetric-cores-binary-relations.html#2520" class="Bound">l1</a><a id="2548" class="Symbol">}</a> <a id="2550" class="Symbol">(</a><a id="2551" href="foundation.symmetric-cores-binary-relations.html#2551" class="Bound">R</a> <a id="2553" class="Symbol">:</a> <a id="2555" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="2564" href="foundation.symmetric-cores-binary-relations.html#2523" class="Bound">l2</a> <a id="2567" href="foundation.symmetric-cores-binary-relations.html#2539" class="Bound">A</a><a id="2568" class="Symbol">)</a>
  <a id="2572" class="Symbol">(</a><a id="2573" href="foundation.symmetric-cores-binary-relations.html#2573" class="Bound">S</a> <a id="2575" class="Symbol">:</a> <a id="2577" href="foundation.symmetric-binary-relations.html#1503" class="Function">Symmetric-Relation</a> <a id="2596" href="foundation.symmetric-cores-binary-relations.html#2526" class="Bound">l3</a> <a id="2599" href="foundation.symmetric-cores-binary-relations.html#2539" class="Bound">A</a><a id="2600" class="Symbol">)</a>
  <a id="2604" class="Keyword">where</a>

  <a id="2613" href="foundation.symmetric-cores-binary-relations.html#2613" class="Function">map-universal-property-symmetric-core-Relation</a> <a id="2660" class="Symbol">:</a>
    <a id="2666" href="foundation.symmetric-binary-relations.html#5752" class="Function">hom-Symmetric-Relation</a> <a id="2689" href="foundation.symmetric-cores-binary-relations.html#2573" class="Bound">S</a> <a id="2691" class="Symbol">(</a><a id="2692" href="foundation.symmetric-cores-binary-relations.html#1944" class="Function">symmetric-core-Relation</a> <a id="2716" href="foundation.symmetric-cores-binary-relations.html#2551" class="Bound">R</a><a id="2717" class="Symbol">)</a> <a id="2719" class="Symbol">→</a>
    <a id="2725" href="foundation.morphisms-binary-relations.html#643" class="Function">hom-Relation</a> <a id="2738" class="Symbol">(</a><a id="2739" href="foundation.symmetric-binary-relations.html#4237" class="Function">relation-Symmetric-Relation</a> <a id="2767" href="foundation.symmetric-cores-binary-relations.html#2573" class="Bound">S</a><a id="2768" class="Symbol">)</a> <a id="2770" href="foundation.symmetric-cores-binary-relations.html#2551" class="Bound">R</a>
  <a id="2774" href="foundation.symmetric-cores-binary-relations.html#2613" class="Function">map-universal-property-symmetric-core-Relation</a> <a id="2821" href="foundation.symmetric-cores-binary-relations.html#2821" class="Bound">f</a> <a id="2823" href="foundation.symmetric-cores-binary-relations.html#2823" class="Bound">x</a> <a id="2825" href="foundation.symmetric-cores-binary-relations.html#2825" class="Bound">y</a> <a id="2827" href="foundation.symmetric-cores-binary-relations.html#2827" class="Bound">s</a> <a id="2829" class="Symbol">=</a>
    <a id="2835" href="foundation.symmetric-cores-binary-relations.html#2131" class="Function">counit-symmetric-core-Relation</a> <a id="2866" href="foundation.symmetric-cores-binary-relations.html#2551" class="Bound">R</a> <a id="2868" class="Symbol">(</a><a id="2869" href="foundation.symmetric-cores-binary-relations.html#2821" class="Bound">f</a> <a id="2871" class="Symbol">(</a><a id="2872" href="foundation.unordered-pairs.html#4836" class="Function">standard-unordered-pair</a> <a id="2896" href="foundation.symmetric-cores-binary-relations.html#2823" class="Bound">x</a> <a id="2898" href="foundation.symmetric-cores-binary-relations.html#2825" class="Bound">y</a><a id="2899" class="Symbol">)</a> <a id="2901" href="foundation.symmetric-cores-binary-relations.html#2827" class="Bound">s</a><a id="2902" class="Symbol">)</a>

  <a id="2907" href="foundation.symmetric-cores-binary-relations.html#2907" class="Function">equiv-universal-property-symmetric-core-Relation</a> <a id="2956" class="Symbol">:</a>
    <a id="2962" href="foundation.symmetric-binary-relations.html#5752" class="Function">hom-Symmetric-Relation</a> <a id="2985" href="foundation.symmetric-cores-binary-relations.html#2573" class="Bound">S</a> <a id="2987" class="Symbol">(</a><a id="2988" href="foundation.symmetric-cores-binary-relations.html#1944" class="Function">symmetric-core-Relation</a> <a id="3012" href="foundation.symmetric-cores-binary-relations.html#2551" class="Bound">R</a><a id="3013" class="Symbol">)</a> <a id="3015" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="3021" href="foundation.morphisms-binary-relations.html#643" class="Function">hom-Relation</a> <a id="3034" class="Symbol">(</a><a id="3035" href="foundation.symmetric-binary-relations.html#4237" class="Function">relation-Symmetric-Relation</a> <a id="3063" href="foundation.symmetric-cores-binary-relations.html#2573" class="Bound">S</a><a id="3064" class="Symbol">)</a> <a id="3066" href="foundation.symmetric-cores-binary-relations.html#2551" class="Bound">R</a>
  <a id="3070" href="foundation.symmetric-cores-binary-relations.html#2907" class="Function">equiv-universal-property-symmetric-core-Relation</a> <a id="3119" class="Symbol">=</a>
    <a id="3125" class="Symbol">(</a> <a id="3127" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a>
      <a id="3154" class="Symbol">(</a> <a id="3156" class="Symbol">λ</a> <a id="3158" href="foundation.symmetric-cores-binary-relations.html#3158" class="Bound">x</a> <a id="3160" class="Symbol">→</a>
        <a id="3170" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a>
          <a id="3201" class="Symbol">(</a> <a id="3203" class="Symbol">λ</a> <a id="3205" href="foundation.symmetric-cores-binary-relations.html#3205" class="Bound">y</a> <a id="3207" class="Symbol">→</a>
            <a id="3221" href="foundation.postcomposition-functions.html#6729" class="Function">equiv-postcomp</a>
              <a id="3250" class="Symbol">(</a> <a id="3252" href="foundation.symmetric-cores-binary-relations.html#2573" class="Bound">S</a> <a id="3254" class="Symbol">(</a><a id="3255" href="foundation.unordered-pairs.html#4836" class="Function">standard-unordered-pair</a> <a id="3279" href="foundation.symmetric-cores-binary-relations.html#3158" class="Bound">x</a> <a id="3281" href="foundation.symmetric-cores-binary-relations.html#3205" class="Bound">y</a><a id="3282" class="Symbol">))</a>
              <a id="3299" class="Symbol">(</a> <a id="3301" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a>
                <a id="3326" class="Symbol">(</a> <a id="3328" href="foundation.symmetric-cores-binary-relations.html#2551" class="Bound">R</a> <a id="3330" class="Symbol">_)</a>
                <a id="3349" class="Symbol">(</a> <a id="3351" href="foundation.unordered-pairs.html#5171" class="Function">compute-other-element-standard-unordered-pair</a> <a id="3397" href="foundation.symmetric-cores-binary-relations.html#3158" class="Bound">x</a> <a id="3399" href="foundation.symmetric-cores-binary-relations.html#3205" class="Bound">y</a>
                  <a id="3419" class="Symbol">(</a> <a id="3421" href="univalent-combinatorics.standard-finite-types.html#5750" class="Function">zero-Fin</a> <a id="3430" class="Number">1</a><a id="3431" class="Symbol">))))))</a> <a id="3438" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
    <a id="3445" class="Symbol">(</a> <a id="3447" href="foundation.unordered-pairs.html#14180" class="Function">equiv-dependent-universal-property-pointed-unordered-pairs</a>
      <a id="3512" class="Symbol">(</a> <a id="3514" class="Symbol">λ</a> <a id="3516" href="foundation.symmetric-cores-binary-relations.html#3516" class="Bound">p</a> <a id="3518" href="foundation.symmetric-cores-binary-relations.html#3518" class="Bound">i</a> <a id="3520" class="Symbol">→</a>
        <a id="3530" href="foundation.symmetric-cores-binary-relations.html#2573" class="Bound">S</a> <a id="3532" href="foundation.symmetric-cores-binary-relations.html#3516" class="Bound">p</a> <a id="3534" class="Symbol">→</a>
        <a id="3544" href="foundation.symmetric-cores-binary-relations.html#2551" class="Bound">R</a> <a id="3546" class="Symbol">(</a><a id="3547" href="foundation.unordered-pairs.html#3321" class="Function">element-unordered-pair</a> <a id="3570" href="foundation.symmetric-cores-binary-relations.html#3516" class="Bound">p</a> <a id="3572" href="foundation.symmetric-cores-binary-relations.html#3518" class="Bound">i</a><a id="3573" class="Symbol">)</a> <a id="3575" class="Symbol">(</a><a id="3576" href="foundation.unordered-pairs.html#3406" class="Function">other-element-unordered-pair</a> <a id="3605" href="foundation.symmetric-cores-binary-relations.html#3516" class="Bound">p</a> <a id="3607" href="foundation.symmetric-cores-binary-relations.html#3518" class="Bound">i</a><a id="3608" class="Symbol">)))</a> <a id="3612" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
    <a id="3619" class="Symbol">(</a> <a id="3621" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a> <a id="3642" class="Symbol">(λ</a> <a id="3645" href="foundation.symmetric-cores-binary-relations.html#3645" class="Bound">p</a> <a id="3647" class="Symbol">→</a> <a id="3649" href="foundation.type-arithmetic-dependent-function-types.html#1522" class="Function">equiv-swap-Π</a><a id="3661" class="Symbol">))</a>

  <a id="3667" href="foundation.symmetric-cores-binary-relations.html#3667" class="Function">universal-property-symmetric-core-Relation</a> <a id="3710" class="Symbol">:</a>
    <a id="3716" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="3725" href="foundation.symmetric-cores-binary-relations.html#2613" class="Function">map-universal-property-symmetric-core-Relation</a>
  <a id="3774" href="foundation.symmetric-cores-binary-relations.html#3667" class="Function">universal-property-symmetric-core-Relation</a> <a id="3817" class="Symbol">=</a>
    <a id="3823" href="foundation-core.equivalences.html#2795" class="Function">is-equiv-map-equiv</a>
      <a id="3848" class="Symbol">(</a> <a id="3850" href="foundation.symmetric-cores-binary-relations.html#2907" class="Function">equiv-universal-property-symmetric-core-Relation</a><a id="3898" class="Symbol">)</a>
</pre>