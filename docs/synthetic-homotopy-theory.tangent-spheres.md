# Tangent spheres

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="synthetic-homotopy-theory.tangent-spheres.html" class="Module">synthetic-homotopy-theory.tangent-spheres</a> <a id="77" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="133" class="Keyword">open</a> <a id="138" class="Keyword">import</a> <a id="145" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="321" class="Keyword">open</a> <a id="326" class="Keyword">import</a> <a id="333" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="354" class="Keyword">open</a> <a id="359" class="Keyword">import</a> <a id="366" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="synthetic-homotopy-theory.cocones-under-spans.html" class="Module">synthetic-homotopy-theory.cocones-under-spans</a>
<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="synthetic-homotopy-theory.mere-spheres.html" class="Module">synthetic-homotopy-theory.mere-spheres</a>
<a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="synthetic-homotopy-theory.pushouts.html" class="Module">synthetic-homotopy-theory.pushouts</a>
<a id="550" class="Keyword">open</a> <a id="555" class="Keyword">import</a> <a id="562" href="synthetic-homotopy-theory.spheres.html" class="Module">synthetic-homotopy-theory.spheres</a>
</pre>
</details>

## Idea

Consider a type `X` and a point `x : X`. We say that `x` **has a tangent
`n`-sphere** if we can construct the following data:

- A [mere sphere](synthetic-homotopy-theory.mere-spheres.md) `T`, which we also
  refer to as the **tangent sphere** of `x`.
- A type `C`, which we call the **complement** of `x`.
- A map `j : T → C` including the tangent sphere into the complement.
- A map `i : C → X` including the complement into the type `X`.
- A [homotopy](foundation-core.homotopies.md) witnessing that the square
  ```text
        j
    T -----> C
    |        |
    |        | i
    ∨      ⌜ ∨
    1 -----> X
        x
  ```
  [commutes](foundation.commuting-squares-of-maps.md), and is a
  [pushout](synthetic-homotopy-theory.pushouts.md).

In other words, a tangent `n`-sphere at a point `x` consistst of a mere sphere
and a complement such that the space `X` can be reconstructed by attaching the
point to the complement via the inclusion of the tangent sphere into the
complement.

## Definitions

### The predicate of having a tangent sphere

<pre class="Agda"><a id="1680" class="Keyword">module</a> <a id="1687" href="synthetic-homotopy-theory.tangent-spheres.html#1687" class="Module">_</a>
  <a id="1691" class="Symbol">{</a><a id="1692" href="synthetic-homotopy-theory.tangent-spheres.html#1692" class="Bound">l</a> <a id="1694" class="Symbol">:</a> <a id="1696" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1701" class="Symbol">}</a> <a id="1703" class="Symbol">(</a><a id="1704" href="synthetic-homotopy-theory.tangent-spheres.html#1704" class="Bound">n</a> <a id="1706" class="Symbol">:</a> <a id="1708" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1709" class="Symbol">)</a> <a id="1711" class="Symbol">{</a><a id="1712" href="synthetic-homotopy-theory.tangent-spheres.html#1712" class="Bound">X</a> <a id="1714" class="Symbol">:</a> <a id="1716" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1719" href="synthetic-homotopy-theory.tangent-spheres.html#1692" class="Bound">l</a><a id="1720" class="Symbol">}</a> <a id="1722" class="Symbol">(</a><a id="1723" href="synthetic-homotopy-theory.tangent-spheres.html#1723" class="Bound">x</a> <a id="1725" class="Symbol">:</a> <a id="1727" href="synthetic-homotopy-theory.tangent-spheres.html#1712" class="Bound">X</a><a id="1728" class="Symbol">)</a>
  <a id="1732" class="Keyword">where</a>

  <a id="1741" href="synthetic-homotopy-theory.tangent-spheres.html#1741" class="Function">has-tangent-sphere</a> <a id="1760" class="Symbol">:</a> <a id="1762" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1765" class="Symbol">(</a><a id="1766" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1771" href="synthetic-homotopy-theory.tangent-spheres.html#1692" class="Bound">l</a><a id="1772" class="Symbol">)</a>
  <a id="1776" href="synthetic-homotopy-theory.tangent-spheres.html#1741" class="Function">has-tangent-sphere</a> <a id="1795" class="Symbol">=</a>
    <a id="1801" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1803" class="Symbol">(</a> <a id="1805" href="synthetic-homotopy-theory.mere-spheres.html#998" class="Function">mere-sphere</a> <a id="1817" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1823" href="synthetic-homotopy-theory.tangent-spheres.html#1704" class="Bound">n</a><a id="1824" class="Symbol">)</a>
      <a id="1832" class="Symbol">(</a> <a id="1834" class="Symbol">λ</a> <a id="1836" href="synthetic-homotopy-theory.tangent-spheres.html#1836" class="Bound">T</a> <a id="1838" class="Symbol">→</a>
        <a id="1848" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1850" class="Symbol">(</a> <a id="1852" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1855" href="synthetic-homotopy-theory.tangent-spheres.html#1692" class="Bound">l</a><a id="1856" class="Symbol">)</a>
          <a id="1868" class="Symbol">(</a> <a id="1870" class="Symbol">λ</a> <a id="1872" href="synthetic-homotopy-theory.tangent-spheres.html#1872" class="Bound">C</a> <a id="1874" class="Symbol">→</a>
            <a id="1888" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1890" class="Symbol">(</a> <a id="1892" href="synthetic-homotopy-theory.mere-spheres.html#1157" class="Function">type-mere-sphere</a> <a id="1909" href="synthetic-homotopy-theory.tangent-spheres.html#1704" class="Bound">n</a> <a id="1911" href="synthetic-homotopy-theory.tangent-spheres.html#1836" class="Bound">T</a> <a id="1913" class="Symbol">→</a> <a id="1915" href="synthetic-homotopy-theory.tangent-spheres.html#1872" class="Bound">C</a><a id="1916" class="Symbol">)</a>
              <a id="1932" class="Symbol">(</a> <a id="1934" class="Symbol">λ</a> <a id="1936" href="synthetic-homotopy-theory.tangent-spheres.html#1936" class="Bound">j</a> <a id="1938" class="Symbol">→</a>
                <a id="1956" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1958" class="Symbol">(</a> <a id="1960" href="synthetic-homotopy-theory.tangent-spheres.html#1872" class="Bound">C</a> <a id="1962" class="Symbol">→</a> <a id="1964" href="synthetic-homotopy-theory.tangent-spheres.html#1712" class="Bound">X</a><a id="1965" class="Symbol">)</a>
                  <a id="1985" class="Symbol">(</a> <a id="1987" class="Symbol">λ</a> <a id="1989" href="synthetic-homotopy-theory.tangent-spheres.html#1989" class="Bound">i</a> <a id="1991" class="Symbol">→</a>
                    <a id="2013" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2015" class="Symbol">(</a> <a id="2017" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
                        <a id="2063" class="Symbol">(</a> <a id="2065" href="synthetic-homotopy-theory.tangent-spheres.html#1936" class="Bound">j</a><a id="2066" class="Symbol">)</a>
                        <a id="2092" class="Symbol">(</a> <a id="2094" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="2107" class="Symbol">(</a><a id="2108" href="synthetic-homotopy-theory.mere-spheres.html#1157" class="Function">type-mere-sphere</a> <a id="2125" href="synthetic-homotopy-theory.tangent-spheres.html#1704" class="Bound">n</a> <a id="2127" href="synthetic-homotopy-theory.tangent-spheres.html#1836" class="Bound">T</a><a id="2128" class="Symbol">))</a>
                        <a id="2155" class="Symbol">(</a> <a id="2157" href="synthetic-homotopy-theory.tangent-spheres.html#1989" class="Bound">i</a><a id="2158" class="Symbol">)</a>
                        <a id="2184" class="Symbol">(</a> <a id="2186" href="foundation.unit-type.html#1422" class="Function">point</a> <a id="2192" href="synthetic-homotopy-theory.tangent-spheres.html#1723" class="Bound">x</a><a id="2193" class="Symbol">))</a>
                      <a id="2218" class="Symbol">(</a> <a id="2220" class="Symbol">λ</a> <a id="2222" href="synthetic-homotopy-theory.tangent-spheres.html#2222" class="Bound">H</a> <a id="2224" class="Symbol">→</a>
                        <a id="2250" href="synthetic-homotopy-theory.pushouts.html#13279" class="Function">is-pushout</a>
                          <a id="2287" class="Symbol">(</a> <a id="2289" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="2302" class="Symbol">(</a><a id="2303" href="synthetic-homotopy-theory.mere-spheres.html#1157" class="Function">type-mere-sphere</a> <a id="2320" href="synthetic-homotopy-theory.tangent-spheres.html#1704" class="Bound">n</a> <a id="2322" href="synthetic-homotopy-theory.tangent-spheres.html#1836" class="Bound">T</a><a id="2323" class="Symbol">))</a>
                          <a id="2352" class="Symbol">(</a> <a id="2354" href="synthetic-homotopy-theory.tangent-spheres.html#1936" class="Bound">j</a><a id="2355" class="Symbol">)</a>
                          <a id="2383" class="Symbol">(</a> <a id="2385" href="foundation.unit-type.html#1422" class="Function">point</a> <a id="2391" href="synthetic-homotopy-theory.tangent-spheres.html#1723" class="Bound">x</a> <a id="2393" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2395" href="synthetic-homotopy-theory.tangent-spheres.html#1989" class="Bound">i</a> <a id="2397" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2399" href="synthetic-homotopy-theory.tangent-spheres.html#2222" class="Bound">H</a><a id="2400" class="Symbol">))))))</a>

<a id="2408" class="Keyword">module</a> <a id="2415" href="synthetic-homotopy-theory.tangent-spheres.html#2415" class="Module">_</a>
  <a id="2419" class="Symbol">{</a><a id="2420" href="synthetic-homotopy-theory.tangent-spheres.html#2420" class="Bound">l</a> <a id="2422" class="Symbol">:</a> <a id="2424" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2429" class="Symbol">}</a> <a id="2431" class="Symbol">(</a><a id="2432" href="synthetic-homotopy-theory.tangent-spheres.html#2432" class="Bound">n</a> <a id="2434" class="Symbol">:</a> <a id="2436" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2437" class="Symbol">)</a> <a id="2439" class="Symbol">{</a><a id="2440" href="synthetic-homotopy-theory.tangent-spheres.html#2440" class="Bound">X</a> <a id="2442" class="Symbol">:</a> <a id="2444" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2447" href="synthetic-homotopy-theory.tangent-spheres.html#2420" class="Bound">l</a><a id="2448" class="Symbol">}</a> <a id="2450" class="Symbol">{</a><a id="2451" href="synthetic-homotopy-theory.tangent-spheres.html#2451" class="Bound">x</a> <a id="2453" class="Symbol">:</a> <a id="2455" href="synthetic-homotopy-theory.tangent-spheres.html#2440" class="Bound">X</a><a id="2456" class="Symbol">}</a> <a id="2458" class="Symbol">(</a><a id="2459" href="synthetic-homotopy-theory.tangent-spheres.html#2459" class="Bound">T</a> <a id="2461" class="Symbol">:</a> <a id="2463" href="synthetic-homotopy-theory.tangent-spheres.html#1741" class="Function">has-tangent-sphere</a> <a id="2482" href="synthetic-homotopy-theory.tangent-spheres.html#2432" class="Bound">n</a> <a id="2484" href="synthetic-homotopy-theory.tangent-spheres.html#2451" class="Bound">x</a><a id="2485" class="Symbol">)</a>
  <a id="2489" class="Keyword">where</a>

  <a id="2498" href="synthetic-homotopy-theory.tangent-spheres.html#2498" class="Function">tangent-sphere-has-tangent-sphere</a> <a id="2532" class="Symbol">:</a> <a id="2534" href="synthetic-homotopy-theory.mere-spheres.html#998" class="Function">mere-sphere</a> <a id="2546" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2552" href="synthetic-homotopy-theory.tangent-spheres.html#2432" class="Bound">n</a>
  <a id="2556" href="synthetic-homotopy-theory.tangent-spheres.html#2498" class="Function">tangent-sphere-has-tangent-sphere</a> <a id="2590" class="Symbol">=</a> <a id="2592" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2596" href="synthetic-homotopy-theory.tangent-spheres.html#2459" class="Bound">T</a>

  <a id="2601" href="synthetic-homotopy-theory.tangent-spheres.html#2601" class="Function">type-tangent-sphere-has-tangent-sphere</a> <a id="2640" class="Symbol">:</a> <a id="2642" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2645" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="2653" href="synthetic-homotopy-theory.tangent-spheres.html#2601" class="Function">type-tangent-sphere-has-tangent-sphere</a> <a id="2692" class="Symbol">=</a>
    <a id="2698" href="synthetic-homotopy-theory.mere-spheres.html#1157" class="Function">type-mere-sphere</a> <a id="2715" href="synthetic-homotopy-theory.tangent-spheres.html#2432" class="Bound">n</a> <a id="2717" href="synthetic-homotopy-theory.tangent-spheres.html#2498" class="Function">tangent-sphere-has-tangent-sphere</a>

  <a id="2754" href="synthetic-homotopy-theory.tangent-spheres.html#2754" class="Function">mere-equiv-tangent-sphere-has-tangent-sphere</a> <a id="2799" class="Symbol">:</a>
    <a id="2805" href="foundation.mere-equivalences.html#960" class="Function">mere-equiv</a> <a id="2816" class="Symbol">(</a><a id="2817" href="synthetic-homotopy-theory.spheres.html#961" class="Function">sphere</a> <a id="2824" href="synthetic-homotopy-theory.tangent-spheres.html#2432" class="Bound">n</a><a id="2825" class="Symbol">)</a> <a id="2827" href="synthetic-homotopy-theory.tangent-spheres.html#2601" class="Function">type-tangent-sphere-has-tangent-sphere</a>
  <a id="2868" href="synthetic-homotopy-theory.tangent-spheres.html#2754" class="Function">mere-equiv-tangent-sphere-has-tangent-sphere</a> <a id="2913" class="Symbol">=</a>
    <a id="2919" href="synthetic-homotopy-theory.mere-spheres.html#1211" class="Function">mere-equiv-mere-sphere</a> <a id="2942" href="synthetic-homotopy-theory.tangent-spheres.html#2432" class="Bound">n</a> <a id="2944" href="synthetic-homotopy-theory.tangent-spheres.html#2498" class="Function">tangent-sphere-has-tangent-sphere</a>

  <a id="2981" href="synthetic-homotopy-theory.tangent-spheres.html#2981" class="Function">complement-has-tangent-sphere</a> <a id="3011" class="Symbol">:</a> <a id="3013" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3016" href="synthetic-homotopy-theory.tangent-spheres.html#2420" class="Bound">l</a>
  <a id="3020" href="synthetic-homotopy-theory.tangent-spheres.html#2981" class="Function">complement-has-tangent-sphere</a> <a id="3050" class="Symbol">=</a> <a id="3052" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3056" class="Symbol">(</a><a id="3057" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3061" href="synthetic-homotopy-theory.tangent-spheres.html#2459" class="Bound">T</a><a id="3062" class="Symbol">)</a>

  <a id="3067" href="synthetic-homotopy-theory.tangent-spheres.html#3067" class="Function">inclusion-tangent-sphere-has-tangent-sphere</a> <a id="3111" class="Symbol">:</a>
    <a id="3117" href="synthetic-homotopy-theory.tangent-spheres.html#2601" class="Function">type-tangent-sphere-has-tangent-sphere</a> <a id="3156" class="Symbol">→</a> <a id="3158" href="synthetic-homotopy-theory.tangent-spheres.html#2981" class="Function">complement-has-tangent-sphere</a>
  <a id="3190" href="synthetic-homotopy-theory.tangent-spheres.html#3067" class="Function">inclusion-tangent-sphere-has-tangent-sphere</a> <a id="3234" class="Symbol">=</a> <a id="3236" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3240" class="Symbol">(</a><a id="3241" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3245" class="Symbol">(</a><a id="3246" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3250" href="synthetic-homotopy-theory.tangent-spheres.html#2459" class="Bound">T</a><a id="3251" class="Symbol">))</a>

  <a id="3257" href="synthetic-homotopy-theory.tangent-spheres.html#3257" class="Function">inclusion-complement-has-tangent-sphere</a> <a id="3297" class="Symbol">:</a>
    <a id="3303" href="synthetic-homotopy-theory.tangent-spheres.html#2981" class="Function">complement-has-tangent-sphere</a> <a id="3333" class="Symbol">→</a> <a id="3335" href="synthetic-homotopy-theory.tangent-spheres.html#2440" class="Bound">X</a>
  <a id="3339" href="synthetic-homotopy-theory.tangent-spheres.html#3257" class="Function">inclusion-complement-has-tangent-sphere</a> <a id="3379" class="Symbol">=</a> <a id="3381" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3385" class="Symbol">(</a><a id="3386" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3390" class="Symbol">(</a><a id="3391" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3395" class="Symbol">(</a><a id="3396" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3400" href="synthetic-homotopy-theory.tangent-spheres.html#2459" class="Bound">T</a><a id="3401" class="Symbol">)))</a>

  <a id="3408" href="synthetic-homotopy-theory.tangent-spheres.html#3408" class="Function">coherence-square-has-tangent-sphere</a> <a id="3444" class="Symbol">:</a>
    <a id="3450" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="3478" class="Symbol">(</a> <a id="3480" href="synthetic-homotopy-theory.tangent-spheres.html#3067" class="Function">inclusion-tangent-sphere-has-tangent-sphere</a><a id="3523" class="Symbol">)</a>
      <a id="3531" class="Symbol">(</a> <a id="3533" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="3546" href="synthetic-homotopy-theory.tangent-spheres.html#2601" class="Function">type-tangent-sphere-has-tangent-sphere</a><a id="3584" class="Symbol">)</a>
      <a id="3592" class="Symbol">(</a> <a id="3594" href="synthetic-homotopy-theory.tangent-spheres.html#3257" class="Function">inclusion-complement-has-tangent-sphere</a><a id="3633" class="Symbol">)</a>
      <a id="3641" class="Symbol">(</a> <a id="3643" href="foundation.unit-type.html#1422" class="Function">point</a> <a id="3649" href="synthetic-homotopy-theory.tangent-spheres.html#2451" class="Bound">x</a><a id="3650" class="Symbol">)</a>
  <a id="3654" href="synthetic-homotopy-theory.tangent-spheres.html#3408" class="Function">coherence-square-has-tangent-sphere</a> <a id="3690" class="Symbol">=</a>
    <a id="3696" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3700" class="Symbol">(</a><a id="3701" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3705" class="Symbol">(</a><a id="3706" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3710" class="Symbol">(</a><a id="3711" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3715" class="Symbol">(</a><a id="3716" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3720" href="synthetic-homotopy-theory.tangent-spheres.html#2459" class="Bound">T</a><a id="3721" class="Symbol">))))</a>

  <a id="3729" href="synthetic-homotopy-theory.tangent-spheres.html#3729" class="Function">cocone-has-tangent-sphere</a> <a id="3755" class="Symbol">:</a>
    <a id="3761" href="synthetic-homotopy-theory.cocones-under-spans.html#1497" class="Function">cocone</a>
      <a id="3774" class="Symbol">(</a> <a id="3776" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="3789" href="synthetic-homotopy-theory.tangent-spheres.html#2601" class="Function">type-tangent-sphere-has-tangent-sphere</a><a id="3827" class="Symbol">)</a>
      <a id="3835" class="Symbol">(</a> <a id="3837" href="synthetic-homotopy-theory.tangent-spheres.html#3067" class="Function">inclusion-tangent-sphere-has-tangent-sphere</a><a id="3880" class="Symbol">)</a>
      <a id="3888" class="Symbol">(</a> <a id="3890" href="synthetic-homotopy-theory.tangent-spheres.html#2440" class="Bound">X</a><a id="3891" class="Symbol">)</a>
  <a id="3895" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3899" href="synthetic-homotopy-theory.tangent-spheres.html#3729" class="Function">cocone-has-tangent-sphere</a> <a id="3925" class="Symbol">=</a> <a id="3927" href="foundation.unit-type.html#1422" class="Function">point</a> <a id="3933" href="synthetic-homotopy-theory.tangent-spheres.html#2451" class="Bound">x</a>
  <a id="3937" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3941" class="Symbol">(</a><a id="3942" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3946" href="synthetic-homotopy-theory.tangent-spheres.html#3729" class="Function">cocone-has-tangent-sphere</a><a id="3971" class="Symbol">)</a> <a id="3973" class="Symbol">=</a> <a id="3975" href="synthetic-homotopy-theory.tangent-spheres.html#3257" class="Function">inclusion-complement-has-tangent-sphere</a>
  <a id="4017" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4021" class="Symbol">(</a><a id="4022" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4026" href="synthetic-homotopy-theory.tangent-spheres.html#3729" class="Function">cocone-has-tangent-sphere</a><a id="4051" class="Symbol">)</a> <a id="4053" class="Symbol">=</a> <a id="4055" href="synthetic-homotopy-theory.tangent-spheres.html#3408" class="Function">coherence-square-has-tangent-sphere</a>

  <a id="4094" href="synthetic-homotopy-theory.tangent-spheres.html#4094" class="Function">is-pushout-has-tangent-sphere</a> <a id="4124" class="Symbol">:</a>
    <a id="4130" href="synthetic-homotopy-theory.pushouts.html#13279" class="Function">is-pushout</a>
      <a id="4147" class="Symbol">(</a> <a id="4149" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="4162" href="synthetic-homotopy-theory.tangent-spheres.html#2601" class="Function">type-tangent-sphere-has-tangent-sphere</a><a id="4200" class="Symbol">)</a>
      <a id="4208" class="Symbol">(</a> <a id="4210" href="synthetic-homotopy-theory.tangent-spheres.html#3067" class="Function">inclusion-tangent-sphere-has-tangent-sphere</a><a id="4253" class="Symbol">)</a>
      <a id="4261" class="Symbol">(</a> <a id="4263" href="synthetic-homotopy-theory.tangent-spheres.html#3729" class="Function">cocone-has-tangent-sphere</a><a id="4288" class="Symbol">)</a>
  <a id="4292" href="synthetic-homotopy-theory.tangent-spheres.html#4094" class="Function">is-pushout-has-tangent-sphere</a> <a id="4322" class="Symbol">=</a>
    <a id="4328" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4332" class="Symbol">(</a><a id="4333" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4337" class="Symbol">(</a><a id="4338" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4342" class="Symbol">(</a><a id="4343" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4347" class="Symbol">(</a><a id="4348" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4352" href="synthetic-homotopy-theory.tangent-spheres.html#2459" class="Bound">T</a><a id="4353" class="Symbol">))))</a>
</pre>