# The sharp modality

<pre class="Agda"><a id="31" class="Symbol">{-#</a> <a id="35" class="Keyword">OPTIONS</a> <a id="43" class="Pragma">--cohesion</a> <a id="54" class="Pragma">--flat-split</a> <a id="67" class="Symbol">#-}</a>

<a id="72" class="Keyword">module</a> <a id="79" href="modal-type-theory.sharp-modality.html" class="Module">modal-type-theory.sharp-modality</a> <a id="112" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation.locally-small-types.html" class="Module">foundation.locally-small-types</a>
<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="464" class="Keyword">open</a> <a id="469" class="Keyword">import</a> <a id="476" href="orthogonal-factorization-systems.locally-small-modal-operators.html" class="Module">orthogonal-factorization-systems.locally-small-modal-operators</a>
<a id="539" class="Keyword">open</a> <a id="544" class="Keyword">import</a> <a id="551" href="orthogonal-factorization-systems.modal-induction.html" class="Module">orthogonal-factorization-systems.modal-induction</a>
<a id="600" class="Keyword">open</a> <a id="605" class="Keyword">import</a> <a id="612" href="orthogonal-factorization-systems.modal-subuniverse-induction.html" class="Module">orthogonal-factorization-systems.modal-subuniverse-induction</a>
</pre>
</details>

## Idea

The {{#concept "sharp modality" Agda=♯}} `♯` is an axiomatized
[monadic modality](orthogonal-factorization-systems.higher-modalities.md) that
we postulate as a right adjoint to the
[flat modality](modal-type-theory.flat-modality.md).

In this file, we postulate that `♯` is a
[modal operator](orthogonal-factorization-systems.modal-operators.md) with a
crisp elimination principle and a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md).

- In the file about
  [sharp codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we
  currently postulate that the [subuniverse](foundation.subuniverses.md) of
  sharp modal types has appropriate closure properties.
- In [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md), we
  postulate that it has the appropriate relation to the flat modality, making it
  a lex modality.

Please note that there is some redundancy between the postulated axioms, and
that they are likely to change in the future.

## Postulates

<pre class="Agda"><a id="1725" class="Keyword">postulate</a>
  <a id="♯"></a><a id="1737" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="1739" class="Symbol">:</a> <a id="1741" class="Symbol">{</a><a id="1742" href="modal-type-theory.sharp-modality.html#1742" class="Bound">l</a> <a id="1744" class="Symbol">:</a> <a id="1746" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1751" class="Symbol">}</a> <a id="1753" class="Symbol">(</a><a id="1754" href="modal-type-theory.sharp-modality.html#1754" class="Bound">A</a> <a id="1756" class="Symbol">:</a> <a id="1758" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1761" href="modal-type-theory.sharp-modality.html#1742" class="Bound">l</a><a id="1762" class="Symbol">)</a> <a id="1764" class="Symbol">→</a> <a id="1766" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1769" href="modal-type-theory.sharp-modality.html#1742" class="Bound">l</a>

  <a id="unit-sharp"></a><a id="1774" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="1785" class="Symbol">:</a> <a id="1787" class="Symbol">{</a><a id="1788" href="modal-type-theory.sharp-modality.html#1788" class="Bound">l</a> <a id="1790" class="Symbol">:</a> <a id="1792" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1797" class="Symbol">}</a> <a id="1799" class="Symbol">{</a><a id="1800" href="modal-type-theory.sharp-modality.html#1800" class="Bound">A</a> <a id="1802" class="Symbol">:</a> <a id="1804" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1807" href="modal-type-theory.sharp-modality.html#1788" class="Bound">l</a><a id="1808" class="Symbol">}</a> <a id="1810" class="Symbol">→</a> <a id="1812" href="modal-type-theory.sharp-modality.html#1800" class="Bound">A</a> <a id="1814" class="Symbol">→</a> <a id="1816" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="1818" href="modal-type-theory.sharp-modality.html#1800" class="Bound">A</a>

<a id="sharp"></a><a id="1821" href="modal-type-theory.sharp-modality.html#1821" class="Function">sharp</a> <a id="1827" class="Symbol">:</a> <a id="1829" class="Symbol">{</a><a id="1830" href="modal-type-theory.sharp-modality.html#1830" class="Bound">l</a> <a id="1832" class="Symbol">:</a> <a id="1834" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1839" class="Symbol">}</a> <a id="1841" class="Symbol">(</a><a id="1842" href="modal-type-theory.sharp-modality.html#1842" class="Bound">A</a> <a id="1844" class="Symbol">:</a> <a id="1846" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1849" href="modal-type-theory.sharp-modality.html#1830" class="Bound">l</a><a id="1850" class="Symbol">)</a> <a id="1852" class="Symbol">→</a> <a id="1854" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1857" href="modal-type-theory.sharp-modality.html#1830" class="Bound">l</a>
<a id="1859" href="modal-type-theory.sharp-modality.html#1821" class="Function">sharp</a> <a id="1865" class="Symbol">=</a> <a id="1867" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a>
</pre>
### Crisp elimination for the sharp modality

Given a crisp element `x :: ♯ A` we recover an element of `A`. We postulate that
this construction is a crisp
[coherent inverse](foundation-core.coherently-invertible-maps.md) to the sharp
unit.

<pre class="Agda"><a id="2124" class="Keyword">postulate</a>
  <a id="crisp-elim-sharp"></a><a id="2136" href="modal-type-theory.sharp-modality.html#2136" class="Postulate">crisp-elim-sharp</a> <a id="2153" class="Symbol">:</a>
    <a id="2159" class="Symbol">{@</a>♭ <a id="2163" href="modal-type-theory.sharp-modality.html#2163" class="Bound">l</a> <a id="2165" class="Symbol">:</a> <a id="2167" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2172" class="Symbol">}</a> <a id="2174" class="Symbol">{@</a>♭ <a id="2178" href="modal-type-theory.sharp-modality.html#2178" class="Bound">A</a> <a id="2180" class="Symbol">:</a> <a id="2182" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2185" href="modal-type-theory.sharp-modality.html#2163" class="Bound">l</a><a id="2186" class="Symbol">}</a> <a id="2188" class="Symbol">→</a> <a id="2190" class="Symbol">@</a>♭ <a id="2193" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="2195" href="modal-type-theory.sharp-modality.html#2178" class="Bound">A</a> <a id="2197" class="Symbol">→</a> <a id="2199" href="modal-type-theory.sharp-modality.html#2178" class="Bound">A</a>

  <a id="compute-crisp-elim-sharp"></a><a id="2204" href="modal-type-theory.sharp-modality.html#2204" class="Postulate">compute-crisp-elim-sharp</a> <a id="2229" class="Symbol">:</a>
    <a id="2235" class="Symbol">{@</a>♭ <a id="2239" href="modal-type-theory.sharp-modality.html#2239" class="Bound">l</a> <a id="2241" class="Symbol">:</a> <a id="2243" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2248" class="Symbol">}</a> <a id="2250" class="Symbol">{@</a>♭ <a id="2254" href="modal-type-theory.sharp-modality.html#2254" class="Bound">A</a> <a id="2256" class="Symbol">:</a> <a id="2258" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2261" href="modal-type-theory.sharp-modality.html#2239" class="Bound">l</a><a id="2262" class="Symbol">}</a> <a id="2264" class="Symbol">(@</a>♭ <a id="2268" href="modal-type-theory.sharp-modality.html#2268" class="Bound">x</a> <a id="2270" class="Symbol">:</a> <a id="2272" href="modal-type-theory.sharp-modality.html#2254" class="Bound">A</a><a id="2273" class="Symbol">)</a> <a id="2275" class="Symbol">→</a>
    <a id="2281" href="modal-type-theory.sharp-modality.html#2136" class="Postulate">crisp-elim-sharp</a> <a id="2298" class="Symbol">(</a><a id="2299" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="2310" href="modal-type-theory.sharp-modality.html#2268" class="Bound">x</a><a id="2311" class="Symbol">)</a> <a id="2313" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2315" href="modal-type-theory.sharp-modality.html#2268" class="Bound">x</a>

  <a id="uniqueness-crisp-elim-sharp"></a><a id="2320" href="modal-type-theory.sharp-modality.html#2320" class="Postulate">uniqueness-crisp-elim-sharp</a> <a id="2348" class="Symbol">:</a>
    <a id="2354" class="Symbol">{@</a>♭ <a id="2358" href="modal-type-theory.sharp-modality.html#2358" class="Bound">l</a> <a id="2360" class="Symbol">:</a> <a id="2362" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2367" class="Symbol">}</a> <a id="2369" class="Symbol">{@</a>♭ <a id="2373" href="modal-type-theory.sharp-modality.html#2373" class="Bound">A</a> <a id="2375" class="Symbol">:</a> <a id="2377" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2380" href="modal-type-theory.sharp-modality.html#2358" class="Bound">l</a><a id="2381" class="Symbol">}</a> <a id="2383" class="Symbol">(@</a>♭ <a id="2387" href="modal-type-theory.sharp-modality.html#2387" class="Bound">x</a> <a id="2389" class="Symbol">:</a> <a id="2391" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="2393" href="modal-type-theory.sharp-modality.html#2373" class="Bound">A</a><a id="2394" class="Symbol">)</a> <a id="2396" class="Symbol">→</a>
    <a id="2402" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="2413" class="Symbol">(</a><a id="2414" href="modal-type-theory.sharp-modality.html#2136" class="Postulate">crisp-elim-sharp</a> <a id="2431" href="modal-type-theory.sharp-modality.html#2387" class="Bound">x</a><a id="2432" class="Symbol">)</a> <a id="2434" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2436" href="modal-type-theory.sharp-modality.html#2387" class="Bound">x</a>

  <a id="coherence-uniqueness-crisp-elim-sharp"></a><a id="2441" href="modal-type-theory.sharp-modality.html#2441" class="Postulate">coherence-uniqueness-crisp-elim-sharp</a> <a id="2479" class="Symbol">:</a>
    <a id="2485" class="Symbol">{@</a>♭ <a id="2489" href="modal-type-theory.sharp-modality.html#2489" class="Bound">l</a> <a id="2491" class="Symbol">:</a> <a id="2493" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2498" class="Symbol">}</a> <a id="2500" class="Symbol">{@</a>♭ <a id="2504" href="modal-type-theory.sharp-modality.html#2504" class="Bound">A</a> <a id="2506" class="Symbol">:</a> <a id="2508" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2511" href="modal-type-theory.sharp-modality.html#2489" class="Bound">l</a><a id="2512" class="Symbol">}</a> <a id="2514" class="Symbol">(@</a>♭ <a id="2518" href="modal-type-theory.sharp-modality.html#2518" class="Bound">x</a> <a id="2520" class="Symbol">:</a> <a id="2522" href="modal-type-theory.sharp-modality.html#2504" class="Bound">A</a><a id="2523" class="Symbol">)</a> <a id="2525" class="Symbol">→</a>
    <a id="2531" class="Symbol">(</a> <a id="2533" href="modal-type-theory.sharp-modality.html#2320" class="Postulate">uniqueness-crisp-elim-sharp</a> <a id="2561" class="Symbol">(</a><a id="2562" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="2573" href="modal-type-theory.sharp-modality.html#2518" class="Bound">x</a><a id="2574" class="Symbol">))</a> <a id="2577" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2583" class="Symbol">(</a> <a id="2585" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="2588" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="2599" class="Symbol">(</a><a id="2600" href="modal-type-theory.sharp-modality.html#2204" class="Postulate">compute-crisp-elim-sharp</a> <a id="2625" href="modal-type-theory.sharp-modality.html#2518" class="Bound">x</a><a id="2626" class="Symbol">))</a>
</pre>
**Rewriting.** In the future we may enable rewrite rules for the computation and
uniqueness property of the crisp elimination principle for the sharp modality.

```text
  {-# REWRITE compute-crisp-elim-sharp uniqueness-crisp-elim-sharp #-}
```

### Crisp induction for the sharp modality

The
{{#concept "crisp induction principle" Disambiguation="for the sharp modality" Agda=crisp-ind-sharp}}
for the sharp modality is a crisp version of the principle that sharp codiscrete
types are local at the flat counit.

<pre class="Agda"><a id="3155" class="Keyword">postulate</a>
  <a id="crisp-ind-sharp"></a><a id="3167" href="modal-type-theory.sharp-modality.html#3167" class="Postulate">crisp-ind-sharp</a> <a id="3183" class="Symbol">:</a>
    <a id="3189" class="Symbol">{@</a>♭ <a id="3193" href="modal-type-theory.sharp-modality.html#3193" class="Bound">l1</a> <a id="3196" class="Symbol">:</a> <a id="3198" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3203" class="Symbol">}</a> <a id="3205" class="Symbol">{</a><a id="3206" href="modal-type-theory.sharp-modality.html#3206" class="Bound">l2</a> <a id="3209" class="Symbol">:</a> <a id="3211" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3216" class="Symbol">}</a> <a id="3218" class="Symbol">{@</a>♭ <a id="3222" href="modal-type-theory.sharp-modality.html#3222" class="Bound">A</a> <a id="3224" class="Symbol">:</a> <a id="3226" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3229" href="modal-type-theory.sharp-modality.html#3193" class="Bound">l1</a><a id="3231" class="Symbol">}</a> <a id="3233" class="Symbol">(</a><a id="3234" href="modal-type-theory.sharp-modality.html#3234" class="Bound">C</a> <a id="3236" class="Symbol">:</a> <a id="3238" href="modal-type-theory.sharp-modality.html#3222" class="Bound">A</a> <a id="3240" class="Symbol">→</a> <a id="3242" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3245" href="modal-type-theory.sharp-modality.html#3206" class="Bound">l2</a><a id="3247" class="Symbol">)</a> <a id="3249" class="Symbol">→</a>
    <a id="3255" class="Symbol">((@</a>♭ <a id="3260" href="modal-type-theory.sharp-modality.html#3260" class="Bound">x</a> <a id="3262" class="Symbol">:</a> <a id="3264" href="modal-type-theory.sharp-modality.html#3222" class="Bound">A</a><a id="3265" class="Symbol">)</a> <a id="3267" class="Symbol">→</a> <a id="3269" href="modal-type-theory.sharp-modality.html#3234" class="Bound">C</a> <a id="3271" href="modal-type-theory.sharp-modality.html#3260" class="Bound">x</a><a id="3272" class="Symbol">)</a> <a id="3274" class="Symbol">→</a> <a id="3276" class="Symbol">(</a><a id="3277" href="modal-type-theory.sharp-modality.html#3277" class="Bound">x</a> <a id="3279" class="Symbol">:</a> <a id="3281" href="modal-type-theory.sharp-modality.html#3222" class="Bound">A</a><a id="3282" class="Symbol">)</a> <a id="3284" class="Symbol">→</a> <a id="3286" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="3288" class="Symbol">(</a><a id="3289" href="modal-type-theory.sharp-modality.html#3234" class="Bound">C</a> <a id="3291" href="modal-type-theory.sharp-modality.html#3277" class="Bound">x</a><a id="3292" class="Symbol">)</a>

  <a id="compute-crisp-ind-sharp"></a><a id="3297" href="modal-type-theory.sharp-modality.html#3297" class="Postulate">compute-crisp-ind-sharp</a> <a id="3321" class="Symbol">:</a>
    <a id="3327" class="Symbol">{@</a>♭ <a id="3331" href="modal-type-theory.sharp-modality.html#3331" class="Bound">l1</a> <a id="3334" class="Symbol">:</a> <a id="3336" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3341" class="Symbol">}</a> <a id="3343" class="Symbol">{</a><a id="3344" href="modal-type-theory.sharp-modality.html#3344" class="Bound">l2</a> <a id="3347" class="Symbol">:</a> <a id="3349" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3354" class="Symbol">}</a> <a id="3356" class="Symbol">{@</a>♭ <a id="3360" href="modal-type-theory.sharp-modality.html#3360" class="Bound">A</a> <a id="3362" class="Symbol">:</a> <a id="3364" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3367" href="modal-type-theory.sharp-modality.html#3331" class="Bound">l1</a><a id="3369" class="Symbol">}</a> <a id="3371" class="Symbol">(</a><a id="3372" href="modal-type-theory.sharp-modality.html#3372" class="Bound">C</a> <a id="3374" class="Symbol">:</a> <a id="3376" href="modal-type-theory.sharp-modality.html#3360" class="Bound">A</a> <a id="3378" class="Symbol">→</a> <a id="3380" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3383" href="modal-type-theory.sharp-modality.html#3344" class="Bound">l2</a><a id="3385" class="Symbol">)</a>
    <a id="3391" class="Symbol">(</a><a id="3392" href="modal-type-theory.sharp-modality.html#3392" class="Bound">f</a> <a id="3394" class="Symbol">:</a> <a id="3396" class="Symbol">(@</a>♭ <a id="3400" href="modal-type-theory.sharp-modality.html#3400" class="Bound">x</a> <a id="3402" class="Symbol">:</a> <a id="3404" href="modal-type-theory.sharp-modality.html#3360" class="Bound">A</a><a id="3405" class="Symbol">)</a> <a id="3407" class="Symbol">→</a> <a id="3409" href="modal-type-theory.sharp-modality.html#3372" class="Bound">C</a> <a id="3411" href="modal-type-theory.sharp-modality.html#3400" class="Bound">x</a><a id="3412" class="Symbol">)</a> <a id="3414" class="Symbol">→</a>
    <a id="3420" class="Symbol">(@</a>♭ <a id="3424" href="modal-type-theory.sharp-modality.html#3424" class="Bound">x</a> <a id="3426" class="Symbol">:</a> <a id="3428" href="modal-type-theory.sharp-modality.html#3360" class="Bound">A</a><a id="3429" class="Symbol">)</a> <a id="3431" class="Symbol">→</a> <a id="3433" href="modal-type-theory.sharp-modality.html#3167" class="Postulate">crisp-ind-sharp</a> <a id="3449" href="modal-type-theory.sharp-modality.html#3372" class="Bound">C</a> <a id="3451" href="modal-type-theory.sharp-modality.html#3392" class="Bound">f</a> <a id="3453" href="modal-type-theory.sharp-modality.html#3424" class="Bound">x</a> <a id="3455" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3457" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="3468" class="Symbol">(</a><a id="3469" href="modal-type-theory.sharp-modality.html#3392" class="Bound">f</a> <a id="3471" href="modal-type-theory.sharp-modality.html#3424" class="Bound">x</a><a id="3472" class="Symbol">)</a>
</pre>
**Rewriting.** In the future, we may enable a rewriting for the computation rule
of the crisp induction principle for the sharp modality.

```text
  {-# REWRITE compute-crisp-ind-sharp #-}
```

### Modal induction for the sharp modality

We postulate that sharp satisfies a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md)
below.

**Note.** It should also be possible to construct it from the more general
`pointwise-sharp` considered below, but we leave this for future work.

<pre class="Agda"><a id="3997" class="Keyword">postulate</a>
  <a id="ind-sharp"></a><a id="4009" href="modal-type-theory.sharp-modality.html#4009" class="Postulate">ind-sharp</a> <a id="4019" class="Symbol">:</a>
    <a id="4025" class="Symbol">{</a><a id="4026" href="modal-type-theory.sharp-modality.html#4026" class="Bound">l1</a> <a id="4029" href="modal-type-theory.sharp-modality.html#4029" class="Bound">l2</a> <a id="4032" class="Symbol">:</a> <a id="4034" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4039" class="Symbol">}</a> <a id="4041" class="Symbol">{</a><a id="4042" href="modal-type-theory.sharp-modality.html#4042" class="Bound">A</a> <a id="4044" class="Symbol">:</a> <a id="4046" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4049" href="modal-type-theory.sharp-modality.html#4026" class="Bound">l1</a><a id="4051" class="Symbol">}</a> <a id="4053" class="Symbol">(</a><a id="4054" href="modal-type-theory.sharp-modality.html#4054" class="Bound">C</a> <a id="4056" class="Symbol">:</a> <a id="4058" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="4060" href="modal-type-theory.sharp-modality.html#4042" class="Bound">A</a> <a id="4062" class="Symbol">→</a> <a id="4064" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4067" href="modal-type-theory.sharp-modality.html#4029" class="Bound">l2</a><a id="4069" class="Symbol">)</a> <a id="4071" class="Symbol">→</a>
    <a id="4077" class="Symbol">((</a><a id="4079" href="modal-type-theory.sharp-modality.html#4079" class="Bound">x</a> <a id="4081" class="Symbol">:</a> <a id="4083" href="modal-type-theory.sharp-modality.html#4042" class="Bound">A</a><a id="4084" class="Symbol">)</a> <a id="4086" class="Symbol">→</a> <a id="4088" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="4090" class="Symbol">(</a><a id="4091" href="modal-type-theory.sharp-modality.html#4054" class="Bound">C</a> <a id="4093" class="Symbol">(</a><a id="4094" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="4105" href="modal-type-theory.sharp-modality.html#4079" class="Bound">x</a><a id="4106" class="Symbol">)))</a> <a id="4110" class="Symbol">→</a>
    <a id="4116" class="Symbol">(</a><a id="4117" href="modal-type-theory.sharp-modality.html#4117" class="Bound">x</a> <a id="4119" class="Symbol">:</a> <a id="4121" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="4123" href="modal-type-theory.sharp-modality.html#4042" class="Bound">A</a><a id="4124" class="Symbol">)</a> <a id="4126" class="Symbol">→</a> <a id="4128" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="4130" class="Symbol">(</a><a id="4131" href="modal-type-theory.sharp-modality.html#4054" class="Bound">C</a> <a id="4133" href="modal-type-theory.sharp-modality.html#4117" class="Bound">x</a><a id="4134" class="Symbol">)</a>

  <a id="compute-ind-sharp"></a><a id="4139" href="modal-type-theory.sharp-modality.html#4139" class="Postulate">compute-ind-sharp</a> <a id="4157" class="Symbol">:</a>
    <a id="4163" class="Symbol">{</a><a id="4164" href="modal-type-theory.sharp-modality.html#4164" class="Bound">l1</a> <a id="4167" href="modal-type-theory.sharp-modality.html#4167" class="Bound">l2</a> <a id="4170" class="Symbol">:</a> <a id="4172" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4177" class="Symbol">}</a> <a id="4179" class="Symbol">{</a><a id="4180" href="modal-type-theory.sharp-modality.html#4180" class="Bound">A</a> <a id="4182" class="Symbol">:</a> <a id="4184" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4187" href="modal-type-theory.sharp-modality.html#4164" class="Bound">l1</a><a id="4189" class="Symbol">}</a> <a id="4191" class="Symbol">(</a><a id="4192" href="modal-type-theory.sharp-modality.html#4192" class="Bound">C</a> <a id="4194" class="Symbol">:</a> <a id="4196" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="4198" href="modal-type-theory.sharp-modality.html#4180" class="Bound">A</a> <a id="4200" class="Symbol">→</a> <a id="4202" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4205" href="modal-type-theory.sharp-modality.html#4167" class="Bound">l2</a><a id="4207" class="Symbol">)</a>
    <a id="4213" class="Symbol">(</a><a id="4214" href="modal-type-theory.sharp-modality.html#4214" class="Bound">f</a> <a id="4216" class="Symbol">:</a> <a id="4218" class="Symbol">(</a><a id="4219" href="modal-type-theory.sharp-modality.html#4219" class="Bound">x</a> <a id="4221" class="Symbol">:</a> <a id="4223" href="modal-type-theory.sharp-modality.html#4180" class="Bound">A</a><a id="4224" class="Symbol">)</a> <a id="4226" class="Symbol">→</a> <a id="4228" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="4230" class="Symbol">(</a><a id="4231" href="modal-type-theory.sharp-modality.html#4192" class="Bound">C</a> <a id="4233" class="Symbol">(</a><a id="4234" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="4245" href="modal-type-theory.sharp-modality.html#4219" class="Bound">x</a><a id="4246" class="Symbol">)))</a> <a id="4250" class="Symbol">→</a>
    <a id="4256" href="modal-type-theory.sharp-modality.html#4009" class="Postulate">ind-sharp</a> <a id="4266" href="modal-type-theory.sharp-modality.html#4192" class="Bound">C</a> <a id="4268" href="modal-type-theory.sharp-modality.html#4214" class="Bound">f</a> <a id="4270" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4272" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="4283" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="4285" href="modal-type-theory.sharp-modality.html#4214" class="Bound">f</a>
</pre>
### The sharp modality's action on "pointwise" type families

**TODO.** This section consists entirely of unfinished work that is not
typechecked as part of the library. This code is included as notes for future
work.

```text
postulate
  pointwise-sharp :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} → (@♭ A → UU l2) → A → UU l2
```

```text
postulate
  unit-pointwise-sharp :
    {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level}
    {B : @♭ A → UU l2} (a : (@♭ x : A) → B x) →
    (x : A) → pointwise-sharp B x

  elim-pointwise-sharp :
    {@♭ l1 l2 : Level} {@♭ A : UU l1} {B : @♭ A → UU l2}
    (f : (@♭ x : A) → pointwise-sharp B x) → (@♭ x : A) → B x

  compute-pointwise-sharp :
    {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level}
    (B : A → UU l2) (x : A) → pointwise-sharp (λ a → B a) x ＝ ♯ (B x)

  {-# REWRITE compute-pointwise-sharp #-}

  compute-unit-pointwise-sharp :
    {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level}
    {B : @♭ A → UU l2} (f : (@♭ x : A) → B x)
    (@♭ x : A) → unit-pointwise-sharp f x ＝ unit-sharp (f x)

  -- {-# REWRITE compute-unit-pointwise-sharp #-}

syntax elim-pointwise-sharp (λ γ → a) ctx = let♯ γ ::= ctx in♯ a ↓↓♯
```

**Warning:** When normalizing `λ B x → unit-pointwise-sharp f x`, the rewrite
`compute-unit-pointwise-sharp` will fire turning it into `unit-sharp (f x)`,
which is ill-typed on cohesive `x : A` (and the typechecker complains).
{{#cite DavidJaz/Cohesion}} (May be outdated info)

```text
postulate
  compute-elim-pointwise-sharp :
    {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
    (@♭ f : (@♭ x : A) → pointwise-sharp B x)
    (@♭ x : A) → elim-pointwise-sharp f x ＝ crisp-elim-sharp (f x)

  {-# REWRITE compute-elim-pointwise-sharp #-}
```

#### Uncrispening contexts

```text
record
  context-uncrisp-sharp
  {@♭ l1 l2 : Level} {@♭ A : UU l1} : UU (lsuc (l1 ⊔ l2))
  where
  constructor ctx
  field
    ᶜB : A → UU l2
    ᶜf : (@♭ x : A) → ♯ (ᶜB x)
    ᶜa : A

open context-uncrisp-sharp

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  uncrisp-sharp : (B : A → UU l2) (f : (@♭ x : A) → ♯ (B x)) → (x : A) → ♯ (B x)
  uncrisp-sharp B f x =
    unit-pointwise-sharp (λ γ → crisp-elim-sharp ((ᶜf γ) (ᶜa γ))) (ctx B f x)

  compute-uncrisp-sharp :
    (@♭ B : A → UU l2) (@♭ f : (@♭ x : A) → ♯ (B x)) (@♭ x : A) →
    uncrisp-sharp B f x ＝ f x
  compute-uncrisp-sharp B f x =
    compute-unit-pointwise-sharp
      ( λ γ → crisp-elim-sharp ((ᶜf γ) (ᶜa γ)))
      ( ctx B f x)

module _
  {@♭ l1 l2 l3 : Level}
  {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  uncrisp-sharp² :
    (C : (x : A) → B x → UU l3)
    (f : (@♭ x : A) (@♭ y : B x) → ♯ (C x y))
    (x : A) (y : B x) → ♯ (C x y)
  uncrisp-sharp² C f x y =
    uncrisp-sharp (λ (x , y) → C x y) (λ p → f (pr1 p) (pr2 p)) (x , y)

  compute-uncrisp-sharp² :
    (@♭ C : (x : A) → B x → UU l3)
    (@♭ f : (@♭ x : A) (@♭ y : B x) → ♯ (C x y))
    (@♭ x : A) (@♭ y : B x) → uncrisp-sharp² C f x y ＝ f x y
  compute-uncrisp-sharp² C f x y =
    compute-uncrisp-sharp (λ (x , y) → C x y) (λ p → f (pr1 p) (pr2 p)) (x , y)
```

#### Sharp induction revisited

The following definitions rely on rewrite rules.

```text
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ C : ♯ A → UU l2)
  (@♭ f : (x : A) → ♯ (C (unit-sharp x)))
  where

  ind-sharp' : (x : ♯ A) → ♯ (C x)
  ind-sharp' =
    crisp-ind-sharp C (λ x → crisp-elim-sharp (f (crisp-elim-sharp x)))

  compute-ind-sharp' : (@♭ x : A) → ind-sharp' (unit-sharp x) ＝ f x
  compute-ind-sharp' x =
    compute-crisp-ind-sharp C
      ( λ x → crisp-elim-sharp (f (crisp-elim-sharp x)))
      ( unit-sharp x)
```

## Definitions

### The sharp modal operator

<pre class="Agda"><a id="sharp-locally-small-operator-modality"></a><a id="7944" href="modal-type-theory.sharp-modality.html#7944" class="Function">sharp-locally-small-operator-modality</a> <a id="7982" class="Symbol">:</a>
  <a id="7986" class="Symbol">(</a><a id="7987" href="modal-type-theory.sharp-modality.html#7987" class="Bound">l</a> <a id="7989" class="Symbol">:</a> <a id="7991" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7996" class="Symbol">)</a> <a id="7998" class="Symbol">→</a> <a id="8000" href="orthogonal-factorization-systems.locally-small-modal-operators.html#868" class="Function">locally-small-operator-modality</a> <a id="8032" href="modal-type-theory.sharp-modality.html#7987" class="Bound">l</a> <a id="8034" href="modal-type-theory.sharp-modality.html#7987" class="Bound">l</a> <a id="8036" href="modal-type-theory.sharp-modality.html#7987" class="Bound">l</a>
<a id="8038" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8042" class="Symbol">(</a><a id="8043" href="modal-type-theory.sharp-modality.html#7944" class="Function">sharp-locally-small-operator-modality</a> <a id="8081" href="modal-type-theory.sharp-modality.html#8081" class="Bound">l</a><a id="8082" class="Symbol">)</a> <a id="8084" class="Symbol">=</a> <a id="8086" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a>
<a id="8088" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8092" class="Symbol">(</a><a id="8093" href="modal-type-theory.sharp-modality.html#7944" class="Function">sharp-locally-small-operator-modality</a> <a id="8131" href="modal-type-theory.sharp-modality.html#8131" class="Bound">l</a><a id="8132" class="Symbol">)</a> <a id="8134" href="modal-type-theory.sharp-modality.html#8134" class="Bound">A</a> <a id="8136" class="Symbol">=</a> <a id="8138" href="foundation.locally-small-types.html#3510" class="Function">is-locally-small&#39;</a> <a id="8156" class="Symbol">{</a><a id="8157" href="modal-type-theory.sharp-modality.html#8131" class="Bound">l</a><a id="8158" class="Symbol">}</a> <a id="8160" class="Symbol">{</a><a id="8161" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="8163" href="modal-type-theory.sharp-modality.html#8134" class="Bound">A</a><a id="8164" class="Symbol">}</a>
</pre>
### The sharp modality's induction principle

<pre class="Agda"><a id="induction-principle-sharp"></a><a id="8225" href="modal-type-theory.sharp-modality.html#8225" class="Function">induction-principle-sharp</a> <a id="8251" class="Symbol">:</a>
  <a id="8255" class="Symbol">{</a><a id="8256" href="modal-type-theory.sharp-modality.html#8256" class="Bound">l</a> <a id="8258" class="Symbol">:</a> <a id="8260" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8265" class="Symbol">}</a> <a id="8267" class="Symbol">→</a> <a id="8269" href="orthogonal-factorization-systems.modal-induction.html#2096" class="Function">induction-principle-modality</a> <a id="8298" class="Symbol">{</a><a id="8299" href="modal-type-theory.sharp-modality.html#8256" class="Bound">l</a><a id="8300" class="Symbol">}</a> <a id="8302" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="8313" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="8317" class="Symbol">(</a><a id="8318" href="modal-type-theory.sharp-modality.html#8225" class="Function">induction-principle-sharp</a> <a id="8344" href="modal-type-theory.sharp-modality.html#8344" class="Bound">P</a><a id="8345" class="Symbol">)</a> <a id="8347" class="Symbol">=</a> <a id="8349" href="modal-type-theory.sharp-modality.html#4009" class="Postulate">ind-sharp</a> <a id="8359" href="modal-type-theory.sharp-modality.html#8344" class="Bound">P</a>
<a id="8361" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="8365" class="Symbol">(</a><a id="8366" href="modal-type-theory.sharp-modality.html#8225" class="Function">induction-principle-sharp</a> <a id="8392" href="modal-type-theory.sharp-modality.html#8392" class="Bound">P</a><a id="8393" class="Symbol">)</a> <a id="8395" class="Symbol">=</a> <a id="8397" href="modal-type-theory.sharp-modality.html#4139" class="Postulate">compute-ind-sharp</a> <a id="8415" href="modal-type-theory.sharp-modality.html#8392" class="Bound">P</a>

<a id="strong-induction-principle-subuniverse-sharp"></a><a id="8418" href="modal-type-theory.sharp-modality.html#8418" class="Function">strong-induction-principle-subuniverse-sharp</a> <a id="8463" class="Symbol">:</a>
  <a id="8467" class="Symbol">{</a><a id="8468" href="modal-type-theory.sharp-modality.html#8468" class="Bound">l</a> <a id="8470" class="Symbol">:</a> <a id="8472" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8477" class="Symbol">}</a> <a id="8479" class="Symbol">→</a> <a id="8481" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#5023" class="Function">strong-induction-principle-subuniverse-modality</a> <a id="8529" class="Symbol">{</a><a id="8530" href="modal-type-theory.sharp-modality.html#8468" class="Bound">l</a><a id="8531" class="Symbol">}</a> <a id="8533" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="8544" href="modal-type-theory.sharp-modality.html#8418" class="Function">strong-induction-principle-subuniverse-sharp</a> <a id="8589" class="Symbol">=</a>
  <a id="8593" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#12507" class="Function">strong-induction-principle-subuniverse-induction-principle-modality</a>
    <a id="8665" class="Symbol">(</a> <a id="8667" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="8677" class="Symbol">)</a>
    <a id="8683" class="Symbol">(</a> <a id="8685" href="modal-type-theory.sharp-modality.html#8225" class="Function">induction-principle-sharp</a><a id="8710" class="Symbol">)</a>

<a id="strong-ind-subuniverse-sharp"></a><a id="8713" href="modal-type-theory.sharp-modality.html#8713" class="Function">strong-ind-subuniverse-sharp</a> <a id="8742" class="Symbol">:</a>
  <a id="8746" class="Symbol">{</a><a id="8747" href="modal-type-theory.sharp-modality.html#8747" class="Bound">l</a> <a id="8749" class="Symbol">:</a> <a id="8751" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8756" class="Symbol">}</a> <a id="8758" class="Symbol">→</a> <a id="8760" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#5279" class="Function">strong-ind-subuniverse-modality</a> <a id="8792" class="Symbol">{</a><a id="8793" href="modal-type-theory.sharp-modality.html#8747" class="Bound">l</a><a id="8794" class="Symbol">}</a> <a id="8796" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="8807" href="modal-type-theory.sharp-modality.html#8713" class="Function">strong-ind-subuniverse-sharp</a> <a id="8836" class="Symbol">=</a>
  <a id="8840" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#5826" class="Function">strong-ind-strong-induction-principle-subuniverse-modality</a>
    <a id="8903" class="Symbol">(</a> <a id="8905" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="8915" class="Symbol">)</a>
    <a id="8921" class="Symbol">(</a> <a id="8923" href="modal-type-theory.sharp-modality.html#8418" class="Function">strong-induction-principle-subuniverse-sharp</a><a id="8967" class="Symbol">)</a>

<a id="compute-strong-ind-subuniverse-sharp"></a><a id="8970" href="modal-type-theory.sharp-modality.html#8970" class="Function">compute-strong-ind-subuniverse-sharp</a> <a id="9007" class="Symbol">:</a>
  <a id="9011" class="Symbol">{</a><a id="9012" href="modal-type-theory.sharp-modality.html#9012" class="Bound">l</a> <a id="9014" class="Symbol">:</a> <a id="9016" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9021" class="Symbol">}</a> <a id="9023" class="Symbol">→</a>
  <a id="9027" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#5503" class="Function">compute-strong-ind-subuniverse-modality</a> <a id="9067" class="Symbol">{</a><a id="9068" href="modal-type-theory.sharp-modality.html#9012" class="Bound">l</a><a id="9069" class="Symbol">}</a>
    <a id="9075" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
    <a id="9090" href="modal-type-theory.sharp-modality.html#8713" class="Function">strong-ind-subuniverse-sharp</a>
<a id="9119" href="modal-type-theory.sharp-modality.html#8970" class="Function">compute-strong-ind-subuniverse-sharp</a> <a id="9156" class="Symbol">=</a>
  <a id="9160" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#6138" class="Function">compute-strong-ind-strong-induction-principle-subuniverse-modality</a>
    <a id="9231" class="Symbol">(</a> <a id="9233" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="9243" class="Symbol">)</a>
    <a id="9249" class="Symbol">(</a> <a id="9251" href="modal-type-theory.sharp-modality.html#8418" class="Function">strong-induction-principle-subuniverse-sharp</a><a id="9295" class="Symbol">)</a>

<a id="induction-principle-subuniverse-sharp"></a><a id="9298" href="modal-type-theory.sharp-modality.html#9298" class="Function">induction-principle-subuniverse-sharp</a> <a id="9336" class="Symbol">:</a>
  <a id="9340" class="Symbol">{</a><a id="9341" href="modal-type-theory.sharp-modality.html#9341" class="Bound">l</a> <a id="9343" class="Symbol">:</a> <a id="9345" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9350" class="Symbol">}</a> <a id="9352" class="Symbol">→</a> <a id="9354" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#1800" class="Function">induction-principle-subuniverse-modality</a> <a id="9395" class="Symbol">{</a><a id="9396" href="modal-type-theory.sharp-modality.html#9341" class="Bound">l</a><a id="9397" class="Symbol">}</a> <a id="9399" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="9410" href="modal-type-theory.sharp-modality.html#9298" class="Function">induction-principle-subuniverse-sharp</a> <a id="9448" class="Symbol">=</a>
  <a id="9452" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#13875" class="Function">induction-principle-subuniverse-induction-principle-modality</a>
    <a id="9517" class="Symbol">(</a> <a id="9519" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="9529" class="Symbol">)</a>
    <a id="9535" class="Symbol">(</a> <a id="9537" href="modal-type-theory.sharp-modality.html#8225" class="Function">induction-principle-sharp</a><a id="9562" class="Symbol">)</a>

<a id="ind-subuniverse-sharp"></a><a id="9565" href="modal-type-theory.sharp-modality.html#9565" class="Function">ind-subuniverse-sharp</a> <a id="9587" class="Symbol">:</a>
  <a id="9591" class="Symbol">{</a><a id="9592" href="modal-type-theory.sharp-modality.html#9592" class="Bound">l</a> <a id="9594" class="Symbol">:</a> <a id="9596" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9601" class="Symbol">}</a> <a id="9603" class="Symbol">→</a> <a id="9605" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#2034" class="Function">ind-subuniverse-modality</a> <a id="9630" class="Symbol">{</a><a id="9631" href="modal-type-theory.sharp-modality.html#9592" class="Bound">l</a><a id="9632" class="Symbol">}</a> <a id="9634" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="9645" href="modal-type-theory.sharp-modality.html#9565" class="Function">ind-subuniverse-sharp</a> <a id="9667" class="Symbol">=</a>
  <a id="9671" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#2498" class="Function">ind-induction-principle-subuniverse-modality</a>
    <a id="9720" class="Symbol">(</a> <a id="9722" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="9732" class="Symbol">)</a>
    <a id="9738" class="Symbol">(</a> <a id="9740" href="modal-type-theory.sharp-modality.html#9298" class="Function">induction-principle-subuniverse-sharp</a><a id="9777" class="Symbol">)</a>

<a id="compute-ind-subuniverse-sharp"></a><a id="9780" href="modal-type-theory.sharp-modality.html#9780" class="Function">compute-ind-subuniverse-sharp</a> <a id="9810" class="Symbol">:</a>
  <a id="9814" class="Symbol">{</a><a id="9815" href="modal-type-theory.sharp-modality.html#9815" class="Bound">l</a> <a id="9817" class="Symbol">:</a> <a id="9819" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9824" class="Symbol">}</a> <a id="9826" class="Symbol">→</a>
  <a id="9830" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#2223" class="Function">compute-ind-subuniverse-modality</a> <a id="9863" class="Symbol">{</a><a id="9864" href="modal-type-theory.sharp-modality.html#9815" class="Bound">l</a><a id="9865" class="Symbol">}</a> <a id="9867" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="9878" href="modal-type-theory.sharp-modality.html#9565" class="Function">ind-subuniverse-sharp</a>
<a id="9900" href="modal-type-theory.sharp-modality.html#9780" class="Function">compute-ind-subuniverse-sharp</a> <a id="9930" class="Symbol">=</a>
  <a id="9934" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#2754" class="Function">compute-ind-induction-principle-subuniverse-modality</a>
    <a id="9991" class="Symbol">(</a> <a id="9993" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="10003" class="Symbol">)</a>
    <a id="10009" class="Symbol">(</a> <a id="10011" href="modal-type-theory.sharp-modality.html#9298" class="Function">induction-principle-subuniverse-sharp</a><a id="10048" class="Symbol">)</a>
</pre>
### The sharp modality's recursion principle

<pre class="Agda"><a id="rec-sharp"></a><a id="10109" href="modal-type-theory.sharp-modality.html#10109" class="Function">rec-sharp</a> <a id="10119" class="Symbol">:</a>
  <a id="10123" class="Symbol">{</a><a id="10124" href="modal-type-theory.sharp-modality.html#10124" class="Bound">l1</a> <a id="10127" href="modal-type-theory.sharp-modality.html#10127" class="Bound">l2</a> <a id="10130" class="Symbol">:</a> <a id="10132" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="10137" class="Symbol">}</a> <a id="10139" class="Symbol">{</a><a id="10140" href="modal-type-theory.sharp-modality.html#10140" class="Bound">A</a> <a id="10142" class="Symbol">:</a> <a id="10144" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="10147" href="modal-type-theory.sharp-modality.html#10124" class="Bound">l1</a><a id="10149" class="Symbol">}</a> <a id="10151" class="Symbol">{</a><a id="10152" href="modal-type-theory.sharp-modality.html#10152" class="Bound">B</a> <a id="10154" class="Symbol">:</a> <a id="10156" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="10159" href="modal-type-theory.sharp-modality.html#10127" class="Bound">l2</a><a id="10161" class="Symbol">}</a> <a id="10163" class="Symbol">→</a>
  <a id="10167" class="Symbol">(</a><a id="10168" href="modal-type-theory.sharp-modality.html#10140" class="Bound">A</a> <a id="10170" class="Symbol">→</a> <a id="10172" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="10174" href="modal-type-theory.sharp-modality.html#10152" class="Bound">B</a><a id="10175" class="Symbol">)</a> <a id="10177" class="Symbol">→</a> <a id="10179" class="Symbol">(</a><a id="10180" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="10182" href="modal-type-theory.sharp-modality.html#10140" class="Bound">A</a> <a id="10184" class="Symbol">→</a> <a id="10186" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="10188" href="modal-type-theory.sharp-modality.html#10152" class="Bound">B</a><a id="10189" class="Symbol">)</a>
<a id="10191" href="modal-type-theory.sharp-modality.html#10109" class="Function">rec-sharp</a> <a id="10201" class="Symbol">{</a><a id="10202" class="Argument">B</a> <a id="10204" class="Symbol">=</a> <a id="10206" href="modal-type-theory.sharp-modality.html#10206" class="Bound">B</a><a id="10207" class="Symbol">}</a> <a id="10209" class="Symbol">=</a> <a id="10211" href="modal-type-theory.sharp-modality.html#4009" class="Postulate">ind-sharp</a> <a id="10221" class="Symbol">(λ</a> <a id="10224" href="modal-type-theory.sharp-modality.html#10224" class="Bound">_</a> <a id="10226" class="Symbol">→</a> <a id="10228" href="modal-type-theory.sharp-modality.html#10206" class="Bound">B</a><a id="10229" class="Symbol">)</a>

<a id="compute-rec-sharp"></a><a id="10232" href="modal-type-theory.sharp-modality.html#10232" class="Function">compute-rec-sharp</a> <a id="10250" class="Symbol">:</a>
  <a id="10254" class="Symbol">{</a><a id="10255" href="modal-type-theory.sharp-modality.html#10255" class="Bound">l1</a> <a id="10258" href="modal-type-theory.sharp-modality.html#10258" class="Bound">l2</a> <a id="10261" class="Symbol">:</a> <a id="10263" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="10268" class="Symbol">}</a> <a id="10270" class="Symbol">{</a><a id="10271" href="modal-type-theory.sharp-modality.html#10271" class="Bound">A</a> <a id="10273" class="Symbol">:</a> <a id="10275" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="10278" href="modal-type-theory.sharp-modality.html#10255" class="Bound">l1</a><a id="10280" class="Symbol">}</a> <a id="10282" class="Symbol">{</a><a id="10283" href="modal-type-theory.sharp-modality.html#10283" class="Bound">B</a> <a id="10285" class="Symbol">:</a> <a id="10287" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="10290" href="modal-type-theory.sharp-modality.html#10258" class="Bound">l2</a><a id="10292" class="Symbol">}</a>
  <a id="10296" class="Symbol">(</a><a id="10297" href="modal-type-theory.sharp-modality.html#10297" class="Bound">f</a> <a id="10299" class="Symbol">:</a> <a id="10301" href="modal-type-theory.sharp-modality.html#10271" class="Bound">A</a> <a id="10303" class="Symbol">→</a> <a id="10305" href="modal-type-theory.sharp-modality.html#1737" class="Postulate">♯</a> <a id="10307" href="modal-type-theory.sharp-modality.html#10283" class="Bound">B</a><a id="10308" class="Symbol">)</a> <a id="10310" class="Symbol">→</a>
  <a id="10314" class="Symbol">(</a><a id="10315" href="modal-type-theory.sharp-modality.html#10109" class="Function">rec-sharp</a> <a id="10325" href="modal-type-theory.sharp-modality.html#10297" class="Bound">f</a> <a id="10327" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="10329" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="10339" class="Symbol">)</a> <a id="10341" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="10343" href="modal-type-theory.sharp-modality.html#10297" class="Bound">f</a>
<a id="10345" href="modal-type-theory.sharp-modality.html#10232" class="Function">compute-rec-sharp</a> <a id="10363" class="Symbol">{</a><a id="10364" class="Argument">B</a> <a id="10366" class="Symbol">=</a> <a id="10368" href="modal-type-theory.sharp-modality.html#10368" class="Bound">B</a><a id="10369" class="Symbol">}</a> <a id="10371" class="Symbol">=</a> <a id="10373" href="modal-type-theory.sharp-modality.html#4139" class="Postulate">compute-ind-sharp</a> <a id="10391" class="Symbol">(λ</a> <a id="10394" href="modal-type-theory.sharp-modality.html#10394" class="Bound">_</a> <a id="10396" class="Symbol">→</a> <a id="10398" href="modal-type-theory.sharp-modality.html#10368" class="Bound">B</a><a id="10399" class="Symbol">)</a>

<a id="recursion-principle-sharp"></a><a id="10402" href="modal-type-theory.sharp-modality.html#10402" class="Function">recursion-principle-sharp</a> <a id="10428" class="Symbol">:</a>
  <a id="10432" class="Symbol">{</a><a id="10433" href="modal-type-theory.sharp-modality.html#10433" class="Bound">l</a> <a id="10435" class="Symbol">:</a> <a id="10437" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="10442" class="Symbol">}</a> <a id="10444" class="Symbol">→</a> <a id="10446" href="orthogonal-factorization-systems.modal-induction.html#3152" class="Function">recursion-principle-modality</a> <a id="10475" class="Symbol">{</a><a id="10476" href="modal-type-theory.sharp-modality.html#10433" class="Bound">l</a><a id="10477" class="Symbol">}</a> <a id="10479" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="10490" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="10494" class="Symbol">(</a><a id="10495" href="modal-type-theory.sharp-modality.html#10402" class="Function">recursion-principle-sharp</a><a id="10520" class="Symbol">)</a> <a id="10522" class="Symbol">=</a> <a id="10524" href="modal-type-theory.sharp-modality.html#10109" class="Function">rec-sharp</a>
<a id="10534" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="10538" class="Symbol">(</a><a id="10539" href="modal-type-theory.sharp-modality.html#10402" class="Function">recursion-principle-sharp</a><a id="10564" class="Symbol">)</a> <a id="10566" class="Symbol">=</a> <a id="10568" href="modal-type-theory.sharp-modality.html#10232" class="Function">compute-rec-sharp</a>

<a id="strong-recursion-principle-subuniverse-sharp"></a><a id="10587" href="modal-type-theory.sharp-modality.html#10587" class="Function">strong-recursion-principle-subuniverse-sharp</a> <a id="10632" class="Symbol">:</a>
  <a id="10636" class="Symbol">{</a><a id="10637" href="modal-type-theory.sharp-modality.html#10637" class="Bound">l</a> <a id="10639" class="Symbol">:</a> <a id="10641" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="10646" class="Symbol">}</a> <a id="10648" class="Symbol">→</a> <a id="10650" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#6732" class="Function">strong-recursion-principle-subuniverse-modality</a> <a id="10698" class="Symbol">{</a><a id="10699" href="modal-type-theory.sharp-modality.html#10637" class="Bound">l</a><a id="10700" class="Symbol">}</a> <a id="10702" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="10713" href="modal-type-theory.sharp-modality.html#10587" class="Function">strong-recursion-principle-subuniverse-sharp</a> <a id="10758" class="Symbol">=</a>
  <a id="10762" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#15403" class="Function">strong-recursion-principle-subuniverse-recursion-principle-modality</a>
    <a id="10834" class="Symbol">(</a> <a id="10836" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="10846" class="Symbol">)</a>
    <a id="10852" class="Symbol">(</a> <a id="10854" href="modal-type-theory.sharp-modality.html#10402" class="Function">recursion-principle-sharp</a><a id="10879" class="Symbol">)</a>

<a id="strong-rec-subuniverse-sharp"></a><a id="10882" href="modal-type-theory.sharp-modality.html#10882" class="Function">strong-rec-subuniverse-sharp</a> <a id="10911" class="Symbol">:</a>
  <a id="10915" class="Symbol">{</a><a id="10916" href="modal-type-theory.sharp-modality.html#10916" class="Bound">l</a> <a id="10918" class="Symbol">:</a> <a id="10920" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="10925" class="Symbol">}</a> <a id="10927" class="Symbol">→</a> <a id="10929" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#6956" class="Function">strong-rec-subuniverse-modality</a> <a id="10961" class="Symbol">{</a><a id="10962" href="modal-type-theory.sharp-modality.html#10916" class="Bound">l</a><a id="10963" class="Symbol">}</a> <a id="10965" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="10976" href="modal-type-theory.sharp-modality.html#10882" class="Function">strong-rec-subuniverse-sharp</a> <a id="11005" class="Symbol">=</a>
  <a id="11009" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#7381" class="Function">strong-rec-strong-recursion-principle-subuniverse-modality</a>
    <a id="11072" class="Symbol">(</a> <a id="11074" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="11084" class="Symbol">)</a>
    <a id="11090" class="Symbol">(</a> <a id="11092" href="modal-type-theory.sharp-modality.html#10587" class="Function">strong-recursion-principle-subuniverse-sharp</a><a id="11136" class="Symbol">)</a>

<a id="compute-strong-rec-subuniverse-sharp"></a><a id="11139" href="modal-type-theory.sharp-modality.html#11139" class="Function">compute-strong-rec-subuniverse-sharp</a> <a id="11176" class="Symbol">:</a>
  <a id="11180" class="Symbol">{</a><a id="11181" href="modal-type-theory.sharp-modality.html#11181" class="Bound">l</a> <a id="11183" class="Symbol">:</a> <a id="11185" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="11190" class="Symbol">}</a> <a id="11192" class="Symbol">→</a>
  <a id="11196" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#7115" class="Function">compute-strong-rec-subuniverse-modality</a> <a id="11236" class="Symbol">{</a><a id="11237" href="modal-type-theory.sharp-modality.html#11181" class="Bound">l</a><a id="11238" class="Symbol">}</a>
    <a id="11244" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
    <a id="11259" href="modal-type-theory.sharp-modality.html#10882" class="Function">strong-rec-subuniverse-sharp</a>
<a id="11288" href="modal-type-theory.sharp-modality.html#11139" class="Function">compute-strong-rec-subuniverse-sharp</a> <a id="11325" class="Symbol">=</a>
  <a id="11329" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#7695" class="Function">compute-strong-rec-strong-recursion-principle-subuniverse-modality</a>
    <a id="11400" class="Symbol">(</a> <a id="11402" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="11412" class="Symbol">)</a>
    <a id="11418" class="Symbol">(</a> <a id="11420" href="modal-type-theory.sharp-modality.html#10587" class="Function">strong-recursion-principle-subuniverse-sharp</a><a id="11464" class="Symbol">)</a>

<a id="recursion-principle-subuniverse-sharp"></a><a id="11467" href="modal-type-theory.sharp-modality.html#11467" class="Function">recursion-principle-subuniverse-sharp</a> <a id="11505" class="Symbol">:</a>
  <a id="11509" class="Symbol">{</a><a id="11510" href="modal-type-theory.sharp-modality.html#11510" class="Bound">l</a> <a id="11512" class="Symbol">:</a> <a id="11514" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="11519" class="Symbol">}</a> <a id="11521" class="Symbol">→</a> <a id="11523" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#3275" class="Function">recursion-principle-subuniverse-modality</a> <a id="11564" class="Symbol">{</a><a id="11565" href="modal-type-theory.sharp-modality.html#11510" class="Bound">l</a><a id="11566" class="Symbol">}</a> <a id="11568" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="11579" href="modal-type-theory.sharp-modality.html#11467" class="Function">recursion-principle-subuniverse-sharp</a> <a id="11617" class="Symbol">=</a>
  <a id="11621" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#16778" class="Function">recursion-principle-subuniverse-recursion-principle-modality</a>
    <a id="11686" class="Symbol">(</a> <a id="11688" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="11698" class="Symbol">)</a>
    <a id="11704" class="Symbol">(</a> <a id="11706" href="modal-type-theory.sharp-modality.html#10402" class="Function">recursion-principle-sharp</a><a id="11731" class="Symbol">)</a>

<a id="rec-subuniverse-sharp"></a><a id="11734" href="modal-type-theory.sharp-modality.html#11734" class="Function">rec-subuniverse-sharp</a> <a id="11756" class="Symbol">:</a>
  <a id="11760" class="Symbol">{</a><a id="11761" href="modal-type-theory.sharp-modality.html#11761" class="Bound">l</a> <a id="11763" class="Symbol">:</a> <a id="11765" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="11770" class="Symbol">}</a> <a id="11772" class="Symbol">→</a> <a id="11774" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#3479" class="Function">rec-subuniverse-modality</a> <a id="11799" class="Symbol">{</a><a id="11800" href="modal-type-theory.sharp-modality.html#11761" class="Bound">l</a><a id="11801" class="Symbol">}</a> <a id="11803" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a>
<a id="11814" href="modal-type-theory.sharp-modality.html#11734" class="Function">rec-subuniverse-sharp</a> <a id="11836" class="Symbol">=</a>
  <a id="11840" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#3847" class="Function">rec-recursion-principle-subuniverse-modality</a>
    <a id="11889" class="Symbol">(</a> <a id="11891" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="11901" class="Symbol">)</a>
    <a id="11907" class="Symbol">(</a> <a id="11909" href="modal-type-theory.sharp-modality.html#11467" class="Function">recursion-principle-subuniverse-sharp</a><a id="11946" class="Symbol">)</a>

<a id="compute-rec-subuniverse-sharp"></a><a id="11949" href="modal-type-theory.sharp-modality.html#11949" class="Function">compute-rec-subuniverse-sharp</a> <a id="11979" class="Symbol">:</a>
  <a id="11983" class="Symbol">{</a><a id="11984" href="modal-type-theory.sharp-modality.html#11984" class="Bound">l</a> <a id="11986" class="Symbol">:</a> <a id="11988" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="11993" class="Symbol">}</a> <a id="11995" class="Symbol">→</a>
  <a id="11999" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#3614" class="Function">compute-rec-subuniverse-modality</a> <a id="12032" class="Symbol">{</a><a id="12033" href="modal-type-theory.sharp-modality.html#11984" class="Bound">l</a><a id="12034" class="Symbol">}</a> <a id="12036" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a> <a id="12047" href="modal-type-theory.sharp-modality.html#11734" class="Function">rec-subuniverse-sharp</a>
<a id="12069" href="modal-type-theory.sharp-modality.html#11949" class="Function">compute-rec-subuniverse-sharp</a> <a id="12099" class="Symbol">=</a>
  <a id="12103" href="orthogonal-factorization-systems.modal-subuniverse-induction.html#4105" class="Function">compute-rec-recursion-principle-subuniverse-modality</a>
    <a id="12160" class="Symbol">(</a> <a id="12162" href="modal-type-theory.sharp-modality.html#1774" class="Postulate">unit-sharp</a><a id="12172" class="Symbol">)</a>
    <a id="12178" class="Symbol">(</a> <a id="12180" href="modal-type-theory.sharp-modality.html#11467" class="Function">recursion-principle-subuniverse-sharp</a><a id="12217" class="Symbol">)</a>
</pre>
## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
{{#reference Felixwellen/DCHoTT-Agda}} {{#reference DavidJaz/Cohesion}}

## External links

- [sharp modality](https://ncatlab.org/nlab/show/sharp+modality) at $n$Lab
