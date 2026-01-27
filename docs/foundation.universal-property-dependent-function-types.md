# The universal property of dependent function types

<pre class="Agda"><a id="63" class="Keyword">module</a> <a id="70" href="foundation.universal-property-dependent-function-types.html" class="Module">foundation.universal-property-dependent-function-types</a> <a id="125" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="foundation.spans-families-of-types.html" class="Module">foundation.spans-families-of-types</a>
<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="foundation.terminal-spans-families-of-types.html" class="Module">foundation.terminal-spans-families-of-types</a>
<a id="413" class="Keyword">open</a> <a id="418" class="Keyword">import</a> <a id="425" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="453" class="Keyword">open</a> <a id="458" class="Keyword">import</a> <a id="465" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="499" class="Keyword">open</a> <a id="504" class="Keyword">import</a> <a id="511" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="546" class="Keyword">open</a> <a id="551" class="Keyword">import</a> <a id="558" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="587" class="Keyword">open</a> <a id="592" class="Keyword">import</a> <a id="599" href="foundation-core.functoriality-dependent-function-types.html" class="Module">foundation-core.functoriality-dependent-function-types</a>
<a id="654" class="Keyword">open</a> <a id="659" class="Keyword">import</a> <a id="666" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
</pre>
</details>

## Idea

Consider a family of types `B` over `A`. Then the dependent function type
`(a : A) → B a` naturally has the structure of a
[span](foundation.spans-families-of-types.md) on the family of types `B` over
`A`, where for each `a : A` the map

```text
  ((x : A) → B x) → B a
```

is given by evaluation at `a`.

A span `𝒮 := (S , f)` is said to satisfy the
{{#concept "universal property of dependent function types" Agda=universal-property-dependent-function-types}}
if for any type `T` the map

```text
  (T → S) → ((x : A) → T → B x)
```

given by `h ↦ λ x t → f x (h t)` is an
[equivalence](foundation-core.equivalences.md). The dependent function type
`(x : A) → B x` equipped with the span structure defined above satisfies the
universal property of dependent function types.

In
[`foundation.dependent-function-types`](foundation.dependent-function-types.md)
we show that dependent function types satisfy the universal property of
dependent function types. In this file we also show that the universal property
of dependent function types is equivalent to being a
[terminal span](foundation.terminal-spans-families-of-types.md) on the type
family `B`.

## Definitions

### The universal property of dependent function types

<pre class="Agda"><a id="1978" class="Keyword">module</a> <a id="1985" href="foundation.universal-property-dependent-function-types.html#1985" class="Module">_</a>
  <a id="1989" class="Symbol">{</a><a id="1990" href="foundation.universal-property-dependent-function-types.html#1990" class="Bound">l1</a> <a id="1993" href="foundation.universal-property-dependent-function-types.html#1993" class="Bound">l2</a> <a id="1996" href="foundation.universal-property-dependent-function-types.html#1996" class="Bound">l3</a> <a id="1999" class="Symbol">:</a> <a id="2001" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2006" class="Symbol">}</a> <a id="2008" class="Symbol">{</a><a id="2009" href="foundation.universal-property-dependent-function-types.html#2009" class="Bound">A</a> <a id="2011" class="Symbol">:</a> <a id="2013" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2016" href="foundation.universal-property-dependent-function-types.html#1990" class="Bound">l1</a><a id="2018" class="Symbol">}</a> <a id="2020" class="Symbol">{</a><a id="2021" href="foundation.universal-property-dependent-function-types.html#2021" class="Bound">B</a> <a id="2023" class="Symbol">:</a> <a id="2025" href="foundation.universal-property-dependent-function-types.html#2009" class="Bound">A</a> <a id="2027" class="Symbol">→</a> <a id="2029" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2032" href="foundation.universal-property-dependent-function-types.html#1993" class="Bound">l2</a><a id="2034" class="Symbol">}</a> <a id="2036" class="Symbol">(</a><a id="2037" href="foundation.universal-property-dependent-function-types.html#2037" class="Bound">𝒮</a> <a id="2039" class="Symbol">:</a> <a id="2041" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="2058" href="foundation.universal-property-dependent-function-types.html#1996" class="Bound">l3</a> <a id="2061" href="foundation.universal-property-dependent-function-types.html#2021" class="Bound">B</a><a id="2062" class="Symbol">)</a>
  <a id="2066" class="Keyword">where</a>

  <a id="2075" href="foundation.universal-property-dependent-function-types.html#2075" class="Function">ev-span-type-family</a> <a id="2095" class="Symbol">:</a>
    <a id="2101" class="Symbol">{</a><a id="2102" href="foundation.universal-property-dependent-function-types.html#2102" class="Bound">l</a> <a id="2104" class="Symbol">:</a> <a id="2106" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2111" class="Symbol">}</a> <a id="2113" class="Symbol">(</a><a id="2114" href="foundation.universal-property-dependent-function-types.html#2114" class="Bound">T</a> <a id="2116" class="Symbol">:</a> <a id="2118" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2121" href="foundation.universal-property-dependent-function-types.html#2102" class="Bound">l</a><a id="2122" class="Symbol">)</a> <a id="2124" class="Symbol">→</a>
    <a id="2130" class="Symbol">(</a><a id="2131" href="foundation.universal-property-dependent-function-types.html#2114" class="Bound">T</a> <a id="2133" class="Symbol">→</a> <a id="2135" href="foundation.spans-families-of-types.html#1038" class="Function">spanning-type-span-type-family</a> <a id="2166" href="foundation.universal-property-dependent-function-types.html#2037" class="Bound">𝒮</a><a id="2167" class="Symbol">)</a> <a id="2169" class="Symbol">→</a> <a id="2171" class="Symbol">(</a><a id="2172" href="foundation.universal-property-dependent-function-types.html#2172" class="Bound">x</a> <a id="2174" class="Symbol">:</a> <a id="2176" href="foundation.universal-property-dependent-function-types.html#2009" class="Bound">A</a><a id="2177" class="Symbol">)</a> <a id="2179" class="Symbol">→</a> <a id="2181" href="foundation.universal-property-dependent-function-types.html#2114" class="Bound">T</a> <a id="2183" class="Symbol">→</a> <a id="2185" href="foundation.universal-property-dependent-function-types.html#2021" class="Bound">B</a> <a id="2187" href="foundation.universal-property-dependent-function-types.html#2172" class="Bound">x</a>
  <a id="2191" href="foundation.universal-property-dependent-function-types.html#2075" class="Function">ev-span-type-family</a> <a id="2211" href="foundation.universal-property-dependent-function-types.html#2211" class="Bound">T</a> <a id="2213" href="foundation.universal-property-dependent-function-types.html#2213" class="Bound">h</a> <a id="2215" href="foundation.universal-property-dependent-function-types.html#2215" class="Bound">x</a> <a id="2217" href="foundation.universal-property-dependent-function-types.html#2217" class="Bound">t</a> <a id="2219" class="Symbol">=</a> <a id="2221" href="foundation.spans-families-of-types.html#1121" class="Function">map-span-type-family</a> <a id="2242" href="foundation.universal-property-dependent-function-types.html#2037" class="Bound">𝒮</a> <a id="2244" href="foundation.universal-property-dependent-function-types.html#2215" class="Bound">x</a> <a id="2246" class="Symbol">(</a><a id="2247" href="foundation.universal-property-dependent-function-types.html#2213" class="Bound">h</a> <a id="2249" href="foundation.universal-property-dependent-function-types.html#2217" class="Bound">t</a><a id="2250" class="Symbol">)</a>

  <a id="2255" href="foundation.universal-property-dependent-function-types.html#2255" class="Function">universal-property-dependent-function-types</a> <a id="2299" class="Symbol">:</a> <a id="2301" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="2307" href="foundation.universal-property-dependent-function-types.html#2255" class="Function">universal-property-dependent-function-types</a> <a id="2351" class="Symbol">=</a>
    <a id="2357" class="Symbol">{</a><a id="2358" href="foundation.universal-property-dependent-function-types.html#2358" class="Bound">l</a> <a id="2360" class="Symbol">:</a> <a id="2362" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2367" class="Symbol">}</a> <a id="2369" class="Symbol">(</a><a id="2370" href="foundation.universal-property-dependent-function-types.html#2370" class="Bound">T</a> <a id="2372" class="Symbol">:</a> <a id="2374" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2377" href="foundation.universal-property-dependent-function-types.html#2358" class="Bound">l</a><a id="2378" class="Symbol">)</a> <a id="2380" class="Symbol">→</a> <a id="2382" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="2391" class="Symbol">(</a><a id="2392" href="foundation.universal-property-dependent-function-types.html#2075" class="Function">ev-span-type-family</a> <a id="2412" href="foundation.universal-property-dependent-function-types.html#2370" class="Bound">T</a><a id="2413" class="Symbol">)</a>
</pre>
## Properties

### A span on a family of types satisfies the universal property of dependent function types if and only if it is terminal

<pre class="Agda"><a id="2567" class="Keyword">module</a> <a id="2574" href="foundation.universal-property-dependent-function-types.html#2574" class="Module">_</a>
  <a id="2578" class="Symbol">{</a><a id="2579" href="foundation.universal-property-dependent-function-types.html#2579" class="Bound">l1</a> <a id="2582" href="foundation.universal-property-dependent-function-types.html#2582" class="Bound">l2</a> <a id="2585" href="foundation.universal-property-dependent-function-types.html#2585" class="Bound">l3</a> <a id="2588" class="Symbol">:</a> <a id="2590" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2595" class="Symbol">}</a> <a id="2597" class="Symbol">{</a><a id="2598" href="foundation.universal-property-dependent-function-types.html#2598" class="Bound">A</a> <a id="2600" class="Symbol">:</a> <a id="2602" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2605" href="foundation.universal-property-dependent-function-types.html#2579" class="Bound">l1</a><a id="2607" class="Symbol">}</a> <a id="2609" class="Symbol">{</a><a id="2610" href="foundation.universal-property-dependent-function-types.html#2610" class="Bound">B</a> <a id="2612" class="Symbol">:</a> <a id="2614" href="foundation.universal-property-dependent-function-types.html#2598" class="Bound">A</a> <a id="2616" class="Symbol">→</a> <a id="2618" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2621" href="foundation.universal-property-dependent-function-types.html#2582" class="Bound">l2</a><a id="2623" class="Symbol">}</a> <a id="2625" class="Symbol">(</a><a id="2626" href="foundation.universal-property-dependent-function-types.html#2626" class="Bound">𝒮</a> <a id="2628" class="Symbol">:</a> <a id="2630" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="2647" href="foundation.universal-property-dependent-function-types.html#2585" class="Bound">l3</a> <a id="2650" href="foundation.universal-property-dependent-function-types.html#2610" class="Bound">B</a><a id="2651" class="Symbol">)</a>
  <a id="2655" class="Keyword">where</a>

  <a id="2664" class="Keyword">abstract</a>
    <a id="2677" href="foundation.universal-property-dependent-function-types.html#2677" class="Function">is-terminal-universal-property-dependent-function-types</a> <a id="2733" class="Symbol">:</a>
      <a id="2741" href="foundation.universal-property-dependent-function-types.html#2255" class="Function">universal-property-dependent-function-types</a> <a id="2785" href="foundation.universal-property-dependent-function-types.html#2626" class="Bound">𝒮</a> <a id="2787" class="Symbol">→</a>
      <a id="2795" href="foundation.terminal-spans-families-of-types.html#929" class="Function">is-terminal-span-type-family</a> <a id="2824" href="foundation.universal-property-dependent-function-types.html#2626" class="Bound">𝒮</a>
    <a id="2830" href="foundation.universal-property-dependent-function-types.html#2677" class="Function">is-terminal-universal-property-dependent-function-types</a> <a id="2886" href="foundation.universal-property-dependent-function-types.html#2886" class="Bound">U</a> <a id="2888" href="foundation.universal-property-dependent-function-types.html#2888" class="Bound">𝒯</a> <a id="2890" class="Symbol">=</a>
      <a id="2898" href="foundation-core.contractible-types.html#2905" class="Function">is-contr-equiv&#39;</a> <a id="2914" class="Symbol">_</a>
        <a id="2924" class="Symbol">(</a> <a id="2926" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a>
          <a id="2946" class="Symbol">(</a> <a id="2948" class="Symbol">λ</a> <a id="2950" href="foundation.universal-property-dependent-function-types.html#2950" class="Bound">h</a> <a id="2952" class="Symbol">→</a>
            <a id="2966" class="Symbol">(</a> <a id="2968" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a>
              <a id="3003" class="Symbol">(</a> <a id="3005" class="Symbol">λ</a> <a id="3007" href="foundation.universal-property-dependent-function-types.html#3007" class="Bound">a</a> <a id="3009" class="Symbol">→</a>
                <a id="3027" class="Symbol">(</a> <a id="3029" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a> <a id="3050" class="Symbol">(λ</a> <a id="3053" href="foundation.universal-property-dependent-function-types.html#3053" class="Bound">t</a> <a id="3055" class="Symbol">→</a> <a id="3057" href="foundation.identity-types.html#1974" class="Function">equiv-inv</a> <a id="3067" class="Symbol">_</a> <a id="3069" class="Symbol">_))</a> <a id="3073" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
                <a id="3092" class="Symbol">(</a> <a id="3094" href="foundation.function-extensionality.html#4394" class="Function">equiv-funext</a><a id="3106" class="Symbol">)))</a> <a id="3110" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
            <a id="3125" class="Symbol">(</a> <a id="3127" href="foundation.function-extensionality.html#4394" class="Function">equiv-funext</a><a id="3139" class="Symbol">)))</a>
        <a id="3151" class="Symbol">(</a> <a id="3153" href="foundation-core.contractible-maps.html#3782" class="Function">is-contr-map-is-equiv</a>
          <a id="3185" class="Symbol">(</a> <a id="3187" href="foundation.universal-property-dependent-function-types.html#2886" class="Bound">U</a> <a id="3189" class="Symbol">(</a><a id="3190" href="foundation.spans-families-of-types.html#1038" class="Function">spanning-type-span-type-family</a> <a id="3221" href="foundation.universal-property-dependent-function-types.html#2888" class="Bound">𝒯</a><a id="3222" class="Symbol">))</a>
          <a id="3235" class="Symbol">(</a> <a id="3237" href="foundation.spans-families-of-types.html#1121" class="Function">map-span-type-family</a> <a id="3258" href="foundation.universal-property-dependent-function-types.html#2888" class="Bound">𝒯</a><a id="3259" class="Symbol">))</a>

  <a id="3265" class="Keyword">abstract</a>
    <a id="3278" href="foundation.universal-property-dependent-function-types.html#3278" class="Function">universal-property-dependent-function-types-is-terminal</a> <a id="3334" class="Symbol">:</a>
      <a id="3342" href="foundation.terminal-spans-families-of-types.html#929" class="Function">is-terminal-span-type-family</a> <a id="3371" href="foundation.universal-property-dependent-function-types.html#2626" class="Bound">𝒮</a> <a id="3373" class="Symbol">→</a>
      <a id="3381" href="foundation.universal-property-dependent-function-types.html#2255" class="Function">universal-property-dependent-function-types</a> <a id="3425" href="foundation.universal-property-dependent-function-types.html#2626" class="Bound">𝒮</a>
    <a id="3431" href="foundation.universal-property-dependent-function-types.html#3278" class="Function">universal-property-dependent-function-types-is-terminal</a> <a id="3487" href="foundation.universal-property-dependent-function-types.html#3487" class="Bound">U</a> <a id="3489" href="foundation.universal-property-dependent-function-types.html#3489" class="Bound">T</a> <a id="3491" class="Symbol">=</a>
      <a id="3499" href="foundation-core.contractible-maps.html#2276" class="Function">is-equiv-is-contr-map</a>
        <a id="3529" class="Symbol">(</a> <a id="3531" class="Symbol">λ</a> <a id="3533" href="foundation.universal-property-dependent-function-types.html#3533" class="Bound">g</a> <a id="3535" class="Symbol">→</a>
          <a id="3547" href="foundation-core.contractible-types.html#2405" class="Function">is-contr-equiv</a> <a id="3562" class="Symbol">_</a>
            <a id="3576" class="Symbol">(</a> <a id="3578" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a>
              <a id="3602" class="Symbol">(</a> <a id="3604" class="Symbol">λ</a> <a id="3606" href="foundation.universal-property-dependent-function-types.html#3606" class="Bound">h</a> <a id="3608" class="Symbol">→</a>
                <a id="3626" class="Symbol">(</a> <a id="3628" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a>
                  <a id="3667" class="Symbol">(</a> <a id="3669" class="Symbol">λ</a> <a id="3671" href="foundation.universal-property-dependent-function-types.html#3671" class="Bound">a</a> <a id="3673" class="Symbol">→</a>
                    <a id="3695" class="Symbol">(</a> <a id="3697" href="foundation-core.functoriality-dependent-function-types.html#3135" class="Function">equiv-Π-equiv-family</a> <a id="3718" class="Symbol">(λ</a> <a id="3721" href="foundation.universal-property-dependent-function-types.html#3721" class="Bound">t</a> <a id="3723" class="Symbol">→</a> <a id="3725" href="foundation.identity-types.html#1974" class="Function">equiv-inv</a> <a id="3735" class="Symbol">_</a> <a id="3737" class="Symbol">_))</a> <a id="3741" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
                    <a id="3764" class="Symbol">(</a> <a id="3766" href="foundation.function-extensionality.html#4394" class="Function">equiv-funext</a><a id="3778" class="Symbol">)))</a> <a id="3782" href="foundation-core.equivalences.html#13321" class="Function Operator">∘e</a>
                <a id="3801" class="Symbol">(</a> <a id="3803" href="foundation.function-extensionality.html#4394" class="Function">equiv-funext</a><a id="3815" class="Symbol">)))</a>
            <a id="3831" class="Symbol">(</a> <a id="3833" href="foundation.universal-property-dependent-function-types.html#3487" class="Bound">U</a> <a id="3835" class="Symbol">(</a><a id="3836" href="foundation.universal-property-dependent-function-types.html#3489" class="Bound">T</a> <a id="3838" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3840" href="foundation.universal-property-dependent-function-types.html#3533" class="Bound">g</a><a id="3841" class="Symbol">)))</a>
</pre>
## See also

- [Dependent function types](foundation.dependent-function-types.md)
