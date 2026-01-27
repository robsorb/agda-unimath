# Coequalizers

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="synthetic-homotopy-theory.coequalizers.html" class="Module">synthetic-homotopy-theory.coequalizers</a> <a id="71" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="foundation.double-arrows.html" class="Module">foundation.double-arrows</a>
<a id="164" class="Keyword">open</a> <a id="169" class="Keyword">import</a> <a id="176" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="synthetic-homotopy-theory.coforks.html" class="Module">synthetic-homotopy-theory.coforks</a>
<a id="379" class="Keyword">open</a> <a id="384" class="Keyword">import</a> <a id="391" href="synthetic-homotopy-theory.dependent-cocones-under-spans.html" class="Module">synthetic-homotopy-theory.dependent-cocones-under-spans</a>
<a id="447" class="Keyword">open</a> <a id="452" class="Keyword">import</a> <a id="459" href="synthetic-homotopy-theory.dependent-universal-property-coequalizers.html" class="Module">synthetic-homotopy-theory.dependent-universal-property-coequalizers</a>
<a id="527" class="Keyword">open</a> <a id="532" class="Keyword">import</a> <a id="539" href="synthetic-homotopy-theory.pushouts.html" class="Module">synthetic-homotopy-theory.pushouts</a>
<a id="574" class="Keyword">open</a> <a id="579" class="Keyword">import</a> <a id="586" href="synthetic-homotopy-theory.universal-property-coequalizers.html" class="Module">synthetic-homotopy-theory.universal-property-coequalizers</a>
</pre>
</details>

## Idea

The **coequalizer** of a [double arrow](foundation.double-arrows.md)
`f, g : A → B` is the colimiting [cofork](synthetic-homotopy-theory.coforks.md),
i.e. a cofork with the
[universal property of coequalizers](synthetic-homotopy-theory.universal-property-coequalizers.md).

## Properties

### All double arrows admit a coequalizer

The
{{#concept "standard coequalizer" Disambiguation="of types" Agda=standard-coequalizer}}
may be obtained as a [pushout](synthetic-homotopy-theory.pushouts.md) of the
span

```text
     ∇         [f,g]
A <----- A + A -----> B
```

where the left map is the
[codiagonal map](foundation.codiagonal-maps-of-types.md), sending `inl(a)` and
`inr(a)` to `a`, and the right map is defined by the universal property of
[coproducts](foundation.coproduct-types.md) to send `inl(a)` to `f(a)` and
`inr(a)` to `g(a)`.

The pushout thus constructed will consist of a copy of `B`, a copy of `A`, and
for every point `a` of `A` there will be a path from `f(a)` to `a` and to
`g(a)`, which corresponds to having a copy of `B` with paths connecting every
`f(a)` to `g(a)`.

The construction from pushouts itself is an implementation detail, which is why
the definition is marked abstract.

<pre class="Agda"><a id="1885" class="Keyword">module</a> <a id="1892" href="synthetic-homotopy-theory.coequalizers.html#1892" class="Module">_</a>
  <a id="1896" class="Symbol">{</a><a id="1897" href="synthetic-homotopy-theory.coequalizers.html#1897" class="Bound">l1</a> <a id="1900" href="synthetic-homotopy-theory.coequalizers.html#1900" class="Bound">l2</a> <a id="1903" class="Symbol">:</a> <a id="1905" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1910" class="Symbol">}</a> <a id="1912" class="Symbol">(</a><a id="1913" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a> <a id="1915" class="Symbol">:</a> <a id="1917" href="foundation.double-arrows.html#879" class="Function">double-arrow</a> <a id="1930" href="synthetic-homotopy-theory.coequalizers.html#1897" class="Bound">l1</a> <a id="1933" href="synthetic-homotopy-theory.coequalizers.html#1900" class="Bound">l2</a><a id="1935" class="Symbol">)</a>
  <a id="1939" class="Keyword">where</a>

  <a id="1948" class="Keyword">abstract</a>
    <a id="1961" href="synthetic-homotopy-theory.coequalizers.html#1961" class="Function">standard-coequalizer</a> <a id="1982" class="Symbol">:</a> <a id="1984" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1987" class="Symbol">(</a><a id="1988" href="synthetic-homotopy-theory.coequalizers.html#1897" class="Bound">l1</a> <a id="1991" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1993" href="synthetic-homotopy-theory.coequalizers.html#1900" class="Bound">l2</a><a id="1995" class="Symbol">)</a>
    <a id="2001" href="synthetic-homotopy-theory.coequalizers.html#1961" class="Function">standard-coequalizer</a> <a id="2022" class="Symbol">=</a>
      <a id="2030" href="synthetic-homotopy-theory.pushouts.html#2914" class="Postulate">pushout</a>
        <a id="2046" class="Symbol">(</a> <a id="2048" href="synthetic-homotopy-theory.coforks.html#6452" class="Function">vertical-map-span-cocone-cofork</a> <a id="2080" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="2081" class="Symbol">)</a>
        <a id="2091" class="Symbol">(</a> <a id="2093" href="synthetic-homotopy-theory.coforks.html#6634" class="Function">horizontal-map-span-cocone-cofork</a> <a id="2127" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="2128" class="Symbol">)</a>

    <a id="2135" href="synthetic-homotopy-theory.coequalizers.html#2135" class="Function">cofork-standard-coequalizer</a> <a id="2163" class="Symbol">:</a> <a id="2165" href="synthetic-homotopy-theory.coforks.html#2195" class="Function">cofork</a> <a id="2172" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a> <a id="2174" href="synthetic-homotopy-theory.coequalizers.html#1961" class="Function">standard-coequalizer</a>
    <a id="2199" href="synthetic-homotopy-theory.coequalizers.html#2135" class="Function">cofork-standard-coequalizer</a> <a id="2227" class="Symbol">=</a>
      <a id="2235" href="synthetic-homotopy-theory.coforks.html#7124" class="Function">cofork-cocone-codiagonal</a> <a id="2260" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a>
        <a id="2270" class="Symbol">(</a> <a id="2272" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a>
          <a id="2297" class="Symbol">(</a> <a id="2299" href="synthetic-homotopy-theory.coforks.html#6452" class="Function">vertical-map-span-cocone-cofork</a> <a id="2331" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="2332" class="Symbol">)</a>
          <a id="2344" class="Symbol">(</a> <a id="2346" href="synthetic-homotopy-theory.coforks.html#6634" class="Function">horizontal-map-span-cocone-cofork</a> <a id="2380" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="2381" class="Symbol">))</a>

    <a id="2389" href="synthetic-homotopy-theory.coequalizers.html#2389" class="Function">dup-standard-coequalizer</a> <a id="2414" class="Symbol">:</a>
      <a id="2422" href="synthetic-homotopy-theory.dependent-universal-property-coequalizers.html#1500" class="Function">dependent-universal-property-coequalizer</a> <a id="2463" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a> <a id="2465" href="synthetic-homotopy-theory.coequalizers.html#2135" class="Function">cofork-standard-coequalizer</a>
    <a id="2497" href="synthetic-homotopy-theory.coequalizers.html#2389" class="Function">dup-standard-coequalizer</a> <a id="2522" class="Symbol">=</a>
      <a id="2530" href="synthetic-homotopy-theory.dependent-universal-property-coequalizers.html#4169" class="Function">dependent-universal-property-coequalizer-dependent-universal-property-pushout</a>
        <a id="2616" class="Symbol">(</a> <a id="2618" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="2619" class="Symbol">)</a>
        <a id="2629" class="Symbol">(</a> <a id="2631" href="synthetic-homotopy-theory.coequalizers.html#2135" class="Function">cofork-standard-coequalizer</a><a id="2658" class="Symbol">)</a>
        <a id="2668" class="Symbol">(</a> <a id="2670" class="Symbol">λ</a> <a id="2672" href="synthetic-homotopy-theory.coequalizers.html#2672" class="Bound">P</a> <a id="2674" class="Symbol">→</a>
          <a id="2686" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a>
            <a id="2701" class="Symbol">(</a> <a id="2703" class="Symbol">λ</a> <a id="2705" href="synthetic-homotopy-theory.coequalizers.html#2705" class="Bound">c</a> <a id="2707" class="Symbol">→</a>
              <a id="2723" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a>
                <a id="2748" class="Symbol">(</a> <a id="2750" href="synthetic-homotopy-theory.dependent-cocones-under-spans.html#6275" class="Function">dependent-cocone-map</a>
                  <a id="2789" class="Symbol">(</a> <a id="2791" href="synthetic-homotopy-theory.coforks.html#6452" class="Function">vertical-map-span-cocone-cofork</a> <a id="2823" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="2824" class="Symbol">)</a>
                  <a id="2844" class="Symbol">(</a> <a id="2846" href="synthetic-homotopy-theory.coforks.html#6634" class="Function">horizontal-map-span-cocone-cofork</a> <a id="2880" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="2881" class="Symbol">)</a>
                  <a id="2901" class="Symbol">(</a> <a id="2903" href="synthetic-homotopy-theory.coequalizers.html#2705" class="Bound">c</a><a id="2904" class="Symbol">)</a>
                  <a id="2924" class="Symbol">(</a> <a id="2926" href="synthetic-homotopy-theory.coequalizers.html#2672" class="Bound">P</a><a id="2927" class="Symbol">)))</a>
            <a id="2943" class="Symbol">(</a> <a id="2945" href="foundation-core.identity-types.html#6358" class="Function">inv</a>
              <a id="2963" class="Symbol">(</a> <a id="2965" href="foundation-core.equivalences.html#7256" class="Function">is-retraction-map-inv-is-equiv</a>
                <a id="3012" class="Symbol">(</a> <a id="3014" href="synthetic-homotopy-theory.coforks.html#10131" class="Function">is-equiv-cofork-cocone-codiagonal</a> <a id="3048" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="3049" class="Symbol">)</a>
                <a id="3067" class="Symbol">(</a> <a id="3069" href="synthetic-homotopy-theory.pushouts.html#3455" class="Function">cocone-pushout</a>
                  <a id="3102" class="Symbol">(</a> <a id="3104" href="synthetic-homotopy-theory.coforks.html#6452" class="Function">vertical-map-span-cocone-cofork</a> <a id="3136" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="3137" class="Symbol">)</a>
                  <a id="3157" class="Symbol">(</a> <a id="3159" href="synthetic-homotopy-theory.coforks.html#6634" class="Function">horizontal-map-span-cocone-cofork</a> <a id="3193" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="3194" class="Symbol">))))</a>
            <a id="3211" class="Symbol">(</a> <a id="3213" href="synthetic-homotopy-theory.pushouts.html#7197" class="Function">dup-pushout</a>
              <a id="3239" class="Symbol">(</a> <a id="3241" href="synthetic-homotopy-theory.coforks.html#6452" class="Function">vertical-map-span-cocone-cofork</a> <a id="3273" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="3274" class="Symbol">)</a>
              <a id="3290" class="Symbol">(</a> <a id="3292" href="synthetic-homotopy-theory.coforks.html#6634" class="Function">horizontal-map-span-cocone-cofork</a> <a id="3326" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a><a id="3327" class="Symbol">)</a>
              <a id="3343" class="Symbol">(</a> <a id="3345" href="synthetic-homotopy-theory.coequalizers.html#2672" class="Bound">P</a><a id="3346" class="Symbol">)))</a>

    <a id="3355" href="synthetic-homotopy-theory.coequalizers.html#3355" class="Function">up-standard-coequalizer</a> <a id="3379" class="Symbol">:</a>
      <a id="3387" href="synthetic-homotopy-theory.universal-property-coequalizers.html#1580" class="Function">universal-property-coequalizer</a> <a id="3418" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a> <a id="3420" href="synthetic-homotopy-theory.coequalizers.html#2135" class="Function">cofork-standard-coequalizer</a>
    <a id="3452" href="synthetic-homotopy-theory.coequalizers.html#3355" class="Function">up-standard-coequalizer</a> <a id="3476" class="Symbol">=</a>
      <a id="3484" href="synthetic-homotopy-theory.dependent-universal-property-coequalizers.html#6137" class="Function">universal-property-dependent-universal-property-coequalizer</a> <a id="3544" href="synthetic-homotopy-theory.coequalizers.html#1913" class="Bound">a</a>
        <a id="3554" class="Symbol">(</a> <a id="3556" href="synthetic-homotopy-theory.coequalizers.html#2135" class="Function">cofork-standard-coequalizer</a><a id="3583" class="Symbol">)</a>
        <a id="3593" class="Symbol">(</a> <a id="3595" href="synthetic-homotopy-theory.coequalizers.html#2389" class="Function">dup-standard-coequalizer</a><a id="3619" class="Symbol">)</a>
</pre>