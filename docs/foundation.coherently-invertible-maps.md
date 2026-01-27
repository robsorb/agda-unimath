# Coherently invertible maps

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="foundation.coherently-invertible-maps.html" class="Module">foundation.coherently-invertible-maps</a> <a id="84" class="Keyword">where</a>

<a id="91" class="Keyword">open</a> <a id="96" class="Keyword">import</a> <a id="103" href="foundation-core.coherently-invertible-maps.html" class="Module">foundation-core.coherently-invertible-maps</a> <a id="146" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="298" class="Keyword">open</a> <a id="303" class="Keyword">import</a> <a id="310" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="foundation.type-arithmetic-dependent-pair-types.html" class="Module">foundation.type-arithmetic-dependent-pair-types</a>
<a id="440" class="Keyword">open</a> <a id="445" class="Keyword">import</a> <a id="452" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="480" class="Keyword">open</a> <a id="485" class="Keyword">import</a> <a id="492" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="526" class="Keyword">open</a> <a id="531" class="Keyword">import</a> <a id="538" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="573" class="Keyword">open</a> <a id="578" class="Keyword">import</a> <a id="585" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="616" class="Keyword">open</a> <a id="621" class="Keyword">import</a> <a id="628" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="679" class="Keyword">open</a> <a id="684" class="Keyword">import</a> <a id="691" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="720" class="Keyword">open</a> <a id="725" class="Keyword">import</a> <a id="732" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="757" class="Keyword">open</a> <a id="762" class="Keyword">import</a> <a id="769" href="foundation-core.type-theoretic-principle-of-choice.html" class="Module">foundation-core.type-theoretic-principle-of-choice</a>
</pre>
</details>

## Properties

### Coherently invertible maps have a contractible type of sections

**Proof:** Since coherently invertible maps are
[contractible maps](foundation.contractible-maps.md), and products of
[contractible types](foundation-core.contractible-types.md) are contractible, it
follows that the type

```text
  (b : B) → fiber f b
```

is contractible, for any coherently invertible map `f`. However, by the
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md)
it follows that this type is equivalent to the type

```text
  Σ (B → A) (λ g → (b : B) → f (g b) ＝ b),
```

which is the type of [sections](foundation.sections.md) of `f`.

<pre class="Agda"><a id="1519" class="Keyword">module</a> <a id="1526" href="foundation.coherently-invertible-maps.html#1526" class="Module">_</a>
  <a id="1530" class="Symbol">{</a><a id="1531" href="foundation.coherently-invertible-maps.html#1531" class="Bound">l1</a> <a id="1534" href="foundation.coherently-invertible-maps.html#1534" class="Bound">l2</a> <a id="1537" class="Symbol">:</a> <a id="1539" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1544" class="Symbol">}</a> <a id="1546" class="Symbol">{</a><a id="1547" href="foundation.coherently-invertible-maps.html#1547" class="Bound">A</a> <a id="1549" class="Symbol">:</a> <a id="1551" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1554" href="foundation.coherently-invertible-maps.html#1531" class="Bound">l1</a><a id="1556" class="Symbol">}</a> <a id="1558" class="Symbol">{</a><a id="1559" href="foundation.coherently-invertible-maps.html#1559" class="Bound">B</a> <a id="1561" class="Symbol">:</a> <a id="1563" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1566" href="foundation.coherently-invertible-maps.html#1534" class="Bound">l2</a><a id="1568" class="Symbol">}</a>
  <a id="1572" class="Keyword">where</a>

  <a id="1581" class="Keyword">abstract</a>
    <a id="1594" href="foundation.coherently-invertible-maps.html#1594" class="Function">is-contr-section-is-coherently-invertible</a> <a id="1636" class="Symbol">:</a>
      <a id="1644" class="Symbol">{</a><a id="1645" href="foundation.coherently-invertible-maps.html#1645" class="Bound">f</a> <a id="1647" class="Symbol">:</a> <a id="1649" href="foundation.coherently-invertible-maps.html#1547" class="Bound">A</a> <a id="1651" class="Symbol">→</a> <a id="1653" href="foundation.coherently-invertible-maps.html#1559" class="Bound">B</a><a id="1654" class="Symbol">}</a> <a id="1656" class="Symbol">→</a> <a id="1658" href="foundation-core.coherently-invertible-maps.html#3344" class="Function">is-coherently-invertible</a> <a id="1683" href="foundation.coherently-invertible-maps.html#1645" class="Bound">f</a> <a id="1685" class="Symbol">→</a> <a id="1687" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="1696" class="Symbol">(</a><a id="1697" href="foundation-core.sections.html#1373" class="Function">section</a> <a id="1705" href="foundation.coherently-invertible-maps.html#1645" class="Bound">f</a><a id="1706" class="Symbol">)</a>
    <a id="1712" href="foundation.coherently-invertible-maps.html#1594" class="Function">is-contr-section-is-coherently-invertible</a> <a id="1754" class="Symbol">{</a><a id="1755" href="foundation.coherently-invertible-maps.html#1755" class="Bound">f</a><a id="1756" class="Symbol">}</a> <a id="1758" href="foundation.coherently-invertible-maps.html#1758" class="Bound">F</a> <a id="1760" class="Symbol">=</a>
      <a id="1768" href="foundation-core.contractible-types.html#2905" class="Function">is-contr-equiv&#39;</a>
        <a id="1792" class="Symbol">(</a> <a id="1794" class="Symbol">(</a><a id="1795" href="foundation.coherently-invertible-maps.html#1795" class="Bound">b</a> <a id="1797" class="Symbol">:</a> <a id="1799" href="foundation.coherently-invertible-maps.html#1559" class="Bound">B</a><a id="1800" class="Symbol">)</a> <a id="1802" class="Symbol">→</a> <a id="1804" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="1810" href="foundation.coherently-invertible-maps.html#1755" class="Bound">f</a> <a id="1812" href="foundation.coherently-invertible-maps.html#1795" class="Bound">b</a><a id="1813" class="Symbol">)</a>
        <a id="1823" class="Symbol">(</a> <a id="1825" href="foundation-core.type-theoretic-principle-of-choice.html#2895" class="Function">distributive-Π-Σ</a><a id="1841" class="Symbol">)</a>
        <a id="1851" class="Symbol">(</a> <a id="1853" href="foundation-core.contractible-types.html#7898" class="Function">is-contr-Π</a> <a id="1864" class="Symbol">(</a><a id="1865" href="foundation-core.contractible-maps.html#3350" class="Function">is-contr-map-is-coherently-invertible</a> <a id="1903" href="foundation.coherently-invertible-maps.html#1758" class="Bound">F</a><a id="1904" class="Symbol">))</a>
</pre>
### Being coherently invertible is a property

<pre class="Agda"><a id="1967" class="Keyword">module</a> <a id="1974" href="foundation.coherently-invertible-maps.html#1974" class="Module">_</a>
  <a id="1978" class="Symbol">{</a><a id="1979" href="foundation.coherently-invertible-maps.html#1979" class="Bound">l1</a> <a id="1982" href="foundation.coherently-invertible-maps.html#1982" class="Bound">l2</a> <a id="1985" class="Symbol">:</a> <a id="1987" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1992" class="Symbol">}</a> <a id="1994" class="Symbol">{</a><a id="1995" href="foundation.coherently-invertible-maps.html#1995" class="Bound">A</a> <a id="1997" class="Symbol">:</a> <a id="1999" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2002" href="foundation.coherently-invertible-maps.html#1979" class="Bound">l1</a><a id="2004" class="Symbol">}</a> <a id="2006" class="Symbol">{</a><a id="2007" href="foundation.coherently-invertible-maps.html#2007" class="Bound">B</a> <a id="2009" class="Symbol">:</a> <a id="2011" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2014" href="foundation.coherently-invertible-maps.html#1982" class="Bound">l2</a><a id="2016" class="Symbol">}</a> <a id="2018" class="Symbol">(</a><a id="2019" href="foundation.coherently-invertible-maps.html#2019" class="Bound">f</a> <a id="2021" class="Symbol">:</a> <a id="2023" href="foundation.coherently-invertible-maps.html#1995" class="Bound">A</a> <a id="2025" class="Symbol">→</a> <a id="2027" href="foundation.coherently-invertible-maps.html#2007" class="Bound">B</a><a id="2028" class="Symbol">)</a>
  <a id="2032" class="Keyword">where</a>

  <a id="2041" class="Keyword">abstract</a>
    <a id="2054" href="foundation.coherently-invertible-maps.html#2054" class="Function">is-proof-irrelevant-is-coherently-invertible</a> <a id="2099" class="Symbol">:</a>
      <a id="2107" href="foundation-core.propositions.html#2085" class="Function">is-proof-irrelevant</a> <a id="2127" class="Symbol">(</a><a id="2128" href="foundation-core.coherently-invertible-maps.html#3344" class="Function">is-coherently-invertible</a> <a id="2153" href="foundation.coherently-invertible-maps.html#2019" class="Bound">f</a><a id="2154" class="Symbol">)</a>
    <a id="2160" href="foundation.coherently-invertible-maps.html#2054" class="Function">is-proof-irrelevant-is-coherently-invertible</a> <a id="2205" href="foundation.coherently-invertible-maps.html#2205" class="Bound">H</a> <a id="2207" class="Symbol">=</a>
      <a id="2215" href="foundation-core.contractible-types.html#2905" class="Function">is-contr-equiv&#39;</a>
        <a id="2239" class="Symbol">(</a> <a id="2241" class="Symbol">_)</a>
        <a id="2252" class="Symbol">(</a> <a id="2254" href="foundation.type-arithmetic-dependent-pair-types.html#6587" class="Function">associative-Σ</a> <a id="2268" class="Symbol">_</a> <a id="2270" class="Symbol">_</a> <a id="2272" class="Symbol">_)</a>
        <a id="2283" class="Symbol">(</a> <a id="2285" href="foundation-core.contractible-types.html#5365" class="Function">is-contr-Σ</a>
          <a id="2306" class="Symbol">(</a> <a id="2308" href="foundation.coherently-invertible-maps.html#1594" class="Function">is-contr-section-is-coherently-invertible</a> <a id="2350" href="foundation.coherently-invertible-maps.html#2205" class="Bound">H</a><a id="2351" class="Symbol">)</a>
          <a id="2363" class="Symbol">(</a> <a id="2365" href="foundation-core.coherently-invertible-maps.html#4748" class="Function">section-is-coherently-invertible</a> <a id="2398" href="foundation.coherently-invertible-maps.html#2205" class="Bound">H</a><a id="2399" class="Symbol">)</a>
          <a id="2411" class="Symbol">(</a> <a id="2413" href="foundation-core.contractible-types.html#2905" class="Function">is-contr-equiv&#39;</a>
            <a id="2441" class="Symbol">(</a> <a id="2443" class="Symbol">_)</a>
            <a id="2458" class="Symbol">(</a> <a id="2460" href="foundation-core.type-theoretic-principle-of-choice.html#2895" class="Function">distributive-Π-Σ</a><a id="2476" class="Symbol">)</a>
            <a id="2490" class="Symbol">(</a> <a id="2492" href="foundation-core.contractible-types.html#7898" class="Function">is-contr-Π</a>
              <a id="2517" class="Symbol">(</a> <a id="2519" class="Symbol">λ</a> <a id="2521" href="foundation.coherently-invertible-maps.html#2521" class="Bound">x</a> <a id="2523" class="Symbol">→</a>
                <a id="2541" href="foundation-core.contractible-types.html#2905" class="Function">is-contr-equiv&#39;</a>
                  <a id="2575" class="Symbol">(</a> <a id="2577" class="Symbol">_)</a>
                  <a id="2598" class="Symbol">(</a> <a id="2600" href="foundation-core.functoriality-dependent-pair-types.html#7287" class="Function">equiv-tot</a>
                    <a id="2630" class="Symbol">(</a> <a id="2632" class="Symbol">λ</a> <a id="2634" href="foundation.coherently-invertible-maps.html#2634" class="Bound">p</a> <a id="2636" class="Symbol">→</a>
                      <a id="2660" href="foundation.identity-types.html#1974" class="Function">equiv-inv</a>
                        <a id="2694" class="Symbol">(</a> <a id="2696" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="2699" href="foundation.coherently-invertible-maps.html#2019" class="Bound">f</a> <a id="2701" href="foundation.coherently-invertible-maps.html#2634" class="Bound">p</a><a id="2702" class="Symbol">)</a>
                        <a id="2728" class="Symbol">(</a> <a id="2730" href="foundation-core.coherently-invertible-maps.html#3789" class="Function">is-section-map-inv-is-coherently-invertible</a> <a id="2774" href="foundation.coherently-invertible-maps.html#2205" class="Bound">H</a> <a id="2776" class="Symbol">(</a><a id="2777" href="foundation.coherently-invertible-maps.html#2019" class="Bound">f</a> <a id="2779" href="foundation.coherently-invertible-maps.html#2521" class="Bound">x</a><a id="2780" class="Symbol">))))</a>
                  <a id="2803" class="Symbol">(</a> <a id="2805" href="foundation-core.contractible-maps.html#3350" class="Function">is-contr-map-is-coherently-invertible</a>
                    <a id="2863" class="Symbol">(</a> <a id="2865" href="foundation-core.coherently-invertible-maps.html#23799" class="Function">is-coherently-invertible-ap-is-coherently-invertible</a> <a id="2918" href="foundation.coherently-invertible-maps.html#2205" class="Bound">H</a><a id="2919" class="Symbol">)</a>
                    <a id="2941" class="Symbol">(</a> <a id="2943" href="foundation-core.coherently-invertible-maps.html#3789" class="Function">is-section-map-inv-is-coherently-invertible</a> <a id="2987" href="foundation.coherently-invertible-maps.html#2205" class="Bound">H</a> <a id="2989" class="Symbol">(</a><a id="2990" href="foundation.coherently-invertible-maps.html#2019" class="Bound">f</a> <a id="2992" href="foundation.coherently-invertible-maps.html#2521" class="Bound">x</a><a id="2993" class="Symbol">)))))))</a>

  <a id="3004" class="Keyword">abstract</a>
    <a id="3017" href="foundation.coherently-invertible-maps.html#3017" class="Function">is-prop-is-coherently-invertible</a> <a id="3050" class="Symbol">:</a> <a id="3052" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3060" class="Symbol">(</a><a id="3061" href="foundation-core.coherently-invertible-maps.html#3344" class="Function">is-coherently-invertible</a> <a id="3086" href="foundation.coherently-invertible-maps.html#2019" class="Bound">f</a><a id="3087" class="Symbol">)</a>
    <a id="3093" href="foundation.coherently-invertible-maps.html#3017" class="Function">is-prop-is-coherently-invertible</a> <a id="3126" class="Symbol">=</a>
      <a id="3134" href="foundation-core.propositions.html#3025" class="Function">is-prop-is-proof-irrelevant</a> <a id="3162" href="foundation.coherently-invertible-maps.html#2054" class="Function">is-proof-irrelevant-is-coherently-invertible</a>

  <a id="3210" class="Keyword">abstract</a>
    <a id="3223" href="foundation.coherently-invertible-maps.html#3223" class="Function">is-equiv-is-coherently-invertible-is-equiv</a> <a id="3266" class="Symbol">:</a>
      <a id="3274" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="3283" class="Symbol">(</a><a id="3284" href="foundation-core.equivalences.html#6384" class="Function">is-coherently-invertible-is-equiv</a> <a id="3318" class="Symbol">{</a><a id="3319" class="Argument">f</a> <a id="3321" class="Symbol">=</a> <a id="3323" href="foundation.coherently-invertible-maps.html#2019" class="Bound">f</a><a id="3324" class="Symbol">})</a>
    <a id="3331" href="foundation.coherently-invertible-maps.html#3223" class="Function">is-equiv-is-coherently-invertible-is-equiv</a> <a id="3374" class="Symbol">=</a>
      <a id="3382" href="foundation.logical-equivalences.html#4351" class="Function">is-equiv-has-converse-is-prop</a>
        <a id="3420" class="Symbol">(</a> <a id="3422" href="foundation.equivalences.html#4907" class="Function">is-property-is-equiv</a> <a id="3443" href="foundation.coherently-invertible-maps.html#2019" class="Bound">f</a><a id="3444" class="Symbol">)</a>
        <a id="3454" class="Symbol">(</a> <a id="3456" href="foundation.coherently-invertible-maps.html#3017" class="Function">is-prop-is-coherently-invertible</a><a id="3488" class="Symbol">)</a>
        <a id="3498" class="Symbol">(</a> <a id="3500" href="foundation-core.equivalences.html#5803" class="Function">is-equiv-is-coherently-invertible</a><a id="3533" class="Symbol">)</a>
</pre>
### Being transpose coherently invertible is a property

This remains to be formalized.

## References

{{#bibliography}} {{#reference UF13}}

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
