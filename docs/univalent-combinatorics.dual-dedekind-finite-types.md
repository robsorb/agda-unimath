# Dual Dedekind finite types

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="univalent-combinatorics.dual-dedekind-finite-types.html" class="Module">univalent-combinatorics.dual-dedekind-finite-types</a> <a id="97" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="267" class="Keyword">open</a> <a id="272" class="Keyword">import</a> <a id="279" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="401" class="Keyword">open</a> <a id="406" class="Keyword">import</a> <a id="413" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="439" class="Keyword">open</a> <a id="444" class="Keyword">import</a> <a id="451" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="477" class="Keyword">open</a> <a id="482" class="Keyword">import</a> <a id="489" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="526" class="Keyword">open</a> <a id="531" class="Keyword">import</a> <a id="538" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="562" class="Keyword">open</a> <a id="567" class="Keyword">import</a> <a id="574" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="590" class="Keyword">open</a> <a id="595" class="Keyword">import</a> <a id="602" href="foundation.split-surjective-maps.html" class="Module">foundation.split-surjective-maps</a>
<a id="635" class="Keyword">open</a> <a id="640" class="Keyword">import</a> <a id="647" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="674" class="Keyword">open</a> <a id="679" class="Keyword">import</a> <a id="686" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="714" class="Keyword">open</a> <a id="719" class="Keyword">import</a> <a id="726" href="synthetic-homotopy-theory.acyclic-maps.html" class="Module">synthetic-homotopy-theory.acyclic-maps</a>
</pre>
</details>

## Idea

{{#concept "Dual Dedekind finite types" Agda=is-dual-dedekind-finite Agda=Dual-Dedekind-Finite-Type}}
are types `X` with the [property](foundation-core.propositions.md) that every
[acyclic](synthetic-homotopy-theory.acyclic-maps.md) endomap `X ↠ X` is an
[equivalence](foundation-core.equivalences.md).

Recall that a
[Dedekind finite type](univalent-combinatorics.dedekind-finite-types.md) is a
type such that every self-[embedding](foundation-core.embeddings.md) is an
equivalence. The dual Dedekind finiteness condition is formally dual to the
Dedekind finiteness condition, since acyclic maps are precisely the
[epimorphisms](foundation.epimorphisms.md) in the
[∞-category of types](foundation.wild-category-of-types.md), while embeddings
are precisely the [monomorphisms](foundation.monomorphisms.md).

## Definitions

### The predicate of being a dual Dedekind finite type

<pre class="Agda"><a id="is-dual-dedekind-finite-Prop"></a><a id="1679" href="univalent-combinatorics.dual-dedekind-finite-types.html#1679" class="Function">is-dual-dedekind-finite-Prop</a> <a id="1708" class="Symbol">:</a> <a id="1710" class="Symbol">{</a><a id="1711" href="univalent-combinatorics.dual-dedekind-finite-types.html#1711" class="Bound">l</a> <a id="1713" class="Symbol">:</a> <a id="1715" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1720" class="Symbol">}</a> <a id="1722" class="Symbol">→</a> <a id="1724" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1727" href="univalent-combinatorics.dual-dedekind-finite-types.html#1711" class="Bound">l</a> <a id="1729" class="Symbol">→</a> <a id="1731" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1736" href="univalent-combinatorics.dual-dedekind-finite-types.html#1711" class="Bound">l</a>
<a id="1738" href="univalent-combinatorics.dual-dedekind-finite-types.html#1679" class="Function">is-dual-dedekind-finite-Prop</a> <a id="1767" href="univalent-combinatorics.dual-dedekind-finite-types.html#1767" class="Bound">X</a> <a id="1769" class="Symbol">=</a>
  <a id="1773" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
    <a id="1784" class="Symbol">(</a> <a id="1786" href="univalent-combinatorics.dual-dedekind-finite-types.html#1767" class="Bound">X</a> <a id="1788" class="Symbol">→</a> <a id="1790" href="univalent-combinatorics.dual-dedekind-finite-types.html#1767" class="Bound">X</a><a id="1791" class="Symbol">)</a>
    <a id="1797" class="Symbol">(</a> <a id="1799" class="Symbol">λ</a> <a id="1801" href="univalent-combinatorics.dual-dedekind-finite-types.html#1801" class="Bound">f</a> <a id="1803" class="Symbol">→</a> <a id="1805" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a> <a id="1819" class="Symbol">(</a><a id="1820" href="synthetic-homotopy-theory.acyclic-maps.html#2515" class="Function">is-acyclic-map</a> <a id="1835" href="univalent-combinatorics.dual-dedekind-finite-types.html#1801" class="Bound">f</a><a id="1836" class="Symbol">)</a> <a id="1838" class="Symbol">(</a><a id="1839" href="foundation.equivalences.html#5072" class="Function">is-equiv-Prop</a> <a id="1853" href="univalent-combinatorics.dual-dedekind-finite-types.html#1801" class="Bound">f</a><a id="1854" class="Symbol">))</a>

<a id="is-dual-dedekind-finite"></a><a id="1858" href="univalent-combinatorics.dual-dedekind-finite-types.html#1858" class="Function">is-dual-dedekind-finite</a> <a id="1882" class="Symbol">:</a> <a id="1884" class="Symbol">{</a><a id="1885" href="univalent-combinatorics.dual-dedekind-finite-types.html#1885" class="Bound">l</a> <a id="1887" class="Symbol">:</a> <a id="1889" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1894" class="Symbol">}</a> <a id="1896" class="Symbol">→</a> <a id="1898" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1901" href="univalent-combinatorics.dual-dedekind-finite-types.html#1885" class="Bound">l</a> <a id="1903" class="Symbol">→</a> <a id="1905" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1908" href="univalent-combinatorics.dual-dedekind-finite-types.html#1885" class="Bound">l</a>
<a id="1910" href="univalent-combinatorics.dual-dedekind-finite-types.html#1858" class="Function">is-dual-dedekind-finite</a> <a id="1934" href="univalent-combinatorics.dual-dedekind-finite-types.html#1934" class="Bound">X</a> <a id="1936" class="Symbol">=</a> <a id="1938" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1948" class="Symbol">(</a><a id="1949" href="univalent-combinatorics.dual-dedekind-finite-types.html#1679" class="Function">is-dual-dedekind-finite-Prop</a> <a id="1978" href="univalent-combinatorics.dual-dedekind-finite-types.html#1934" class="Bound">X</a><a id="1979" class="Symbol">)</a>

<a id="is-prop-is-dual-dedekind-finite"></a><a id="1982" href="univalent-combinatorics.dual-dedekind-finite-types.html#1982" class="Function">is-prop-is-dual-dedekind-finite</a> <a id="2014" class="Symbol">:</a>
  <a id="2018" class="Symbol">{</a><a id="2019" href="univalent-combinatorics.dual-dedekind-finite-types.html#2019" class="Bound">l</a> <a id="2021" class="Symbol">:</a> <a id="2023" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2028" class="Symbol">}</a> <a id="2030" class="Symbol">{</a><a id="2031" href="univalent-combinatorics.dual-dedekind-finite-types.html#2031" class="Bound">X</a> <a id="2033" class="Symbol">:</a> <a id="2035" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2038" href="univalent-combinatorics.dual-dedekind-finite-types.html#2019" class="Bound">l</a><a id="2039" class="Symbol">}</a> <a id="2041" class="Symbol">→</a> <a id="2043" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2051" class="Symbol">(</a><a id="2052" href="univalent-combinatorics.dual-dedekind-finite-types.html#1858" class="Function">is-dual-dedekind-finite</a> <a id="2076" href="univalent-combinatorics.dual-dedekind-finite-types.html#2031" class="Bound">X</a><a id="2077" class="Symbol">)</a>
<a id="2079" href="univalent-combinatorics.dual-dedekind-finite-types.html#1982" class="Function">is-prop-is-dual-dedekind-finite</a> <a id="2111" class="Symbol">{</a><a id="2112" class="Argument">X</a> <a id="2114" class="Symbol">=</a> <a id="2116" href="univalent-combinatorics.dual-dedekind-finite-types.html#2116" class="Bound">X</a><a id="2117" class="Symbol">}</a> <a id="2119" class="Symbol">=</a>
  <a id="2123" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2141" class="Symbol">(</a><a id="2142" href="univalent-combinatorics.dual-dedekind-finite-types.html#1679" class="Function">is-dual-dedekind-finite-Prop</a> <a id="2171" href="univalent-combinatorics.dual-dedekind-finite-types.html#2116" class="Bound">X</a><a id="2172" class="Symbol">)</a>
</pre>
### The subuniverse of dual Dedekind finite types

<pre class="Agda"><a id="Dual-Dedekind-Finite-Type"></a><a id="2238" href="univalent-combinatorics.dual-dedekind-finite-types.html#2238" class="Function">Dual-Dedekind-Finite-Type</a> <a id="2264" class="Symbol">:</a> <a id="2266" class="Symbol">(</a><a id="2267" href="univalent-combinatorics.dual-dedekind-finite-types.html#2267" class="Bound">l</a> <a id="2269" class="Symbol">:</a> <a id="2271" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2276" class="Symbol">)</a> <a id="2278" class="Symbol">→</a> <a id="2280" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2283" class="Symbol">(</a><a id="2284" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2289" href="univalent-combinatorics.dual-dedekind-finite-types.html#2267" class="Bound">l</a><a id="2290" class="Symbol">)</a>
<a id="2292" href="univalent-combinatorics.dual-dedekind-finite-types.html#2238" class="Function">Dual-Dedekind-Finite-Type</a> <a id="2318" href="univalent-combinatorics.dual-dedekind-finite-types.html#2318" class="Bound">l</a> <a id="2320" class="Symbol">=</a> <a id="2322" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2324" class="Symbol">(</a><a id="2325" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2328" href="univalent-combinatorics.dual-dedekind-finite-types.html#2318" class="Bound">l</a><a id="2329" class="Symbol">)</a> <a id="2331" href="univalent-combinatorics.dual-dedekind-finite-types.html#1858" class="Function">is-dual-dedekind-finite</a>

<a id="2356" class="Keyword">module</a> <a id="2363" href="univalent-combinatorics.dual-dedekind-finite-types.html#2363" class="Module">_</a>
  <a id="2367" class="Symbol">{</a><a id="2368" href="univalent-combinatorics.dual-dedekind-finite-types.html#2368" class="Bound">l</a> <a id="2370" class="Symbol">:</a> <a id="2372" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2377" class="Symbol">}</a> <a id="2379" class="Symbol">(</a><a id="2380" href="univalent-combinatorics.dual-dedekind-finite-types.html#2380" class="Bound">X</a> <a id="2382" class="Symbol">:</a> <a id="2384" href="univalent-combinatorics.dual-dedekind-finite-types.html#2238" class="Function">Dual-Dedekind-Finite-Type</a> <a id="2410" href="univalent-combinatorics.dual-dedekind-finite-types.html#2368" class="Bound">l</a><a id="2411" class="Symbol">)</a>
  <a id="2415" class="Keyword">where</a>

  <a id="2424" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a> <a id="2455" class="Symbol">:</a> <a id="2457" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2460" href="univalent-combinatorics.dual-dedekind-finite-types.html#2368" class="Bound">l</a>
  <a id="2464" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a> <a id="2495" class="Symbol">=</a> <a id="2497" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2501" href="univalent-combinatorics.dual-dedekind-finite-types.html#2380" class="Bound">X</a>

  <a id="2506" href="univalent-combinatorics.dual-dedekind-finite-types.html#2506" class="Function">is-dual-dedekind-finite-Dual-Dedekind-Finite-Type</a> <a id="2556" class="Symbol">:</a>
    <a id="2562" href="univalent-combinatorics.dual-dedekind-finite-types.html#1858" class="Function">is-dual-dedekind-finite</a> <a id="2586" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a>
  <a id="2619" href="univalent-combinatorics.dual-dedekind-finite-types.html#2506" class="Function">is-dual-dedekind-finite-Dual-Dedekind-Finite-Type</a> <a id="2669" class="Symbol">=</a> <a id="2671" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2675" href="univalent-combinatorics.dual-dedekind-finite-types.html#2380" class="Bound">X</a>
</pre>
## Properties

### If two dual Dedekind finite types mutually project, they are equivalent

This can be understood as a constructive dual
[Cantor–Schröder–Bernstein theorem](foundation.cantor-schroder-bernstein-escardo.md)
for dual Dedekind finite types.

**Proof.** Given epimorphisms `f : X ↠ Y` and `g : Y ↠ X`, we have a commuting
diagram

```text
       g ∘ f
    X ------> X
    |       ∧ |
  f |   g /   | f
    |   /     |
    ∨ /       ∨
    Y ------> Y.
       f ∘ g
```

The top and bottom rows are equivalences by dual Dedekind finiteness, so by the
6-for-2 property of equivalences every edge in this diagram is an equivalence. ∎

<pre class="Agda"><a id="3334" class="Keyword">module</a> <a id="3341" href="univalent-combinatorics.dual-dedekind-finite-types.html#3341" class="Module">_</a>
  <a id="3345" class="Symbol">{</a><a id="3346" href="univalent-combinatorics.dual-dedekind-finite-types.html#3346" class="Bound">l1</a> <a id="3349" href="univalent-combinatorics.dual-dedekind-finite-types.html#3349" class="Bound">l2</a> <a id="3352" class="Symbol">:</a> <a id="3354" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3359" class="Symbol">}</a>
  <a id="3363" class="Symbol">(</a><a id="3364" href="univalent-combinatorics.dual-dedekind-finite-types.html#3364" class="Bound">X</a> <a id="3366" class="Symbol">:</a> <a id="3368" href="univalent-combinatorics.dual-dedekind-finite-types.html#2238" class="Function">Dual-Dedekind-Finite-Type</a> <a id="3394" href="univalent-combinatorics.dual-dedekind-finite-types.html#3346" class="Bound">l1</a><a id="3396" class="Symbol">)</a>
  <a id="3400" class="Symbol">(</a><a id="3401" href="univalent-combinatorics.dual-dedekind-finite-types.html#3401" class="Bound">Y</a> <a id="3403" class="Symbol">:</a> <a id="3405" href="univalent-combinatorics.dual-dedekind-finite-types.html#2238" class="Function">Dual-Dedekind-Finite-Type</a> <a id="3431" href="univalent-combinatorics.dual-dedekind-finite-types.html#3349" class="Bound">l2</a><a id="3433" class="Symbol">)</a>
  <a id="3437" class="Symbol">(</a><a id="3438" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a> <a id="3440" class="Symbol">:</a>
    <a id="3446" href="synthetic-homotopy-theory.acyclic-maps.html#2793" class="Function">acyclic-map</a>
      <a id="3464" class="Symbol">(</a> <a id="3466" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a> <a id="3497" href="univalent-combinatorics.dual-dedekind-finite-types.html#3364" class="Bound">X</a><a id="3498" class="Symbol">)</a>
      <a id="3506" class="Symbol">(</a> <a id="3508" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a> <a id="3539" href="univalent-combinatorics.dual-dedekind-finite-types.html#3401" class="Bound">Y</a><a id="3540" class="Symbol">))</a>
  <a id="3545" class="Symbol">(</a><a id="3546" href="univalent-combinatorics.dual-dedekind-finite-types.html#3546" class="Bound">g</a> <a id="3548" class="Symbol">:</a>
    <a id="3554" href="synthetic-homotopy-theory.acyclic-maps.html#2793" class="Function">acyclic-map</a>
      <a id="3572" class="Symbol">(</a> <a id="3574" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a> <a id="3605" href="univalent-combinatorics.dual-dedekind-finite-types.html#3401" class="Bound">Y</a><a id="3606" class="Symbol">)</a>
      <a id="3614" class="Symbol">(</a> <a id="3616" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a> <a id="3647" href="univalent-combinatorics.dual-dedekind-finite-types.html#3364" class="Bound">X</a><a id="3648" class="Symbol">))</a>
  <a id="3653" class="Keyword">where</a>

  <a id="3662" href="univalent-combinatorics.dual-dedekind-finite-types.html#3662" class="Function">is-equiv-map-Cantor-Schröder-Bernstein-Dual-Dedekind-Finite-Type</a> <a id="3727" class="Symbol">:</a>
    <a id="3733" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="3742" class="Symbol">(</a><a id="3743" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="3759" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a><a id="3760" class="Symbol">)</a>
  <a id="3764" href="univalent-combinatorics.dual-dedekind-finite-types.html#3662" class="Function">is-equiv-map-Cantor-Schröder-Bernstein-Dual-Dedekind-Finite-Type</a> <a id="3829" class="Symbol">=</a>
    <a id="3835" href="foundation.equivalences.html#12459" class="Function">is-equiv-left-is-equiv-top-is-equiv-bottom-square</a>
      <a id="3891" class="Symbol">(</a> <a id="3893" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="3909" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a><a id="3910" class="Symbol">)</a>
      <a id="3918" class="Symbol">(</a> <a id="3920" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="3936" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a><a id="3937" class="Symbol">)</a>
      <a id="3945" class="Symbol">(</a> <a id="3947" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="3963" href="univalent-combinatorics.dual-dedekind-finite-types.html#3546" class="Bound">g</a><a id="3964" class="Symbol">)</a>
      <a id="3972" class="Symbol">(</a> <a id="3974" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="3983" class="Symbol">)</a>
      <a id="3991" class="Symbol">(</a> <a id="3993" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a><a id="4002" class="Symbol">)</a>
      <a id="4010" class="Symbol">(</a> <a id="4012" href="univalent-combinatorics.dual-dedekind-finite-types.html#2506" class="Function">is-dual-dedekind-finite-Dual-Dedekind-Finite-Type</a> <a id="4062" href="univalent-combinatorics.dual-dedekind-finite-types.html#3364" class="Bound">X</a>
        <a id="4072" class="Symbol">(</a> <a id="4074" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="4090" href="univalent-combinatorics.dual-dedekind-finite-types.html#3546" class="Bound">g</a> <a id="4092" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4094" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="4110" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a><a id="4111" class="Symbol">)</a>
        <a id="4121" class="Symbol">(</a> <a id="4123" href="synthetic-homotopy-theory.acyclic-maps.html#10461" class="Function">is-acyclic-map-comp-acyclic-map</a> <a id="4155" href="univalent-combinatorics.dual-dedekind-finite-types.html#3546" class="Bound">g</a> <a id="4157" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a><a id="4158" class="Symbol">))</a>
      <a id="4167" class="Symbol">(</a> <a id="4169" href="univalent-combinatorics.dual-dedekind-finite-types.html#2506" class="Function">is-dual-dedekind-finite-Dual-Dedekind-Finite-Type</a> <a id="4219" href="univalent-combinatorics.dual-dedekind-finite-types.html#3401" class="Bound">Y</a>
        <a id="4229" class="Symbol">(</a> <a id="4231" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="4247" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a> <a id="4249" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4251" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="4267" href="univalent-combinatorics.dual-dedekind-finite-types.html#3546" class="Bound">g</a><a id="4268" class="Symbol">)</a>
        <a id="4278" class="Symbol">(</a> <a id="4280" href="synthetic-homotopy-theory.acyclic-maps.html#10461" class="Function">is-acyclic-map-comp-acyclic-map</a> <a id="4312" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a> <a id="4314" href="univalent-combinatorics.dual-dedekind-finite-types.html#3546" class="Bound">g</a><a id="4315" class="Symbol">))</a>

  <a id="4321" href="univalent-combinatorics.dual-dedekind-finite-types.html#4321" class="Function">Cantor-Schröder-Bernstein-Dual-Dedekind-Finite-Type</a> <a id="4373" class="Symbol">:</a>
    <a id="4379" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a> <a id="4410" href="univalent-combinatorics.dual-dedekind-finite-types.html#3364" class="Bound">X</a> <a id="4412" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="4414" href="univalent-combinatorics.dual-dedekind-finite-types.html#2424" class="Function">type-Dual-Dedekind-Finite-Type</a> <a id="4445" href="univalent-combinatorics.dual-dedekind-finite-types.html#3401" class="Bound">Y</a>
  <a id="4449" href="univalent-combinatorics.dual-dedekind-finite-types.html#4321" class="Function">Cantor-Schröder-Bernstein-Dual-Dedekind-Finite-Type</a> <a id="4501" class="Symbol">=</a>
    <a id="4507" class="Symbol">(</a> <a id="4509" href="synthetic-homotopy-theory.acyclic-maps.html#2984" class="Function">map-acyclic-map</a> <a id="4525" href="univalent-combinatorics.dual-dedekind-finite-types.html#3438" class="Bound">f</a> <a id="4527" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="4535" href="univalent-combinatorics.dual-dedekind-finite-types.html#3662" class="Function">is-equiv-map-Cantor-Schröder-Bernstein-Dual-Dedekind-Finite-Type</a><a id="4599" class="Symbol">)</a>
</pre>
## See also

- [Dedekind finite types](univalent-combinatorics.dedekind-finite-types.md)

## External links

- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
