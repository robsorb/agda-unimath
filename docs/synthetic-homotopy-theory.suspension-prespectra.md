# Suspension prespectra

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="synthetic-homotopy-theory.suspension-prespectra.html" class="Module">synthetic-homotopy-theory.suspension-prespectra</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>

<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html" class="Module">synthetic-homotopy-theory.iterated-suspensions-of-pointed-types</a>
<a id="445" class="Keyword">open</a> <a id="450" class="Keyword">import</a> <a id="457" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
<a id="495" class="Keyword">open</a> <a id="500" class="Keyword">import</a> <a id="507" href="synthetic-homotopy-theory.prespectra.html" class="Module">synthetic-homotopy-theory.prespectra</a>
<a id="544" class="Keyword">open</a> <a id="549" class="Keyword">import</a> <a id="556" href="synthetic-homotopy-theory.suspensions-of-pointed-types.html" class="Module">synthetic-homotopy-theory.suspensions-of-pointed-types</a>
<a id="611" class="Keyword">open</a> <a id="616" class="Keyword">import</a> <a id="623" href="synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.html" class="Module">synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types</a>
</pre>
</details>

## Idea

Given a [pointed type](structured-types.pointed-types.md) `A`, the
[sequence](lists.sequences.md) of
[iterated suspensions](synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.md)
of `A`

```text
  A   Σ¹A   Σ²A   Σ³A   ...
```

defines a [prespectrum](synthetic-homotopy-theory.prespectra.md) `Σ^∞A` that we
call the **suspension prespectrum** of `A`. Its structure map is defined
degreewise by the identity

```text
  Σⁿ⁺¹A = Σⁿ⁺¹A   ↝   ΣⁿA →∗ ΩΣⁿ⁺¹A
```

**Note:** Even though the suspension prespectrum is defined degreewise by the
adjoint to the identity map, it is not in general a
[spectrum](synthetic-homotopy-theory.spectra.md), as the transposing map of the
[loop-suspension adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md)
does not generally send [equivalences](foundation-core.equivalences.md) to
equivalences.

## Definition

<pre class="Agda"><a id="pointed-structure-map-suspension-Prespectrum"></a><a id="1624" href="synthetic-homotopy-theory.suspension-prespectra.html#1624" class="Function">pointed-structure-map-suspension-Prespectrum</a> <a id="1669" class="Symbol">:</a>
  <a id="1673" class="Symbol">{</a><a id="1674" href="synthetic-homotopy-theory.suspension-prespectra.html#1674" class="Bound">l</a> <a id="1676" class="Symbol">:</a> <a id="1678" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1683" class="Symbol">}</a> <a id="1685" class="Symbol">(</a><a id="1686" href="synthetic-homotopy-theory.suspension-prespectra.html#1686" class="Bound">A</a> <a id="1688" class="Symbol">:</a> <a id="1690" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1703" href="synthetic-homotopy-theory.suspension-prespectra.html#1674" class="Bound">l</a><a id="1704" class="Symbol">)</a> <a id="1706" class="Symbol">(</a><a id="1707" href="synthetic-homotopy-theory.suspension-prespectra.html#1707" class="Bound">n</a> <a id="1709" class="Symbol">:</a> <a id="1711" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1712" class="Symbol">)</a> <a id="1714" class="Symbol">→</a>
  <a id="1718" href="synthetic-homotopy-theory.suspensions-of-pointed-types.html#674" class="Function">suspension-Pointed-Type</a> <a id="1742" class="Symbol">(</a><a id="1743" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html#710" class="Function">iterated-suspension-Pointed-Type</a> <a id="1776" href="synthetic-homotopy-theory.suspension-prespectra.html#1707" class="Bound">n</a> <a id="1778" href="synthetic-homotopy-theory.suspension-prespectra.html#1686" class="Bound">A</a><a id="1779" class="Symbol">)</a> <a id="1781" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a>
  <a id="1786" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html#710" class="Function">iterated-suspension-Pointed-Type</a> <a id="1819" class="Symbol">(</a><a id="1820" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1827" href="synthetic-homotopy-theory.suspension-prespectra.html#1707" class="Bound">n</a><a id="1828" class="Symbol">)</a> <a id="1830" href="synthetic-homotopy-theory.suspension-prespectra.html#1686" class="Bound">A</a>
<a id="1832" href="synthetic-homotopy-theory.suspension-prespectra.html#1624" class="Function">pointed-structure-map-suspension-Prespectrum</a> <a id="1877" href="synthetic-homotopy-theory.suspension-prespectra.html#1877" class="Bound">A</a> <a id="1879" href="synthetic-homotopy-theory.suspension-prespectra.html#1879" class="Bound">n</a> <a id="1881" class="Symbol">=</a> <a id="1883" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a>

<a id="pointed-adjoint-structure-map-suspension-Prespectrum"></a><a id="1899" href="synthetic-homotopy-theory.suspension-prespectra.html#1899" class="Function">pointed-adjoint-structure-map-suspension-Prespectrum</a> <a id="1952" class="Symbol">:</a>
  <a id="1956" class="Symbol">{</a><a id="1957" href="synthetic-homotopy-theory.suspension-prespectra.html#1957" class="Bound">l</a> <a id="1959" class="Symbol">:</a> <a id="1961" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1966" class="Symbol">}</a> <a id="1968" class="Symbol">(</a><a id="1969" href="synthetic-homotopy-theory.suspension-prespectra.html#1969" class="Bound">A</a> <a id="1971" class="Symbol">:</a> <a id="1973" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1986" href="synthetic-homotopy-theory.suspension-prespectra.html#1957" class="Bound">l</a><a id="1987" class="Symbol">)</a> <a id="1989" class="Symbol">(</a><a id="1990" href="synthetic-homotopy-theory.suspension-prespectra.html#1990" class="Bound">n</a> <a id="1992" class="Symbol">:</a> <a id="1994" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1995" class="Symbol">)</a> <a id="1997" class="Symbol">→</a>
  <a id="2001" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html#710" class="Function">iterated-suspension-Pointed-Type</a> <a id="2034" href="synthetic-homotopy-theory.suspension-prespectra.html#1990" class="Bound">n</a> <a id="2036" href="synthetic-homotopy-theory.suspension-prespectra.html#1969" class="Bound">A</a> <a id="2038" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a>
  <a id="2043" href="synthetic-homotopy-theory.loop-spaces.html#1152" class="Function">Ω</a> <a id="2045" class="Symbol">(</a><a id="2046" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html#710" class="Function">iterated-suspension-Pointed-Type</a> <a id="2079" class="Symbol">(</a><a id="2080" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2087" href="synthetic-homotopy-theory.suspension-prespectra.html#1990" class="Bound">n</a><a id="2088" class="Symbol">)</a> <a id="2090" href="synthetic-homotopy-theory.suspension-prespectra.html#1969" class="Bound">A</a><a id="2091" class="Symbol">)</a>
<a id="2093" href="synthetic-homotopy-theory.suspension-prespectra.html#1899" class="Function">pointed-adjoint-structure-map-suspension-Prespectrum</a> <a id="2146" href="synthetic-homotopy-theory.suspension-prespectra.html#2146" class="Bound">A</a> <a id="2148" href="synthetic-homotopy-theory.suspension-prespectra.html#2148" class="Bound">n</a> <a id="2150" class="Symbol">=</a>
  <a id="2154" href="synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.html#3732" class="Function">transpose-suspension-loop-adjunction</a>
    <a id="2195" class="Symbol">(</a> <a id="2197" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html#710" class="Function">iterated-suspension-Pointed-Type</a> <a id="2230" href="synthetic-homotopy-theory.suspension-prespectra.html#2148" class="Bound">n</a> <a id="2232" href="synthetic-homotopy-theory.suspension-prespectra.html#2146" class="Bound">A</a><a id="2233" class="Symbol">)</a>
    <a id="2239" class="Symbol">(</a> <a id="2241" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html#710" class="Function">iterated-suspension-Pointed-Type</a> <a id="2274" class="Symbol">(</a><a id="2275" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2282" href="synthetic-homotopy-theory.suspension-prespectra.html#2148" class="Bound">n</a><a id="2283" class="Symbol">)</a> <a id="2285" href="synthetic-homotopy-theory.suspension-prespectra.html#2146" class="Bound">A</a><a id="2286" class="Symbol">)</a>
    <a id="2292" class="Symbol">(</a> <a id="2294" href="synthetic-homotopy-theory.suspension-prespectra.html#1624" class="Function">pointed-structure-map-suspension-Prespectrum</a> <a id="2339" href="synthetic-homotopy-theory.suspension-prespectra.html#2146" class="Bound">A</a> <a id="2341" href="synthetic-homotopy-theory.suspension-prespectra.html#2148" class="Bound">n</a><a id="2342" class="Symbol">)</a>

<a id="suspension-Prespectrum"></a><a id="2345" href="synthetic-homotopy-theory.suspension-prespectra.html#2345" class="Function">suspension-Prespectrum</a> <a id="2368" class="Symbol">:</a> <a id="2370" class="Symbol">{</a><a id="2371" href="synthetic-homotopy-theory.suspension-prespectra.html#2371" class="Bound">l</a> <a id="2373" class="Symbol">:</a> <a id="2375" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2380" class="Symbol">}</a> <a id="2382" class="Symbol">→</a> <a id="2384" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2397" href="synthetic-homotopy-theory.suspension-prespectra.html#2371" class="Bound">l</a> <a id="2399" class="Symbol">→</a> <a id="2401" href="synthetic-homotopy-theory.prespectra.html#1274" class="Function">Prespectrum</a> <a id="2413" href="synthetic-homotopy-theory.suspension-prespectra.html#2371" class="Bound">l</a>
<a id="2415" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2419" class="Symbol">(</a><a id="2420" href="synthetic-homotopy-theory.suspension-prespectra.html#2345" class="Function">suspension-Prespectrum</a> <a id="2443" href="synthetic-homotopy-theory.suspension-prespectra.html#2443" class="Bound">A</a><a id="2444" class="Symbol">)</a> <a id="2446" href="synthetic-homotopy-theory.suspension-prespectra.html#2446" class="Bound">n</a> <a id="2448" class="Symbol">=</a> <a id="2450" href="synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.html#710" class="Function">iterated-suspension-Pointed-Type</a> <a id="2483" href="synthetic-homotopy-theory.suspension-prespectra.html#2446" class="Bound">n</a> <a id="2485" href="synthetic-homotopy-theory.suspension-prespectra.html#2443" class="Bound">A</a>
<a id="2487" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2491" class="Symbol">(</a><a id="2492" href="synthetic-homotopy-theory.suspension-prespectra.html#2345" class="Function">suspension-Prespectrum</a> <a id="2515" href="synthetic-homotopy-theory.suspension-prespectra.html#2515" class="Bound">A</a><a id="2516" class="Symbol">)</a> <a id="2518" class="Symbol">=</a>
  <a id="2522" href="synthetic-homotopy-theory.suspension-prespectra.html#1899" class="Function">pointed-adjoint-structure-map-suspension-Prespectrum</a> <a id="2575" href="synthetic-homotopy-theory.suspension-prespectra.html#2515" class="Bound">A</a>
</pre>