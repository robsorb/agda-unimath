# Coherently idempotent maps

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="foundation.coherently-idempotent-maps.html" class="Module">foundation.coherently-idempotent-maps</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation.homotopy-algebra.html" class="Module">foundation.homotopy-algebra</a>
<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="foundation.quasicoherently-idempotent-maps.html" class="Module">foundation.quasicoherently-idempotent-maps</a>
<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a>
<a id="378" class="Keyword">open</a> <a id="383" class="Keyword">import</a> <a id="390" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="475" class="Keyword">open</a> <a id="480" class="Keyword">import</a> <a id="487" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="518" class="Keyword">open</a> <a id="523" class="Keyword">import</a> <a id="530" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="557" class="Keyword">open</a> <a id="562" class="Keyword">import</a> <a id="569" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="598" class="Keyword">open</a> <a id="603" class="Keyword">import</a> <a id="610" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>
<a id="638" class="Keyword">open</a> <a id="643" class="Keyword">import</a> <a id="650" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
</pre>
</details>

## Idea

A
{{#concept "coherently idempotent map" Disambiguation="of types" Agda=is-coherently-idempotent}}
is an [idempotent](foundation.idempotent-maps.md) map `f : A → A`
[equipped](foundation.structure.md) with an infinitely coherent hierarchy of
[homotopies](foundation-core.homotopies.md) making it a "homotopy-correct"
definition of an idempotent map in Homotopy Type Theory.

The infinite coherence condition is given by taking the
[sequential limit](foundation.sequential-limits.md) of iterated application of
the splitting construction on
[quasicoherently idempotent maps](foundation.quasicoherently-idempotent-maps.md)
given in {{#cite Shu17}}:

```text
  is-coherently-idempotent f :=
    Σ (a : ℕ → is-quasicoherently-idempotent f), (Π (n : ℕ), split(aₙ₊₁) ~ aₙ)
```

**Terminology.** Our definition of a _coherently idempotent map_ corresponds to
the definition of a _(fully coherent) idempotent map_ in {{#reference Shu17}}
and {{#reference Shu14SplittingIdempotents}}. Our definition of an _idempotent
map_ corresponds in their terminology to a _pre-idempotent map_.

## Definitions

### The structure on a map of coherent idempotence

<pre class="Agda"><a id="is-coherently-idempotent"></a><a id="1848" href="foundation.coherently-idempotent-maps.html#1848" class="Function">is-coherently-idempotent</a> <a id="1873" class="Symbol">:</a> <a id="1875" class="Symbol">{</a><a id="1876" href="foundation.coherently-idempotent-maps.html#1876" class="Bound">l</a> <a id="1878" class="Symbol">:</a> <a id="1880" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1885" class="Symbol">}</a> <a id="1887" class="Symbol">{</a><a id="1888" href="foundation.coherently-idempotent-maps.html#1888" class="Bound">A</a> <a id="1890" class="Symbol">:</a> <a id="1892" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1895" href="foundation.coherently-idempotent-maps.html#1876" class="Bound">l</a><a id="1896" class="Symbol">}</a> <a id="1898" class="Symbol">→</a> <a id="1900" class="Symbol">(</a><a id="1901" href="foundation.coherently-idempotent-maps.html#1888" class="Bound">A</a> <a id="1903" class="Symbol">→</a> <a id="1905" href="foundation.coherently-idempotent-maps.html#1888" class="Bound">A</a><a id="1906" class="Symbol">)</a> <a id="1908" class="Symbol">→</a> <a id="1910" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1913" href="foundation.coherently-idempotent-maps.html#1876" class="Bound">l</a>
<a id="1915" href="foundation.coherently-idempotent-maps.html#1848" class="Function">is-coherently-idempotent</a> <a id="1940" href="foundation.coherently-idempotent-maps.html#1940" class="Bound">f</a> <a id="1942" class="Symbol">=</a>
  <a id="1946" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1948" class="Symbol">(</a> <a id="1950" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1952" class="Symbol">→</a> <a id="1954" href="foundation.quasicoherently-idempotent-maps.html#2385" class="Function">is-quasicoherently-idempotent</a> <a id="1984" href="foundation.coherently-idempotent-maps.html#1940" class="Bound">f</a><a id="1985" class="Symbol">)</a>
    <a id="1991" class="Symbol">(</a> <a id="1993" class="Symbol">λ</a> <a id="1995" href="foundation.coherently-idempotent-maps.html#1995" class="Bound">a</a> <a id="1997" class="Symbol">→</a>
      <a id="2005" class="Symbol">(</a><a id="2006" href="foundation.coherently-idempotent-maps.html#2006" class="Bound">n</a> <a id="2008" class="Symbol">:</a> <a id="2010" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2011" class="Symbol">)</a> <a id="2013" class="Symbol">→</a>
      <a id="2021" href="foundation.quasicoherently-idempotent-maps.html#15263" class="Function">htpy-is-quasicoherently-idempotent</a>
        <a id="2064" class="Symbol">(</a> <a id="2066" href="foundation.split-idempotent-maps.html#18562" class="Function">is-quasicoherently-idempotent-is-split-idempotent</a>
          <a id="2126" class="Symbol">(</a> <a id="2128" href="foundation.split-idempotent-maps.html#39540" class="Function">is-split-idempotent-is-quasicoherently-idempotent</a>
            <a id="2190" class="Symbol">(</a> <a id="2192" href="foundation.coherently-idempotent-maps.html#1995" class="Bound">a</a> <a id="2194" class="Symbol">(</a><a id="2195" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2202" href="foundation.coherently-idempotent-maps.html#2006" class="Bound">n</a><a id="2203" class="Symbol">))))</a>
        <a id="2216" class="Symbol">(</a> <a id="2218" href="foundation.coherently-idempotent-maps.html#1995" class="Bound">a</a> <a id="2220" href="foundation.coherently-idempotent-maps.html#2006" class="Bound">n</a><a id="2221" class="Symbol">))</a>
</pre>
## See also

- [Split idempotent maps](foundation.split-idempotent-maps.md)

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
