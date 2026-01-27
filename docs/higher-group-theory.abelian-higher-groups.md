# Abelian higher groups

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="higher-group-theory.abelian-higher-groups.html" class="Module">higher-group-theory.abelian-higher-groups</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.small-types.html" class="Module">foundation.small-types</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="higher-group-theory.equivalences-higher-groups.html" class="Module">higher-group-theory.equivalences-higher-groups</a>
<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>
<a id="399" class="Keyword">open</a> <a id="404" class="Keyword">import</a> <a id="411" href="higher-group-theory.small-higher-groups.html" class="Module">higher-group-theory.small-higher-groups</a>

<a id="452" class="Keyword">open</a> <a id="457" class="Keyword">import</a> <a id="464" href="structured-types.pointed-equivalences.html" class="Module">structured-types.pointed-equivalences</a>
<a id="502" class="Keyword">open</a> <a id="507" class="Keyword">import</a> <a id="514" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
<a id="545" class="Keyword">open</a> <a id="550" class="Keyword">import</a> <a id="557" href="structured-types.small-pointed-types.html" class="Module">structured-types.small-pointed-types</a>

<a id="595" class="Keyword">open</a> <a id="600" class="Keyword">import</a> <a id="607" href="synthetic-homotopy-theory.connective-spectra.html" class="Module">synthetic-homotopy-theory.connective-spectra</a>
</pre>
</details>

## Idea

An {{#concept "abelian" Disambiguation="∞-group"}}, or
{{#concept "commutative" Disambiguation="∞-group"}} ∞-group is a
[higher group](higher-group-theory.higher-groups.md) `A₀` that is commutative in
a fully coherent way. There are multiple ways to express this in Homotopy Type
Theory. One way is to say there is a
[connective spectrum](synthetic-homotopy-theory.connective-spectra.md) `𝒜` such
that the ∞-group appears as the first type in the sequence. {{#cite BvDR18}}
I.e., there exists a sequence of increasingly
[connected](foundation.connected-types.md) ∞-groups

```text
  A₀   A₁   A₂   A₃   ⋯   Aᵢ   ⋯
```

such that

```text
  Aᵢ ≃∗ Ω Aᵢ₊₁
```

Abelian ∞-groups thus give an example of another infinitely coherent structure
that is definable in Homotopy Type Theory.

## Definitions

### The connective spectrum condition of being abelian with respect to a universe level

<pre class="Agda"><a id="is-abelian-level-connective-spectrum-condition-∞-Group"></a><a id="1572" href="higher-group-theory.abelian-higher-groups.html#1572" class="Function">is-abelian-level-connective-spectrum-condition-∞-Group</a> <a id="1627" class="Symbol">:</a>
  <a id="1631" class="Symbol">{</a><a id="1632" href="higher-group-theory.abelian-higher-groups.html#1632" class="Bound">l</a> <a id="1634" class="Symbol">:</a> <a id="1636" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1641" class="Symbol">}</a> <a id="1643" class="Symbol">(</a><a id="1644" href="higher-group-theory.abelian-higher-groups.html#1644" class="Bound">l1</a> <a id="1647" class="Symbol">:</a> <a id="1649" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1654" class="Symbol">)</a> <a id="1656" class="Symbol">→</a> <a id="1658" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="1666" href="higher-group-theory.abelian-higher-groups.html#1632" class="Bound">l</a> <a id="1668" class="Symbol">→</a> <a id="1670" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1673" class="Symbol">(</a><a id="1674" href="higher-group-theory.abelian-higher-groups.html#1632" class="Bound">l</a> <a id="1676" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1678" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1683" href="higher-group-theory.abelian-higher-groups.html#1644" class="Bound">l1</a><a id="1685" class="Symbol">)</a>
<a id="1687" href="higher-group-theory.abelian-higher-groups.html#1572" class="Function">is-abelian-level-connective-spectrum-condition-∞-Group</a> <a id="1742" href="higher-group-theory.abelian-higher-groups.html#1742" class="Bound">l1</a> <a id="1745" href="higher-group-theory.abelian-higher-groups.html#1745" class="Bound">G</a> <a id="1747" class="Symbol">=</a>
  <a id="1751" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1753" class="Symbol">(</a> <a id="1755" href="synthetic-homotopy-theory.connective-spectra.html#1963" class="Function">Connective-Spectrum</a> <a id="1775" href="higher-group-theory.abelian-higher-groups.html#1742" class="Bound">l1</a><a id="1777" class="Symbol">)</a>
    <a id="1783" class="Symbol">(</a> <a id="1785" class="Symbol">λ</a> <a id="1787" href="higher-group-theory.abelian-higher-groups.html#1787" class="Bound">A</a> <a id="1789" class="Symbol">→</a> <a id="1791" href="higher-group-theory.higher-groups.html#2979" class="Function">pointed-type-∞-Group</a> <a id="1812" href="higher-group-theory.abelian-higher-groups.html#1745" class="Bound">G</a> <a id="1814" href="structured-types.pointed-equivalences.html#7291" class="Function Operator">≃∗</a> <a id="1817" href="synthetic-homotopy-theory.connective-spectra.html#2222" class="Function">pointed-type-Connective-Spectrum</a> <a id="1850" href="higher-group-theory.abelian-higher-groups.html#1787" class="Bound">A</a> <a id="1852" class="Number">0</a><a id="1853" class="Symbol">)</a>
</pre>
### The connective spectrum condition of being abelian

<pre class="Agda"><a id="is-abelian-connective-spectrum-condition-∞-Group"></a><a id="1924" href="higher-group-theory.abelian-higher-groups.html#1924" class="Function">is-abelian-connective-spectrum-condition-∞-Group</a> <a id="1973" class="Symbol">:</a>
  <a id="1977" class="Symbol">{</a><a id="1978" href="higher-group-theory.abelian-higher-groups.html#1978" class="Bound">l</a> <a id="1980" class="Symbol">:</a> <a id="1982" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1987" class="Symbol">}</a> <a id="1989" class="Symbol">→</a> <a id="1991" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="1999" href="higher-group-theory.abelian-higher-groups.html#1978" class="Bound">l</a> <a id="2001" class="Symbol">→</a> <a id="2003" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2006" class="Symbol">(</a><a id="2007" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2012" href="higher-group-theory.abelian-higher-groups.html#1978" class="Bound">l</a><a id="2013" class="Symbol">)</a>
<a id="2015" href="higher-group-theory.abelian-higher-groups.html#1924" class="Function">is-abelian-connective-spectrum-condition-∞-Group</a> <a id="2064" class="Symbol">{</a><a id="2065" href="higher-group-theory.abelian-higher-groups.html#2065" class="Bound">l</a><a id="2066" class="Symbol">}</a> <a id="2068" href="higher-group-theory.abelian-higher-groups.html#2068" class="Bound">G</a> <a id="2070" class="Symbol">=</a>
  <a id="2074" href="higher-group-theory.abelian-higher-groups.html#1572" class="Function">is-abelian-level-connective-spectrum-condition-∞-Group</a> <a id="2129" href="higher-group-theory.abelian-higher-groups.html#2065" class="Bound">l</a> <a id="2131" href="higher-group-theory.abelian-higher-groups.html#2068" class="Bound">G</a>
</pre>
## References

{{#bibliography}}

## External links

- [abelian infinity-group](https://ncatlab.org/nlab/show/abelian+infinity-group)
  at $n$Lab
