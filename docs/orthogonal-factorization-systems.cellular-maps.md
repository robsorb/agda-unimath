# Cellular maps

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="orthogonal-factorization-systems.cellular-maps.html" class="Module">orthogonal-factorization-systems.cellular-maps</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.connected-maps.html" class="Module">foundation.connected-maps</a>
<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="orthogonal-factorization-systems.mere-lifting-properties.html" class="Module">orthogonal-factorization-systems.mere-lifting-properties</a>
</pre>
</details>

## Idea

A map `f : A → B` is said to be **`k`-cellular** if it satisfies the left
[mere lifting property](orthogonal-factorization-systems.mere-lifting-properties.md)
with respect to [`k`-connected maps](foundation.connected-maps.md). In other
words, a map `f` is `k`-cellular if the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md)

```text
  ⟨ f , g ⟩
```

with any `k`-connected map `g` is [surjective](foundation.surjective-maps.md).
The terminology `k`-cellular comes from the fact that the `k`-connected maps are
precisely the maps that satisfy the right mere lifting property with respect to
the [spheres](synthetic-homotopy-theory.spheres.md)

```text
  Sⁱ → unit
```

for all `-1 ≤ i ≤ k`. In this sense, `k`-cellular maps are "built out of
spheres". Alternatively, `k`-cellular maps might also be called **`k`-projective
maps**. This emphasizes the condition that `k`-projective maps lift against
`k`-connected maps.

In the topos of spaces, the `k`-cellular maps are the left class of an
_external_ weak factorization system on spaces of which the right class is the
class of `k`-connected maps, but there is no such weak factorization system
definable internally.

## Definitions

### The predicate of being a `k`-cellular map

<pre class="Agda"><a id="1606" class="Keyword">module</a> <a id="1613" href="orthogonal-factorization-systems.cellular-maps.html#1613" class="Module">_</a>
  <a id="1617" class="Symbol">{</a><a id="1618" href="orthogonal-factorization-systems.cellular-maps.html#1618" class="Bound">l1</a> <a id="1621" href="orthogonal-factorization-systems.cellular-maps.html#1621" class="Bound">l2</a> <a id="1624" class="Symbol">:</a> <a id="1626" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1631" class="Symbol">}</a> <a id="1633" class="Symbol">(</a><a id="1634" href="orthogonal-factorization-systems.cellular-maps.html#1634" class="Bound">k</a> <a id="1636" class="Symbol">:</a> <a id="1638" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="1639" class="Symbol">)</a> <a id="1641" class="Symbol">{</a><a id="1642" href="orthogonal-factorization-systems.cellular-maps.html#1642" class="Bound">A</a> <a id="1644" class="Symbol">:</a> <a id="1646" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1649" href="orthogonal-factorization-systems.cellular-maps.html#1618" class="Bound">l1</a><a id="1651" class="Symbol">}</a> <a id="1653" class="Symbol">{</a><a id="1654" href="orthogonal-factorization-systems.cellular-maps.html#1654" class="Bound">B</a> <a id="1656" class="Symbol">:</a> <a id="1658" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1661" href="orthogonal-factorization-systems.cellular-maps.html#1621" class="Bound">l2</a><a id="1663" class="Symbol">}</a> <a id="1665" class="Symbol">(</a><a id="1666" href="orthogonal-factorization-systems.cellular-maps.html#1666" class="Bound">f</a> <a id="1668" class="Symbol">:</a> <a id="1670" href="orthogonal-factorization-systems.cellular-maps.html#1642" class="Bound">A</a> <a id="1672" class="Symbol">→</a> <a id="1674" href="orthogonal-factorization-systems.cellular-maps.html#1654" class="Bound">B</a><a id="1675" class="Symbol">)</a>
  <a id="1679" class="Keyword">where</a>

  <a id="1688" href="orthogonal-factorization-systems.cellular-maps.html#1688" class="Function">is-cellular-map</a> <a id="1704" class="Symbol">:</a> <a id="1706" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1712" href="orthogonal-factorization-systems.cellular-maps.html#1688" class="Function">is-cellular-map</a> <a id="1728" class="Symbol">=</a>
    <a id="1734" class="Symbol">{</a><a id="1735" href="orthogonal-factorization-systems.cellular-maps.html#1735" class="Bound">l3</a> <a id="1738" href="orthogonal-factorization-systems.cellular-maps.html#1738" class="Bound">l4</a> <a id="1741" class="Symbol">:</a> <a id="1743" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1748" class="Symbol">}</a> <a id="1750" class="Symbol">{</a><a id="1751" href="orthogonal-factorization-systems.cellular-maps.html#1751" class="Bound">X</a> <a id="1753" class="Symbol">:</a> <a id="1755" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1758" href="orthogonal-factorization-systems.cellular-maps.html#1735" class="Bound">l3</a><a id="1760" class="Symbol">}</a> <a id="1762" class="Symbol">{</a><a id="1763" href="orthogonal-factorization-systems.cellular-maps.html#1763" class="Bound">Y</a> <a id="1765" class="Symbol">:</a> <a id="1767" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1770" href="orthogonal-factorization-systems.cellular-maps.html#1738" class="Bound">l4</a><a id="1772" class="Symbol">}</a> <a id="1774" class="Symbol">(</a><a id="1775" href="orthogonal-factorization-systems.cellular-maps.html#1775" class="Bound">g</a> <a id="1777" class="Symbol">:</a> <a id="1779" href="orthogonal-factorization-systems.cellular-maps.html#1751" class="Bound">X</a> <a id="1781" class="Symbol">→</a> <a id="1783" href="orthogonal-factorization-systems.cellular-maps.html#1763" class="Bound">Y</a><a id="1784" class="Symbol">)</a> <a id="1786" class="Symbol">→</a>
    <a id="1792" href="foundation.connected-maps.html#1763" class="Function">is-connected-map</a> <a id="1809" href="orthogonal-factorization-systems.cellular-maps.html#1634" class="Bound">k</a> <a id="1811" href="orthogonal-factorization-systems.cellular-maps.html#1775" class="Bound">g</a> <a id="1813" class="Symbol">→</a> <a id="1815" href="orthogonal-factorization-systems.mere-lifting-properties.html#989" class="Function">mere-diagonal-lift</a> <a id="1834" href="orthogonal-factorization-systems.cellular-maps.html#1666" class="Bound">f</a> <a id="1836" href="orthogonal-factorization-systems.cellular-maps.html#1775" class="Bound">g</a>
</pre>