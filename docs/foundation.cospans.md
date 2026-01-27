# Cospans of types

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="foundation.cospans.html" class="Module">foundation.cospans</a> <a id="55" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="111" class="Keyword">open</a> <a id="116" class="Keyword">import</a> <a id="123" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="155" class="Keyword">open</a> <a id="160" class="Keyword">import</a> <a id="167" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.homotopy-induction.html" class="Module">foundation.homotopy-induction</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.structure-identity-principle.html" class="Module">foundation.structure-identity-principle</a>
<a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="foundation-core.commuting-triangles-of-maps.html" class="Module">foundation-core.commuting-triangles-of-maps</a>
<a id="492" class="Keyword">open</a> <a id="497" class="Keyword">import</a> <a id="504" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="533" class="Keyword">open</a> <a id="538" class="Keyword">import</a> <a id="545" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="576" class="Keyword">open</a> <a id="581" class="Keyword">import</a> <a id="588" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="615" class="Keyword">open</a> <a id="620" class="Keyword">import</a> <a id="627" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="658" class="Keyword">open</a> <a id="663" class="Keyword">import</a> <a id="670" href="foundation-core.torsorial-type-families.html" class="Module">foundation-core.torsorial-type-families</a>
</pre>
</details>

## Idea

A {{#concept "cospan" Disambiguation="types" Agda=cospan}} from `A` to `B`
consists of a type `X` and maps `f : A → X` and `g : B → X`, as indicated in the
diagram

```text
      f         g
  A -----> X <----- B
```

We disambiguate between cospans and
[cospan diagrams](foundation.cospan-diagrams.md). We consider a cospan from `A`
to `B` a morphism from `A` to `B` in the category of types and cospans between
them, whereas we consider cospan diagrams to be _objects_ in the category of
diagrams of types of the form `* <---- * ----> *`. Conceptually there is a
subtle, but important distinction between cospans and cospan diagrams. Cospan
diagrams are more suitable for functorial operations that take "cospans" as
input, but for which the functorial action takes a natural transformation, i.e.,
a morphism of cospan diagrams, as input. Examples of this kind include
[pullbacks](foundation.pullbacks.md).

## Definitions

### Cospans

<pre class="Agda"><a id="cospan"></a><a id="1683" href="foundation.cospans.html#1683" class="Function">cospan</a> <a id="1690" class="Symbol">:</a>
  <a id="1694" class="Symbol">{</a><a id="1695" href="foundation.cospans.html#1695" class="Bound">l1</a> <a id="1698" href="foundation.cospans.html#1698" class="Bound">l2</a> <a id="1701" class="Symbol">:</a> <a id="1703" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1708" class="Symbol">}</a> <a id="1710" class="Symbol">(</a><a id="1711" href="foundation.cospans.html#1711" class="Bound">l</a> <a id="1713" class="Symbol">:</a> <a id="1715" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1720" class="Symbol">)</a> <a id="1722" class="Symbol">(</a><a id="1723" href="foundation.cospans.html#1723" class="Bound">A</a> <a id="1725" class="Symbol">:</a> <a id="1727" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1730" href="foundation.cospans.html#1695" class="Bound">l1</a><a id="1732" class="Symbol">)</a> <a id="1734" class="Symbol">(</a><a id="1735" href="foundation.cospans.html#1735" class="Bound">B</a> <a id="1737" class="Symbol">:</a> <a id="1739" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1742" href="foundation.cospans.html#1698" class="Bound">l2</a><a id="1744" class="Symbol">)</a> <a id="1746" class="Symbol">→</a>
  <a id="1750" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1753" class="Symbol">(</a><a id="1754" href="foundation.cospans.html#1695" class="Bound">l1</a> <a id="1757" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1759" href="foundation.cospans.html#1698" class="Bound">l2</a> <a id="1762" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1764" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1769" href="foundation.cospans.html#1711" class="Bound">l</a><a id="1770" class="Symbol">)</a>
<a id="1772" href="foundation.cospans.html#1683" class="Function">cospan</a> <a id="1779" href="foundation.cospans.html#1779" class="Bound">l</a> <a id="1781" href="foundation.cospans.html#1781" class="Bound">A</a> <a id="1783" href="foundation.cospans.html#1783" class="Bound">B</a> <a id="1785" class="Symbol">=</a> <a id="1787" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1789" class="Symbol">(</a><a id="1790" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1793" href="foundation.cospans.html#1779" class="Bound">l</a><a id="1794" class="Symbol">)</a> <a id="1796" class="Symbol">(λ</a> <a id="1799" href="foundation.cospans.html#1799" class="Bound">X</a> <a id="1801" class="Symbol">→</a> <a id="1803" class="Symbol">(</a><a id="1804" href="foundation.cospans.html#1781" class="Bound">A</a> <a id="1806" class="Symbol">→</a> <a id="1808" href="foundation.cospans.html#1799" class="Bound">X</a><a id="1809" class="Symbol">)</a> <a id="1811" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1813" class="Symbol">(</a><a id="1814" href="foundation.cospans.html#1783" class="Bound">B</a> <a id="1816" class="Symbol">→</a> <a id="1818" href="foundation.cospans.html#1799" class="Bound">X</a><a id="1819" class="Symbol">))</a>

<a id="1823" class="Keyword">module</a> <a id="1830" href="foundation.cospans.html#1830" class="Module">_</a>
  <a id="1834" class="Symbol">{</a><a id="1835" href="foundation.cospans.html#1835" class="Bound">l1</a> <a id="1838" href="foundation.cospans.html#1838" class="Bound">l2</a> <a id="1841" class="Symbol">:</a> <a id="1843" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1848" class="Symbol">}</a> <a id="1850" class="Symbol">{</a><a id="1851" href="foundation.cospans.html#1851" class="Bound">l</a> <a id="1853" class="Symbol">:</a> <a id="1855" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1860" class="Symbol">}</a> <a id="1862" class="Symbol">{</a><a id="1863" href="foundation.cospans.html#1863" class="Bound">A</a> <a id="1865" class="Symbol">:</a> <a id="1867" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1870" href="foundation.cospans.html#1835" class="Bound">l1</a><a id="1872" class="Symbol">}</a> <a id="1874" class="Symbol">{</a><a id="1875" href="foundation.cospans.html#1875" class="Bound">B</a> <a id="1877" class="Symbol">:</a> <a id="1879" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1882" href="foundation.cospans.html#1838" class="Bound">l2</a><a id="1884" class="Symbol">}</a> <a id="1886" class="Symbol">(</a><a id="1887" href="foundation.cospans.html#1887" class="Bound">c</a> <a id="1889" class="Symbol">:</a> <a id="1891" href="foundation.cospans.html#1683" class="Function">cospan</a> <a id="1898" href="foundation.cospans.html#1851" class="Bound">l</a> <a id="1900" href="foundation.cospans.html#1863" class="Bound">A</a> <a id="1902" href="foundation.cospans.html#1875" class="Bound">B</a><a id="1903" class="Symbol">)</a>
  <a id="1907" class="Keyword">where</a>

  <a id="1916" href="foundation.cospans.html#1916" class="Function">codomain-cospan</a> <a id="1932" class="Symbol">:</a> <a id="1934" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1937" href="foundation.cospans.html#1851" class="Bound">l</a>
  <a id="1941" href="foundation.cospans.html#1916" class="Function">codomain-cospan</a> <a id="1957" class="Symbol">=</a> <a id="1959" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1963" href="foundation.cospans.html#1887" class="Bound">c</a>

  <a id="1968" href="foundation.cospans.html#1968" class="Function">left-map-cospan</a> <a id="1984" class="Symbol">:</a> <a id="1986" href="foundation.cospans.html#1863" class="Bound">A</a> <a id="1988" class="Symbol">→</a> <a id="1990" href="foundation.cospans.html#1916" class="Function">codomain-cospan</a>
  <a id="2008" href="foundation.cospans.html#1968" class="Function">left-map-cospan</a> <a id="2024" class="Symbol">=</a> <a id="2026" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2030" class="Symbol">(</a><a id="2031" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2035" href="foundation.cospans.html#1887" class="Bound">c</a><a id="2036" class="Symbol">)</a>

  <a id="2041" href="foundation.cospans.html#2041" class="Function">right-map-cospan</a> <a id="2058" class="Symbol">:</a> <a id="2060" href="foundation.cospans.html#1875" class="Bound">B</a> <a id="2062" class="Symbol">→</a> <a id="2064" href="foundation.cospans.html#1916" class="Function">codomain-cospan</a>
  <a id="2082" href="foundation.cospans.html#2041" class="Function">right-map-cospan</a> <a id="2099" class="Symbol">=</a> <a id="2101" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2105" class="Symbol">(</a><a id="2106" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2110" href="foundation.cospans.html#1887" class="Bound">c</a><a id="2111" class="Symbol">)</a>
</pre>
### The identity cospan

<pre class="Agda"><a id="id-cospan"></a><a id="2151" href="foundation.cospans.html#2151" class="Function">id-cospan</a> <a id="2161" class="Symbol">:</a> <a id="2163" class="Symbol">{</a><a id="2164" href="foundation.cospans.html#2164" class="Bound">l</a> <a id="2166" class="Symbol">:</a> <a id="2168" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2173" class="Symbol">}</a> <a id="2175" class="Symbol">(</a><a id="2176" href="foundation.cospans.html#2176" class="Bound">A</a> <a id="2178" class="Symbol">:</a> <a id="2180" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2183" href="foundation.cospans.html#2164" class="Bound">l</a><a id="2184" class="Symbol">)</a> <a id="2186" class="Symbol">→</a> <a id="2188" href="foundation.cospans.html#1683" class="Function">cospan</a> <a id="2195" href="foundation.cospans.html#2164" class="Bound">l</a> <a id="2197" href="foundation.cospans.html#2176" class="Bound">A</a> <a id="2199" href="foundation.cospans.html#2176" class="Bound">A</a>
<a id="2201" href="foundation.cospans.html#2151" class="Function">id-cospan</a> <a id="2211" href="foundation.cospans.html#2211" class="Bound">A</a> <a id="2213" class="Symbol">=</a> <a id="2215" class="Symbol">(</a><a id="2216" href="foundation.cospans.html#2211" class="Bound">A</a> <a id="2218" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2220" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2223" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2225" href="foundation-core.function-types.html#307" class="Function">id</a><a id="2227" class="Symbol">)</a>
</pre>
### The swapping operation on cospans

<pre class="Agda"><a id="swap-cospan"></a><a id="2281" href="foundation.cospans.html#2281" class="Function">swap-cospan</a> <a id="2293" class="Symbol">:</a>
  <a id="2297" class="Symbol">{</a><a id="2298" href="foundation.cospans.html#2298" class="Bound">l1</a> <a id="2301" href="foundation.cospans.html#2301" class="Bound">l2</a> <a id="2304" class="Symbol">:</a> <a id="2306" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2311" class="Symbol">}</a> <a id="2313" class="Symbol">{</a><a id="2314" href="foundation.cospans.html#2314" class="Bound">l</a> <a id="2316" class="Symbol">:</a> <a id="2318" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2323" class="Symbol">}</a> <a id="2325" class="Symbol">{</a><a id="2326" href="foundation.cospans.html#2326" class="Bound">A</a> <a id="2328" class="Symbol">:</a> <a id="2330" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2333" href="foundation.cospans.html#2298" class="Bound">l1</a><a id="2335" class="Symbol">}</a> <a id="2337" class="Symbol">{</a><a id="2338" href="foundation.cospans.html#2338" class="Bound">B</a> <a id="2340" class="Symbol">:</a> <a id="2342" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2345" href="foundation.cospans.html#2301" class="Bound">l2</a><a id="2347" class="Symbol">}</a> <a id="2349" class="Symbol">→</a>
  <a id="2353" href="foundation.cospans.html#1683" class="Function">cospan</a> <a id="2360" href="foundation.cospans.html#2314" class="Bound">l</a> <a id="2362" href="foundation.cospans.html#2326" class="Bound">A</a> <a id="2364" href="foundation.cospans.html#2338" class="Bound">B</a> <a id="2366" class="Symbol">→</a> <a id="2368" href="foundation.cospans.html#1683" class="Function">cospan</a> <a id="2375" href="foundation.cospans.html#2314" class="Bound">l</a> <a id="2377" href="foundation.cospans.html#2338" class="Bound">B</a> <a id="2379" href="foundation.cospans.html#2326" class="Bound">A</a>
<a id="2381" href="foundation.cospans.html#2281" class="Function">swap-cospan</a> <a id="2393" class="Symbol">(</a><a id="2394" href="foundation.cospans.html#2394" class="Bound">C</a> <a id="2396" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2398" href="foundation.cospans.html#2398" class="Bound">f</a> <a id="2400" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2402" href="foundation.cospans.html#2402" class="Bound">g</a><a id="2403" class="Symbol">)</a> <a id="2405" class="Symbol">=</a> <a id="2407" class="Symbol">(</a><a id="2408" href="foundation.cospans.html#2394" class="Bound">C</a> <a id="2410" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2412" href="foundation.cospans.html#2402" class="Bound">g</a> <a id="2414" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2416" href="foundation.cospans.html#2398" class="Bound">f</a><a id="2417" class="Symbol">)</a>
</pre>
## See also

- The formal dual of cospans is [spans](foundation.spans.md).
- [Pullbacks](foundation-core.pullbacks.md) are limits of
  [cospan diagrams](foundation.cospan-diagrams.md).

### Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
