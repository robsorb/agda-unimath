# The universal property of the conatural numbers

<pre class="Agda"><a id="60" class="Keyword">module</a> <a id="67" href="elementary-number-theory.universal-property-conatural-numbers.html" class="Module">elementary-number-theory.universal-property-conatural-numbers</a> <a id="129" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.coalgebras-maybe.html" class="Module">foundation.coalgebras-maybe</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="267" class="Keyword">open</a> <a id="272" class="Keyword">import</a> <a id="279" href="foundation.morphisms-coalgebras-maybe.html" class="Module">foundation.morphisms-coalgebras-maybe</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The [conatural numbers](elementary-number-theory.conatural-numbers.md) `ℕ∞`
enjoys many universal properties, among others:

1. It is the one-point compactification of the
   [natural numbers](elementary-number-theory.natural-numbers.md).
2. It classifies downward-stable subsets of the natural numbers.
3. It is the final coalgebra of the [maybe monad](foundation.maybe.md).

On this page we consider the last of these. Thus, a
`Maybe`-[coalgebra](foundation.coalgebras-maybe.md) `η : X → Maybe X` satisfies
the
{{#concept "universal property of the conatural numbers" Agda=universal-property-conatural-numbers}}
if, for every other `Maybe`-coalgebra `η' : Y → Maybe Y` there is a
[unique](foundation-core.contractible-types.md)
[coalgebra homomorphism](foundation.morphisms-coalgebras-maybe.md)

```text
            f
     Y ----------> X
     |             |
   η'|             | η
     ∨             ∨
  Maybe Y ----> Maybe X.
         Maybe f
```

## Definitions

### The universal property of the conatural numbers at a universe level

<pre class="Agda"><a id="universal-property-conatural-numbers-Level"></a><a id="1432" href="elementary-number-theory.universal-property-conatural-numbers.html#1432" class="Function">universal-property-conatural-numbers-Level</a> <a id="1475" class="Symbol">:</a>
  <a id="1479" class="Symbol">{</a><a id="1480" href="elementary-number-theory.universal-property-conatural-numbers.html#1480" class="Bound">l1</a> <a id="1483" class="Symbol">:</a> <a id="1485" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1490" class="Symbol">}</a> <a id="1492" class="Symbol">→</a> <a id="1494" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1510" href="elementary-number-theory.universal-property-conatural-numbers.html#1480" class="Bound">l1</a> <a id="1513" class="Symbol">→</a> <a id="1515" class="Symbol">(</a><a id="1516" href="elementary-number-theory.universal-property-conatural-numbers.html#1516" class="Bound">l</a> <a id="1518" class="Symbol">:</a> <a id="1520" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1525" class="Symbol">)</a> <a id="1527" class="Symbol">→</a> <a id="1529" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1532" class="Symbol">(</a><a id="1533" href="elementary-number-theory.universal-property-conatural-numbers.html#1480" class="Bound">l1</a> <a id="1536" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1538" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1543" href="elementary-number-theory.universal-property-conatural-numbers.html#1516" class="Bound">l</a><a id="1544" class="Symbol">)</a>
<a id="1546" href="elementary-number-theory.universal-property-conatural-numbers.html#1432" class="Function">universal-property-conatural-numbers-Level</a> <a id="1589" href="elementary-number-theory.universal-property-conatural-numbers.html#1589" class="Bound">N∞</a> <a id="1592" href="elementary-number-theory.universal-property-conatural-numbers.html#1592" class="Bound">l</a> <a id="1594" class="Symbol">=</a>
  <a id="1598" class="Symbol">(</a><a id="1599" href="elementary-number-theory.universal-property-conatural-numbers.html#1599" class="Bound">X</a> <a id="1601" class="Symbol">:</a> <a id="1603" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1619" href="elementary-number-theory.universal-property-conatural-numbers.html#1592" class="Bound">l</a><a id="1620" class="Symbol">)</a> <a id="1622" class="Symbol">→</a> <a id="1624" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="1633" class="Symbol">(</a><a id="1634" href="foundation.morphisms-coalgebras-maybe.html#1252" class="Function">hom-coalgebra-Maybe</a> <a id="1654" href="elementary-number-theory.universal-property-conatural-numbers.html#1599" class="Bound">X</a> <a id="1656" href="elementary-number-theory.universal-property-conatural-numbers.html#1589" class="Bound">N∞</a><a id="1658" class="Symbol">)</a>
</pre>
### The universal property of the conatural numbers at a universe level

<pre class="Agda"><a id="universal-property-conatural-numbers"></a><a id="1746" href="elementary-number-theory.universal-property-conatural-numbers.html#1746" class="Function">universal-property-conatural-numbers</a> <a id="1783" class="Symbol">:</a>
  <a id="1787" class="Symbol">{</a><a id="1788" href="elementary-number-theory.universal-property-conatural-numbers.html#1788" class="Bound">l1</a> <a id="1791" class="Symbol">:</a> <a id="1793" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1798" class="Symbol">}</a> <a id="1800" class="Symbol">→</a> <a id="1802" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="1818" href="elementary-number-theory.universal-property-conatural-numbers.html#1788" class="Bound">l1</a> <a id="1821" class="Symbol">→</a> <a id="1823" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
<a id="1827" href="elementary-number-theory.universal-property-conatural-numbers.html#1746" class="Function">universal-property-conatural-numbers</a> <a id="1864" href="elementary-number-theory.universal-property-conatural-numbers.html#1864" class="Bound">N∞</a> <a id="1867" class="Symbol">=</a>
  <a id="1871" class="Symbol">{</a><a id="1872" href="elementary-number-theory.universal-property-conatural-numbers.html#1872" class="Bound">l</a> <a id="1874" class="Symbol">:</a> <a id="1876" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1881" class="Symbol">}</a> <a id="1883" class="Symbol">→</a> <a id="1885" href="elementary-number-theory.universal-property-conatural-numbers.html#1432" class="Function">universal-property-conatural-numbers-Level</a> <a id="1928" href="elementary-number-theory.universal-property-conatural-numbers.html#1864" class="Bound">N∞</a> <a id="1931" href="elementary-number-theory.universal-property-conatural-numbers.html#1872" class="Bound">l</a>
</pre>