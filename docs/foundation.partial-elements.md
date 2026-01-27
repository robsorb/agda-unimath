# Partial elements

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="foundation.partial-elements.html" class="Module">foundation.partial-elements</a> <a id="64" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="120" class="Keyword">open</a> <a id="125" class="Keyword">import</a> <a id="132" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="164" class="Keyword">open</a> <a id="169" class="Keyword">import</a> <a id="176" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A {{#concept "partial element" Agda=partial-element}} of `X` consists of a
[proposition](foundation-core.propositions.md) `P` and a map `P → X`. That is,
the type of partial elements of `X` is defined to be

```text
  Σ (P : Prop), (P → X).
```

We say that a partial element `(P, f)` is
{{#concept "defined" Disambiguation="partial element"}} if the proposition `P`
holds.

Alternatively, the type of partial elements of `X` can be described as the
codomain of the
[composition](species.composition-cauchy-series-species-of-types.md)

```text
    1   ∅     ∅
    |   |     |
  T | ∘ |  =  |
    ∨   ∨     ∨
  Prop  X   P T X
```

of [polynomial endofunctors](trees.polynomial-endofunctors.md). Indeed, the
codomain of this composition operation of morphisms is the polynomial
endofunctor `P T` of the map `T : 1 → Prop` evaluated at `X`, which is exactly
the type of partial elements of `X`.

## Definitions

### Partial elements of a type

<pre class="Agda"><a id="partial-element"></a><a id="1254" href="foundation.partial-elements.html#1254" class="Function">partial-element</a> <a id="1270" class="Symbol">:</a> <a id="1272" class="Symbol">{</a><a id="1273" href="foundation.partial-elements.html#1273" class="Bound">l1</a> <a id="1276" class="Symbol">:</a> <a id="1278" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1283" class="Symbol">}</a> <a id="1285" class="Symbol">(</a><a id="1286" href="foundation.partial-elements.html#1286" class="Bound">l2</a> <a id="1289" class="Symbol">:</a> <a id="1291" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1296" class="Symbol">)</a> <a id="1298" class="Symbol">→</a> <a id="1300" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1303" href="foundation.partial-elements.html#1273" class="Bound">l1</a> <a id="1306" class="Symbol">→</a> <a id="1308" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1311" class="Symbol">(</a><a id="1312" href="foundation.partial-elements.html#1273" class="Bound">l1</a> <a id="1315" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1317" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1322" href="foundation.partial-elements.html#1286" class="Bound">l2</a><a id="1324" class="Symbol">)</a>
<a id="1326" href="foundation.partial-elements.html#1254" class="Function">partial-element</a> <a id="1342" href="foundation.partial-elements.html#1342" class="Bound">l2</a> <a id="1345" href="foundation.partial-elements.html#1345" class="Bound">X</a> <a id="1347" class="Symbol">=</a> <a id="1349" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1351" class="Symbol">(</a><a id="1352" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1357" href="foundation.partial-elements.html#1342" class="Bound">l2</a><a id="1359" class="Symbol">)</a> <a id="1361" class="Symbol">(λ</a> <a id="1364" href="foundation.partial-elements.html#1364" class="Bound">P</a> <a id="1366" class="Symbol">→</a> <a id="1368" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1378" href="foundation.partial-elements.html#1364" class="Bound">P</a> <a id="1380" class="Symbol">→</a> <a id="1382" href="foundation.partial-elements.html#1345" class="Bound">X</a><a id="1383" class="Symbol">)</a>

<a id="1386" class="Keyword">module</a> <a id="1393" href="foundation.partial-elements.html#1393" class="Module">_</a>
  <a id="1397" class="Symbol">{</a><a id="1398" href="foundation.partial-elements.html#1398" class="Bound">l1</a> <a id="1401" href="foundation.partial-elements.html#1401" class="Bound">l2</a> <a id="1404" class="Symbol">:</a> <a id="1406" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1411" class="Symbol">}</a> <a id="1413" class="Symbol">{</a><a id="1414" href="foundation.partial-elements.html#1414" class="Bound">X</a> <a id="1416" class="Symbol">:</a> <a id="1418" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1421" href="foundation.partial-elements.html#1398" class="Bound">l1</a><a id="1423" class="Symbol">}</a> <a id="1425" class="Symbol">(</a><a id="1426" href="foundation.partial-elements.html#1426" class="Bound">x</a> <a id="1428" class="Symbol">:</a> <a id="1430" href="foundation.partial-elements.html#1254" class="Function">partial-element</a> <a id="1446" href="foundation.partial-elements.html#1401" class="Bound">l2</a> <a id="1449" href="foundation.partial-elements.html#1414" class="Bound">X</a><a id="1450" class="Symbol">)</a>
  <a id="1454" class="Keyword">where</a>

  <a id="1463" href="foundation.partial-elements.html#1463" class="Function">is-defined-prop-partial-element</a> <a id="1495" class="Symbol">:</a> <a id="1497" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1502" href="foundation.partial-elements.html#1401" class="Bound">l2</a>
  <a id="1507" href="foundation.partial-elements.html#1463" class="Function">is-defined-prop-partial-element</a> <a id="1539" class="Symbol">=</a> <a id="1541" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1545" href="foundation.partial-elements.html#1426" class="Bound">x</a>

  <a id="1550" href="foundation.partial-elements.html#1550" class="Function">is-defined-partial-element</a> <a id="1577" class="Symbol">:</a> <a id="1579" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1582" href="foundation.partial-elements.html#1401" class="Bound">l2</a>
  <a id="1587" href="foundation.partial-elements.html#1550" class="Function">is-defined-partial-element</a> <a id="1614" class="Symbol">=</a> <a id="1616" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1626" href="foundation.partial-elements.html#1463" class="Function">is-defined-prop-partial-element</a>
</pre>
### The unit of the partial element operator

<pre class="Agda"><a id="unit-partial-element"></a><a id="1717" href="foundation.partial-elements.html#1717" class="Function">unit-partial-element</a> <a id="1738" class="Symbol">:</a>
  <a id="1742" class="Symbol">{</a><a id="1743" href="foundation.partial-elements.html#1743" class="Bound">l1</a> <a id="1746" class="Symbol">:</a> <a id="1748" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1753" class="Symbol">}</a> <a id="1755" class="Symbol">{</a><a id="1756" href="foundation.partial-elements.html#1756" class="Bound">X</a> <a id="1758" class="Symbol">:</a> <a id="1760" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1763" href="foundation.partial-elements.html#1743" class="Bound">l1</a><a id="1765" class="Symbol">}</a> <a id="1767" class="Symbol">→</a> <a id="1769" href="foundation.partial-elements.html#1756" class="Bound">X</a> <a id="1771" class="Symbol">→</a> <a id="1773" href="foundation.partial-elements.html#1254" class="Function">partial-element</a> <a id="1789" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1795" href="foundation.partial-elements.html#1756" class="Bound">X</a>
<a id="1797" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1801" class="Symbol">(</a><a id="1802" href="foundation.partial-elements.html#1717" class="Function">unit-partial-element</a> <a id="1823" href="foundation.partial-elements.html#1823" class="Bound">x</a><a id="1824" class="Symbol">)</a> <a id="1826" class="Symbol">=</a> <a id="1828" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a>
<a id="1838" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1842" class="Symbol">(</a><a id="1843" href="foundation.partial-elements.html#1717" class="Function">unit-partial-element</a> <a id="1864" href="foundation.partial-elements.html#1864" class="Bound">x</a><a id="1865" class="Symbol">)</a> <a id="1867" href="foundation.partial-elements.html#1867" class="Bound">y</a> <a id="1869" class="Symbol">=</a> <a id="1871" href="foundation.partial-elements.html#1864" class="Bound">x</a>
</pre>
## Properties

### The type of partial elements is a directed complete poset

This remains to be shown.
[#734](https://github.com/UniMath/agda-unimath/issues/734)

## See also

- [Copartial elements](foundation.copartial-elements.md)
- [Partial functions](foundation.partial-functions.md)
- [Partial sequences](lists.partial-sequences.md)
- [Total partial functions](foundation.total-partial-functions.md)
