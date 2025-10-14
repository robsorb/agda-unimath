# Multivariable sections

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="foundation.multivariable-sections.html" class="Module">foundation.multivariable-sections</a> <a id="76" class="Keyword">where</a>

<a id="83" class="Keyword">open</a> <a id="88" class="Keyword">import</a> <a id="95" href="foundation.telescopes.html" class="Module">foundation.telescopes</a> <a id="117" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="foundation.iterated-dependent-product-types.html" class="Module">foundation.iterated-dependent-product-types</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation.multivariable-homotopies.html" class="Module">foundation.multivariable-homotopies</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="416" class="Keyword">open</a> <a id="421" class="Keyword">import</a> <a id="428" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

A **multivariable section** is a map of multivariable maps that is a right
inverse. Thus, a map

```text
  s : ((x₁ : A₁) ... (xₙ : Aₙ) → A x) → (y₁ : B₁) ... (yₙ : Bₙ) → B y
```

is a section of a map of type

```text
  f : ((y₁ : B₁) ... (yₙ : Bₙ) → B y) → (x₁ : A₁) ... (xₙ : Aₙ) → A x
```

if the composition `f ∘ s` is
[multivariable homotopic](foundation.multivariable-homotopies.md) to the
identity at

```text
  (y₁ : B₁) ... (yₙ : Bₙ) → B y.
```

Note that sections of multivariable maps are equivalent to common
[sections](foundation-core.sections.md) by function extensionality, so this
definition only finds it utility in avoiding unnecessary applications of
[function extensionality](foundation.function-extensionality.md). For instance,
this is useful when defining induction principles on function types.

## Definition

<pre class="Agda"><a id="1329" class="Keyword">module</a> <a id="1336" href="foundation.multivariable-sections.html#1336" class="Module">_</a>
  <a id="1340" class="Symbol">{</a><a id="1341" href="foundation.multivariable-sections.html#1341" class="Bound">l1</a> <a id="1344" href="foundation.multivariable-sections.html#1344" class="Bound">l2</a> <a id="1347" class="Symbol">:</a> <a id="1349" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1354" class="Symbol">}</a> <a id="1356" class="Symbol">(</a><a id="1357" href="foundation.multivariable-sections.html#1357" class="Bound">n</a> <a id="1359" class="Symbol">:</a> <a id="1361" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1362" class="Symbol">)</a>
  <a id="1366" class="Symbol">{{</a><a id="1368" href="foundation.multivariable-sections.html#1368" class="Bound">A</a> <a id="1370" class="Symbol">:</a> <a id="1372" href="foundation.telescopes.html#1281" class="Datatype">telescope</a> <a id="1382" href="foundation.multivariable-sections.html#1341" class="Bound">l1</a> <a id="1385" href="foundation.multivariable-sections.html#1357" class="Bound">n</a><a id="1386" class="Symbol">}}</a> <a id="1389" class="Symbol">{{</a><a id="1391" href="foundation.multivariable-sections.html#1391" class="Bound">B</a> <a id="1393" class="Symbol">:</a> <a id="1395" href="foundation.telescopes.html#1281" class="Datatype">telescope</a> <a id="1405" href="foundation.multivariable-sections.html#1344" class="Bound">l2</a> <a id="1408" href="foundation.multivariable-sections.html#1357" class="Bound">n</a><a id="1409" class="Symbol">}}</a>
  <a id="1414" class="Symbol">(</a><a id="1415" href="foundation.multivariable-sections.html#1415" class="Bound">f</a> <a id="1417" class="Symbol">:</a> <a id="1419" href="foundation.iterated-dependent-product-types.html#1350" class="Function">iterated-Π</a> <a id="1430" href="foundation.multivariable-sections.html#1368" class="Bound">A</a> <a id="1432" class="Symbol">→</a> <a id="1434" href="foundation.iterated-dependent-product-types.html#1350" class="Function">iterated-Π</a> <a id="1445" href="foundation.multivariable-sections.html#1391" class="Bound">B</a><a id="1446" class="Symbol">)</a>
  <a id="1450" class="Keyword">where</a>

  <a id="1459" href="foundation.multivariable-sections.html#1459" class="Function">multivariable-section</a> <a id="1481" class="Symbol">:</a> <a id="1483" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1486" class="Symbol">(</a><a id="1487" href="foundation.multivariable-sections.html#1341" class="Bound">l1</a> <a id="1490" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1492" href="foundation.multivariable-sections.html#1344" class="Bound">l2</a><a id="1494" class="Symbol">)</a>
  <a id="1498" href="foundation.multivariable-sections.html#1459" class="Function">multivariable-section</a> <a id="1520" class="Symbol">=</a>
    <a id="1526" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1528" class="Symbol">(</a> <a id="1530" href="foundation.iterated-dependent-product-types.html#1350" class="Function">iterated-Π</a> <a id="1541" href="foundation.multivariable-sections.html#1391" class="Bound">B</a> <a id="1543" class="Symbol">→</a> <a id="1545" href="foundation.iterated-dependent-product-types.html#1350" class="Function">iterated-Π</a> <a id="1556" href="foundation.multivariable-sections.html#1368" class="Bound">A</a><a id="1557" class="Symbol">)</a>
      <a id="1565" class="Symbol">(</a> <a id="1567" class="Symbol">λ</a> <a id="1569" href="foundation.multivariable-sections.html#1569" class="Bound">s</a> <a id="1571" class="Symbol">→</a>
        <a id="1581" href="foundation.multivariable-homotopies.html#1285" class="Function">multivariable-htpy</a>
          <a id="1610" class="Symbol">{</a> <a id="1612" class="Argument">n</a> <a id="1614" class="Symbol">=</a> <a id="1616" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1623" href="foundation.multivariable-sections.html#1357" class="Bound">n</a><a id="1624" class="Symbol">}</a>
          <a id="1636" class="Symbol">{{</a><a id="1638" class="Argument">A</a> <a id="1640" class="Symbol">=</a> <a id="1642" href="foundation.telescopes.html#1527" class="Function">prepend-telescope</a> <a id="1660" class="Symbol">(</a><a id="1661" href="foundation.iterated-dependent-product-types.html#1350" class="Function">iterated-Π</a> <a id="1672" href="foundation.multivariable-sections.html#1391" class="Bound">B</a><a id="1673" class="Symbol">)</a> <a id="1675" href="foundation.multivariable-sections.html#1391" class="Bound">B</a><a id="1676" class="Symbol">}}</a>
          <a id="1689" class="Symbol">(</a> <a id="1691" href="foundation.multivariable-sections.html#1415" class="Bound">f</a> <a id="1693" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1695" href="foundation.multivariable-sections.html#1569" class="Bound">s</a><a id="1696" class="Symbol">)</a>
          <a id="1708" class="Symbol">(</a> <a id="1710" href="foundation-core.function-types.html#307" class="Function">id</a><a id="1712" class="Symbol">))</a>

  <a id="1718" href="foundation.multivariable-sections.html#1718" class="Function">map-multivariable-section</a> <a id="1744" class="Symbol">:</a>
    <a id="1750" href="foundation.multivariable-sections.html#1459" class="Function">multivariable-section</a> <a id="1772" class="Symbol">→</a> <a id="1774" href="foundation.iterated-dependent-product-types.html#1350" class="Function">iterated-Π</a> <a id="1785" href="foundation.multivariable-sections.html#1391" class="Bound">B</a> <a id="1787" class="Symbol">→</a> <a id="1789" href="foundation.iterated-dependent-product-types.html#1350" class="Function">iterated-Π</a> <a id="1800" href="foundation.multivariable-sections.html#1368" class="Bound">A</a>
  <a id="1804" href="foundation.multivariable-sections.html#1718" class="Function">map-multivariable-section</a> <a id="1830" class="Symbol">=</a> <a id="1832" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="1839" href="foundation.multivariable-sections.html#1839" class="Function">is-multivariable-section-map-multivariable-section</a> <a id="1890" class="Symbol">:</a>
    <a id="1896" class="Symbol">(</a><a id="1897" href="foundation.multivariable-sections.html#1897" class="Bound">s</a> <a id="1899" class="Symbol">:</a> <a id="1901" href="foundation.multivariable-sections.html#1459" class="Function">multivariable-section</a><a id="1922" class="Symbol">)</a> <a id="1924" class="Symbol">→</a>
    <a id="1930" href="foundation.multivariable-homotopies.html#1285" class="Function">multivariable-htpy</a>
      <a id="1955" class="Symbol">{</a> <a id="1957" class="Argument">n</a> <a id="1959" class="Symbol">=</a> <a id="1961" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1968" href="foundation.multivariable-sections.html#1357" class="Bound">n</a><a id="1969" class="Symbol">}</a>
      <a id="1977" class="Symbol">{{</a><a id="1979" class="Argument">A</a> <a id="1981" class="Symbol">=</a> <a id="1983" href="foundation.telescopes.html#1527" class="Function">prepend-telescope</a> <a id="2001" class="Symbol">(</a><a id="2002" href="foundation.iterated-dependent-product-types.html#1350" class="Function">iterated-Π</a> <a id="2013" href="foundation.multivariable-sections.html#1391" class="Bound">B</a><a id="2014" class="Symbol">)</a> <a id="2016" href="foundation.multivariable-sections.html#1391" class="Bound">B</a><a id="2017" class="Symbol">}}</a>
      <a id="2026" class="Symbol">(</a> <a id="2028" href="foundation.multivariable-sections.html#1415" class="Bound">f</a> <a id="2030" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2032" href="foundation.multivariable-sections.html#1718" class="Function">map-multivariable-section</a> <a id="2058" href="foundation.multivariable-sections.html#1897" class="Bound">s</a><a id="2059" class="Symbol">)</a>
      <a id="2067" class="Symbol">(</a> <a id="2069" href="foundation-core.function-types.html#307" class="Function">id</a><a id="2071" class="Symbol">)</a>
  <a id="2075" href="foundation.multivariable-sections.html#1839" class="Function">is-multivariable-section-map-multivariable-section</a> <a id="2126" class="Symbol">=</a> <a id="2128" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>