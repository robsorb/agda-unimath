# Subterminal precategories

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="category-theory.subterminal-precategories.html" class="Module">category-theory.subterminal-precategories</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="category-theory.composition-operations-on-binary-families-of-sets.html" class="Module">category-theory.composition-operations-on-binary-families-of-sets</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="category-theory.fully-faithful-functors-precategories.html" class="Module">category-theory.fully-faithful-functors-precategories</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="category-theory.isomorphisms-in-precategories.html" class="Module">category-theory.isomorphisms-in-precategories</a>
<a id="345" class="Keyword">open</a> <a id="350" class="Keyword">import</a> <a id="357" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="category-theory.pregroupoids.html" class="Module">category-theory.pregroupoids</a>
<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="category-theory.strict-categories.html" class="Module">category-theory.strict-categories</a>
<a id="474" class="Keyword">open</a> <a id="479" class="Keyword">import</a> <a id="486" href="category-theory.terminal-category.html" class="Module">category-theory.terminal-category</a>

<a id="521" class="Keyword">open</a> <a id="526" class="Keyword">import</a> <a id="533" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="580" class="Keyword">open</a> <a id="585" class="Keyword">import</a> <a id="592" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="622" class="Keyword">open</a> <a id="627" class="Keyword">import</a> <a id="634" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="666" class="Keyword">open</a> <a id="671" class="Keyword">import</a> <a id="678" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="700" class="Keyword">open</a> <a id="705" class="Keyword">import</a> <a id="712" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="736" class="Keyword">open</a> <a id="741" class="Keyword">import</a> <a id="748" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="774" class="Keyword">open</a> <a id="779" class="Keyword">import</a> <a id="786" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="835" class="Keyword">open</a> <a id="840" class="Keyword">import</a> <a id="847" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="869" class="Keyword">open</a> <a id="874" class="Keyword">import</a> <a id="881" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="907" class="Keyword">open</a> <a id="912" class="Keyword">import</a> <a id="919" href="foundation.iterated-dependent-product-types.html" class="Module">foundation.iterated-dependent-product-types</a>
<a id="963" class="Keyword">open</a> <a id="968" class="Keyword">import</a> <a id="975" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="999" class="Keyword">open</a> <a id="1004" class="Keyword">import</a> <a id="1011" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="1027" class="Keyword">open</a> <a id="1032" class="Keyword">import</a> <a id="1039" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="1077" class="Keyword">open</a> <a id="1082" class="Keyword">import</a> <a id="1089" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="1110" class="Keyword">open</a> <a id="1115" class="Keyword">import</a> <a id="1122" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A [precategory](category-theory.precategories.md) is **subterminal** if its
[terminal projection functor](category-theory.terminal-category.md) is
[fully faithful](category-theory.fully-faithful-functors-precategories.md).

## Definitions

### The predicate on precategories of being subterminal

<pre class="Agda"><a id="1480" class="Keyword">module</a> <a id="1487" href="category-theory.subterminal-precategories.html#1487" class="Module">_</a>
  <a id="1491" class="Symbol">{</a><a id="1492" href="category-theory.subterminal-precategories.html#1492" class="Bound">l1</a> <a id="1495" href="category-theory.subterminal-precategories.html#1495" class="Bound">l2</a> <a id="1498" class="Symbol">:</a> <a id="1500" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1505" class="Symbol">}</a> <a id="1507" class="Symbol">(</a><a id="1508" href="category-theory.subterminal-precategories.html#1508" class="Bound">C</a> <a id="1510" class="Symbol">:</a> <a id="1512" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1524" href="category-theory.subterminal-precategories.html#1492" class="Bound">l1</a> <a id="1527" href="category-theory.subterminal-precategories.html#1495" class="Bound">l2</a><a id="1529" class="Symbol">)</a>
  <a id="1533" class="Keyword">where</a>

  <a id="1542" href="category-theory.subterminal-precategories.html#1542" class="Function">is-subterminal-Precategory</a> <a id="1569" class="Symbol">:</a> <a id="1571" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1574" class="Symbol">(</a><a id="1575" href="category-theory.subterminal-precategories.html#1492" class="Bound">l1</a> <a id="1578" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1580" href="category-theory.subterminal-precategories.html#1495" class="Bound">l2</a><a id="1582" class="Symbol">)</a>
  <a id="1586" href="category-theory.subterminal-precategories.html#1542" class="Function">is-subterminal-Precategory</a> <a id="1613" class="Symbol">=</a>
    <a id="1619" href="category-theory.fully-faithful-functors-precategories.html#1849" class="Function">is-fully-faithful-functor-Precategory</a> <a id="1657" href="category-theory.subterminal-precategories.html#1508" class="Bound">C</a> <a id="1659" href="category-theory.terminal-category.html#2988" class="Function">terminal-Precategory</a>
      <a id="1686" class="Symbol">(</a> <a id="1688" href="category-theory.terminal-category.html#6988" class="Function">terminal-functor-Precategory</a> <a id="1717" href="category-theory.subterminal-precategories.html#1508" class="Bound">C</a><a id="1718" class="Symbol">)</a>

  <a id="1723" href="category-theory.subterminal-precategories.html#1723" class="Function">is-subterminal-prop-Precategory</a> <a id="1755" class="Symbol">:</a> <a id="1757" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1762" class="Symbol">(</a><a id="1763" href="category-theory.subterminal-precategories.html#1492" class="Bound">l1</a> <a id="1766" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1768" href="category-theory.subterminal-precategories.html#1495" class="Bound">l2</a><a id="1770" class="Symbol">)</a>
  <a id="1774" href="category-theory.subterminal-precategories.html#1723" class="Function">is-subterminal-prop-Precategory</a> <a id="1806" class="Symbol">=</a>
    <a id="1812" href="category-theory.fully-faithful-functors-precategories.html#2266" class="Function">is-fully-faithful-prop-functor-Precategory</a> <a id="1855" href="category-theory.subterminal-precategories.html#1508" class="Bound">C</a> <a id="1857" href="category-theory.terminal-category.html#2988" class="Function">terminal-Precategory</a>
      <a id="1884" class="Symbol">(</a> <a id="1886" href="category-theory.terminal-category.html#6988" class="Function">terminal-functor-Precategory</a> <a id="1915" href="category-theory.subterminal-precategories.html#1508" class="Bound">C</a><a id="1916" class="Symbol">)</a>

  <a id="1921" href="category-theory.subterminal-precategories.html#1921" class="Function">is-prop-is-subterminal-Precategory</a> <a id="1956" class="Symbol">:</a> <a id="1958" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1966" href="category-theory.subterminal-precategories.html#1542" class="Function">is-subterminal-Precategory</a>
  <a id="1995" href="category-theory.subterminal-precategories.html#1921" class="Function">is-prop-is-subterminal-Precategory</a> <a id="2030" class="Symbol">=</a>
    <a id="2036" href="category-theory.fully-faithful-functors-precategories.html#2026" class="Function">is-prop-is-fully-faithful-functor-Precategory</a> <a id="2082" href="category-theory.subterminal-precategories.html#1508" class="Bound">C</a> <a id="2084" href="category-theory.terminal-category.html#2988" class="Function">terminal-Precategory</a>
      <a id="2111" class="Symbol">(</a> <a id="2113" href="category-theory.terminal-category.html#6988" class="Function">terminal-functor-Precategory</a> <a id="2142" href="category-theory.subterminal-precategories.html#1508" class="Bound">C</a><a id="2143" class="Symbol">)</a>
</pre>