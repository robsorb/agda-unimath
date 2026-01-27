# Homotopy automorphism groups

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="group-theory.homotopy-automorphism-groups.html" class="Module">group-theory.homotopy-automorphism-groups</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.1-types.html" class="Module">foundation.1-types</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.connected-components.html" class="Module">foundation.connected-components</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="307" class="Keyword">open</a> <a id="312" class="Keyword">import</a> <a id="319" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="404" class="Keyword">open</a> <a id="409" class="Keyword">import</a> <a id="416" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="foundation.mere-equality.html" class="Module">foundation.mere-equality</a>
<a id="479" class="Keyword">open</a> <a id="484" class="Keyword">import</a> <a id="491" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="528" class="Keyword">open</a> <a id="533" class="Keyword">import</a> <a id="540" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="578" class="Keyword">open</a> <a id="583" class="Keyword">import</a> <a id="590" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a>
<a id="625" class="Keyword">open</a> <a id="630" class="Keyword">import</a> <a id="637" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="666" class="Keyword">open</a> <a id="671" class="Keyword">import</a> <a id="678" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="701" class="Keyword">open</a> <a id="706" class="Keyword">import</a> <a id="713" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="741" class="Keyword">open</a> <a id="746" class="Keyword">import</a> <a id="753" href="group-theory.automorphism-groups.html" class="Module">group-theory.automorphism-groups</a>
<a id="786" class="Keyword">open</a> <a id="791" class="Keyword">import</a> <a id="798" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="827" class="Keyword">open</a> <a id="832" class="Keyword">import</a> <a id="839" href="group-theory.equivalences-concrete-groups.html" class="Module">group-theory.equivalences-concrete-groups</a>

<a id="882" class="Keyword">open</a> <a id="887" class="Keyword">import</a> <a id="894" href="higher-group-theory.automorphism-groups.html" class="Module">higher-group-theory.automorphism-groups</a>
<a id="934" class="Keyword">open</a> <a id="939" class="Keyword">import</a> <a id="946" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>

<a id="981" class="Keyword">open</a> <a id="986" class="Keyword">import</a> <a id="993" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The concrete
{{#concept "homotopy automorphism group" Disambiguation="of a pointed type" Agda=concrete-group-Pointed-Type}}
of a [pointed type](structured-types.pointed-types.md) `A` is the
[automorphism group](group-theory.automorphism-groups.md) of the
[groupoidification](foundation.truncations.md) of `A` at its base point.

## Definitions

### Homotopy automorphism groups of pointed types

<pre class="Agda"><a id="1454" class="Keyword">module</a> <a id="1461" href="group-theory.homotopy-automorphism-groups.html#1461" class="Module">_</a>
  <a id="1465" class="Symbol">{</a><a id="1466" href="group-theory.homotopy-automorphism-groups.html#1466" class="Bound">l</a> <a id="1468" class="Symbol">:</a> <a id="1470" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1475" class="Symbol">}</a> <a id="1477" class="Symbol">(</a><a id="1478" href="group-theory.homotopy-automorphism-groups.html#1478" class="Bound">A</a> <a id="1480" class="Symbol">:</a> <a id="1482" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1495" href="group-theory.homotopy-automorphism-groups.html#1466" class="Bound">l</a><a id="1496" class="Symbol">)</a>
  <a id="1500" class="Keyword">where</a>

  <a id="1509" href="group-theory.homotopy-automorphism-groups.html#1509" class="Function">concrete-group-Pointed-Type</a> <a id="1537" class="Symbol">:</a> <a id="1539" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="1554" href="group-theory.homotopy-automorphism-groups.html#1466" class="Bound">l</a>
  <a id="1558" href="group-theory.homotopy-automorphism-groups.html#1509" class="Function">concrete-group-Pointed-Type</a> <a id="1586" class="Symbol">=</a>
    <a id="1592" href="group-theory.automorphism-groups.html#1545" class="Function">Automorphism-Group</a>
      <a id="1617" class="Symbol">(</a> <a id="1619" href="foundation.truncations.html#1445" class="Function">trunc</a> <a id="1625" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a> <a id="1631" class="Symbol">(</a><a id="1632" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1650" href="group-theory.homotopy-automorphism-groups.html#1478" class="Bound">A</a><a id="1651" class="Symbol">))</a>
      <a id="1660" class="Symbol">(</a> <a id="1662" href="foundation.truncations.html#1585" class="Postulate">unit-trunc</a> <a id="1673" class="Symbol">(</a><a id="1674" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1693" href="group-theory.homotopy-automorphism-groups.html#1478" class="Bound">A</a><a id="1694" class="Symbol">))</a>

  <a id="1700" href="group-theory.homotopy-automorphism-groups.html#1700" class="Function">classifying-type-concrete-group-Pointed-Type</a> <a id="1745" class="Symbol">:</a> <a id="1747" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1750" href="group-theory.homotopy-automorphism-groups.html#1466" class="Bound">l</a>
  <a id="1754" href="group-theory.homotopy-automorphism-groups.html#1700" class="Function">classifying-type-concrete-group-Pointed-Type</a> <a id="1799" class="Symbol">=</a>
    <a id="1805" href="group-theory.concrete-groups.html#1503" class="Function">classifying-type-Concrete-Group</a> <a id="1837" href="group-theory.homotopy-automorphism-groups.html#1509" class="Function">concrete-group-Pointed-Type</a>

  <a id="1868" href="group-theory.homotopy-automorphism-groups.html#1868" class="Function">shape-concrete-group-Pointed-Type</a> <a id="1902" class="Symbol">:</a>
    <a id="1908" href="group-theory.homotopy-automorphism-groups.html#1700" class="Function">classifying-type-concrete-group-Pointed-Type</a>
  <a id="1955" href="group-theory.homotopy-automorphism-groups.html#1868" class="Function">shape-concrete-group-Pointed-Type</a> <a id="1989" class="Symbol">=</a>
    <a id="1995" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="2016" href="group-theory.homotopy-automorphism-groups.html#1509" class="Function">concrete-group-Pointed-Type</a>

  <a id="2047" href="group-theory.homotopy-automorphism-groups.html#2047" class="Function">∞-group-concrete-group-Pointed-Type</a> <a id="2083" class="Symbol">:</a> <a id="2085" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="2093" href="group-theory.homotopy-automorphism-groups.html#1466" class="Bound">l</a>
  <a id="2097" href="group-theory.homotopy-automorphism-groups.html#2047" class="Function">∞-group-concrete-group-Pointed-Type</a> <a id="2133" class="Symbol">=</a>
    <a id="2139" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="2162" href="group-theory.homotopy-automorphism-groups.html#1509" class="Function">concrete-group-Pointed-Type</a>
</pre>