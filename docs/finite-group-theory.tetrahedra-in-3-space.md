# Tetrahedra in `3`-dimensional space

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="finite-group-theory.tetrahedra-in-3-space.html" class="Module">finite-group-theory.tetrahedra-in-3-space</a> <a id="97" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="univalent-combinatorics.2-element-decidable-subtypes.html" class="Module">univalent-combinatorics.2-element-decidable-subtypes</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="univalent-combinatorics.cyclic-finite-types.html" class="Module">univalent-combinatorics.cyclic-finite-types</a>
<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

The type of tetrahedra in 3-dimensional space is a type of tetrahedra that can
be rotated, but not reflected. In other words, the symmetry group of the
tetrahedra in 3-dimensional space is the alternating group `A₄`.

Note that any rotation of a tetrahedron in 3-space induces a rotation on the set
of opposing pairs of edges. There are three such pairs of edges.

## Definition

<pre class="Agda"><a id="tetrahedron-in-3-space"></a><a id="856" href="finite-group-theory.tetrahedra-in-3-space.html#856" class="Function">tetrahedron-in-3-space</a> <a id="879" class="Symbol">:</a> <a id="881" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="884" class="Symbol">(</a><a id="885" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="890" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="895" class="Symbol">)</a>
<a id="897" href="finite-group-theory.tetrahedra-in-3-space.html#856" class="Function">tetrahedron-in-3-space</a> <a id="920" class="Symbol">=</a>
  <a id="924" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="926" class="Symbol">(</a> <a id="928" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="952" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="958" class="Number">4</a><a id="959" class="Symbol">)</a>
    <a id="965" class="Symbol">(</a> <a id="967" class="Symbol">λ</a> <a id="969" href="finite-group-theory.tetrahedra-in-3-space.html#969" class="Bound">X</a> <a id="971" class="Symbol">→</a>
      <a id="979" href="univalent-combinatorics.cyclic-finite-types.html#3715" class="Function">cyclic-structure</a> <a id="996" class="Number">3</a>
        <a id="1006" class="Symbol">(</a> <a id="1008" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1010" class="Symbol">(</a> <a id="1012" href="univalent-combinatorics.2-element-decidable-subtypes.html#2125" class="Function">2-Element-Decidable-Subtype</a> <a id="1040" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
              <a id="1060" class="Symbol">(</a> <a id="1062" href="univalent-combinatorics.2-element-decidable-subtypes.html#2125" class="Function">2-Element-Decidable-Subtype</a> <a id="1090" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
                <a id="1112" class="Symbol">(</a> <a id="1114" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1143" class="Number">4</a> <a id="1145" href="finite-group-theory.tetrahedra-in-3-space.html#969" class="Bound">X</a><a id="1146" class="Symbol">)))</a>
            <a id="1162" class="Symbol">(</a> <a id="1164" class="Symbol">λ</a> <a id="1166" href="finite-group-theory.tetrahedra-in-3-space.html#1166" class="Bound">Q</a> <a id="1168" class="Symbol">→</a>
              <a id="1184" class="Symbol">(</a><a id="1185" href="finite-group-theory.tetrahedra-in-3-space.html#1185" class="Bound">x</a> <a id="1187" class="Symbol">:</a> <a id="1189" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1218" class="Number">4</a> <a id="1220" href="finite-group-theory.tetrahedra-in-3-space.html#969" class="Bound">X</a><a id="1221" class="Symbol">)</a> <a id="1223" class="Symbol">→</a>
              <a id="1239" href="foundation-core.empty-types.html#972" class="Function">is-empty</a>
                <a id="1264" class="Symbol">(</a> <a id="1266" class="Symbol">(</a><a id="1267" href="finite-group-theory.tetrahedra-in-3-space.html#1267" class="Bound">P</a> <a id="1269" class="Symbol">:</a> <a id="1271" href="univalent-combinatorics.2-element-decidable-subtypes.html#3603" class="Function">type-2-Element-Decidable-Subtype</a> <a id="1304" href="finite-group-theory.tetrahedra-in-3-space.html#1166" class="Bound">Q</a><a id="1305" class="Symbol">)</a> <a id="1307" class="Symbol">→</a>
                  <a id="1327" href="univalent-combinatorics.2-element-decidable-subtypes.html#2988" class="Function">is-in-2-Element-Decidable-Subtype</a>
                    <a id="1381" class="Symbol">(</a><a id="1382" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1386" href="finite-group-theory.tetrahedra-in-3-space.html#1267" class="Bound">P</a><a id="1387" class="Symbol">)</a>
                    <a id="1409" class="Symbol">(</a> <a id="1411" href="finite-group-theory.tetrahedra-in-3-space.html#1185" class="Bound">x</a><a id="1412" class="Symbol">)))))</a>

<a id="1419" class="Keyword">module</a> <a id="1426" href="finite-group-theory.tetrahedra-in-3-space.html#1426" class="Module">_</a>
  <a id="1430" class="Symbol">(</a><a id="1431" href="finite-group-theory.tetrahedra-in-3-space.html#1431" class="Bound">T</a> <a id="1433" class="Symbol">:</a> <a id="1435" href="finite-group-theory.tetrahedra-in-3-space.html#856" class="Function">tetrahedron-in-3-space</a><a id="1457" class="Symbol">)</a>
  <a id="1461" class="Keyword">where</a>

  <a id="1470" href="finite-group-theory.tetrahedra-in-3-space.html#1470" class="Function">vertex-tetrahedron-in-3-space</a> <a id="1500" class="Symbol">:</a> <a id="1502" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1505" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="1513" href="finite-group-theory.tetrahedra-in-3-space.html#1470" class="Function">vertex-tetrahedron-in-3-space</a> <a id="1543" class="Symbol">=</a> <a id="1545" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1574" class="Number">4</a> <a id="1576" class="Symbol">(</a><a id="1577" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1581" href="finite-group-theory.tetrahedra-in-3-space.html#1431" class="Bound">T</a><a id="1582" class="Symbol">)</a>

  <a id="1587" href="finite-group-theory.tetrahedra-in-3-space.html#1587" class="Function">cyclic-structure-tetrahedron-in-3-space</a> <a id="1627" class="Symbol">:</a>
    <a id="1633" href="univalent-combinatorics.cyclic-finite-types.html#3715" class="Function">cyclic-structure</a> <a id="1650" class="Number">3</a>
      <a id="1658" class="Symbol">(</a> <a id="1660" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1662" class="Symbol">(</a> <a id="1664" href="univalent-combinatorics.2-element-decidable-subtypes.html#2125" class="Function">2-Element-Decidable-Subtype</a> <a id="1692" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
            <a id="1710" class="Symbol">(</a> <a id="1712" href="univalent-combinatorics.2-element-decidable-subtypes.html#2125" class="Function">2-Element-Decidable-Subtype</a> <a id="1740" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
              <a id="1760" class="Symbol">(</a> <a id="1762" href="finite-group-theory.tetrahedra-in-3-space.html#1470" class="Function">vertex-tetrahedron-in-3-space</a><a id="1791" class="Symbol">)))</a>
          <a id="1805" class="Symbol">(</a> <a id="1807" class="Symbol">λ</a> <a id="1809" href="finite-group-theory.tetrahedra-in-3-space.html#1809" class="Bound">Q</a> <a id="1811" class="Symbol">→</a>
            <a id="1825" class="Symbol">(</a><a id="1826" href="finite-group-theory.tetrahedra-in-3-space.html#1826" class="Bound">x</a> <a id="1828" class="Symbol">:</a> <a id="1830" href="finite-group-theory.tetrahedra-in-3-space.html#1470" class="Function">vertex-tetrahedron-in-3-space</a><a id="1859" class="Symbol">)</a> <a id="1861" class="Symbol">→</a>
            <a id="1875" href="foundation-core.empty-types.html#972" class="Function">is-empty</a>
              <a id="1898" class="Symbol">(</a> <a id="1900" class="Symbol">(</a><a id="1901" href="finite-group-theory.tetrahedra-in-3-space.html#1901" class="Bound">P</a> <a id="1903" class="Symbol">:</a> <a id="1905" href="univalent-combinatorics.2-element-decidable-subtypes.html#3603" class="Function">type-2-Element-Decidable-Subtype</a> <a id="1938" href="finite-group-theory.tetrahedra-in-3-space.html#1809" class="Bound">Q</a><a id="1939" class="Symbol">)</a> <a id="1941" class="Symbol">→</a>
                <a id="1959" href="univalent-combinatorics.2-element-decidable-subtypes.html#2988" class="Function">is-in-2-Element-Decidable-Subtype</a>
                  <a id="2011" class="Symbol">(</a><a id="2012" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2016" href="finite-group-theory.tetrahedra-in-3-space.html#1901" class="Bound">P</a><a id="2017" class="Symbol">)</a>
                  <a id="2037" class="Symbol">(</a> <a id="2039" href="finite-group-theory.tetrahedra-in-3-space.html#1826" class="Bound">x</a><a id="2040" class="Symbol">))))</a>
  <a id="2047" href="finite-group-theory.tetrahedra-in-3-space.html#1587" class="Function">cyclic-structure-tetrahedron-in-3-space</a> <a id="2087" class="Symbol">=</a> <a id="2089" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2093" href="finite-group-theory.tetrahedra-in-3-space.html#1431" class="Bound">T</a>
</pre>