# Complements of double negation stable subtypes

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="logic.complements-double-negation-stable-subtypes.html" class="Module">logic.complements-double-negation-stable-subtypes</a> <a id="116" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.double-negation.html" class="Module">foundation.double-negation</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.double-negation-stable-propositions.html" class="Module">foundation.double-negation-stable-propositions</a>
<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="foundation.full-subtypes.html" class="Module">foundation.full-subtypes</a>
<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="386" class="Keyword">open</a> <a id="391" class="Keyword">import</a> <a id="398" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="foundation.postcomposition-functions.html" class="Module">foundation.postcomposition-functions</a>
<a id="467" class="Keyword">open</a> <a id="472" class="Keyword">import</a> <a id="479" href="foundation.powersets.html" class="Module">foundation.powersets</a>
<a id="500" class="Keyword">open</a> <a id="505" class="Keyword">import</a> <a id="512" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="549" class="Keyword">open</a> <a id="554" class="Keyword">import</a> <a id="561" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="581" class="Keyword">open</a> <a id="586" class="Keyword">import</a> <a id="593" href="foundation.unions-subtypes.html" class="Module">foundation.unions-subtypes</a>
<a id="620" class="Keyword">open</a> <a id="625" class="Keyword">import</a> <a id="632" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="660" class="Keyword">open</a> <a id="665" class="Keyword">import</a> <a id="672" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>

<a id="704" class="Keyword">open</a> <a id="709" class="Keyword">import</a> <a id="716" href="logic.double-negation-stable-subtypes.html" class="Module">logic.double-negation-stable-subtypes</a>
</pre>
</details>

## Idea

The
{{#concept "complement" Disambiguation="of a double negation stable subtype" Agda=complement-double-negation-stable-subtype}}
of a [double negation stable subtype](logic.double-negation-stable-subtypes.md)
`B ⊆ A` consists of the elements that are not in `B`.

## Definition

### Complements of double negation stable subtypes

<pre class="Agda"><a id="complement-double-negation-stable-subtype"></a><a id="1120" href="logic.complements-double-negation-stable-subtypes.html#1120" class="Function">complement-double-negation-stable-subtype</a> <a id="1162" class="Symbol">:</a>
  <a id="1166" class="Symbol">{</a><a id="1167" href="logic.complements-double-negation-stable-subtypes.html#1167" class="Bound">l1</a> <a id="1170" href="logic.complements-double-negation-stable-subtypes.html#1170" class="Bound">l2</a> <a id="1173" class="Symbol">:</a> <a id="1175" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1180" class="Symbol">}</a> <a id="1182" class="Symbol">{</a><a id="1183" href="logic.complements-double-negation-stable-subtypes.html#1183" class="Bound">A</a> <a id="1185" class="Symbol">:</a> <a id="1187" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1190" href="logic.complements-double-negation-stable-subtypes.html#1167" class="Bound">l1</a><a id="1192" class="Symbol">}</a> <a id="1194" class="Symbol">→</a>
  <a id="1198" href="logic.double-negation-stable-subtypes.html#2451" class="Function">double-negation-stable-subtype</a> <a id="1229" href="logic.complements-double-negation-stable-subtypes.html#1170" class="Bound">l2</a> <a id="1232" href="logic.complements-double-negation-stable-subtypes.html#1183" class="Bound">A</a> <a id="1234" class="Symbol">→</a>
  <a id="1238" href="logic.double-negation-stable-subtypes.html#2451" class="Function">double-negation-stable-subtype</a> <a id="1269" href="logic.complements-double-negation-stable-subtypes.html#1170" class="Bound">l2</a> <a id="1272" href="logic.complements-double-negation-stable-subtypes.html#1183" class="Bound">A</a>
<a id="1274" href="logic.complements-double-negation-stable-subtypes.html#1120" class="Function">complement-double-negation-stable-subtype</a> <a id="1316" href="logic.complements-double-negation-stable-subtypes.html#1316" class="Bound">P</a> <a id="1318" href="logic.complements-double-negation-stable-subtypes.html#1318" class="Bound">x</a> <a id="1320" class="Symbol">=</a>
  <a id="1324" href="foundation.double-negation-stable-propositions.html#8649" class="Function">neg-Double-Negation-Stable-Prop</a> <a id="1356" class="Symbol">(</a><a id="1357" href="logic.complements-double-negation-stable-subtypes.html#1316" class="Bound">P</a> <a id="1359" href="logic.complements-double-negation-stable-subtypes.html#1318" class="Bound">x</a><a id="1360" class="Symbol">)</a>
</pre>
## Properties

### Taking complements is an involution on double negation stable subtypes

<pre class="Agda"><a id="is-involution-complement-double-negation-stable-subtype"></a><a id="1466" href="logic.complements-double-negation-stable-subtypes.html#1466" class="Function">is-involution-complement-double-negation-stable-subtype</a> <a id="1522" class="Symbol">:</a>
  <a id="1526" class="Symbol">{</a><a id="1527" href="logic.complements-double-negation-stable-subtypes.html#1527" class="Bound">l1</a> <a id="1530" href="logic.complements-double-negation-stable-subtypes.html#1530" class="Bound">l2</a> <a id="1533" class="Symbol">:</a> <a id="1535" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1540" class="Symbol">}</a> <a id="1542" class="Symbol">{</a><a id="1543" href="logic.complements-double-negation-stable-subtypes.html#1543" class="Bound">A</a> <a id="1545" class="Symbol">:</a> <a id="1547" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1550" href="logic.complements-double-negation-stable-subtypes.html#1527" class="Bound">l1</a><a id="1552" class="Symbol">}</a> <a id="1554" class="Symbol">→</a>
  <a id="1558" href="foundation.involutions.html#1144" class="Function">is-involution</a> <a id="1572" class="Symbol">(</a><a id="1573" href="logic.complements-double-negation-stable-subtypes.html#1120" class="Function">complement-double-negation-stable-subtype</a> <a id="1615" class="Symbol">{</a><a id="1616" href="logic.complements-double-negation-stable-subtypes.html#1527" class="Bound">l1</a><a id="1618" class="Symbol">}</a> <a id="1620" class="Symbol">{</a><a id="1621" href="logic.complements-double-negation-stable-subtypes.html#1530" class="Bound">l2</a><a id="1623" class="Symbol">}</a> <a id="1625" class="Symbol">{</a><a id="1626" href="logic.complements-double-negation-stable-subtypes.html#1543" class="Bound">A</a><a id="1627" class="Symbol">})</a>
<a id="1630" href="logic.complements-double-negation-stable-subtypes.html#1466" class="Function">is-involution-complement-double-negation-stable-subtype</a> <a id="1686" href="logic.complements-double-negation-stable-subtypes.html#1686" class="Bound">P</a> <a id="1688" class="Symbol">=</a>
  <a id="1692" href="logic.double-negation-stable-subtypes.html#11691" class="Function">eq-has-same-elements-double-negation-stable-subtype</a>
    <a id="1748" class="Symbol">(</a> <a id="1750" href="logic.complements-double-negation-stable-subtypes.html#1120" class="Function">complement-double-negation-stable-subtype</a>
      <a id="1798" class="Symbol">(</a> <a id="1800" href="logic.complements-double-negation-stable-subtypes.html#1120" class="Function">complement-double-negation-stable-subtype</a> <a id="1842" href="logic.complements-double-negation-stable-subtypes.html#1686" class="Bound">P</a><a id="1843" class="Symbol">))</a>
    <a id="1850" class="Symbol">(</a> <a id="1852" href="logic.complements-double-negation-stable-subtypes.html#1686" class="Bound">P</a><a id="1853" class="Symbol">)</a>
    <a id="1859" class="Symbol">(</a> <a id="1861" class="Symbol">λ</a> <a id="1863" href="logic.complements-double-negation-stable-subtypes.html#1863" class="Bound">x</a> <a id="1865" class="Symbol">→</a>
      <a id="1873" class="Symbol">(</a> <a id="1875" href="logic.double-negation-stable-subtypes.html#2927" class="Function">is-double-negation-stable-double-negation-stable-subtype</a> <a id="1932" href="logic.complements-double-negation-stable-subtypes.html#1686" class="Bound">P</a> <a id="1934" href="logic.complements-double-negation-stable-subtypes.html#1863" class="Bound">x</a> <a id="1936" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
        <a id="1946" href="foundation.double-negation.html#782" class="Function">intro-double-negation</a><a id="1967" class="Symbol">))</a>
</pre>