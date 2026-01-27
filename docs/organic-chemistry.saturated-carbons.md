# Saturated carbons

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="organic-chemistry.saturated-carbons.html" class="Module">organic-chemistry.saturated-carbons</a> <a id="73" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="129" class="Keyword">open</a> <a id="134" class="Keyword">import</a> <a id="141" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="organic-chemistry.hydrocarbons.html" class="Module">organic-chemistry.hydrocarbons</a>

<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

An important distinguishing property of organic compounds is the presence of
double or triple carbon-carbon bonds, i.e., the presence or absence of
_unsaturated carbons_. In this module we define what it means for a carbon atom
to be saturated, and what it means for carbon atoms to have double and triple
bonds.

## Definition

<pre class="Agda"><a id="793" class="Keyword">module</a> <a id="800" href="organic-chemistry.saturated-carbons.html#800" class="Module">_</a>
  <a id="804" class="Symbol">{</a><a id="805" href="organic-chemistry.saturated-carbons.html#805" class="Bound">l1</a> <a id="808" href="organic-chemistry.saturated-carbons.html#808" class="Bound">l2</a> <a id="811" class="Symbol">:</a> <a id="813" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="818" class="Symbol">}</a> <a id="820" class="Symbol">(</a><a id="821" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a> <a id="823" class="Symbol">:</a> <a id="825" href="organic-chemistry.hydrocarbons.html#1569" class="Function">hydrocarbon</a> <a id="837" href="organic-chemistry.saturated-carbons.html#805" class="Bound">l1</a> <a id="840" href="organic-chemistry.saturated-carbons.html#808" class="Bound">l2</a><a id="842" class="Symbol">)</a>
  <a id="846" class="Keyword">where</a>
  <a id="854" href="organic-chemistry.saturated-carbons.html#854" class="Function">is-saturated-carbon-hydrocarbon</a> <a id="886" class="Symbol">:</a> <a id="888" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="907" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a> <a id="909" class="Symbol">→</a> <a id="911" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="914" class="Symbol">(</a><a id="915" href="organic-chemistry.saturated-carbons.html#805" class="Bound">l1</a> <a id="918" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="920" href="organic-chemistry.saturated-carbons.html#808" class="Bound">l2</a><a id="922" class="Symbol">)</a>
  <a id="926" href="organic-chemistry.saturated-carbons.html#854" class="Function">is-saturated-carbon-hydrocarbon</a> <a id="958" href="organic-chemistry.saturated-carbons.html#958" class="Bound">c</a> <a id="960" class="Symbol">=</a>
      <a id="968" class="Symbol">(</a><a id="969" href="organic-chemistry.saturated-carbons.html#969" class="Bound">c&#39;</a> <a id="972" class="Symbol">:</a> <a id="974" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="993" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a><a id="994" class="Symbol">)</a> <a id="996" class="Symbol">→</a>
      <a id="1004" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1012" class="Symbol">(</a><a id="1013" href="organic-chemistry.hydrocarbons.html#3426" class="Function">edge-hydrocarbon</a> <a id="1030" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a> <a id="1032" class="Symbol">(</a><a id="1033" href="foundation.unordered-pairs.html#4836" class="Function">standard-unordered-pair</a> <a id="1057" href="organic-chemistry.saturated-carbons.html#958" class="Bound">c</a> <a id="1059" href="organic-chemistry.saturated-carbons.html#969" class="Bound">c&#39;</a><a id="1061" class="Symbol">))</a>
</pre>
Type-theoretically, the saturation condition on a carbon atom (fix one and call
it `c`) is incarnated by asking that, for every other carbon atom `c'`, the type
of edges `c --- c'` is a proposition. Since edges incident on `c` are a subtype
of the type representing electrons of `c`, this guarantees that `c` shares no
more than 1 electron with any other carbon in the structure. An **alkane** is a
hydrocarbon such that every carbon is saturated.

<pre class="Agda">  <a id="1528" href="organic-chemistry.saturated-carbons.html#1528" class="Function">double-bond-on-hydrocarbon</a> <a id="1555" class="Symbol">:</a> <a id="1557" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="1576" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a> <a id="1578" class="Symbol">→</a> <a id="1580" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1583" class="Symbol">(</a><a id="1584" href="organic-chemistry.saturated-carbons.html#805" class="Bound">l1</a> <a id="1587" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1589" href="organic-chemistry.saturated-carbons.html#808" class="Bound">l2</a><a id="1591" class="Symbol">)</a>
  <a id="1595" href="organic-chemistry.saturated-carbons.html#1528" class="Function">double-bond-on-hydrocarbon</a> <a id="1622" href="organic-chemistry.saturated-carbons.html#1622" class="Bound">c</a> <a id="1624" class="Symbol">=</a> <a id="1626" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1628" class="Symbol">(</a><a id="1629" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="1648" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a><a id="1649" class="Symbol">)</a> <a id="1651" class="Symbol">λ</a> <a id="1653" href="organic-chemistry.saturated-carbons.html#1653" class="Bound">c&#39;</a> <a id="1656" class="Symbol">→</a>
    <a id="1662" href="univalent-combinatorics.finite-types.html#3146" class="Function">has-cardinality-ℕ</a> <a id="1680" class="Number">2</a> <a id="1682" class="Symbol">(</a><a id="1683" href="organic-chemistry.hydrocarbons.html#3426" class="Function">edge-hydrocarbon</a> <a id="1700" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a> <a id="1702" class="Symbol">(</a><a id="1703" href="foundation.unordered-pairs.html#4836" class="Function">standard-unordered-pair</a> <a id="1727" href="organic-chemistry.saturated-carbons.html#1622" class="Bound">c</a> <a id="1729" href="organic-chemistry.saturated-carbons.html#1653" class="Bound">c&#39;</a><a id="1731" class="Symbol">))</a>

  <a id="1737" href="organic-chemistry.saturated-carbons.html#1737" class="Function">has-double-bond-hydrocarbon</a> <a id="1765" class="Symbol">:</a> <a id="1767" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="1786" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a> <a id="1788" class="Symbol">→</a> <a id="1790" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1795" class="Symbol">(</a><a id="1796" href="organic-chemistry.saturated-carbons.html#805" class="Bound">l1</a> <a id="1799" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1801" href="organic-chemistry.saturated-carbons.html#808" class="Bound">l2</a><a id="1803" class="Symbol">)</a>
  <a id="1807" href="organic-chemistry.saturated-carbons.html#1737" class="Function">has-double-bond-hydrocarbon</a> <a id="1835" href="organic-chemistry.saturated-carbons.html#1835" class="Bound">c</a> <a id="1837" class="Symbol">=</a> <a id="1839" href="foundation.propositional-truncations.html#2109" class="Function">trunc-Prop</a> <a id="1850" class="Symbol">(</a><a id="1851" href="organic-chemistry.saturated-carbons.html#1528" class="Function">double-bond-on-hydrocarbon</a> <a id="1878" href="organic-chemistry.saturated-carbons.html#1835" class="Bound">c</a><a id="1879" class="Symbol">)</a>

  <a id="1884" href="organic-chemistry.saturated-carbons.html#1884" class="Function">has-triple-bond-hydrocarbon</a> <a id="1912" class="Symbol">:</a> <a id="1914" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="1933" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a> <a id="1935" class="Symbol">→</a> <a id="1937" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1940" class="Symbol">(</a><a id="1941" href="organic-chemistry.saturated-carbons.html#805" class="Bound">l1</a> <a id="1944" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1946" href="organic-chemistry.saturated-carbons.html#808" class="Bound">l2</a><a id="1948" class="Symbol">)</a>
  <a id="1952" href="organic-chemistry.saturated-carbons.html#1884" class="Function">has-triple-bond-hydrocarbon</a> <a id="1980" href="organic-chemistry.saturated-carbons.html#1980" class="Bound">c</a> <a id="1982" class="Symbol">=</a> <a id="1984" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1986" class="Symbol">(</a><a id="1987" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="2006" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a><a id="2007" class="Symbol">)</a> <a id="2009" class="Symbol">λ</a> <a id="2011" href="organic-chemistry.saturated-carbons.html#2011" class="Bound">c&#39;</a> <a id="2014" class="Symbol">→</a>
    <a id="2020" href="univalent-combinatorics.finite-types.html#3146" class="Function">has-cardinality-ℕ</a> <a id="2038" class="Number">3</a> <a id="2040" class="Symbol">(</a><a id="2041" href="organic-chemistry.hydrocarbons.html#3426" class="Function">edge-hydrocarbon</a> <a id="2058" href="organic-chemistry.saturated-carbons.html#821" class="Bound">H</a> <a id="2060" class="Symbol">(</a><a id="2061" href="foundation.unordered-pairs.html#4836" class="Function">standard-unordered-pair</a> <a id="2085" href="organic-chemistry.saturated-carbons.html#1980" class="Bound">c</a> <a id="2087" href="organic-chemistry.saturated-carbons.html#2011" class="Bound">c&#39;</a><a id="2089" class="Symbol">))</a>
</pre>
For a carbon atom `c` to have a double (respectively, a triple) bond, we must
find another carbon `c'` such that the type of edges `c --- c'` has cardinality
2 (respectively, 3). If all we care about is that the carbon atom has _some_
double bond, we use the truncated version. We note that, since in the graph
representation of hydrocarbons, vertices can have at most three incident edges,
if a carbon atom can have at most one triple bond.
