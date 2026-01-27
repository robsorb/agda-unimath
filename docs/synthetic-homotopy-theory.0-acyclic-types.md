# `0`-acyclic types

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="synthetic-homotopy-theory.0-acyclic-types.html" class="Module">synthetic-homotopy-theory.0-acyclic-types</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="407" class="Keyword">open</a> <a id="412" class="Keyword">import</a> <a id="419" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="481" class="Keyword">open</a> <a id="486" class="Keyword">import</a> <a id="493" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="521" class="Keyword">open</a> <a id="526" class="Keyword">import</a> <a id="533" href="synthetic-homotopy-theory.0-acyclic-maps.html" class="Module">synthetic-homotopy-theory.0-acyclic-maps</a>
<a id="574" class="Keyword">open</a> <a id="579" class="Keyword">import</a> <a id="586" href="synthetic-homotopy-theory.truncated-acyclic-maps.html" class="Module">synthetic-homotopy-theory.truncated-acyclic-maps</a>
<a id="635" class="Keyword">open</a> <a id="640" class="Keyword">import</a> <a id="647" href="synthetic-homotopy-theory.truncated-acyclic-types.html" class="Module">synthetic-homotopy-theory.truncated-acyclic-types</a>
</pre>
</details>

## Idea

A type is **`0`-acyclic** if its
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`0`-connected](foundation.0-connected-types.md).

We can characterize the `0`-acyclic types as the
[inhabited types](foundation.inhabited-types.md).

## Definition

### The predicate of being a `0`-acyclic type

<pre class="Agda"><a id="1044" class="Keyword">module</a> <a id="1051" href="synthetic-homotopy-theory.0-acyclic-types.html#1051" class="Module">_</a>
  <a id="1055" class="Symbol">{</a><a id="1056" href="synthetic-homotopy-theory.0-acyclic-types.html#1056" class="Bound">l</a> <a id="1058" class="Symbol">:</a> <a id="1060" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1065" class="Symbol">}</a> <a id="1067" class="Symbol">(</a><a id="1068" href="synthetic-homotopy-theory.0-acyclic-types.html#1068" class="Bound">A</a> <a id="1070" class="Symbol">:</a> <a id="1072" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1075" href="synthetic-homotopy-theory.0-acyclic-types.html#1056" class="Bound">l</a><a id="1076" class="Symbol">)</a>
  <a id="1080" class="Keyword">where</a>

  <a id="1089" href="synthetic-homotopy-theory.0-acyclic-types.html#1089" class="Function">is-0-acyclic-Prop</a> <a id="1107" class="Symbol">:</a> <a id="1109" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1114" href="synthetic-homotopy-theory.0-acyclic-types.html#1056" class="Bound">l</a>
  <a id="1118" href="synthetic-homotopy-theory.0-acyclic-types.html#1089" class="Function">is-0-acyclic-Prop</a> <a id="1136" class="Symbol">=</a> <a id="1138" href="synthetic-homotopy-theory.truncated-acyclic-types.html#840" class="Function">is-truncated-acyclic-Prop</a> <a id="1164" href="foundation-core.truncation-levels.html#672" class="Function">zero-𝕋</a> <a id="1171" href="synthetic-homotopy-theory.0-acyclic-types.html#1068" class="Bound">A</a>

  <a id="1176" href="synthetic-homotopy-theory.0-acyclic-types.html#1176" class="Function">is-0-acyclic</a> <a id="1189" class="Symbol">:</a> <a id="1191" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1194" href="synthetic-homotopy-theory.0-acyclic-types.html#1056" class="Bound">l</a>
  <a id="1198" href="synthetic-homotopy-theory.0-acyclic-types.html#1176" class="Function">is-0-acyclic</a> <a id="1211" class="Symbol">=</a> <a id="1213" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1223" href="synthetic-homotopy-theory.0-acyclic-types.html#1089" class="Function">is-0-acyclic-Prop</a>

  <a id="1244" href="synthetic-homotopy-theory.0-acyclic-types.html#1244" class="Function">is-prop-is-0-acyclic</a> <a id="1265" class="Symbol">:</a> <a id="1267" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1275" href="synthetic-homotopy-theory.0-acyclic-types.html#1176" class="Function">is-0-acyclic</a>
  <a id="1290" href="synthetic-homotopy-theory.0-acyclic-types.html#1244" class="Function">is-prop-is-0-acyclic</a> <a id="1311" class="Symbol">=</a> <a id="1313" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1331" href="synthetic-homotopy-theory.0-acyclic-types.html#1089" class="Function">is-0-acyclic-Prop</a>
</pre>
## Properties

### A type is `0`-acyclic if and only if it is inhabited

<pre class="Agda"><a id="1435" class="Keyword">module</a> <a id="1442" href="synthetic-homotopy-theory.0-acyclic-types.html#1442" class="Module">_</a>
  <a id="1446" class="Symbol">{</a><a id="1447" href="synthetic-homotopy-theory.0-acyclic-types.html#1447" class="Bound">l</a> <a id="1449" class="Symbol">:</a> <a id="1451" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1456" class="Symbol">}</a> <a id="1458" class="Symbol">{</a><a id="1459" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a> <a id="1461" class="Symbol">:</a> <a id="1463" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1466" href="synthetic-homotopy-theory.0-acyclic-types.html#1447" class="Bound">l</a><a id="1467" class="Symbol">}</a>
  <a id="1471" class="Keyword">where</a>

  <a id="1480" href="synthetic-homotopy-theory.0-acyclic-types.html#1480" class="Function">is-inhabited-is-0-acyclic</a> <a id="1506" class="Symbol">:</a> <a id="1508" href="synthetic-homotopy-theory.0-acyclic-types.html#1176" class="Function">is-0-acyclic</a> <a id="1521" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a> <a id="1523" class="Symbol">→</a> <a id="1525" href="foundation.inhabited-types.html#1345" class="Function">is-inhabited</a> <a id="1538" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a>
  <a id="1542" href="synthetic-homotopy-theory.0-acyclic-types.html#1480" class="Function">is-inhabited-is-0-acyclic</a> <a id="1568" href="synthetic-homotopy-theory.0-acyclic-types.html#1568" class="Bound">ac</a> <a id="1571" class="Symbol">=</a>
    <a id="1577" href="foundation.functoriality-propositional-truncation.html#1256" class="Function">map-trunc-Prop</a>
      <a id="1598" class="Symbol">(</a> <a id="1600" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a><a id="1603" class="Symbol">)</a>
      <a id="1611" class="Symbol">(</a> <a id="1613" href="synthetic-homotopy-theory.0-acyclic-maps.html#1486" class="Function">is-surjective-is-0-acyclic-map</a>
        <a id="1652" class="Symbol">(</a> <a id="1654" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="1667" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a><a id="1668" class="Symbol">)</a>
        <a id="1678" class="Symbol">(</a> <a id="1680" href="synthetic-homotopy-theory.truncated-acyclic-maps.html#4399" class="Function">is-truncated-acyclic-map-terminal-map-is-truncated-acyclic</a> <a id="1739" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a> <a id="1741" href="synthetic-homotopy-theory.0-acyclic-types.html#1568" class="Bound">ac</a><a id="1743" class="Symbol">)</a>
        <a id="1753" class="Symbol">(</a> <a id="1755" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="1759" class="Symbol">))</a>

  <a id="1765" href="synthetic-homotopy-theory.0-acyclic-types.html#1765" class="Function">is-0-acyclic-is-inhabited</a> <a id="1791" class="Symbol">:</a> <a id="1793" href="foundation.inhabited-types.html#1345" class="Function">is-inhabited</a> <a id="1806" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a> <a id="1808" class="Symbol">→</a> <a id="1810" href="synthetic-homotopy-theory.0-acyclic-types.html#1176" class="Function">is-0-acyclic</a> <a id="1823" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a>
  <a id="1827" href="synthetic-homotopy-theory.0-acyclic-types.html#1765" class="Function">is-0-acyclic-is-inhabited</a> <a id="1853" href="synthetic-homotopy-theory.0-acyclic-types.html#1853" class="Bound">h</a> <a id="1855" class="Symbol">=</a>
    <a id="1861" href="synthetic-homotopy-theory.truncated-acyclic-maps.html#4673" class="Function">is-truncated-acyclic-is-truncated-acyclic-map-terminal-map</a> <a id="1920" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a>
      <a id="1928" class="Symbol">(</a> <a id="1930" href="synthetic-homotopy-theory.0-acyclic-maps.html#1707" class="Function">is-0-acyclic-map-is-surjective</a>
        <a id="1969" class="Symbol">(</a> <a id="1971" href="foundation.unit-type.html#1269" class="Function">terminal-map</a> <a id="1984" href="synthetic-homotopy-theory.0-acyclic-types.html#1459" class="Bound">A</a><a id="1985" class="Symbol">)</a>
        <a id="1995" class="Symbol">(</a> <a id="1997" class="Symbol">λ</a> <a id="1999" href="synthetic-homotopy-theory.0-acyclic-types.html#1999" class="Bound">u</a> <a id="2001" class="Symbol">→</a>
          <a id="2013" href="foundation.functoriality-propositional-truncation.html#1256" class="Function">map-trunc-Prop</a>
            <a id="2040" class="Symbol">(λ</a> <a id="2043" href="synthetic-homotopy-theory.0-acyclic-types.html#2043" class="Bound">a</a> <a id="2045" class="Symbol">→</a> <a id="2047" class="Symbol">(</a><a id="2048" href="synthetic-homotopy-theory.0-acyclic-types.html#2043" class="Bound">a</a> <a id="2050" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2052" class="Symbol">(</a><a id="2053" href="foundation-core.contractible-types.html#1324" class="Function">contraction</a> <a id="2065" href="foundation.unit-type.html#2082" class="Function">is-contr-unit</a> <a id="2079" href="synthetic-homotopy-theory.0-acyclic-types.html#1999" class="Bound">u</a><a id="2080" class="Symbol">)))</a>
            <a id="2096" class="Symbol">(</a> <a id="2098" href="synthetic-homotopy-theory.0-acyclic-types.html#1853" class="Bound">h</a><a id="2099" class="Symbol">)))</a>
</pre>
## See also

- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
