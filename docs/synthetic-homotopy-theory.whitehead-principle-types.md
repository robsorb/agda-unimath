# The Whitehead principle for types

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="synthetic-homotopy-theory.whitehead-principle-types.html" class="Module">synthetic-homotopy-theory.whitehead-principle-types</a> <a id="105" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="foundation.functoriality-truncation.html" class="Module">foundation.functoriality-truncation</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="foundation.infinity-connected-types.html" class="Module">foundation.infinity-connected-types</a>
<a id="340" class="Keyword">open</a> <a id="345" class="Keyword">import</a> <a id="352" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="416" class="Keyword">open</a> <a id="421" class="Keyword">import</a> <a id="428" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="456" class="Keyword">open</a> <a id="461" class="Keyword">import</a> <a id="468" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="544" class="Keyword">open</a> <a id="549" class="Keyword">import</a> <a id="556" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="587" class="Keyword">open</a> <a id="592" class="Keyword">import</a> <a id="599" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="630" class="Keyword">open</a> <a id="635" class="Keyword">import</a> <a id="642" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

The {{#concept "Whitehead principle" Agda=Whitehead-Principle}} asserts that
[∞-connected types](foundation.infinity-connected-types.md) are
[contractible](foundation-core.contractible-types.md). I.e., if a type is
$n$-[connected](foundation.connected-types.md) for every $n$, then it is
contractible. This principle is also referred to as _hypercompleteness_ and is
not validated in every ∞-topos.

In
[`whitehead-principle-maps`](synthetic-homotopy-theory.whitehead-principle-maps.md)
we show, assuming the Whitehead principle in enough universes, that the
Whitehead principle for types is
[equivalent](foundation.logical-equivalences.md) to asking that maps whose
[fibers](foundation-core.fibers-of-maps.md) are ∞-connected are
[equivalences](foundation-core.equivalences.md).

## Definition

<pre class="Agda"><a id="Whitehead-Principle-Level"></a><a id="1501" href="synthetic-homotopy-theory.whitehead-principle-types.html#1501" class="Function">Whitehead-Principle-Level</a> <a id="1527" class="Symbol">:</a> <a id="1529" class="Symbol">(</a><a id="1530" href="synthetic-homotopy-theory.whitehead-principle-types.html#1530" class="Bound">l</a> <a id="1532" class="Symbol">:</a> <a id="1534" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1539" class="Symbol">)</a> <a id="1541" class="Symbol">→</a> <a id="1543" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1546" class="Symbol">(</a><a id="1547" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1552" href="synthetic-homotopy-theory.whitehead-principle-types.html#1530" class="Bound">l</a><a id="1553" class="Symbol">)</a>
<a id="1555" href="synthetic-homotopy-theory.whitehead-principle-types.html#1501" class="Function">Whitehead-Principle-Level</a> <a id="1581" href="synthetic-homotopy-theory.whitehead-principle-types.html#1581" class="Bound">l</a> <a id="1583" class="Symbol">=</a> <a id="1585" class="Symbol">(</a><a id="1586" href="synthetic-homotopy-theory.whitehead-principle-types.html#1586" class="Bound">X</a> <a id="1588" class="Symbol">:</a> <a id="1590" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1593" href="synthetic-homotopy-theory.whitehead-principle-types.html#1581" class="Bound">l</a><a id="1594" class="Symbol">)</a> <a id="1596" class="Symbol">→</a> <a id="1598" href="foundation.infinity-connected-types.html#1000" class="Function">is-∞-connected</a> <a id="1613" href="synthetic-homotopy-theory.whitehead-principle-types.html#1586" class="Bound">X</a> <a id="1615" class="Symbol">→</a> <a id="1617" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="1626" href="synthetic-homotopy-theory.whitehead-principle-types.html#1586" class="Bound">X</a>

<a id="Whitehead-Principle"></a><a id="1629" href="synthetic-homotopy-theory.whitehead-principle-types.html#1629" class="Function">Whitehead-Principle</a> <a id="1649" class="Symbol">:</a> <a id="1651" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
<a id="1655" href="synthetic-homotopy-theory.whitehead-principle-types.html#1629" class="Function">Whitehead-Principle</a> <a id="1675" class="Symbol">=</a> <a id="1677" class="Symbol">{</a><a id="1678" href="synthetic-homotopy-theory.whitehead-principle-types.html#1678" class="Bound">l</a> <a id="1680" class="Symbol">:</a> <a id="1682" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1687" class="Symbol">}</a> <a id="1689" class="Symbol">→</a> <a id="1691" href="synthetic-homotopy-theory.whitehead-principle-types.html#1501" class="Function">Whitehead-Principle-Level</a> <a id="1717" href="synthetic-homotopy-theory.whitehead-principle-types.html#1678" class="Bound">l</a>
</pre>
## See also

- [The plus principle](synthetic-homotopy-theory.plus-principle.md)

## External links

- [hypercomplete object](https://ncatlab.org/nlab/show/hypercomplete+object) on
  $n$Lab
- [Whitehead theorem](https://en.m.wikipedia.org/w/index.php?title=Whitehead_theorem)
  on Wikipedia

## References

For the equivalent concept in the ∞-categorical semantics of homotopy type
theory, cf. §6.5.2 of Lurie's _Higher Topos Theory_ {{#cite Lurie09}}.

{{#bibliography}}
