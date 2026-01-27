# Dedekind finite sets

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="univalent-combinatorics.dedekind-finite-sets.html" class="Module">univalent-combinatorics.dedekind-finite-sets</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="391" class="Keyword">open</a> <a id="396" class="Keyword">import</a> <a id="403" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="431" class="Keyword">open</a> <a id="436" class="Keyword">import</a> <a id="443" href="univalent-combinatorics.dedekind-finite-types.html" class="Module">univalent-combinatorics.dedekind-finite-types</a>
</pre>
</details>

## Idea

{{#concept "Dedekind finite sets" Agda=set-Dedekind-Finite-Set}} are
[sets](foundation-core.sets.md) `X` with the
[property](foundation-core.propositions.md) that every
self-[embedding](foundation-core.embeddings.md) `X ↪ X` is an
[equivalence](foundation-core.equivalences.md).

## Definitions

### The predicate of being a Dedekind finite set

<pre class="Agda"><a id="is-dedekind-finite-set-Prop"></a><a id="869" href="univalent-combinatorics.dedekind-finite-sets.html#869" class="Function">is-dedekind-finite-set-Prop</a> <a id="897" class="Symbol">:</a> <a id="899" class="Symbol">{</a><a id="900" href="univalent-combinatorics.dedekind-finite-sets.html#900" class="Bound">l</a> <a id="902" class="Symbol">:</a> <a id="904" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="909" class="Symbol">}</a> <a id="911" class="Symbol">→</a> <a id="913" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="917" href="univalent-combinatorics.dedekind-finite-sets.html#900" class="Bound">l</a> <a id="919" class="Symbol">→</a> <a id="921" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="926" href="univalent-combinatorics.dedekind-finite-sets.html#900" class="Bound">l</a>
<a id="928" href="univalent-combinatorics.dedekind-finite-sets.html#869" class="Function">is-dedekind-finite-set-Prop</a> <a id="956" href="univalent-combinatorics.dedekind-finite-sets.html#956" class="Bound">X</a> <a id="958" class="Symbol">=</a>
  <a id="962" href="univalent-combinatorics.dedekind-finite-types.html#1080" class="Function">is-dedekind-finite-Prop</a> <a id="986" class="Symbol">(</a><a id="987" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="996" href="univalent-combinatorics.dedekind-finite-sets.html#956" class="Bound">X</a><a id="997" class="Symbol">)</a>

<a id="is-dedekind-finite-set"></a><a id="1000" href="univalent-combinatorics.dedekind-finite-sets.html#1000" class="Function">is-dedekind-finite-set</a> <a id="1023" class="Symbol">:</a> <a id="1025" class="Symbol">{</a><a id="1026" href="univalent-combinatorics.dedekind-finite-sets.html#1026" class="Bound">l</a> <a id="1028" class="Symbol">:</a> <a id="1030" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1035" class="Symbol">}</a> <a id="1037" class="Symbol">→</a> <a id="1039" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1043" href="univalent-combinatorics.dedekind-finite-sets.html#1026" class="Bound">l</a> <a id="1045" class="Symbol">→</a> <a id="1047" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1050" href="univalent-combinatorics.dedekind-finite-sets.html#1026" class="Bound">l</a>
<a id="1052" href="univalent-combinatorics.dedekind-finite-sets.html#1000" class="Function">is-dedekind-finite-set</a> <a id="1075" href="univalent-combinatorics.dedekind-finite-sets.html#1075" class="Bound">X</a> <a id="1077" class="Symbol">=</a> <a id="1079" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1089" class="Symbol">(</a><a id="1090" href="univalent-combinatorics.dedekind-finite-sets.html#869" class="Function">is-dedekind-finite-set-Prop</a> <a id="1118" href="univalent-combinatorics.dedekind-finite-sets.html#1075" class="Bound">X</a><a id="1119" class="Symbol">)</a>
</pre>
### The subuniverse of Dedekind finite sets

<pre class="Agda"><a id="Dedekind-Finite-Set"></a><a id="1179" href="univalent-combinatorics.dedekind-finite-sets.html#1179" class="Function">Dedekind-Finite-Set</a> <a id="1199" class="Symbol">:</a> <a id="1201" class="Symbol">(</a><a id="1202" href="univalent-combinatorics.dedekind-finite-sets.html#1202" class="Bound">l</a> <a id="1204" class="Symbol">:</a> <a id="1206" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1211" class="Symbol">)</a> <a id="1213" class="Symbol">→</a> <a id="1215" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1218" class="Symbol">(</a><a id="1219" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1224" href="univalent-combinatorics.dedekind-finite-sets.html#1202" class="Bound">l</a><a id="1225" class="Symbol">)</a>
<a id="1227" href="univalent-combinatorics.dedekind-finite-sets.html#1179" class="Function">Dedekind-Finite-Set</a> <a id="1247" href="univalent-combinatorics.dedekind-finite-sets.html#1247" class="Bound">l</a> <a id="1249" class="Symbol">=</a> <a id="1251" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1253" class="Symbol">(</a><a id="1254" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1258" href="univalent-combinatorics.dedekind-finite-sets.html#1247" class="Bound">l</a><a id="1259" class="Symbol">)</a> <a id="1261" href="univalent-combinatorics.dedekind-finite-sets.html#1000" class="Function">is-dedekind-finite-set</a>

<a id="1285" class="Keyword">module</a> <a id="1292" href="univalent-combinatorics.dedekind-finite-sets.html#1292" class="Module">_</a>
  <a id="1296" class="Symbol">{</a><a id="1297" href="univalent-combinatorics.dedekind-finite-sets.html#1297" class="Bound">l</a> <a id="1299" class="Symbol">:</a> <a id="1301" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1306" class="Symbol">}</a> <a id="1308" class="Symbol">(</a><a id="1309" href="univalent-combinatorics.dedekind-finite-sets.html#1309" class="Bound">X</a> <a id="1311" class="Symbol">:</a> <a id="1313" href="univalent-combinatorics.dedekind-finite-sets.html#1179" class="Function">Dedekind-Finite-Set</a> <a id="1333" href="univalent-combinatorics.dedekind-finite-sets.html#1297" class="Bound">l</a><a id="1334" class="Symbol">)</a>
  <a id="1338" class="Keyword">where</a>

  <a id="1347" href="univalent-combinatorics.dedekind-finite-sets.html#1347" class="Function">set-Dedekind-Finite-Set</a> <a id="1371" class="Symbol">:</a> <a id="1373" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1377" href="univalent-combinatorics.dedekind-finite-sets.html#1297" class="Bound">l</a>
  <a id="1381" href="univalent-combinatorics.dedekind-finite-sets.html#1347" class="Function">set-Dedekind-Finite-Set</a> <a id="1405" class="Symbol">=</a> <a id="1407" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1411" href="univalent-combinatorics.dedekind-finite-sets.html#1309" class="Bound">X</a>

  <a id="1416" href="univalent-combinatorics.dedekind-finite-sets.html#1416" class="Function">type-Dedekind-Finite-Set</a> <a id="1441" class="Symbol">:</a> <a id="1443" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1446" href="univalent-combinatorics.dedekind-finite-sets.html#1297" class="Bound">l</a>
  <a id="1450" href="univalent-combinatorics.dedekind-finite-sets.html#1416" class="Function">type-Dedekind-Finite-Set</a> <a id="1475" class="Symbol">=</a> <a id="1477" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1486" href="univalent-combinatorics.dedekind-finite-sets.html#1347" class="Function">set-Dedekind-Finite-Set</a>

  <a id="1513" href="univalent-combinatorics.dedekind-finite-sets.html#1513" class="Function">is-set-type-Dedekind-Finite-Set</a> <a id="1545" class="Symbol">:</a> <a id="1547" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="1554" href="univalent-combinatorics.dedekind-finite-sets.html#1416" class="Function">type-Dedekind-Finite-Set</a>
  <a id="1581" href="univalent-combinatorics.dedekind-finite-sets.html#1513" class="Function">is-set-type-Dedekind-Finite-Set</a> <a id="1613" class="Symbol">=</a> <a id="1615" href="foundation-core.sets.html#1076" class="Function">is-set-type-Set</a> <a id="1631" href="univalent-combinatorics.dedekind-finite-sets.html#1347" class="Function">set-Dedekind-Finite-Set</a>

  <a id="1658" href="univalent-combinatorics.dedekind-finite-sets.html#1658" class="Function">is-dedekind-finite-set-Dedekind-Finite-Set</a> <a id="1701" class="Symbol">:</a>
    <a id="1707" href="univalent-combinatorics.dedekind-finite-sets.html#1000" class="Function">is-dedekind-finite-set</a> <a id="1730" href="univalent-combinatorics.dedekind-finite-sets.html#1347" class="Function">set-Dedekind-Finite-Set</a>
  <a id="1756" href="univalent-combinatorics.dedekind-finite-sets.html#1658" class="Function">is-dedekind-finite-set-Dedekind-Finite-Set</a> <a id="1799" class="Symbol">=</a> <a id="1801" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1805" href="univalent-combinatorics.dedekind-finite-sets.html#1309" class="Bound">X</a>
</pre>
## See also

- [Finite types](univalent-combinatorics.finite-types.md)
- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)

## References

{{#bibliography}} {{#reference Sto87}}

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Dedekind`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Dedekind.html)
  at TypeTopology
- [finite object#Dedekind finiteness](https://ncatlab.org/nlab/show/finite+object#dedekind_finiteness)
  at $n$Lab
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
