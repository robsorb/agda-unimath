# Infinite sets

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="set-theory.infinite-sets.html" class="Module">set-theory.infinite-sets</a> <a id="58" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="114" class="Keyword">open</a> <a id="119" class="Keyword">import</a> <a id="126" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.mere-embeddings.html" class="Module">foundation.mere-embeddings</a>
<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

A [set](foundation-core.sets.md) `A` is said to be
{{#concept "infinite" Disambiguation="set" WD="infinite set" WDID=Q205140}} if
it contains arbitrarily [large](set-theory.cardinalities.md)
[finite](univalent-combinatorics.finite-types.md)
[subsets](foundation-core.subtypes.md).

## Definition

### The predicate on a set of being infinite

<pre class="Agda"><a id="is-infinite-Set-Prop"></a><a id="790" href="set-theory.infinite-sets.html#790" class="Function">is-infinite-Set-Prop</a> <a id="811" class="Symbol">:</a> <a id="813" class="Symbol">{</a><a id="814" href="set-theory.infinite-sets.html#814" class="Bound">l</a> <a id="816" class="Symbol">:</a> <a id="818" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="823" class="Symbol">}</a> <a id="825" class="Symbol">→</a> <a id="827" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="831" href="set-theory.infinite-sets.html#814" class="Bound">l</a> <a id="833" class="Symbol">→</a> <a id="835" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="840" href="set-theory.infinite-sets.html#814" class="Bound">l</a>
<a id="842" href="set-theory.infinite-sets.html#790" class="Function">is-infinite-Set-Prop</a> <a id="863" href="set-theory.infinite-sets.html#863" class="Bound">X</a> <a id="865" class="Symbol">=</a> <a id="867" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="874" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="876" class="Symbol">(λ</a> <a id="879" href="set-theory.infinite-sets.html#879" class="Bound">n</a> <a id="881" class="Symbol">→</a> <a id="883" href="foundation.mere-embeddings.html#508" class="Function">mere-emb-Prop</a> <a id="897" class="Symbol">(</a><a id="898" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="902" href="set-theory.infinite-sets.html#879" class="Bound">n</a><a id="903" class="Symbol">)</a> <a id="905" class="Symbol">(</a><a id="906" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="915" href="set-theory.infinite-sets.html#863" class="Bound">X</a><a id="916" class="Symbol">))</a>

<a id="is-infinite-Set"></a><a id="920" href="set-theory.infinite-sets.html#920" class="Function">is-infinite-Set</a> <a id="936" class="Symbol">:</a> <a id="938" class="Symbol">{</a><a id="939" href="set-theory.infinite-sets.html#939" class="Bound">l</a> <a id="941" class="Symbol">:</a> <a id="943" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="948" class="Symbol">}</a> <a id="950" class="Symbol">→</a> <a id="952" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="956" href="set-theory.infinite-sets.html#939" class="Bound">l</a> <a id="958" class="Symbol">→</a> <a id="960" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="963" href="set-theory.infinite-sets.html#939" class="Bound">l</a>
<a id="965" href="set-theory.infinite-sets.html#920" class="Function">is-infinite-Set</a> <a id="981" href="set-theory.infinite-sets.html#981" class="Bound">X</a> <a id="983" class="Symbol">=</a> <a id="985" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="995" class="Symbol">(</a><a id="996" href="set-theory.infinite-sets.html#790" class="Function">is-infinite-Set-Prop</a> <a id="1017" href="set-theory.infinite-sets.html#981" class="Bound">X</a><a id="1018" class="Symbol">)</a>
</pre>
### The universe of infinite sets

<pre class="Agda"><a id="Infinite-Set"></a><a id="1068" href="set-theory.infinite-sets.html#1068" class="Function">Infinite-Set</a> <a id="1081" class="Symbol">:</a> <a id="1083" class="Symbol">(</a><a id="1084" href="set-theory.infinite-sets.html#1084" class="Bound">l</a> <a id="1086" class="Symbol">:</a> <a id="1088" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1093" class="Symbol">)</a> <a id="1095" class="Symbol">→</a> <a id="1097" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1100" class="Symbol">(</a><a id="1101" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1106" href="set-theory.infinite-sets.html#1084" class="Bound">l</a><a id="1107" class="Symbol">)</a>
<a id="1109" href="set-theory.infinite-sets.html#1068" class="Function">Infinite-Set</a> <a id="1122" href="set-theory.infinite-sets.html#1122" class="Bound">l</a> <a id="1124" class="Symbol">=</a> <a id="1126" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1128" class="Symbol">(</a><a id="1129" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1133" href="set-theory.infinite-sets.html#1122" class="Bound">l</a><a id="1134" class="Symbol">)</a> <a id="1136" class="Symbol">(</a><a id="1137" href="set-theory.infinite-sets.html#920" class="Function">is-infinite-Set</a><a id="1152" class="Symbol">)</a>

<a id="1155" class="Keyword">module</a> <a id="1162" href="set-theory.infinite-sets.html#1162" class="Module">_</a>
  <a id="1166" class="Symbol">{</a><a id="1167" href="set-theory.infinite-sets.html#1167" class="Bound">l</a> <a id="1169" class="Symbol">:</a> <a id="1171" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1176" class="Symbol">}</a> <a id="1178" class="Symbol">(</a><a id="1179" href="set-theory.infinite-sets.html#1179" class="Bound">X</a> <a id="1181" class="Symbol">:</a> <a id="1183" href="set-theory.infinite-sets.html#1068" class="Function">Infinite-Set</a> <a id="1196" href="set-theory.infinite-sets.html#1167" class="Bound">l</a><a id="1197" class="Symbol">)</a>
  <a id="1201" class="Keyword">where</a>

  <a id="1210" href="set-theory.infinite-sets.html#1210" class="Function">set-Infinite-Set</a> <a id="1227" class="Symbol">:</a> <a id="1229" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1233" href="set-theory.infinite-sets.html#1167" class="Bound">l</a>
  <a id="1237" href="set-theory.infinite-sets.html#1210" class="Function">set-Infinite-Set</a> <a id="1254" class="Symbol">=</a> <a id="1256" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1260" href="set-theory.infinite-sets.html#1179" class="Bound">X</a>

  <a id="1265" href="set-theory.infinite-sets.html#1265" class="Function">type-Infinite-Set</a> <a id="1283" class="Symbol">:</a> <a id="1285" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1288" href="set-theory.infinite-sets.html#1167" class="Bound">l</a>
  <a id="1292" href="set-theory.infinite-sets.html#1265" class="Function">type-Infinite-Set</a> <a id="1310" class="Symbol">=</a> <a id="1312" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1321" href="set-theory.infinite-sets.html#1210" class="Function">set-Infinite-Set</a>

  <a id="1341" href="set-theory.infinite-sets.html#1341" class="Function">is-infinite-Infinite-Set</a> <a id="1366" class="Symbol">:</a> <a id="1368" href="set-theory.infinite-sets.html#920" class="Function">is-infinite-Set</a> <a id="1384" href="set-theory.infinite-sets.html#1210" class="Function">set-Infinite-Set</a>
  <a id="1403" href="set-theory.infinite-sets.html#1341" class="Function">is-infinite-Infinite-Set</a> <a id="1428" class="Symbol">=</a> <a id="1430" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1434" href="set-theory.infinite-sets.html#1179" class="Bound">X</a>
</pre>
## External links

- [infinite set](https://ncatlab.org/nlab/show/infinite+set) at $n$Lab
- [Infinite set](https://en.wikipedia.org/wiki/Infinite_set) at Wikipedia
