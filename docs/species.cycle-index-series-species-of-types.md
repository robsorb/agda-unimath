# Cycle index series of species

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="species.cycle-index-series-species-of-types.html" class="Module">species.cycle-index-series-species-of-types</a> <a id="93" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="univalent-combinatorics.cyclic-finite-types.html" class="Module">univalent-combinatorics.cyclic-finite-types</a>
</pre>
</details>

## Idea

The {{#concept "cycle index series" Disambiguation="of species of types"}} of a
[species of types](species.species-of-types.md) `F` is a type family indexed by
finite families of
[cyclic types](univalent-combinatorics.cyclic-finite-types.md). Note that a
finite family of cyclic types `Cᵢ` uniquely determines a permutation `e` on the
disjoint union `C := Σᵢ Cᵢ` of the underlying types of the `Cᵢ`. This
permutation determines an action `F e` on `F C`. The cycle index series of `F`
at the family `Cᵢ` is the type `Fix (F e)` of fixed points of `F e`.

## Definition

<pre class="Agda"><a id="total-type-family-of-cyclic-types"></a><a id="946" href="species.cycle-index-series-species-of-types.html#946" class="Function">total-type-family-of-cyclic-types</a> <a id="980" class="Symbol">:</a>
  <a id="984" class="Symbol">{</a><a id="985" href="species.cycle-index-series-species-of-types.html#985" class="Bound">l1</a> <a id="988" href="species.cycle-index-series-species-of-types.html#988" class="Bound">l2</a> <a id="991" class="Symbol">:</a> <a id="993" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="998" class="Symbol">}</a> <a id="1000" class="Symbol">(</a><a id="1001" href="species.cycle-index-series-species-of-types.html#1001" class="Bound">X</a> <a id="1003" class="Symbol">:</a> <a id="1005" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1008" href="species.cycle-index-series-species-of-types.html#985" class="Bound">l1</a><a id="1010" class="Symbol">)</a> <a id="1012" class="Symbol">(</a><a id="1013" href="species.cycle-index-series-species-of-types.html#1013" class="Bound">C</a> <a id="1015" class="Symbol">:</a> <a id="1017" href="species.cycle-index-series-species-of-types.html#1001" class="Bound">X</a> <a id="1019" class="Symbol">→</a> <a id="1021" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1023" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1025" class="Symbol">(</a><a id="1026" href="univalent-combinatorics.cyclic-finite-types.html#2438" class="Function">Cyclic-Type</a> <a id="1038" href="species.cycle-index-series-species-of-types.html#988" class="Bound">l2</a><a id="1040" class="Symbol">))</a> <a id="1043" class="Symbol">→</a>
  <a id="1047" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1050" class="Symbol">(</a><a id="1051" href="species.cycle-index-series-species-of-types.html#985" class="Bound">l1</a> <a id="1054" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1056" href="species.cycle-index-series-species-of-types.html#988" class="Bound">l2</a><a id="1058" class="Symbol">)</a>
<a id="1060" href="species.cycle-index-series-species-of-types.html#946" class="Function">total-type-family-of-cyclic-types</a> <a id="1094" href="species.cycle-index-series-species-of-types.html#1094" class="Bound">X</a> <a id="1096" href="species.cycle-index-series-species-of-types.html#1096" class="Bound">C</a> <a id="1098" class="Symbol">=</a>
  <a id="1102" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1104" href="species.cycle-index-series-species-of-types.html#1094" class="Bound">X</a> <a id="1106" class="Symbol">(λ</a> <a id="1109" href="species.cycle-index-series-species-of-types.html#1109" class="Bound">x</a> <a id="1111" class="Symbol">→</a> <a id="1113" href="univalent-combinatorics.cyclic-finite-types.html#2707" class="Function">type-Cyclic-Type</a> <a id="1130" class="Symbol">(</a><a id="1131" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1135" class="Symbol">(</a><a id="1136" href="species.cycle-index-series-species-of-types.html#1096" class="Bound">C</a> <a id="1138" href="species.cycle-index-series-species-of-types.html#1109" class="Bound">x</a><a id="1139" class="Symbol">))</a> <a id="1142" class="Symbol">(</a><a id="1143" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1147" class="Symbol">(</a><a id="1148" href="species.cycle-index-series-species-of-types.html#1096" class="Bound">C</a> <a id="1150" href="species.cycle-index-series-species-of-types.html#1109" class="Bound">x</a><a id="1151" class="Symbol">)))</a>

<a id="1156" class="Comment">{-
permutation-family-of-cyclic-types :
  {l1 l2 : Level} (X : Finite-Type l1) (C : type-Finite-Type X → Σ ℕ (Cyclic-Type l2)) →
  Aut (total-type-family-of-cyclic-types X C)
permutation-family-of-cyclic-types X C = {!!}

cycle-index-series-species-types :
  {l1 l2 : Level} (F : species-types l1 l2) (X : Finite-Type l1) →
  (type-Finite-Type X → Σ ℕ (Cyclic-Type {!!} ∘ succ-ℕ)) →
  UU {!!}
cycle-index-series-species-types F X C =
  Σ {!F (total-type-family-of-cyclic-types X C)!} {!!}
  -}</a>
</pre>