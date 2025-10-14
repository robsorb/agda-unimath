# The identity modality

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="orthogonal-factorization-systems.identity-modality.html" class="Module">orthogonal-factorization-systems.identity-modality</a> <a id="92" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="184" class="Keyword">open</a> <a id="189" class="Keyword">import</a> <a id="196" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="orthogonal-factorization-systems.modal-operators.html" class="Module">orthogonal-factorization-systems.modal-operators</a>
<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="orthogonal-factorization-systems.types-local-at-maps.html" class="Module">orthogonal-factorization-systems.types-local-at-maps</a>
<a id="388" class="Keyword">open</a> <a id="393" class="Keyword">import</a> <a id="400" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html" class="Module">orthogonal-factorization-systems.uniquely-eliminating-modalities</a>
</pre>
</details>

## Idea

The identity operation on types is trivially a
[higher modality](orthogonal-factorization-systems.higher-modalities.md).

## Definition

<pre class="Agda"><a id="operator-id-modality"></a><a id="636" href="orthogonal-factorization-systems.identity-modality.html#636" class="Function">operator-id-modality</a> <a id="657" class="Symbol">:</a>
  <a id="661" class="Symbol">(</a><a id="662" href="orthogonal-factorization-systems.identity-modality.html#662" class="Bound">l</a> <a id="664" class="Symbol">:</a> <a id="666" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="671" class="Symbol">)</a> <a id="673" class="Symbol">→</a> <a id="675" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="693" href="orthogonal-factorization-systems.identity-modality.html#662" class="Bound">l</a> <a id="695" href="orthogonal-factorization-systems.identity-modality.html#662" class="Bound">l</a>
<a id="697" href="orthogonal-factorization-systems.identity-modality.html#636" class="Function">operator-id-modality</a> <a id="718" href="orthogonal-factorization-systems.identity-modality.html#718" class="Bound">l</a> <a id="720" class="Symbol">=</a> <a id="722" href="foundation-core.function-types.html#307" class="Function">id</a>

<a id="unit-id-modality"></a><a id="726" href="orthogonal-factorization-systems.identity-modality.html#726" class="Function">unit-id-modality</a> <a id="743" class="Symbol">:</a>
  <a id="747" class="Symbol">{</a><a id="748" href="orthogonal-factorization-systems.identity-modality.html#748" class="Bound">l</a> <a id="750" class="Symbol">:</a> <a id="752" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="757" class="Symbol">}</a> <a id="759" class="Symbol">→</a> <a id="761" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="775" class="Symbol">(</a><a id="776" href="orthogonal-factorization-systems.identity-modality.html#636" class="Function">operator-id-modality</a> <a id="797" href="orthogonal-factorization-systems.identity-modality.html#748" class="Bound">l</a><a id="798" class="Symbol">)</a>
<a id="800" href="orthogonal-factorization-systems.identity-modality.html#726" class="Function">unit-id-modality</a> <a id="817" class="Symbol">=</a> <a id="819" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>
## Properties

### The identity modality is a uniquely eliminating modality

<pre class="Agda"><a id="is-uniquely-eliminating-modality-id-modality"></a><a id="912" href="orthogonal-factorization-systems.identity-modality.html#912" class="Function">is-uniquely-eliminating-modality-id-modality</a> <a id="957" class="Symbol">:</a>
  <a id="961" class="Symbol">{</a><a id="962" href="orthogonal-factorization-systems.identity-modality.html#962" class="Bound">l</a> <a id="964" class="Symbol">:</a> <a id="966" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="971" class="Symbol">}</a> <a id="973" class="Symbol">→</a> <a id="975" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html#1327" class="Function">is-uniquely-eliminating-modality</a> <a id="1008" class="Symbol">(</a><a id="1009" href="orthogonal-factorization-systems.identity-modality.html#726" class="Function">unit-id-modality</a> <a id="1026" class="Symbol">{</a><a id="1027" href="orthogonal-factorization-systems.identity-modality.html#962" class="Bound">l</a><a id="1028" class="Symbol">})</a>
<a id="1031" href="orthogonal-factorization-systems.identity-modality.html#912" class="Function">is-uniquely-eliminating-modality-id-modality</a> <a id="1076" class="Symbol">{</a><a id="1077" href="orthogonal-factorization-systems.identity-modality.html#1077" class="Bound">l</a><a id="1078" class="Symbol">}</a> <a id="1080" href="orthogonal-factorization-systems.identity-modality.html#1080" class="Bound">P</a> <a id="1082" class="Symbol">=</a>
  <a id="1086" href="orthogonal-factorization-systems.types-local-at-maps.html#12246" class="Function">is-local-dependent-type-is-equiv</a>
    <a id="1123" class="Symbol">(</a> <a id="1125" href="orthogonal-factorization-systems.identity-modality.html#726" class="Function">unit-id-modality</a><a id="1141" class="Symbol">)</a>
    <a id="1147" class="Symbol">(</a> <a id="1149" href="foundation-core.equivalences.html#3753" class="Function">is-equiv-id</a><a id="1160" class="Symbol">)</a>
    <a id="1166" class="Symbol">(</a> <a id="1168" href="orthogonal-factorization-systems.identity-modality.html#636" class="Function">operator-id-modality</a> <a id="1189" href="orthogonal-factorization-systems.identity-modality.html#1077" class="Bound">l</a> <a id="1191" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1193" href="orthogonal-factorization-systems.identity-modality.html#1080" class="Bound">P</a><a id="1194" class="Symbol">)</a>
</pre>