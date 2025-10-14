# The raise modalities

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="orthogonal-factorization-systems.raise-modalities.html" class="Module">orthogonal-factorization-systems.raise-modalities</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="184" class="Keyword">open</a> <a id="189" class="Keyword">import</a> <a id="196" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="orthogonal-factorization-systems.modal-operators.html" class="Module">orthogonal-factorization-systems.modal-operators</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="orthogonal-factorization-systems.types-local-at-maps.html" class="Module">orthogonal-factorization-systems.types-local-at-maps</a>
<a id="397" class="Keyword">open</a> <a id="402" class="Keyword">import</a> <a id="409" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html" class="Module">orthogonal-factorization-systems.uniquely-eliminating-modalities</a>
</pre>
</details>

## Idea

The operations of
[raising universe levels](foundation.raising-universe-levels.md) are trivially
[higher modalities](orthogonal-factorization-systems.higher-modalities.md), and
in the case that `l1 ⊔ l2 = l1`, we recover the
[identity modality](orthogonal-factorization-systems.identity-modality.md).

## Definition

<pre class="Agda"><a id="operator-raise-modality"></a><a id="825" href="orthogonal-factorization-systems.raise-modalities.html#825" class="Function">operator-raise-modality</a> <a id="849" class="Symbol">:</a>
  <a id="853" class="Symbol">(</a><a id="854" href="orthogonal-factorization-systems.raise-modalities.html#854" class="Bound">l1</a> <a id="857" href="orthogonal-factorization-systems.raise-modalities.html#857" class="Bound">l2</a> <a id="860" class="Symbol">:</a> <a id="862" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="867" class="Symbol">)</a> <a id="869" class="Symbol">→</a> <a id="871" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="889" href="orthogonal-factorization-systems.raise-modalities.html#854" class="Bound">l1</a> <a id="892" class="Symbol">(</a><a id="893" href="orthogonal-factorization-systems.raise-modalities.html#854" class="Bound">l1</a> <a id="896" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="898" href="orthogonal-factorization-systems.raise-modalities.html#857" class="Bound">l2</a><a id="900" class="Symbol">)</a>
<a id="902" href="orthogonal-factorization-systems.raise-modalities.html#825" class="Function">operator-raise-modality</a> <a id="926" href="orthogonal-factorization-systems.raise-modalities.html#926" class="Bound">l1</a> <a id="929" href="orthogonal-factorization-systems.raise-modalities.html#929" class="Bound">l2</a> <a id="932" class="Symbol">=</a> <a id="934" href="foundation.raising-universe-levels.html#1034" class="Datatype">raise</a> <a id="940" href="orthogonal-factorization-systems.raise-modalities.html#929" class="Bound">l2</a>

<a id="unit-raise-modality"></a><a id="944" href="orthogonal-factorization-systems.raise-modalities.html#944" class="Function">unit-raise-modality</a> <a id="964" class="Symbol">:</a>
  <a id="968" class="Symbol">{</a><a id="969" href="orthogonal-factorization-systems.raise-modalities.html#969" class="Bound">l1</a> <a id="972" href="orthogonal-factorization-systems.raise-modalities.html#972" class="Bound">l2</a> <a id="975" class="Symbol">:</a> <a id="977" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="982" class="Symbol">}</a> <a id="984" class="Symbol">→</a> <a id="986" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="1000" class="Symbol">(</a><a id="1001" href="orthogonal-factorization-systems.raise-modalities.html#825" class="Function">operator-raise-modality</a> <a id="1025" href="orthogonal-factorization-systems.raise-modalities.html#969" class="Bound">l1</a> <a id="1028" href="orthogonal-factorization-systems.raise-modalities.html#972" class="Bound">l2</a><a id="1030" class="Symbol">)</a>
<a id="1032" href="orthogonal-factorization-systems.raise-modalities.html#944" class="Function">unit-raise-modality</a> <a id="1052" class="Symbol">=</a> <a id="1054" href="foundation.raising-universe-levels.html#1099" class="InductiveConstructor">map-raise</a>
</pre>
## Properties

### The raise modality is a uniquely eliminating modality

<pre class="Agda"><a id="is-uniquely-eliminating-modality-raise-modality"></a><a id="1151" href="orthogonal-factorization-systems.raise-modalities.html#1151" class="Function">is-uniquely-eliminating-modality-raise-modality</a> <a id="1199" class="Symbol">:</a>
  <a id="1203" class="Symbol">{</a><a id="1204" href="orthogonal-factorization-systems.raise-modalities.html#1204" class="Bound">l1</a> <a id="1207" href="orthogonal-factorization-systems.raise-modalities.html#1207" class="Bound">l2</a> <a id="1210" class="Symbol">:</a> <a id="1212" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1217" class="Symbol">}</a> <a id="1219" class="Symbol">→</a>
  <a id="1223" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html#1327" class="Function">is-uniquely-eliminating-modality</a> <a id="1256" class="Symbol">(</a><a id="1257" href="orthogonal-factorization-systems.raise-modalities.html#944" class="Function">unit-raise-modality</a> <a id="1277" class="Symbol">{</a><a id="1278" href="orthogonal-factorization-systems.raise-modalities.html#1204" class="Bound">l1</a><a id="1280" class="Symbol">}</a> <a id="1282" class="Symbol">{</a><a id="1283" href="orthogonal-factorization-systems.raise-modalities.html#1207" class="Bound">l2</a><a id="1285" class="Symbol">})</a>
<a id="1288" href="orthogonal-factorization-systems.raise-modalities.html#1151" class="Function">is-uniquely-eliminating-modality-raise-modality</a> <a id="1336" class="Symbol">{</a><a id="1337" href="orthogonal-factorization-systems.raise-modalities.html#1337" class="Bound">l1</a><a id="1339" class="Symbol">}</a> <a id="1341" class="Symbol">{</a><a id="1342" href="orthogonal-factorization-systems.raise-modalities.html#1342" class="Bound">l2</a><a id="1344" class="Symbol">}</a> <a id="1346" href="orthogonal-factorization-systems.raise-modalities.html#1346" class="Bound">P</a> <a id="1348" class="Symbol">=</a>
  <a id="1352" href="orthogonal-factorization-systems.types-local-at-maps.html#12246" class="Function">is-local-dependent-type-is-equiv</a>
    <a id="1389" class="Symbol">(</a> <a id="1391" href="orthogonal-factorization-systems.raise-modalities.html#944" class="Function">unit-raise-modality</a><a id="1410" class="Symbol">)</a>
    <a id="1416" class="Symbol">(</a> <a id="1418" href="foundation.raising-universe-levels.html#1617" class="Function">is-equiv-map-raise</a><a id="1436" class="Symbol">)</a>
    <a id="1442" class="Symbol">(</a> <a id="1444" href="orthogonal-factorization-systems.raise-modalities.html#825" class="Function">operator-raise-modality</a> <a id="1468" href="orthogonal-factorization-systems.raise-modalities.html#1337" class="Bound">l1</a> <a id="1471" href="orthogonal-factorization-systems.raise-modalities.html#1342" class="Bound">l2</a> <a id="1474" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1476" href="orthogonal-factorization-systems.raise-modalities.html#1346" class="Bound">P</a><a id="1477" class="Symbol">)</a>
</pre>
### In the case that `l1 ⊔ l2 = l1` we recover the identity modality

This remains to be made formal.
[#739](https://github.com/UniMath/agda-unimath/issues/739)
