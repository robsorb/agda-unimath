# The zero modality

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="orthogonal-factorization-systems.zero-modality.html" class="Module">orthogonal-factorization-systems.zero-modality</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="213" class="Keyword">open</a> <a id="218" class="Keyword">import</a> <a id="225" href="orthogonal-factorization-systems.modal-operators.html" class="Module">orthogonal-factorization-systems.modal-operators</a>
<a id="274" class="Keyword">open</a> <a id="279" class="Keyword">import</a> <a id="286" href="orthogonal-factorization-systems.types-local-at-maps.html" class="Module">orthogonal-factorization-systems.types-local-at-maps</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html" class="Module">orthogonal-factorization-systems.uniquely-eliminating-modalities</a>
</pre>
</details>

## Idea

The **zero modality** is the
[modality](orthogonal-factorization-systems.higher-modalities.md) that maps
every type to the [unit type](foundation.unit-type.md).

## Definition

<pre class="Agda"><a id="operator-zero-modality"></a><a id="627" href="orthogonal-factorization-systems.zero-modality.html#627" class="Function">operator-zero-modality</a> <a id="650" class="Symbol">:</a>
  <a id="654" class="Symbol">(</a><a id="655" href="orthogonal-factorization-systems.zero-modality.html#655" class="Bound">l1</a> <a id="658" href="orthogonal-factorization-systems.zero-modality.html#658" class="Bound">l2</a> <a id="661" class="Symbol">:</a> <a id="663" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="668" class="Symbol">)</a> <a id="670" class="Symbol">→</a> <a id="672" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="690" href="orthogonal-factorization-systems.zero-modality.html#655" class="Bound">l1</a> <a id="693" href="orthogonal-factorization-systems.zero-modality.html#658" class="Bound">l2</a>
<a id="696" href="orthogonal-factorization-systems.zero-modality.html#627" class="Function">operator-zero-modality</a> <a id="719" href="orthogonal-factorization-systems.zero-modality.html#719" class="Bound">l1</a> <a id="722" href="orthogonal-factorization-systems.zero-modality.html#722" class="Bound">l2</a> <a id="725" class="Symbol">_</a> <a id="727" class="Symbol">=</a> <a id="729" href="foundation.unit-type.html#1545" class="Function">raise-unit</a> <a id="740" href="orthogonal-factorization-systems.zero-modality.html#722" class="Bound">l2</a>

<a id="unit-zero-modality"></a><a id="744" href="orthogonal-factorization-systems.zero-modality.html#744" class="Function">unit-zero-modality</a> <a id="763" class="Symbol">:</a>
  <a id="767" class="Symbol">{</a><a id="768" href="orthogonal-factorization-systems.zero-modality.html#768" class="Bound">l1</a> <a id="771" href="orthogonal-factorization-systems.zero-modality.html#771" class="Bound">l2</a> <a id="774" class="Symbol">:</a> <a id="776" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="781" class="Symbol">}</a> <a id="783" class="Symbol">→</a> <a id="785" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="799" class="Symbol">(</a><a id="800" href="orthogonal-factorization-systems.zero-modality.html#627" class="Function">operator-zero-modality</a> <a id="823" href="orthogonal-factorization-systems.zero-modality.html#768" class="Bound">l1</a> <a id="826" href="orthogonal-factorization-systems.zero-modality.html#771" class="Bound">l2</a><a id="828" class="Symbol">)</a>
<a id="830" href="orthogonal-factorization-systems.zero-modality.html#744" class="Function">unit-zero-modality</a> <a id="849" class="Symbol">_</a> <a id="851" class="Symbol">=</a> <a id="853" href="foundation.unit-type.html#1606" class="Function">raise-star</a>
</pre>
## Properties

### The zero modality is a uniquely eliminating modality

<pre class="Agda"><a id="is-uniquely-eliminating-modality-zero-modality"></a><a id="950" href="orthogonal-factorization-systems.zero-modality.html#950" class="Function">is-uniquely-eliminating-modality-zero-modality</a> <a id="997" class="Symbol">:</a>
  <a id="1001" class="Symbol">{</a><a id="1002" href="orthogonal-factorization-systems.zero-modality.html#1002" class="Bound">l1</a> <a id="1005" href="orthogonal-factorization-systems.zero-modality.html#1005" class="Bound">l2</a> <a id="1008" class="Symbol">:</a> <a id="1010" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1015" class="Symbol">}</a> <a id="1017" class="Symbol">→</a>
  <a id="1021" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html#1327" class="Function">is-uniquely-eliminating-modality</a> <a id="1054" class="Symbol">(</a><a id="1055" href="orthogonal-factorization-systems.zero-modality.html#744" class="Function">unit-zero-modality</a> <a id="1074" class="Symbol">{</a><a id="1075" href="orthogonal-factorization-systems.zero-modality.html#1002" class="Bound">l1</a><a id="1077" class="Symbol">}</a> <a id="1079" class="Symbol">{</a><a id="1080" href="orthogonal-factorization-systems.zero-modality.html#1005" class="Bound">l2</a><a id="1082" class="Symbol">})</a>
<a id="1085" href="orthogonal-factorization-systems.zero-modality.html#950" class="Function">is-uniquely-eliminating-modality-zero-modality</a> <a id="1132" class="Symbol">{</a><a id="1133" class="Argument">l2</a> <a id="1136" class="Symbol">=</a> <a id="1138" href="orthogonal-factorization-systems.zero-modality.html#1138" class="Bound">l2</a><a id="1140" class="Symbol">}</a> <a id="1142" href="orthogonal-factorization-systems.zero-modality.html#1142" class="Bound">P</a> <a id="1144" class="Symbol">=</a>
  <a id="1148" href="orthogonal-factorization-systems.types-local-at-maps.html#13023" class="Function">is-local-is-contr</a>
    <a id="1170" class="Symbol">(</a> <a id="1172" href="orthogonal-factorization-systems.zero-modality.html#744" class="Function">unit-zero-modality</a><a id="1190" class="Symbol">)</a>
    <a id="1196" class="Symbol">(</a> <a id="1198" href="foundation.unit-type.html#1545" class="Function">raise-unit</a> <a id="1209" href="orthogonal-factorization-systems.zero-modality.html#1138" class="Bound">l2</a><a id="1211" class="Symbol">)</a>
    <a id="1217" class="Symbol">(</a> <a id="1219" href="foundation.unit-type.html#2180" class="Function">is-contr-raise-unit</a><a id="1238" class="Symbol">)</a>
</pre>
### The zero modality is equivalent to `-2`-truncation

This remains to be made formal.
[#739](https://github.com/UniMath/agda-unimath/issues/739)
