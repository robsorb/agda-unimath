# Σ-closed reflective modalities

<pre class="Agda"><a id="43" class="Keyword">module</a> <a id="50" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html" class="Module">orthogonal-factorization-systems.sigma-closed-reflective-modalities</a> <a id="118" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="orthogonal-factorization-systems.modal-operators.html" class="Module">orthogonal-factorization-systems.modal-operators</a>
<a id="366" class="Keyword">open</a> <a id="371" class="Keyword">import</a> <a id="378" href="orthogonal-factorization-systems.reflective-modalities.html" class="Module">orthogonal-factorization-systems.reflective-modalities</a>
<a id="433" class="Keyword">open</a> <a id="438" class="Keyword">import</a> <a id="445" href="orthogonal-factorization-systems.sigma-closed-modalities.html" class="Module">orthogonal-factorization-systems.sigma-closed-modalities</a>
</pre>
</details>

## Idea

A [modality](orthogonal-factorization-systems.modal-operators.md) is **Σ-closed
reflective** if it is
[reflective](orthogonal-factorization-systems.reflective-modalities.md) and
[Σ-closed](orthogonal-factorization-systems.sigma-closed-modalities.md).

## Definition

<pre class="Agda"><a id="is-closed-under-Σ-reflective-modality"></a><a id="803" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#803" class="Function">is-closed-under-Σ-reflective-modality</a> <a id="841" class="Symbol">:</a>
  <a id="845" class="Symbol">{</a><a id="846" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#846" class="Bound">l</a> <a id="848" class="Symbol">:</a> <a id="850" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="855" class="Symbol">}</a> <a id="857" class="Symbol">{</a><a id="858" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#858" class="Bound">○</a> <a id="860" class="Symbol">:</a> <a id="862" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="880" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#846" class="Bound">l</a> <a id="882" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#846" class="Bound">l</a><a id="883" class="Symbol">}</a> <a id="885" class="Symbol">→</a>
  <a id="889" class="Symbol">(</a><a id="890" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#890" class="Bound">unit-○</a> <a id="897" class="Symbol">:</a> <a id="899" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="913" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#858" class="Bound">○</a><a id="914" class="Symbol">)</a> <a id="916" class="Symbol">→</a> <a id="918" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="921" class="Symbol">(</a><a id="922" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="927" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#846" class="Bound">l</a><a id="928" class="Symbol">)</a>
<a id="930" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#803" class="Function">is-closed-under-Σ-reflective-modality</a> <a id="968" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#968" class="Bound">unit-○</a> <a id="975" class="Symbol">=</a>
  <a id="979" class="Symbol">(</a><a id="980" href="orthogonal-factorization-systems.reflective-modalities.html#688" class="Function">is-reflective-modality</a> <a id="1003" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#968" class="Bound">unit-○</a><a id="1009" class="Symbol">)</a> <a id="1011" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1013" class="Symbol">(</a><a id="1014" href="orthogonal-factorization-systems.sigma-closed-modalities.html#739" class="Function">is-closed-under-Σ-modality</a> <a id="1041" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#968" class="Bound">unit-○</a><a id="1047" class="Symbol">)</a>

<a id="closed-under-Σ-reflective-modality"></a><a id="1050" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1050" class="Function">closed-under-Σ-reflective-modality</a> <a id="1085" class="Symbol">:</a> <a id="1087" class="Symbol">(</a><a id="1088" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1088" class="Bound">l</a> <a id="1090" class="Symbol">:</a> <a id="1092" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1097" class="Symbol">)</a> <a id="1099" class="Symbol">→</a> <a id="1101" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1104" class="Symbol">(</a><a id="1105" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1110" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1088" class="Bound">l</a><a id="1111" class="Symbol">)</a>
<a id="1113" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1050" class="Function">closed-under-Σ-reflective-modality</a> <a id="1148" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1148" class="Bound">l</a> <a id="1150" class="Symbol">=</a>
  <a id="1154" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1156" class="Symbol">(</a> <a id="1158" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="1176" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1148" class="Bound">l</a> <a id="1178" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1148" class="Bound">l</a><a id="1179" class="Symbol">)</a>
    <a id="1185" class="Symbol">(</a> <a id="1187" class="Symbol">λ</a> <a id="1189" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1189" class="Bound">○</a> <a id="1191" class="Symbol">→</a>
      <a id="1199" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1201" class="Symbol">(</a> <a id="1203" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="1217" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#1189" class="Bound">○</a><a id="1218" class="Symbol">)</a>
        <a id="1228" class="Symbol">(</a> <a id="1230" href="orthogonal-factorization-systems.sigma-closed-reflective-modalities.html#803" class="Function">is-closed-under-Σ-reflective-modality</a><a id="1267" class="Symbol">))</a>
</pre>
## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Stable orthogonal factorization systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.md)
