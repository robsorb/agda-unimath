# Alkenes

<pre class="Agda"><a id="20" class="Keyword">module</a> <a id="27" href="organic-chemistry.alkenes.html" class="Module">organic-chemistry.alkenes</a> <a id="53" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="109" class="Keyword">open</a> <a id="114" class="Keyword">import</a> <a id="121" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="organic-chemistry.hydrocarbons.html" class="Module">organic-chemistry.hydrocarbons</a>
<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="organic-chemistry.saturated-carbons.html" class="Module">organic-chemistry.saturated-carbons</a>

<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

An **n-alkene** is a hydrocarbon equipped with a choice of $n$ carbons, each of
which has a double bond. For an n-alkene, the embedding from the given type (the
first component of the n-alkene structure) specifies which carbons have double
bonds. For example, 1-butene and but-2-ene have the same geometry, and the
embedding is what differentiates them (while the third tautometer, isobutylene,
is branched, thus has a different geometry).

## Definition

<pre class="Agda"><a id="n-alkene"></a><a id="912" href="organic-chemistry.alkenes.html#912" class="Function">n-alkene</a> <a id="921" class="Symbol">:</a> <a id="923" class="Symbol">{</a><a id="924" href="organic-chemistry.alkenes.html#924" class="Bound">l1</a> <a id="927" href="organic-chemistry.alkenes.html#927" class="Bound">l2</a> <a id="930" class="Symbol">:</a> <a id="932" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="937" class="Symbol">}</a> <a id="939" class="Symbol">→</a> <a id="941" href="organic-chemistry.hydrocarbons.html#1569" class="Function">hydrocarbon</a> <a id="953" href="organic-chemistry.alkenes.html#924" class="Bound">l1</a> <a id="956" href="organic-chemistry.alkenes.html#927" class="Bound">l2</a> <a id="959" class="Symbol">→</a> <a id="961" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="963" class="Symbol">→</a> <a id="965" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="968" class="Symbol">(</a><a id="969" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="974" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="980" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="982" href="organic-chemistry.alkenes.html#924" class="Bound">l1</a> <a id="985" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="987" href="organic-chemistry.alkenes.html#927" class="Bound">l2</a><a id="989" class="Symbol">)</a>
<a id="991" href="organic-chemistry.alkenes.html#912" class="Function">n-alkene</a> <a id="1000" href="organic-chemistry.alkenes.html#1000" class="Bound">H</a> <a id="1002" href="organic-chemistry.alkenes.html#1002" class="Bound">n</a> <a id="1004" class="Symbol">=</a>
  <a id="1008" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1010" class="Symbol">(</a><a id="1011" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="1035" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1041" href="organic-chemistry.alkenes.html#1002" class="Bound">n</a><a id="1042" class="Symbol">)</a> <a id="1044" class="Symbol">λ</a> <a id="1046" href="organic-chemistry.alkenes.html#1046" class="Bound">carbons</a> <a id="1054" class="Symbol">→</a>
    <a id="1060" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1062" class="Symbol">(</a> <a id="1064" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1093" href="organic-chemistry.alkenes.html#1002" class="Bound">n</a> <a id="1095" href="organic-chemistry.alkenes.html#1046" class="Bound">carbons</a> <a id="1103" href="foundation-core.embeddings.html#1627" class="Function Operator">↪</a> <a id="1105" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="1124" href="organic-chemistry.alkenes.html#1000" class="Bound">H</a><a id="1125" class="Symbol">)</a>
      <a id="1133" class="Symbol">(</a> <a id="1135" class="Symbol">λ</a> <a id="1137" href="organic-chemistry.alkenes.html#1137" class="Bound">embed-carbons</a> <a id="1151" class="Symbol">→</a>
        <a id="1161" class="Symbol">(</a> <a id="1163" href="organic-chemistry.alkenes.html#1163" class="Bound">c</a> <a id="1165" class="Symbol">:</a> <a id="1167" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="1196" href="organic-chemistry.alkenes.html#1002" class="Bound">n</a> <a id="1198" href="organic-chemistry.alkenes.html#1046" class="Bound">carbons</a><a id="1205" class="Symbol">)</a> <a id="1207" class="Symbol">→</a>
        <a id="1217" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1221" class="Symbol">(</a><a id="1222" href="organic-chemistry.saturated-carbons.html#1737" class="Function">has-double-bond-hydrocarbon</a> <a id="1250" href="organic-chemistry.alkenes.html#1000" class="Bound">H</a> <a id="1252" class="Symbol">(</a><a id="1253" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1257" href="organic-chemistry.alkenes.html#1137" class="Bound">embed-carbons</a> <a id="1271" href="organic-chemistry.alkenes.html#1163" class="Bound">c</a><a id="1272" class="Symbol">)))</a>
</pre>