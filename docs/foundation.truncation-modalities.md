# The truncation modalities

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="foundation.truncation-modalities.html" class="Module">foundation.truncation-modalities</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="209" class="Keyword">open</a> <a id="214" class="Keyword">import</a> <a id="221" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>

<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="orthogonal-factorization-systems.modal-operators.html" class="Module">orthogonal-factorization-systems.modal-operators</a>
<a id="360" class="Keyword">open</a> <a id="365" class="Keyword">import</a> <a id="372" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html" class="Module">orthogonal-factorization-systems.uniquely-eliminating-modalities</a>
</pre>
</details>

## Idea

The [truncation](foundation.truncations.md) operations are
[higher modalities](orthogonal-factorization-systems.higher-modalities.md).

## Definition

<pre class="Agda"><a id="operator-trunc-modality"></a><a id="622" href="foundation.truncation-modalities.html#622" class="Function">operator-trunc-modality</a> <a id="646" class="Symbol">:</a>
  <a id="650" class="Symbol">(</a><a id="651" href="foundation.truncation-modalities.html#651" class="Bound">l</a> <a id="653" class="Symbol">:</a> <a id="655" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="660" class="Symbol">)</a> <a id="662" class="Symbol">(</a><a id="663" href="foundation.truncation-modalities.html#663" class="Bound">k</a> <a id="665" class="Symbol">:</a> <a id="667" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="668" class="Symbol">)</a> <a id="670" class="Symbol">→</a> <a id="672" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="690" href="foundation.truncation-modalities.html#651" class="Bound">l</a> <a id="692" href="foundation.truncation-modalities.html#651" class="Bound">l</a>
<a id="694" href="foundation.truncation-modalities.html#622" class="Function">operator-trunc-modality</a> <a id="718" class="Symbol">_</a> <a id="720" class="Symbol">=</a> <a id="722" href="foundation.truncations.html#1297" class="Postulate">type-trunc</a>

<a id="unit-trunc-modality"></a><a id="734" href="foundation.truncation-modalities.html#734" class="Function">unit-trunc-modality</a> <a id="754" class="Symbol">:</a>
  <a id="758" class="Symbol">{</a><a id="759" href="foundation.truncation-modalities.html#759" class="Bound">l</a> <a id="761" class="Symbol">:</a> <a id="763" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="768" class="Symbol">}</a> <a id="770" class="Symbol">{</a><a id="771" href="foundation.truncation-modalities.html#771" class="Bound">k</a> <a id="773" class="Symbol">:</a> <a id="775" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="776" class="Symbol">}</a> <a id="778" class="Symbol">→</a> <a id="780" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="794" class="Symbol">(</a><a id="795" href="foundation.truncation-modalities.html#622" class="Function">operator-trunc-modality</a> <a id="819" href="foundation.truncation-modalities.html#759" class="Bound">l</a> <a id="821" href="foundation.truncation-modalities.html#771" class="Bound">k</a><a id="822" class="Symbol">)</a>
<a id="824" href="foundation.truncation-modalities.html#734" class="Function">unit-trunc-modality</a> <a id="844" class="Symbol">=</a> <a id="846" href="foundation.truncations.html#1585" class="Postulate">unit-trunc</a>
</pre>
## Properties

### The truncation modalities are uniquely eliminating modalities

<pre class="Agda"><a id="is-uniquely-eliminating-modality-trunc-modality"></a><a id="952" href="foundation.truncation-modalities.html#952" class="Function">is-uniquely-eliminating-modality-trunc-modality</a> <a id="1000" class="Symbol">:</a>
  <a id="1004" class="Symbol">{</a><a id="1005" href="foundation.truncation-modalities.html#1005" class="Bound">l</a> <a id="1007" class="Symbol">:</a> <a id="1009" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1014" class="Symbol">}</a> <a id="1016" class="Symbol">{</a><a id="1017" href="foundation.truncation-modalities.html#1017" class="Bound">k</a> <a id="1019" class="Symbol">:</a> <a id="1021" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="1022" class="Symbol">}</a> <a id="1024" class="Symbol">→</a>
  <a id="1028" href="orthogonal-factorization-systems.uniquely-eliminating-modalities.html#1327" class="Function">is-uniquely-eliminating-modality</a> <a id="1061" class="Symbol">(</a><a id="1062" href="foundation.truncation-modalities.html#734" class="Function">unit-trunc-modality</a> <a id="1082" class="Symbol">{</a><a id="1083" href="foundation.truncation-modalities.html#1005" class="Bound">l</a><a id="1084" class="Symbol">}</a> <a id="1086" class="Symbol">{</a><a id="1087" href="foundation.truncation-modalities.html#1017" class="Bound">k</a><a id="1088" class="Symbol">})</a>
<a id="1091" href="foundation.truncation-modalities.html#952" class="Function">is-uniquely-eliminating-modality-trunc-modality</a> <a id="1139" class="Symbol">{</a><a id="1140" class="Argument">k</a> <a id="1142" class="Symbol">=</a> <a id="1144" href="foundation.truncation-modalities.html#1144" class="Bound">k</a><a id="1145" class="Symbol">}</a> <a id="1147" href="foundation.truncation-modalities.html#1147" class="Bound">P</a> <a id="1149" class="Symbol">=</a>
  <a id="1153" href="foundation.truncations.html#3491" class="Function">dependent-universal-property-trunc</a> <a id="1188" class="Symbol">(</a><a id="1189" href="foundation.truncations.html#1445" class="Function">trunc</a> <a id="1195" href="foundation.truncation-modalities.html#1144" class="Bound">k</a> <a id="1197" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1199" href="foundation.truncation-modalities.html#1147" class="Bound">P</a><a id="1200" class="Symbol">)</a>
</pre>