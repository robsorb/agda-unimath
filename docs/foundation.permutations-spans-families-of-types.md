# Permutations of spans of families of types

<pre class="Agda"><a id="55" class="Keyword">module</a> <a id="62" href="foundation.permutations-spans-families-of-types.html" class="Module">foundation.permutations-spans-families-of-types</a> <a id="110" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="foundation.spans-families-of-types.html" class="Module">foundation.spans-families-of-types</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

Permutations of spans of families of types are a generalization of the
[opposite](foundation.opposite-spans.md) of a
[binary span](foundation.spans.md). Consider a
[span](foundation.spans-families-of-types.md) `(S , f)` on a type family
`A : I → 𝒰` and an [equivalence](foundation-core.equivalences.md) `e : I ≃ I`.
Then the {{#concept "permutation" Disambiguation="spans of families of types"}}
is the span `(S , f ∘ e)` on the type family `A ∘ e`.

## Definitions

### Permutations of spans of families of types

<pre class="Agda"><a id="930" class="Keyword">module</a> <a id="937" href="foundation.permutations-spans-families-of-types.html#937" class="Module">_</a>
  <a id="941" class="Symbol">{</a><a id="942" href="foundation.permutations-spans-families-of-types.html#942" class="Bound">l1</a> <a id="945" href="foundation.permutations-spans-families-of-types.html#945" class="Bound">l2</a> <a id="948" href="foundation.permutations-spans-families-of-types.html#948" class="Bound">l3</a> <a id="951" class="Symbol">:</a> <a id="953" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="958" class="Symbol">}</a> <a id="960" class="Symbol">{</a><a id="961" href="foundation.permutations-spans-families-of-types.html#961" class="Bound">I</a> <a id="963" class="Symbol">:</a> <a id="965" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="968" href="foundation.permutations-spans-families-of-types.html#942" class="Bound">l1</a><a id="970" class="Symbol">}</a> <a id="972" class="Symbol">{</a><a id="973" href="foundation.permutations-spans-families-of-types.html#973" class="Bound">A</a> <a id="975" class="Symbol">:</a> <a id="977" href="foundation.permutations-spans-families-of-types.html#961" class="Bound">I</a> <a id="979" class="Symbol">→</a> <a id="981" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="984" href="foundation.permutations-spans-families-of-types.html#945" class="Bound">l2</a><a id="986" class="Symbol">}</a>
  <a id="990" class="Keyword">where</a>

  <a id="999" href="foundation.permutations-spans-families-of-types.html#999" class="Function">permutation-span-type-family</a> <a id="1028" class="Symbol">:</a>
    <a id="1034" class="Symbol">(</a><a id="1035" href="foundation.permutations-spans-families-of-types.html#1035" class="Bound">e</a> <a id="1037" class="Symbol">:</a> <a id="1039" href="foundation.permutations-spans-families-of-types.html#961" class="Bound">I</a> <a id="1041" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1043" href="foundation.permutations-spans-families-of-types.html#961" class="Bound">I</a><a id="1044" class="Symbol">)</a> <a id="1046" class="Symbol">→</a> <a id="1048" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="1065" href="foundation.permutations-spans-families-of-types.html#948" class="Bound">l3</a> <a id="1068" href="foundation.permutations-spans-families-of-types.html#973" class="Bound">A</a> <a id="1070" class="Symbol">→</a>
    <a id="1076" href="foundation.spans-families-of-types.html#839" class="Function">span-type-family</a> <a id="1093" href="foundation.permutations-spans-families-of-types.html#948" class="Bound">l3</a> <a id="1096" class="Symbol">(</a><a id="1097" href="foundation.permutations-spans-families-of-types.html#973" class="Bound">A</a> <a id="1099" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1101" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="1111" href="foundation.permutations-spans-families-of-types.html#1035" class="Bound">e</a><a id="1112" class="Symbol">)</a>
  <a id="1116" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1120" class="Symbol">(</a><a id="1121" href="foundation.permutations-spans-families-of-types.html#999" class="Function">permutation-span-type-family</a> <a id="1150" href="foundation.permutations-spans-families-of-types.html#1150" class="Bound">e</a> <a id="1152" href="foundation.permutations-spans-families-of-types.html#1152" class="Bound">s</a><a id="1153" class="Symbol">)</a> <a id="1155" class="Symbol">=</a>
    <a id="1161" href="foundation.spans-families-of-types.html#1038" class="Function">spanning-type-span-type-family</a> <a id="1192" href="foundation.permutations-spans-families-of-types.html#1152" class="Bound">s</a>
  <a id="1196" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1200" class="Symbol">(</a><a id="1201" href="foundation.permutations-spans-families-of-types.html#999" class="Function">permutation-span-type-family</a> <a id="1230" href="foundation.permutations-spans-families-of-types.html#1230" class="Bound">e</a> <a id="1232" href="foundation.permutations-spans-families-of-types.html#1232" class="Bound">s</a><a id="1233" class="Symbol">)</a> <a id="1235" href="foundation.permutations-spans-families-of-types.html#1235" class="Bound">i</a> <a id="1237" class="Symbol">=</a>
    <a id="1243" href="foundation.spans-families-of-types.html#1121" class="Function">map-span-type-family</a> <a id="1264" href="foundation.permutations-spans-families-of-types.html#1232" class="Bound">s</a> <a id="1266" class="Symbol">(</a><a id="1267" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="1277" href="foundation.permutations-spans-families-of-types.html#1230" class="Bound">e</a> <a id="1279" href="foundation.permutations-spans-families-of-types.html#1235" class="Bound">i</a><a id="1280" class="Symbol">)</a>
</pre>