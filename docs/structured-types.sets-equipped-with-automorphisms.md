# Sets equipped with automorphisms

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="structured-types.sets-equipped-with-automorphisms.html" class="Module">structured-types.sets-equipped-with-automorphisms</a> <a id="102" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="195" class="Keyword">open</a> <a id="200" class="Keyword">import</a> <a id="207" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="341" class="Keyword">open</a> <a id="346" class="Keyword">import</a> <a id="353" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A **set equipped with an automorphism** is a pair consisting of a
[set](foundation.sets.md) `A` and an [automorphism](foundation.automorphisms.md)
on `e : A ≃ A`.

## Definitions

### Sets equipped with automorphisms

<pre class="Agda"><a id="Set-With-Automorphism"></a><a id="632" href="structured-types.sets-equipped-with-automorphisms.html#632" class="Function">Set-With-Automorphism</a> <a id="654" class="Symbol">:</a> <a id="656" class="Symbol">(</a><a id="657" href="structured-types.sets-equipped-with-automorphisms.html#657" class="Bound">l</a> <a id="659" class="Symbol">:</a> <a id="661" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="666" class="Symbol">)</a> <a id="668" class="Symbol">→</a> <a id="670" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="673" class="Symbol">(</a><a id="674" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="679" href="structured-types.sets-equipped-with-automorphisms.html#657" class="Bound">l</a><a id="680" class="Symbol">)</a>
<a id="682" href="structured-types.sets-equipped-with-automorphisms.html#632" class="Function">Set-With-Automorphism</a> <a id="704" href="structured-types.sets-equipped-with-automorphisms.html#704" class="Bound">l</a> <a id="706" class="Symbol">=</a> <a id="708" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="710" class="Symbol">(</a><a id="711" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="715" href="structured-types.sets-equipped-with-automorphisms.html#704" class="Bound">l</a><a id="716" class="Symbol">)</a> <a id="718" class="Symbol">(</a><a id="719" href="foundation.automorphisms.html#538" class="Function">Aut</a> <a id="723" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="725" href="foundation-core.sets.html#1025" class="Function">type-Set</a><a id="733" class="Symbol">)</a>

<a id="736" class="Keyword">module</a> <a id="743" href="structured-types.sets-equipped-with-automorphisms.html#743" class="Module">_</a>
  <a id="747" class="Symbol">{</a><a id="748" href="structured-types.sets-equipped-with-automorphisms.html#748" class="Bound">l</a> <a id="750" class="Symbol">:</a> <a id="752" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="757" class="Symbol">}</a> <a id="759" class="Symbol">(</a><a id="760" href="structured-types.sets-equipped-with-automorphisms.html#760" class="Bound">A</a> <a id="762" class="Symbol">:</a> <a id="764" href="structured-types.sets-equipped-with-automorphisms.html#632" class="Function">Set-With-Automorphism</a> <a id="786" href="structured-types.sets-equipped-with-automorphisms.html#748" class="Bound">l</a><a id="787" class="Symbol">)</a>
  <a id="791" class="Keyword">where</a>

  <a id="800" href="structured-types.sets-equipped-with-automorphisms.html#800" class="Function">set-Set-With-Automorphism</a> <a id="826" class="Symbol">:</a> <a id="828" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="832" href="structured-types.sets-equipped-with-automorphisms.html#748" class="Bound">l</a>
  <a id="836" href="structured-types.sets-equipped-with-automorphisms.html#800" class="Function">set-Set-With-Automorphism</a> <a id="862" class="Symbol">=</a> <a id="864" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="868" href="structured-types.sets-equipped-with-automorphisms.html#760" class="Bound">A</a>

  <a id="873" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a> <a id="900" class="Symbol">:</a> <a id="902" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="905" href="structured-types.sets-equipped-with-automorphisms.html#748" class="Bound">l</a>
  <a id="909" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a> <a id="936" class="Symbol">=</a> <a id="938" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="947" href="structured-types.sets-equipped-with-automorphisms.html#800" class="Function">set-Set-With-Automorphism</a>

  <a id="976" href="structured-types.sets-equipped-with-automorphisms.html#976" class="Function">is-set-type-Set-With-Automorphism</a> <a id="1010" class="Symbol">:</a> <a id="1012" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="1019" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a>
  <a id="1048" href="structured-types.sets-equipped-with-automorphisms.html#976" class="Function">is-set-type-Set-With-Automorphism</a> <a id="1082" class="Symbol">=</a> <a id="1084" href="foundation-core.sets.html#1076" class="Function">is-set-type-Set</a> <a id="1100" href="structured-types.sets-equipped-with-automorphisms.html#800" class="Function">set-Set-With-Automorphism</a>

  <a id="1129" href="structured-types.sets-equipped-with-automorphisms.html#1129" class="Function">aut-Set-With-Automorphism</a> <a id="1155" class="Symbol">:</a> <a id="1157" href="foundation.automorphisms.html#538" class="Function">Aut</a> <a id="1161" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a>
  <a id="1190" href="structured-types.sets-equipped-with-automorphisms.html#1129" class="Function">aut-Set-With-Automorphism</a> <a id="1216" class="Symbol">=</a> <a id="1218" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1222" href="structured-types.sets-equipped-with-automorphisms.html#760" class="Bound">A</a>

  <a id="1227" href="structured-types.sets-equipped-with-automorphisms.html#1227" class="Function">map-Set-With-Automorphism</a> <a id="1253" class="Symbol">:</a>
    <a id="1259" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a> <a id="1286" class="Symbol">→</a> <a id="1288" href="structured-types.sets-equipped-with-automorphisms.html#873" class="Function">type-Set-With-Automorphism</a>
  <a id="1317" href="structured-types.sets-equipped-with-automorphisms.html#1227" class="Function">map-Set-With-Automorphism</a> <a id="1343" class="Symbol">=</a> <a id="1345" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="1355" href="structured-types.sets-equipped-with-automorphisms.html#1129" class="Function">aut-Set-With-Automorphism</a>
</pre>