# Reflective modalities

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="orthogonal-factorization-systems.reflective-modalities.html" class="Module">orthogonal-factorization-systems.reflective-modalities</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="orthogonal-factorization-systems.modal-operators.html" class="Module">orthogonal-factorization-systems.modal-operators</a>
<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="orthogonal-factorization-systems.reflective-subuniverses.html" class="Module">orthogonal-factorization-systems.reflective-subuniverses</a>
</pre>
</details>

## Idea

A [modal operator](orthogonal-factorization-systems.modal-operators.md) with
unit is **reflective** if its [subuniverse](foundation.subuniverses.md) of modal
types is
[reflective](orthogonal-factorization-systems.reflective-subuniverses.md).

## Definitions

### Reflective subuniverses

<pre class="Agda"><a id="is-reflective-modality"></a><a id="688" href="orthogonal-factorization-systems.reflective-modalities.html#688" class="Function">is-reflective-modality</a> <a id="711" class="Symbol">:</a>
  <a id="715" class="Symbol">{</a><a id="716" href="orthogonal-factorization-systems.reflective-modalities.html#716" class="Bound">l</a> <a id="718" class="Symbol">:</a> <a id="720" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="725" class="Symbol">}</a> <a id="727" class="Symbol">{</a><a id="728" href="orthogonal-factorization-systems.reflective-modalities.html#728" class="Bound">○</a> <a id="730" class="Symbol">:</a> <a id="732" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="750" href="orthogonal-factorization-systems.reflective-modalities.html#716" class="Bound">l</a> <a id="752" href="orthogonal-factorization-systems.reflective-modalities.html#716" class="Bound">l</a><a id="753" class="Symbol">}</a> <a id="755" class="Symbol">→</a> <a id="757" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="771" href="orthogonal-factorization-systems.reflective-modalities.html#728" class="Bound">○</a> <a id="773" class="Symbol">→</a> <a id="775" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="778" class="Symbol">(</a><a id="779" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="784" href="orthogonal-factorization-systems.reflective-modalities.html#716" class="Bound">l</a><a id="785" class="Symbol">)</a>
<a id="787" href="orthogonal-factorization-systems.reflective-modalities.html#688" class="Function">is-reflective-modality</a> <a id="810" href="orthogonal-factorization-systems.reflective-modalities.html#810" class="Bound">unit-○</a> <a id="817" class="Symbol">=</a>
  <a id="821" href="orthogonal-factorization-systems.reflective-subuniverses.html#1709" class="Function">is-reflective-subuniverse</a> <a id="847" class="Symbol">(</a><a id="848" href="orthogonal-factorization-systems.modal-operators.html#1719" class="Function">modal-type-subuniverse</a> <a id="871" href="orthogonal-factorization-systems.reflective-modalities.html#810" class="Bound">unit-○</a><a id="877" class="Symbol">)</a>

<a id="reflective-modality"></a><a id="880" href="orthogonal-factorization-systems.reflective-modalities.html#880" class="Function">reflective-modality</a> <a id="900" class="Symbol">:</a> <a id="902" class="Symbol">(</a><a id="903" href="orthogonal-factorization-systems.reflective-modalities.html#903" class="Bound">l</a> <a id="905" class="Symbol">:</a> <a id="907" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="912" class="Symbol">)</a> <a id="914" class="Symbol">→</a> <a id="916" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="919" class="Symbol">(</a><a id="920" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="925" href="orthogonal-factorization-systems.reflective-modalities.html#903" class="Bound">l</a><a id="926" class="Symbol">)</a>
<a id="928" href="orthogonal-factorization-systems.reflective-modalities.html#880" class="Function">reflective-modality</a> <a id="948" href="orthogonal-factorization-systems.reflective-modalities.html#948" class="Bound">l</a> <a id="950" class="Symbol">=</a>
  <a id="954" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="956" class="Symbol">(</a><a id="957" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="975" href="orthogonal-factorization-systems.reflective-modalities.html#948" class="Bound">l</a> <a id="977" href="orthogonal-factorization-systems.reflective-modalities.html#948" class="Bound">l</a><a id="978" class="Symbol">)</a> <a id="980" class="Symbol">(λ</a> <a id="983" href="orthogonal-factorization-systems.reflective-modalities.html#983" class="Bound">○</a> <a id="985" class="Symbol">→</a> <a id="987" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="989" class="Symbol">(</a><a id="990" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="1004" href="orthogonal-factorization-systems.reflective-modalities.html#983" class="Bound">○</a><a id="1005" class="Symbol">)</a> <a id="1007" class="Symbol">(</a><a id="1008" href="orthogonal-factorization-systems.reflective-modalities.html#688" class="Function">is-reflective-modality</a><a id="1030" class="Symbol">))</a>
</pre>
## See also

- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-at-subuniverses.md)
