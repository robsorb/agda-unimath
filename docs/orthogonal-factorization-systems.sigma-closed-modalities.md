# Σ-closed modalities

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="orthogonal-factorization-systems.sigma-closed-modalities.html" class="Module">orthogonal-factorization-systems.sigma-closed-modalities</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="234" class="Keyword">open</a> <a id="239" class="Keyword">import</a> <a id="246" href="foundation.sigma-closed-subuniverses.html" class="Module">foundation.sigma-closed-subuniverses</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="orthogonal-factorization-systems.modal-operators.html" class="Module">orthogonal-factorization-systems.modal-operators</a>
</pre>
</details>

## Idea

A [modal operator](orthogonal-factorization-systems.modal-operators.md) with
unit is **Σ-closed** if its [subuniverse](foundation.subuniverses.md) of modal
types is [Σ-closed](foundation.sigma-closed-subuniverses.md). I.e., if `Σ A B`
is modal whenever `B` is a family of modal types over modal base `A`.

## Definition

<pre class="Agda"><a id="is-closed-under-Σ-modality"></a><a id="739" href="orthogonal-factorization-systems.sigma-closed-modalities.html#739" class="Function">is-closed-under-Σ-modality</a> <a id="766" class="Symbol">:</a>
  <a id="770" class="Symbol">{</a><a id="771" href="orthogonal-factorization-systems.sigma-closed-modalities.html#771" class="Bound">l</a> <a id="773" class="Symbol">:</a> <a id="775" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="780" class="Symbol">}</a> <a id="782" class="Symbol">{</a><a id="783" href="orthogonal-factorization-systems.sigma-closed-modalities.html#783" class="Bound">○</a> <a id="785" class="Symbol">:</a> <a id="787" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="805" href="orthogonal-factorization-systems.sigma-closed-modalities.html#771" class="Bound">l</a> <a id="807" href="orthogonal-factorization-systems.sigma-closed-modalities.html#771" class="Bound">l</a><a id="808" class="Symbol">}</a> <a id="810" class="Symbol">→</a> <a id="812" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="826" href="orthogonal-factorization-systems.sigma-closed-modalities.html#783" class="Bound">○</a> <a id="828" class="Symbol">→</a> <a id="830" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="833" class="Symbol">(</a><a id="834" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="839" href="orthogonal-factorization-systems.sigma-closed-modalities.html#771" class="Bound">l</a><a id="840" class="Symbol">)</a>
<a id="842" href="orthogonal-factorization-systems.sigma-closed-modalities.html#739" class="Function">is-closed-under-Σ-modality</a> <a id="869" class="Symbol">=</a>
  <a id="873" href="foundation.sigma-closed-subuniverses.html#1111" class="Function">is-closed-under-Σ-subuniverse</a> <a id="903" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="905" href="orthogonal-factorization-systems.modal-operators.html#1719" class="Function">modal-type-subuniverse</a>

<a id="closed-under-Σ-modality"></a><a id="929" href="orthogonal-factorization-systems.sigma-closed-modalities.html#929" class="Function">closed-under-Σ-modality</a> <a id="953" class="Symbol">:</a> <a id="955" class="Symbol">(</a><a id="956" href="orthogonal-factorization-systems.sigma-closed-modalities.html#956" class="Bound">l</a> <a id="958" class="Symbol">:</a> <a id="960" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="965" class="Symbol">)</a> <a id="967" class="Symbol">→</a> <a id="969" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="972" class="Symbol">(</a><a id="973" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="978" href="orthogonal-factorization-systems.sigma-closed-modalities.html#956" class="Bound">l</a><a id="979" class="Symbol">)</a>
<a id="981" href="orthogonal-factorization-systems.sigma-closed-modalities.html#929" class="Function">closed-under-Σ-modality</a> <a id="1005" href="orthogonal-factorization-systems.sigma-closed-modalities.html#1005" class="Bound">l</a> <a id="1007" class="Symbol">=</a>
  <a id="1011" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1013" class="Symbol">(</a> <a id="1015" href="orthogonal-factorization-systems.modal-operators.html#715" class="Function">operator-modality</a> <a id="1033" href="orthogonal-factorization-systems.sigma-closed-modalities.html#1005" class="Bound">l</a> <a id="1035" href="orthogonal-factorization-systems.sigma-closed-modalities.html#1005" class="Bound">l</a><a id="1036" class="Symbol">)</a>
    <a id="1042" class="Symbol">(</a> <a id="1044" class="Symbol">λ</a> <a id="1046" href="orthogonal-factorization-systems.sigma-closed-modalities.html#1046" class="Bound">○</a> <a id="1048" class="Symbol">→</a> <a id="1050" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1052" class="Symbol">(</a><a id="1053" href="orthogonal-factorization-systems.modal-operators.html#846" class="Function">unit-modality</a> <a id="1067" href="orthogonal-factorization-systems.sigma-closed-modalities.html#1046" class="Bound">○</a><a id="1068" class="Symbol">)</a> <a id="1070" class="Symbol">(</a><a id="1071" href="orthogonal-factorization-systems.sigma-closed-modalities.html#739" class="Function">is-closed-under-Σ-modality</a><a id="1097" class="Symbol">))</a>
</pre>
## See also

- [Reflective modalities](orthogonal-factorization-systems.reflective-modalities.md)
