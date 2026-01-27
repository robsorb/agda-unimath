# Σ-closed reflective subuniverses

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html" class="Module">orthogonal-factorization-systems.sigma-closed-reflective-subuniverses</a> <a id="122" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.sigma-closed-subuniverses.html" class="Module">foundation.sigma-closed-subuniverses</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="orthogonal-factorization-systems.reflective-subuniverses.html" class="Module">orthogonal-factorization-systems.reflective-subuniverses</a>
</pre>
</details>

## Idea

A
[reflective subuniverse](orthogonal-factorization-systems.reflective-subuniverses.md)
is **Σ-closed** if it is closed under the formation of
[Σ-types](foundation.dependent-pair-types.md).

## Definition

<pre class="Agda"><a id="is-closed-under-Σ-reflective-subuniverse"></a><a id="620" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#620" class="Function">is-closed-under-Σ-reflective-subuniverse</a> <a id="661" class="Symbol">:</a>
  <a id="665" class="Symbol">{</a><a id="666" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#666" class="Bound">l</a> <a id="668" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#668" class="Bound">lP</a> <a id="671" class="Symbol">:</a> <a id="673" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="678" class="Symbol">}</a> <a id="680" class="Symbol">→</a> <a id="682" href="orthogonal-factorization-systems.reflective-subuniverses.html#2993" class="Function">reflective-subuniverse</a> <a id="705" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#666" class="Bound">l</a> <a id="707" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#668" class="Bound">lP</a> <a id="710" class="Symbol">→</a> <a id="712" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="715" class="Symbol">(</a><a id="716" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="721" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#666" class="Bound">l</a> <a id="723" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="725" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#668" class="Bound">lP</a><a id="727" class="Symbol">)</a>
<a id="729" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#620" class="Function">is-closed-under-Σ-reflective-subuniverse</a> <a id="770" class="Symbol">(</a><a id="771" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#771" class="Bound">P</a> <a id="773" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="775" class="Symbol">_)</a> <a id="778" class="Symbol">=</a>
  <a id="782" href="foundation.sigma-closed-subuniverses.html#1111" class="Function">is-closed-under-Σ-subuniverse</a> <a id="812" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#771" class="Bound">P</a>

<a id="closed-under-Σ-reflective-subuniverse"></a><a id="815" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#815" class="Function">closed-under-Σ-reflective-subuniverse</a> <a id="853" class="Symbol">:</a>
  <a id="857" class="Symbol">(</a><a id="858" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#858" class="Bound">l</a> <a id="860" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#860" class="Bound">lP</a> <a id="863" class="Symbol">:</a> <a id="865" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="870" class="Symbol">)</a> <a id="872" class="Symbol">→</a> <a id="874" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="877" class="Symbol">(</a><a id="878" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="883" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#858" class="Bound">l</a> <a id="885" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="887" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="892" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#860" class="Bound">lP</a><a id="894" class="Symbol">)</a>
<a id="896" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#815" class="Function">closed-under-Σ-reflective-subuniverse</a> <a id="934" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#934" class="Bound">l</a> <a id="936" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#936" class="Bound">lP</a> <a id="939" class="Symbol">=</a>
  <a id="943" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="945" class="Symbol">(</a> <a id="947" href="orthogonal-factorization-systems.reflective-subuniverses.html#2993" class="Function">reflective-subuniverse</a> <a id="970" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#934" class="Bound">l</a> <a id="972" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#936" class="Bound">lP</a><a id="974" class="Symbol">)</a>
    <a id="980" class="Symbol">(</a> <a id="982" href="orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.html#620" class="Function">is-closed-under-Σ-reflective-subuniverse</a><a id="1022" class="Symbol">)</a>
</pre>
## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Stable orthogonal factorization systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.md)
- [Σ-closed reflective modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.md)

## References

{{#bibliography}} {{#reference RSS20}}
