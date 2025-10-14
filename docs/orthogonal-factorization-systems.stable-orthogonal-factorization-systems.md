# Stable orthogonal factorization systems

<pre class="Agda"><a id="52" class="Keyword">module</a> <a id="59" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html" class="Module">orthogonal-factorization-systems.stable-orthogonal-factorization-systems</a> <a id="132" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="orthogonal-factorization-systems.function-classes.html" class="Module">orthogonal-factorization-systems.function-classes</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="orthogonal-factorization-systems.orthogonal-factorization-systems.html" class="Module">orthogonal-factorization-systems.orthogonal-factorization-systems</a>
</pre>
</details>

## Idea

A **stable orthogonal factorization system**, or **stable factorization system**
for short, is an
[orthogonal factorization system](orthogonal-factorization-systems.orthogonal-factorization-systems.md)
whose left class is stable under [pullbacks](foundation.pullbacks.md). The right
class of an orthogonal factorization system, however, is always stable under
pullbacks.

## Definition

<pre class="Agda"><a id="is-stable-orthogonal-factorization-system"></a><a id="789" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#789" class="Function">is-stable-orthogonal-factorization-system</a> <a id="831" class="Symbol">:</a>
  <a id="835" class="Symbol">{</a><a id="836" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#836" class="Bound">l1</a> <a id="839" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#839" class="Bound">lL</a> <a id="842" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#842" class="Bound">lR</a> <a id="845" class="Symbol">:</a> <a id="847" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="852" class="Symbol">}</a> <a id="854" class="Symbol">→</a>
  <a id="858" href="orthogonal-factorization-systems.orthogonal-factorization-systems.html#2717" class="Function">orthogonal-factorization-system</a> <a id="890" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#836" class="Bound">l1</a> <a id="893" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#839" class="Bound">lL</a> <a id="896" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#842" class="Bound">lR</a> <a id="899" class="Symbol">→</a> <a id="901" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="904" class="Symbol">(</a><a id="905" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="910" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#836" class="Bound">l1</a> <a id="913" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="915" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#839" class="Bound">lL</a><a id="917" class="Symbol">)</a>
<a id="919" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#789" class="Function">is-stable-orthogonal-factorization-system</a> <a id="961" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#961" class="Bound">OFS</a> <a id="965" class="Symbol">=</a>
  <a id="969" href="orthogonal-factorization-systems.function-classes.html#5437" class="Function">is-pullback-stable-function-class</a>
    <a id="1007" class="Symbol">(</a> <a id="1009" href="orthogonal-factorization-systems.orthogonal-factorization-systems.html#5285" class="Function">left-class-orthogonal-factorization-system</a> <a id="1052" href="orthogonal-factorization-systems.stable-orthogonal-factorization-systems.html#961" class="Bound">OFS</a><a id="1055" class="Symbol">)</a>
</pre>
## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)

## References

{{#bibliography}} {{#reference RSS20}}
