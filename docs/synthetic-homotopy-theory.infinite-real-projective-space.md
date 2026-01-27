# The infinite dimensional real projective space

<pre class="Agda"><a id="59" class="Keyword">module</a> <a id="66" href="synthetic-homotopy-theory.infinite-real-projective-space.html" class="Module">synthetic-homotopy-theory.infinite-real-projective-space</a> <a id="123" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="group-theory.symmetric-concrete-groups.html" class="Module">group-theory.symmetric-concrete-groups</a>

<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The {{#concept "infinite dimensional real projective space" Agda=ℝP∞}} `ℝP∞` is
the classifying space of the
[symmetric group](group-theory.symmetric-concrete-groups.md) on a
[two-element type](univalent-combinatorics.2-element-types.md).

## Definitions

### As the delooping of a two-element type

<pre class="Agda"><a id="ℝP∞"></a><a id="663" href="synthetic-homotopy-theory.infinite-real-projective-space.html#663" class="Function">ℝP∞</a> <a id="667" class="Symbol">:</a> <a id="669" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="672" class="Symbol">(</a><a id="673" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="678" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="683" class="Symbol">)</a>
<a id="685" href="synthetic-homotopy-theory.infinite-real-projective-space.html#663" class="Function">ℝP∞</a> <a id="689" class="Symbol">=</a> <a id="691" href="group-theory.symmetric-concrete-groups.html#775" class="Function">classifying-type-symmetric-Concrete-Group</a> <a id="733" class="Symbol">(</a><a id="734" href="univalent-combinatorics.standard-finite-types.html#2084" class="Function">Fin-Set</a> <a id="742" class="Number">2</a><a id="743" class="Symbol">)</a>

<a id="point-ℝP∞"></a><a id="746" href="synthetic-homotopy-theory.infinite-real-projective-space.html#746" class="Function">point-ℝP∞</a> <a id="756" class="Symbol">:</a> <a id="758" href="synthetic-homotopy-theory.infinite-real-projective-space.html#663" class="Function">ℝP∞</a>
<a id="762" href="synthetic-homotopy-theory.infinite-real-projective-space.html#746" class="Function">point-ℝP∞</a> <a id="772" class="Symbol">=</a> <a id="774" href="group-theory.symmetric-concrete-groups.html#937" class="Function">shape-symmetric-Concrete-Group</a> <a id="805" class="Symbol">(</a><a id="806" href="univalent-combinatorics.standard-finite-types.html#2084" class="Function">Fin-Set</a> <a id="814" class="Number">2</a><a id="815" class="Symbol">)</a>
</pre>
### As the sequential colimit of the finite dimensional real projective spaces

The infinite dimensional real projective space `ℝP∞` may be realized as a
[sequential colimit](synthetic-homotopy-theory.sequential-colimits.md) of finite
dimensional real projective spaces, see Section IV {{#cite BR17}}.

```text
  ℝP⁻¹ ──→ ℝP⁰ ──→ ℝP¹ ──→ ℝP² ──→ ⋯ ──→ ℝPⁿ ──→ ℝPⁿ⁺¹ ──→ ⋯ ──→ ℝP∞
```

> This remains to be formalized.

## References

{{#bibliography}}

## See also

- [The infinite dimensional complex projective space](synthetic-homotopy-theory.infinite-complex-projective-space.md)
