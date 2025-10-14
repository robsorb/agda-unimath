# The infinite dimensional complex projective space

<pre class="Agda"><a id="62" class="Keyword">module</a> <a id="69" href="synthetic-homotopy-theory.infinite-complex-projective-space.html" class="Module">synthetic-homotopy-theory.infinite-complex-projective-space</a> <a id="129" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
</pre>
</details>

## Definitions

### `ℂP∞` as the `1`-connected component of the universe at the circle

<pre class="Agda"><a id="ℂP∞"></a><a id="502" href="synthetic-homotopy-theory.infinite-complex-projective-space.html#502" class="Function">ℂP∞</a> <a id="506" class="Symbol">:</a> <a id="508" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="511" class="Symbol">(</a><a id="512" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="517" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="522" class="Symbol">)</a>
<a id="524" href="synthetic-homotopy-theory.infinite-complex-projective-space.html#502" class="Function">ℂP∞</a> <a id="528" class="Symbol">=</a> <a id="530" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="532" class="Symbol">(</a><a id="533" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="536" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="541" class="Symbol">)</a> <a id="543" class="Symbol">(λ</a> <a id="546" href="synthetic-homotopy-theory.infinite-complex-projective-space.html#546" class="Bound">X</a> <a id="548" class="Symbol">→</a> <a id="550" href="foundation.set-truncations.html#2028" class="Function">type-trunc-Set</a> <a id="565" class="Symbol">(</a><a id="566" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a> <a id="569" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="571" href="synthetic-homotopy-theory.infinite-complex-projective-space.html#546" class="Bound">X</a><a id="572" class="Symbol">))</a>

<a id="point-ℂP∞"></a><a id="576" href="synthetic-homotopy-theory.infinite-complex-projective-space.html#576" class="Function">point-ℂP∞</a> <a id="586" class="Symbol">:</a> <a id="588" href="synthetic-homotopy-theory.infinite-complex-projective-space.html#502" class="Function">ℂP∞</a>
<a id="592" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="596" href="synthetic-homotopy-theory.infinite-complex-projective-space.html#576" class="Function">point-ℂP∞</a> <a id="606" class="Symbol">=</a> <a id="608" href="synthetic-homotopy-theory.circle.html#1827" class="Postulate">𝕊¹</a>
<a id="611" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="615" href="synthetic-homotopy-theory.infinite-complex-projective-space.html#576" class="Function">point-ℂP∞</a> <a id="625" class="Symbol">=</a> <a id="627" href="foundation.set-truncations.html#2227" class="Function">unit-trunc-Set</a> <a id="642" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
</pre>
### `ℂP∞` as the `2`-truncation of the `2`-sphere

This remains to be defined.
[#742](https://github.com/UniMath/agda-unimath/issues/742)

## See also

- [The infinite dimensional real projective space](synthetic-homotopy-theory.infinite-real-projective-space.md)
