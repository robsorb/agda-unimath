# Cubes of natural numbers

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="elementary-number-theory.cubes-natural-numbers.html" class="Module">elementary-number-theory.cubes-natural-numbers</a> <a id="91" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="147" class="Keyword">open</a> <a id="152" class="Keyword">import</a> <a id="159" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="elementary-number-theory.squares-natural-numbers.html" class="Module">elementary-number-theory.squares-natural-numbers</a>

<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="412" class="Keyword">open</a> <a id="417" class="Keyword">import</a> <a id="424" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The {{#concept "cube" Disambiguation="natural number" Agda=cube-ℕ}} `n³` of a
[natural number](elementary-number-theory.natural-numbers.md) `n` is the triple
[product](elementary-number-theory.multiplication-natural-numbers.md)

```text
  n³ := n * n * n
```

of `n` with itself.

## Definitions

### Cubes of natural numbers

<pre class="Agda"><a id="cube-ℕ"></a><a id="812" href="elementary-number-theory.cubes-natural-numbers.html#812" class="Function">cube-ℕ</a> <a id="819" class="Symbol">:</a> <a id="821" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="823" class="Symbol">→</a> <a id="825" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="827" href="elementary-number-theory.cubes-natural-numbers.html#812" class="Function">cube-ℕ</a> <a id="834" href="elementary-number-theory.cubes-natural-numbers.html#834" class="Bound">n</a> <a id="836" class="Symbol">=</a> <a id="838" href="elementary-number-theory.squares-natural-numbers.html#1250" class="Function">square-ℕ</a> <a id="847" href="elementary-number-theory.cubes-natural-numbers.html#834" class="Bound">n</a> <a id="849" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="852" href="elementary-number-theory.cubes-natural-numbers.html#834" class="Bound">n</a>
</pre>
### The predicate of being a cube of natural numbers

<pre class="Agda"><a id="is-cube-ℕ"></a><a id="921" href="elementary-number-theory.cubes-natural-numbers.html#921" class="Function">is-cube-ℕ</a> <a id="931" class="Symbol">:</a> <a id="933" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="935" class="Symbol">→</a> <a id="937" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="940" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="946" href="elementary-number-theory.cubes-natural-numbers.html#921" class="Function">is-cube-ℕ</a> <a id="956" class="Symbol">=</a> <a id="958" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="964" href="elementary-number-theory.cubes-natural-numbers.html#812" class="Function">cube-ℕ</a>
</pre>
### The cubic root of cubic natural numbers

<pre class="Agda"><a id="cubic-root-ℕ"></a><a id="1029" href="elementary-number-theory.cubes-natural-numbers.html#1029" class="Function">cubic-root-ℕ</a> <a id="1042" class="Symbol">:</a> <a id="1044" class="Symbol">(</a><a id="1045" href="elementary-number-theory.cubes-natural-numbers.html#1045" class="Bound">n</a> <a id="1047" class="Symbol">:</a> <a id="1049" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1050" class="Symbol">)</a> <a id="1052" class="Symbol">→</a> <a id="1054" href="elementary-number-theory.cubes-natural-numbers.html#921" class="Function">is-cube-ℕ</a> <a id="1064" href="elementary-number-theory.cubes-natural-numbers.html#1045" class="Bound">n</a> <a id="1066" class="Symbol">→</a> <a id="1068" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1070" href="elementary-number-theory.cubes-natural-numbers.html#1029" class="Function">cubic-root-ℕ</a> <a id="1083" href="elementary-number-theory.cubes-natural-numbers.html#1083" class="Bound">n</a> <a id="1085" class="Symbol">=</a> <a id="1087" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>
</pre>
## See also

- [Squares of natural numbers](elementary-number-theory.squares-natural-numbers.md)
