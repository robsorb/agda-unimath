# Multivariable correspondences

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="foundation.multivariable-correspondences.html" class="Module">foundation.multivariable-correspondences</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

Consider a family of types `A` indexed by `Fin n`. An `n`-ary correspondence of
tuples `(x₁, …, xₙ)` where `xᵢ : A i` is a type family over `(i : Fin n) → A i`.

## Definition

<pre class="Agda"><a id="multivariable-correspondence"></a><a id="509" href="foundation.multivariable-correspondences.html#509" class="Function">multivariable-correspondence</a> <a id="538" class="Symbol">:</a>
  <a id="542" class="Symbol">{</a><a id="543" href="foundation.multivariable-correspondences.html#543" class="Bound">l1</a> <a id="546" class="Symbol">:</a> <a id="548" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="553" class="Symbol">}</a> <a id="555" class="Symbol">(</a><a id="556" href="foundation.multivariable-correspondences.html#556" class="Bound">l2</a> <a id="559" class="Symbol">:</a> <a id="561" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="566" class="Symbol">)</a> <a id="568" class="Symbol">(</a><a id="569" href="foundation.multivariable-correspondences.html#569" class="Bound">n</a> <a id="571" class="Symbol">:</a> <a id="573" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="574" class="Symbol">)</a> <a id="576" class="Symbol">(</a><a id="577" href="foundation.multivariable-correspondences.html#577" class="Bound">A</a> <a id="579" class="Symbol">:</a> <a id="581" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="585" href="foundation.multivariable-correspondences.html#569" class="Bound">n</a> <a id="587" class="Symbol">→</a> <a id="589" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="592" href="foundation.multivariable-correspondences.html#543" class="Bound">l1</a><a id="594" class="Symbol">)</a> <a id="596" class="Symbol">→</a> <a id="598" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="601" class="Symbol">(</a><a id="602" href="foundation.multivariable-correspondences.html#543" class="Bound">l1</a> <a id="605" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="607" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="612" href="foundation.multivariable-correspondences.html#556" class="Bound">l2</a><a id="614" class="Symbol">)</a>
<a id="616" href="foundation.multivariable-correspondences.html#509" class="Function">multivariable-correspondence</a> <a id="645" href="foundation.multivariable-correspondences.html#645" class="Bound">l2</a> <a id="648" href="foundation.multivariable-correspondences.html#648" class="Bound">n</a> <a id="650" href="foundation.multivariable-correspondences.html#650" class="Bound">A</a> <a id="652" class="Symbol">=</a> <a id="654" class="Symbol">((</a><a id="656" href="foundation.multivariable-correspondences.html#656" class="Bound">i</a> <a id="658" class="Symbol">:</a> <a id="660" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="664" href="foundation.multivariable-correspondences.html#648" class="Bound">n</a><a id="665" class="Symbol">)</a> <a id="667" class="Symbol">→</a> <a id="669" href="foundation.multivariable-correspondences.html#650" class="Bound">A</a> <a id="671" href="foundation.multivariable-correspondences.html#656" class="Bound">i</a><a id="672" class="Symbol">)</a> <a id="674" class="Symbol">→</a> <a id="676" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="679" href="foundation.multivariable-correspondences.html#645" class="Bound">l2</a>
</pre>