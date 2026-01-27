# The `E₈`-lattice

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="group-theory.e8-lattice.html" class="Module">group-theory.e8-lattice</a> <a id="60" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="116" class="Keyword">open</a> <a id="121" class="Keyword">import</a> <a id="128" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>

<a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Definition

### The ambient set of the E₈ lattice

The E₈ lattice itself is a subset of the following set.

<pre class="Agda"><a id="ambient-set-E8-lattice"></a><a id="473" href="group-theory.e8-lattice.html#473" class="Function">ambient-set-E8-lattice</a> <a id="496" class="Symbol">:</a> <a id="498" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="502" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="508" href="group-theory.e8-lattice.html#473" class="Function">ambient-set-E8-lattice</a> <a id="531" class="Symbol">=</a>
  <a id="535" href="foundation.equality-coproduct-types.html#12262" class="Function">coproduct-Set</a> <a id="549" class="Symbol">(</a><a id="550" href="foundation.sets.html#4326" class="Function">hom-set-Set</a> <a id="562" class="Symbol">(</a><a id="563" href="univalent-combinatorics.standard-finite-types.html#2084" class="Function">Fin-Set</a> <a id="571" class="Number">8</a><a id="572" class="Symbol">)</a> <a id="574" href="elementary-number-theory.integers.html#3629" class="Function">ℤ-Set</a><a id="579" class="Symbol">)</a> <a id="581" class="Symbol">(</a><a id="582" href="foundation.sets.html#4326" class="Function">hom-set-Set</a> <a id="594" class="Symbol">(</a><a id="595" href="univalent-combinatorics.standard-finite-types.html#2084" class="Function">Fin-Set</a> <a id="603" class="Number">8</a><a id="604" class="Symbol">)</a> <a id="606" href="elementary-number-theory.integers.html#3629" class="Function">ℤ-Set</a><a id="611" class="Symbol">)</a>
</pre>