# Machine integers

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="primitives.machine-integers.html" class="Module">primitives.machine-integers</a> <a id="64" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="120" class="Keyword">open</a> <a id="125" class="Keyword">import</a> <a id="132" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The `Word64` type represents 64-bit machine words. Agda provides primitive
functions to manipulate them.

## Definitions

<pre class="Agda"><a id="407" class="Keyword">postulate</a>
  <a id="Word64"></a><a id="419" href="primitives.machine-integers.html#419" class="Postulate">Word64</a> <a id="426" class="Symbol">:</a> <a id="428" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="431" href="Agda.Primitive.html#915" class="Primitive">lzero</a>

<a id="438" class="Symbol">{-#</a> <a id="442" class="Keyword">BUILTIN</a> <a id="450" class="Keyword">WORD64</a> <a id="457" href="primitives.machine-integers.html#419" class="Postulate">Word64</a> <a id="464" class="Symbol">#-}</a>

<a id="469" class="Keyword">primitive</a>
  <a id="primWord64ToNat"></a><a id="481" href="primitives.machine-integers.html#481" class="Primitive">primWord64ToNat</a> <a id="497" class="Symbol">:</a> <a id="499" href="primitives.machine-integers.html#419" class="Postulate">Word64</a> <a id="506" class="Symbol">→</a> <a id="508" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
  <a id="primWord64FromNat"></a><a id="512" href="primitives.machine-integers.html#512" class="Primitive">primWord64FromNat</a> <a id="530" class="Symbol">:</a> <a id="532" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="534" class="Symbol">→</a> <a id="536" href="primitives.machine-integers.html#419" class="Postulate">Word64</a>
  <a id="primWord64ToNatInjective"></a><a id="545" href="primitives.machine-integers.html#545" class="Primitive">primWord64ToNatInjective</a> <a id="570" class="Symbol">:</a>
    <a id="576" class="Symbol">(</a><a id="577" href="primitives.machine-integers.html#577" class="Bound">a</a> <a id="579" href="primitives.machine-integers.html#579" class="Bound">b</a> <a id="581" class="Symbol">:</a> <a id="583" href="primitives.machine-integers.html#419" class="Postulate">Word64</a><a id="589" class="Symbol">)</a> <a id="591" class="Symbol">→</a> <a id="593" href="primitives.machine-integers.html#481" class="Primitive">primWord64ToNat</a> <a id="609" href="primitives.machine-integers.html#577" class="Bound">a</a> <a id="611" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="613" href="primitives.machine-integers.html#481" class="Primitive">primWord64ToNat</a> <a id="629" href="primitives.machine-integers.html#579" class="Bound">b</a> <a id="631" class="Symbol">→</a> <a id="633" href="primitives.machine-integers.html#577" class="Bound">a</a> <a id="635" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="637" href="primitives.machine-integers.html#579" class="Bound">b</a>
</pre>