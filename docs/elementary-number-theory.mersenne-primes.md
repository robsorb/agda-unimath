# Mersenne primes

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="elementary-number-theory.mersenne-primes.html" class="Module">elementary-number-theory.mersenne-primes</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a>
<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="elementary-number-theory.exponentiation-natural-numbers.html" class="Module">elementary-number-theory.exponentiation-natural-numbers</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a>

<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="458" class="Keyword">open</a> <a id="463" class="Keyword">import</a> <a id="470" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="496" class="Keyword">open</a> <a id="501" class="Keyword">import</a> <a id="508" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A Mersenne prime is a prime number that is one less than a power of two.

## Definition

<pre class="Agda"><a id="is-mersenne-prime"></a><a id="658" href="elementary-number-theory.mersenne-primes.html#658" class="Function">is-mersenne-prime</a> <a id="676" class="Symbol">:</a> <a id="678" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="680" class="Symbol">→</a> <a id="682" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="685" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="691" href="elementary-number-theory.mersenne-primes.html#658" class="Function">is-mersenne-prime</a> <a id="709" href="elementary-number-theory.mersenne-primes.html#709" class="Bound">n</a> <a id="711" class="Symbol">=</a> <a id="713" href="elementary-number-theory.prime-numbers.html#1562" class="Function">is-prime-ℕ</a> <a id="724" href="elementary-number-theory.mersenne-primes.html#709" class="Bound">n</a> <a id="726" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="728" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="730" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="732" class="Symbol">(λ</a> <a id="735" href="elementary-number-theory.mersenne-primes.html#735" class="Bound">k</a> <a id="737" class="Symbol">→</a> <a id="739" href="elementary-number-theory.distance-natural-numbers.html#1461" class="Function">dist-ℕ</a> <a id="746" class="Symbol">(</a><a id="747" href="elementary-number-theory.exponentiation-natural-numbers.html#927" class="Function">exp-ℕ</a> <a id="753" class="Number">2</a> <a id="755" href="elementary-number-theory.mersenne-primes.html#735" class="Bound">k</a><a id="756" class="Symbol">)</a> <a id="758" class="Number">1</a> <a id="760" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="762" href="elementary-number-theory.mersenne-primes.html#709" class="Bound">n</a><a id="763" class="Symbol">)</a>

<a id="is-mersenne-prime-power"></a><a id="766" href="elementary-number-theory.mersenne-primes.html#766" class="Function">is-mersenne-prime-power</a> <a id="790" class="Symbol">:</a> <a id="792" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="794" class="Symbol">→</a> <a id="796" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="799" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="805" href="elementary-number-theory.mersenne-primes.html#766" class="Function">is-mersenne-prime-power</a> <a id="829" href="elementary-number-theory.mersenne-primes.html#829" class="Bound">k</a> <a id="831" class="Symbol">=</a> <a id="833" href="elementary-number-theory.prime-numbers.html#1562" class="Function">is-prime-ℕ</a> <a id="844" class="Symbol">(</a><a id="845" href="elementary-number-theory.distance-natural-numbers.html#1461" class="Function">dist-ℕ</a> <a id="852" class="Symbol">(</a><a id="853" href="elementary-number-theory.exponentiation-natural-numbers.html#927" class="Function">exp-ℕ</a> <a id="859" class="Number">2</a> <a id="861" href="elementary-number-theory.mersenne-primes.html#829" class="Bound">k</a><a id="862" class="Symbol">)</a> <a id="864" class="Number">1</a><a id="865" class="Symbol">)</a>
</pre>