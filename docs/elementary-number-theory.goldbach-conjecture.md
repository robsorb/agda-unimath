# The Goldbach conjecture

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="elementary-number-theory.goldbach-conjecture.html" class="Module">elementary-number-theory.goldbach-conjecture</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="elementary-number-theory.parity-natural-numbers.html" class="Module">elementary-number-theory.parity-natural-numbers</a>
<a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a>

<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="489" class="Keyword">open</a> <a id="494" class="Keyword">import</a> <a id="501" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="533" class="Keyword">open</a> <a id="538" class="Keyword">import</a> <a id="545" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="571" class="Keyword">open</a> <a id="576" class="Keyword">import</a> <a id="583" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The
{{#concept "Goldbach conjecture" WD="Goldbach's conjecture" WDID=Q485520 Agda=Goldbach-conjecture}}
states that every even
[natural number](elementary-number-theory.natural-numbers.md) `n`
[greater than](elementary-number-theory.strict-inequality-natural-numbers.md)
two is [equal](foundation-core.identity-types.md) to a
[sum](elementary-number-theory.addition-natural-numbers.md) of two
[primes](elementary-number-theory.prime-numbers.md)

```text
  n = p + q.
```

## Conjecture

<pre class="Agda"><a id="Goldbach-conjecture"></a><a id="1131" href="elementary-number-theory.goldbach-conjecture.html#1131" class="Function">Goldbach-conjecture</a> <a id="1151" class="Symbol">:</a> <a id="1153" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1156" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1162" href="elementary-number-theory.goldbach-conjecture.html#1131" class="Function">Goldbach-conjecture</a> <a id="1182" class="Symbol">=</a>
  <a id="1186" class="Symbol">(</a> <a id="1188" href="elementary-number-theory.goldbach-conjecture.html#1188" class="Bound">n</a> <a id="1190" class="Symbol">:</a> <a id="1192" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1193" class="Symbol">)</a> <a id="1195" class="Symbol">→</a> <a id="1197" class="Symbol">(</a><a id="1198" href="elementary-number-theory.strict-inequality-natural-numbers.html#1676" class="Function">le-ℕ</a> <a id="1203" class="Number">2</a> <a id="1205" href="elementary-number-theory.goldbach-conjecture.html#1188" class="Bound">n</a><a id="1206" class="Symbol">)</a> <a id="1208" class="Symbol">→</a> <a id="1210" class="Symbol">(</a><a id="1211" href="elementary-number-theory.parity-natural-numbers.html#1149" class="Function">is-even-ℕ</a> <a id="1221" href="elementary-number-theory.goldbach-conjecture.html#1188" class="Bound">n</a><a id="1222" class="Symbol">)</a> <a id="1224" class="Symbol">→</a>
    <a id="1230" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1232" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1234" class="Symbol">(λ</a> <a id="1237" href="elementary-number-theory.goldbach-conjecture.html#1237" class="Bound">p</a> <a id="1239" class="Symbol">→</a> <a id="1241" class="Symbol">(</a><a id="1242" href="elementary-number-theory.prime-numbers.html#1562" class="Function">is-prime-ℕ</a> <a id="1253" href="elementary-number-theory.goldbach-conjecture.html#1237" class="Bound">p</a><a id="1254" class="Symbol">)</a> <a id="1256" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1258" class="Symbol">(</a><a id="1259" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1261" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1263" class="Symbol">(λ</a> <a id="1266" href="elementary-number-theory.goldbach-conjecture.html#1266" class="Bound">q</a> <a id="1268" class="Symbol">→</a> <a id="1270" class="Symbol">(</a><a id="1271" href="elementary-number-theory.prime-numbers.html#1562" class="Function">is-prime-ℕ</a> <a id="1282" href="elementary-number-theory.goldbach-conjecture.html#1266" class="Bound">q</a><a id="1283" class="Symbol">)</a> <a id="1285" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="1287" class="Symbol">(</a><a id="1288" href="elementary-number-theory.goldbach-conjecture.html#1237" class="Bound">p</a> <a id="1290" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="1293" href="elementary-number-theory.goldbach-conjecture.html#1266" class="Bound">q</a> <a id="1295" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1297" href="elementary-number-theory.goldbach-conjecture.html#1188" class="Bound">n</a><a id="1298" class="Symbol">))))</a>
</pre>
## External links

- [Goldbach conjecture](https://www.britannica.com/science/Goldbach-conjecture)
  at Britannica
- [Goldbach's conjecture](https://en.wikipedia.org/wiki/Goldbach%27s_conjecture)
  at Wikipedia
- [Goldbach Conjecture](https://mathworld.wolfram.com/GoldbachConjecture.html)
  at Wolfram MathWorld
