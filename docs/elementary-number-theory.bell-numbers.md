# The Bell numbers

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="elementary-number-theory.bell-numbers.html" class="Module">elementary-number-theory.bell-numbers</a> <a id="74" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="130" class="Keyword">open</a> <a id="135" class="Keyword">import</a> <a id="142" href="elementary-number-theory.binomial-coefficients.html" class="Module">elementary-number-theory.binomial-coefficients</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="elementary-number-theory.strong-induction-natural-numbers.html" class="Module">elementary-number-theory.strong-induction-natural-numbers</a>
<a id="451" class="Keyword">open</a> <a id="456" class="Keyword">import</a> <a id="463" href="elementary-number-theory.sums-of-natural-numbers.html" class="Module">elementary-number-theory.sums-of-natural-numbers</a>
</pre>
</details>

## Idea

The {{#concept "Bell numbers" Agda=bell-number-ℕ WDID=Q816063 WD="Bell number"}}
[count](univalent-combinatorics.counting.md) the number of ways to
[partition](univalent-combinatorics.partitions.md) a
[set of size](univalent-combinatorics.finite-types.md) $n$. The Bell numbers can
be defined recursively by $B_0 := 1$ and

$$
  B_{n+1} := \sum_{k=0}^{n} \binom{n}{k}B_k.
$$

The Bell numbers are listed as sequence A000110 in the
[OEIS](literature.oeis.md) {{#cite OEIS}}.

## Definitions

### The Bell numbers

<pre class="Agda"><a id="bell-number-ℕ"></a><a id="1059" href="elementary-number-theory.bell-numbers.html#1059" class="Function">bell-number-ℕ</a> <a id="1073" class="Symbol">:</a> <a id="1075" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1077" class="Symbol">→</a> <a id="1079" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1081" href="elementary-number-theory.bell-numbers.html#1059" class="Function">bell-number-ℕ</a> <a id="1095" class="Symbol">=</a>
  <a id="1099" href="elementary-number-theory.strong-induction-natural-numbers.html#8010" class="Function">strong-rec-ℕ</a> <a id="1112" class="Number">1</a>
    <a id="1118" class="Symbol">(</a> <a id="1120" class="Symbol">λ</a> <a id="1122" href="elementary-number-theory.bell-numbers.html#1122" class="Bound">n</a> <a id="1124" href="elementary-number-theory.bell-numbers.html#1124" class="Bound">B</a> <a id="1126" class="Symbol">→</a>
      <a id="1134" href="elementary-number-theory.sums-of-natural-numbers.html#1684" class="Function">bounded-sum-ℕ</a>
        <a id="1156" class="Symbol">(</a> <a id="1158" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1165" href="elementary-number-theory.bell-numbers.html#1122" class="Bound">n</a><a id="1166" class="Symbol">)</a>
        <a id="1176" class="Symbol">(</a> <a id="1178" class="Symbol">λ</a> <a id="1180" href="elementary-number-theory.bell-numbers.html#1180" class="Bound">k</a> <a id="1182" href="elementary-number-theory.bell-numbers.html#1182" class="Bound">H</a> <a id="1184" class="Symbol">→</a>
          <a id="1196" href="elementary-number-theory.binomial-coefficients.html#1394" class="Function">binomial-coefficient-ℕ</a> <a id="1219" href="elementary-number-theory.bell-numbers.html#1122" class="Bound">n</a> <a id="1221" href="elementary-number-theory.bell-numbers.html#1180" class="Bound">k</a> <a id="1223" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="1226" href="elementary-number-theory.bell-numbers.html#1124" class="Bound">B</a> <a id="1228" href="elementary-number-theory.bell-numbers.html#1180" class="Bound">k</a> <a id="1230" class="Symbol">(</a><a id="1231" href="elementary-number-theory.strict-inequality-natural-numbers.html#8701" class="Function">leq-le-succ-ℕ</a> <a id="1245" href="elementary-number-theory.bell-numbers.html#1180" class="Bound">k</a> <a id="1247" href="elementary-number-theory.bell-numbers.html#1122" class="Bound">n</a> <a id="1249" href="elementary-number-theory.bell-numbers.html#1182" class="Bound">H</a><a id="1250" class="Symbol">)))</a>
</pre>
## References

{{#bibliography}}
