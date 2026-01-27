# Sylvester's sequence

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="elementary-number-theory.sylvesters-sequence.html" class="Module">elementary-number-theory.sylvesters-sequence</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="elementary-number-theory.ordinal-induction-natural-numbers.html" class="Module">elementary-number-theory.ordinal-induction-natural-numbers</a>
<a id="265" class="Keyword">open</a> <a id="270" class="Keyword">import</a> <a id="277" href="elementary-number-theory.products-of-natural-numbers.html" class="Module">elementary-number-theory.products-of-natural-numbers</a>

<a id="331" class="Keyword">open</a> <a id="336" class="Keyword">import</a> <a id="343" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

{{#concept "Sylvester's sequence" WD="Sylvester's sequence" WDID=Q2293800 Agda=sylvesters-sequence-ℕ}}
is the [sequence](lists.sequences.md) `s` of
[natural numbers](elementary-number-theory.natural-numbers.md) in which `s n` is
the successor of the
[product](elementary-number-theory.products-of-natural-numbers.md) of all the
numbers `s i` for `i < n`, i.e.,

$$
  s_n := 1+\left(\prod_{i<n}s_i\right).
$$

The first few entries in this sequence are `s 0 = 2`, `s 1 = 3`, `s 2 = 7`, and
`s 3 = 43`.

Sylvester's sequence is listed as [A000058](https://oeis.org/A000058) in the
[OEIS](literature.oeis.md) {{#cite oeis}}.

## Definitions

<pre class="Agda"><a id="sylvesters-sequence-ℕ"></a><a id="1062" href="elementary-number-theory.sylvesters-sequence.html#1062" class="Function">sylvesters-sequence-ℕ</a> <a id="1084" class="Symbol">:</a> <a id="1086" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1088" class="Symbol">→</a> <a id="1090" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1092" href="elementary-number-theory.sylvesters-sequence.html#1062" class="Function">sylvesters-sequence-ℕ</a> <a id="1114" class="Symbol">=</a>
  <a id="1118" href="elementary-number-theory.ordinal-induction-natural-numbers.html#1435" class="Function">ordinal-ind-ℕ</a>
    <a id="1136" class="Symbol">(</a> <a id="1138" class="Symbol">λ</a> <a id="1140" href="elementary-number-theory.sylvesters-sequence.html#1140" class="Bound">_</a> <a id="1142" class="Symbol">→</a> <a id="1144" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1145" class="Symbol">)</a>
    <a id="1151" class="Symbol">(</a> <a id="1153" class="Symbol">λ</a> <a id="1155" href="elementary-number-theory.sylvesters-sequence.html#1155" class="Bound">n</a> <a id="1157" href="elementary-number-theory.sylvesters-sequence.html#1157" class="Bound">f</a> <a id="1159" class="Symbol">→</a>
      <a id="1167" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1174" class="Symbol">(</a><a id="1175" href="elementary-number-theory.products-of-natural-numbers.html#908" class="Function">Π-ℕ</a> <a id="1179" href="elementary-number-theory.sylvesters-sequence.html#1155" class="Bound">n</a> <a id="1181" class="Symbol">(λ</a> <a id="1184" href="elementary-number-theory.sylvesters-sequence.html#1184" class="Bound">i</a> <a id="1186" class="Symbol">→</a> <a id="1188" href="elementary-number-theory.sylvesters-sequence.html#1157" class="Bound">f</a> <a id="1190" class="Symbol">(</a><a id="1191" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a> <a id="1199" href="elementary-number-theory.sylvesters-sequence.html#1155" class="Bound">n</a> <a id="1201" href="elementary-number-theory.sylvesters-sequence.html#1184" class="Bound">i</a><a id="1202" class="Symbol">)</a> <a id="1204" class="Symbol">(</a><a id="1205" href="univalent-combinatorics.standard-finite-types.html#7161" class="Function">strict-upper-bound-nat-Fin</a> <a id="1232" href="elementary-number-theory.sylvesters-sequence.html#1155" class="Bound">n</a> <a id="1234" href="elementary-number-theory.sylvesters-sequence.html#1184" class="Bound">i</a><a id="1235" class="Symbol">))))</a>
</pre>
## References

{{#bibliography}}
