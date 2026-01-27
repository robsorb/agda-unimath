# Multiset coefficients

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="elementary-number-theory.multiset-coefficients.html" class="Module">elementary-number-theory.multiset-coefficients</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
</pre>
</details>

## Idea

The multiset coefficients count the number of [multisets](trees.multisets.md) of
size `k` of elements of a [set](foundation-core.sets.md) of size `n`. In other
words, it counts the number of
[connected components](foundation.connected-components.md) of the type

```text
  Σ (A : Fin n → Finite-Type), ║ Fin k ≃ Σ (i : Fin n), A i ║.
```

The first few numbers are

|  n\k  |   0 |   1 |   2 |   3 |   4 |   5 |
| :---: | --: | --: | --: | --: | --: | --: |
| **0** |   1 |   0 |   0 |   0 |   0 |   0 |
| **1** |   1 |   1 |   1 |   1 |   1 |   1 |
| **2** |   1 |   2 |   3 |   4 |   5 |   6 |
| **3** |   1 |   3 |   6 |  10 |  15 |  21 |
| **4** |   1 |   4 |  10 |  20 |  35 |  56 |
| **5** |   1 |   5 |  15 |  35 |  70 | 126 |

## Definition

<pre class="Agda"><a id="multiset-coefficient"></a><a id="1043" href="elementary-number-theory.multiset-coefficients.html#1043" class="Function">multiset-coefficient</a> <a id="1064" class="Symbol">:</a> <a id="1066" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1068" class="Symbol">→</a> <a id="1070" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1072" class="Symbol">→</a> <a id="1074" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1076" href="elementary-number-theory.multiset-coefficients.html#1043" class="Function">multiset-coefficient</a> <a id="1097" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1104" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1111" class="Symbol">=</a> <a id="1113" class="Number">1</a>
<a id="1115" href="elementary-number-theory.multiset-coefficients.html#1043" class="Function">multiset-coefficient</a> <a id="1136" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1143" class="Symbol">(</a><a id="1144" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1151" href="elementary-number-theory.multiset-coefficients.html#1151" class="Bound">k</a><a id="1152" class="Symbol">)</a> <a id="1154" class="Symbol">=</a> <a id="1156" class="Number">0</a>
<a id="1158" href="elementary-number-theory.multiset-coefficients.html#1043" class="Function">multiset-coefficient</a> <a id="1179" class="Symbol">(</a><a id="1180" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1187" href="elementary-number-theory.multiset-coefficients.html#1187" class="Bound">n</a><a id="1188" class="Symbol">)</a> <a id="1190" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1197" class="Symbol">=</a> <a id="1199" class="Number">1</a>
<a id="1201" href="elementary-number-theory.multiset-coefficients.html#1043" class="Function">multiset-coefficient</a> <a id="1222" class="Symbol">(</a><a id="1223" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1230" href="elementary-number-theory.multiset-coefficients.html#1230" class="Bound">n</a><a id="1231" class="Symbol">)</a> <a id="1233" class="Symbol">(</a><a id="1234" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1241" href="elementary-number-theory.multiset-coefficients.html#1241" class="Bound">k</a><a id="1242" class="Symbol">)</a> <a id="1244" class="Symbol">=</a>
  <a id="1248" class="Symbol">(</a><a id="1249" href="elementary-number-theory.multiset-coefficients.html#1043" class="Function">multiset-coefficient</a> <a id="1270" class="Symbol">(</a><a id="1271" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1278" href="elementary-number-theory.multiset-coefficients.html#1230" class="Bound">n</a><a id="1279" class="Symbol">)</a> <a id="1281" href="elementary-number-theory.multiset-coefficients.html#1241" class="Bound">k</a><a id="1282" class="Symbol">)</a> <a id="1284" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="1287" class="Symbol">(</a><a id="1288" href="elementary-number-theory.multiset-coefficients.html#1043" class="Function">multiset-coefficient</a> <a id="1309" href="elementary-number-theory.multiset-coefficients.html#1230" class="Bound">n</a> <a id="1311" class="Symbol">(</a><a id="1312" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1319" href="elementary-number-theory.multiset-coefficients.html#1241" class="Bound">k</a><a id="1320" class="Symbol">))</a>
</pre>