# Partial sums of sequences in semirings

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="ring-theory.partial-sums-sequences-semirings.html" class="Module">ring-theory.partial-sums-sequences-semirings</a> <a id="103" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="159" class="Keyword">open</a> <a id="164" class="Keyword">import</a> <a id="171" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="213" class="Keyword">open</a> <a id="218" class="Keyword">import</a> <a id="225" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="lists.finite-sequences.html" class="Module">lists.finite-sequences</a>
<a id="360" class="Keyword">open</a> <a id="365" class="Keyword">import</a> <a id="372" href="lists.sequences.html" class="Module">lists.sequences</a>

<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="ring-theory.semirings.html" class="Module">ring-theory.semirings</a>
<a id="423" class="Keyword">open</a> <a id="428" class="Keyword">import</a> <a id="435" href="ring-theory.sums-of-finite-sequences-of-elements-semirings.html" class="Module">ring-theory.sums-of-finite-sequences-of-elements-semirings</a>
</pre>
</details>

## Ideas

The
{{#concept "sequence of partial sums" Disambiguation="of a sequence in a semiring" Agda=seq-sum-sequence-Semiring}}
of a [sequence](lists.sequences.md) `u` in a
[semiring](ring-theory.semirings.md) is the sequence of sums of terms of `u`:

```text
n ↦ Σ (k ≤ n) (u k).
```

## Definitions

### Partial sums of terms of a sequence in a semiring

<pre class="Agda"><a id="878" class="Keyword">module</a> <a id="885" href="ring-theory.partial-sums-sequences-semirings.html#885" class="Module">_</a>
  <a id="889" class="Symbol">{</a><a id="890" href="ring-theory.partial-sums-sequences-semirings.html#890" class="Bound">l</a> <a id="892" class="Symbol">:</a> <a id="894" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="899" class="Symbol">}</a> <a id="901" class="Symbol">(</a><a id="902" href="ring-theory.partial-sums-sequences-semirings.html#902" class="Bound">R</a> <a id="904" class="Symbol">:</a> <a id="906" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="915" href="ring-theory.partial-sums-sequences-semirings.html#890" class="Bound">l</a><a id="916" class="Symbol">)</a> <a id="918" class="Symbol">(</a><a id="919" href="ring-theory.partial-sums-sequences-semirings.html#919" class="Bound">u</a> <a id="921" class="Symbol">:</a> <a id="923" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="925" class="Symbol">→</a> <a id="927" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="941" href="ring-theory.partial-sums-sequences-semirings.html#902" class="Bound">R</a><a id="942" class="Symbol">)</a>
  <a id="946" class="Keyword">where</a>

  <a id="955" href="ring-theory.partial-sums-sequences-semirings.html#955" class="Function">seq-sum-sequence-Semiring</a> <a id="981" class="Symbol">:</a> <a id="983" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="985" class="Symbol">→</a> <a id="987" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="1001" href="ring-theory.partial-sums-sequences-semirings.html#902" class="Bound">R</a>
  <a id="1005" href="ring-theory.partial-sums-sequences-semirings.html#955" class="Function">seq-sum-sequence-Semiring</a> <a id="1031" href="ring-theory.partial-sums-sequences-semirings.html#1031" class="Bound">n</a> <a id="1033" class="Symbol">=</a>
    <a id="1039" href="ring-theory.sums-of-finite-sequences-of-elements-semirings.html#1345" class="Function">sum-fin-sequence-type-Semiring</a>
      <a id="1076" class="Symbol">(</a> <a id="1078" href="ring-theory.partial-sums-sequences-semirings.html#902" class="Bound">R</a><a id="1079" class="Symbol">)</a>
      <a id="1087" class="Symbol">(</a> <a id="1089" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1096" href="ring-theory.partial-sums-sequences-semirings.html#1031" class="Bound">n</a><a id="1097" class="Symbol">)</a>
      <a id="1105" class="Symbol">(</a> <a id="1107" href="lists.finite-sequences.html#4326" class="Function">fin-sequence-sequence</a> <a id="1129" href="ring-theory.partial-sums-sequences-semirings.html#919" class="Bound">u</a> <a id="1131" class="Symbol">(</a><a id="1132" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1139" href="ring-theory.partial-sums-sequences-semirings.html#1031" class="Bound">n</a><a id="1140" class="Symbol">))</a>
</pre>
## Properties

### Homotopic sequences have homotopic partial sums

<pre class="Agda"><a id="1224" class="Keyword">module</a> <a id="1231" href="ring-theory.partial-sums-sequences-semirings.html#1231" class="Module">_</a>
  <a id="1235" class="Symbol">{</a><a id="1236" href="ring-theory.partial-sums-sequences-semirings.html#1236" class="Bound">l</a> <a id="1238" class="Symbol">:</a> <a id="1240" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1245" class="Symbol">}</a> <a id="1247" class="Symbol">(</a><a id="1248" href="ring-theory.partial-sums-sequences-semirings.html#1248" class="Bound">R</a> <a id="1250" class="Symbol">:</a> <a id="1252" href="ring-theory.semirings.html#2353" class="Function">Semiring</a> <a id="1261" href="ring-theory.partial-sums-sequences-semirings.html#1236" class="Bound">l</a><a id="1262" class="Symbol">)</a> <a id="1264" class="Symbol">{</a><a id="1265" href="ring-theory.partial-sums-sequences-semirings.html#1265" class="Bound">u</a> <a id="1267" href="ring-theory.partial-sums-sequences-semirings.html#1267" class="Bound">v</a> <a id="1269" class="Symbol">:</a> <a id="1271" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1273" class="Symbol">→</a> <a id="1275" href="ring-theory.semirings.html#3067" class="Function">type-Semiring</a> <a id="1289" href="ring-theory.partial-sums-sequences-semirings.html#1248" class="Bound">R</a><a id="1290" class="Symbol">}</a>
  <a id="1294" class="Keyword">where</a>

  <a id="1303" href="ring-theory.partial-sums-sequences-semirings.html#1303" class="Function">htpy-seq-sum-sequence-Semiring</a> <a id="1334" class="Symbol">:</a>
    <a id="1340" class="Symbol">(</a><a id="1341" href="ring-theory.partial-sums-sequences-semirings.html#1265" class="Bound">u</a> <a id="1343" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1345" href="ring-theory.partial-sums-sequences-semirings.html#1267" class="Bound">v</a><a id="1346" class="Symbol">)</a> <a id="1348" class="Symbol">→</a>
    <a id="1354" href="ring-theory.partial-sums-sequences-semirings.html#955" class="Function">seq-sum-sequence-Semiring</a> <a id="1380" href="ring-theory.partial-sums-sequences-semirings.html#1248" class="Bound">R</a> <a id="1382" href="ring-theory.partial-sums-sequences-semirings.html#1265" class="Bound">u</a> <a id="1384" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1386" href="ring-theory.partial-sums-sequences-semirings.html#955" class="Function">seq-sum-sequence-Semiring</a> <a id="1412" href="ring-theory.partial-sums-sequences-semirings.html#1248" class="Bound">R</a> <a id="1414" href="ring-theory.partial-sums-sequences-semirings.html#1267" class="Bound">v</a>
  <a id="1418" href="ring-theory.partial-sums-sequences-semirings.html#1303" class="Function">htpy-seq-sum-sequence-Semiring</a> <a id="1449" href="ring-theory.partial-sums-sequences-semirings.html#1449" class="Bound">H</a> <a id="1451" href="ring-theory.partial-sums-sequences-semirings.html#1451" class="Bound">n</a> <a id="1453" class="Symbol">=</a>
    <a id="1459" href="ring-theory.sums-of-finite-sequences-of-elements-semirings.html#2392" class="Function">htpy-sum-fin-sequence-type-Semiring</a>
      <a id="1501" class="Symbol">(</a> <a id="1503" href="ring-theory.partial-sums-sequences-semirings.html#1248" class="Bound">R</a><a id="1504" class="Symbol">)</a>
      <a id="1512" class="Symbol">(</a> <a id="1514" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1521" href="ring-theory.partial-sums-sequences-semirings.html#1451" class="Bound">n</a><a id="1522" class="Symbol">)</a>
      <a id="1530" class="Symbol">(</a> <a id="1532" href="lists.finite-sequences.html#5030" class="Function">htpy-fin-sequence-sequence</a> <a id="1559" href="ring-theory.partial-sums-sequences-semirings.html#1265" class="Bound">u</a> <a id="1561" href="ring-theory.partial-sums-sequences-semirings.html#1267" class="Bound">v</a> <a id="1563" href="ring-theory.partial-sums-sequences-semirings.html#1449" class="Bound">H</a> <a id="1565" class="Symbol">(</a><a id="1566" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1573" href="ring-theory.partial-sums-sequences-semirings.html#1451" class="Bound">n</a><a id="1574" class="Symbol">))</a>
</pre>