# Telephone numbers

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="elementary-number-theory.telephone-numbers.html" class="Module">elementary-number-theory.telephone-numbers</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
</pre>
</details>

## Idea

The
{{#concept "telephone numbers" WD="Telephone number" WDID=Q7696507 Agda=telephone-number}}
are a sequence of natural numbers that count the way `n` telephone lines can be
connected to each other, where each line can be connected to at most one other
line. They also occur in several other combinatorics problems.

## Definitions

<pre class="Agda"><a id="telephone-number"></a><a id="687" href="elementary-number-theory.telephone-numbers.html#687" class="Function">telephone-number</a> <a id="704" class="Symbol">:</a> <a id="706" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="708" class="Symbol">→</a> <a id="710" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="712" href="elementary-number-theory.telephone-numbers.html#687" class="Function">telephone-number</a> <a id="729" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="736" class="Symbol">=</a> <a id="738" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="745" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a>
<a id="752" href="elementary-number-theory.telephone-numbers.html#687" class="Function">telephone-number</a> <a id="769" class="Symbol">(</a><a id="770" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="777" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="783" class="Symbol">)</a> <a id="785" class="Symbol">=</a> <a id="787" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="794" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a>
<a id="801" href="elementary-number-theory.telephone-numbers.html#687" class="Function">telephone-number</a> <a id="818" class="Symbol">(</a><a id="819" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="826" class="Symbol">(</a><a id="827" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="834" href="elementary-number-theory.telephone-numbers.html#834" class="Bound">n</a><a id="835" class="Symbol">))</a> <a id="838" class="Symbol">=</a>
  <a id="842" class="Symbol">(</a><a id="843" href="elementary-number-theory.telephone-numbers.html#687" class="Function">telephone-number</a> <a id="860" class="Symbol">(</a><a id="861" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="868" href="elementary-number-theory.telephone-numbers.html#834" class="Bound">n</a><a id="869" class="Symbol">))</a> <a id="872" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="875" class="Symbol">((</a><a id="877" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="884" href="elementary-number-theory.telephone-numbers.html#834" class="Bound">n</a><a id="885" class="Symbol">)</a> <a id="887" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="890" class="Symbol">(</a><a id="891" href="elementary-number-theory.telephone-numbers.html#687" class="Function">telephone-number</a> <a id="908" href="elementary-number-theory.telephone-numbers.html#834" class="Bound">n</a><a id="909" class="Symbol">))</a>
</pre>