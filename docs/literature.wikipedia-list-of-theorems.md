# Wikipedia's list of theorems

On this page, we record formalized results in the agda-unimath library that are
on Wikipedia's
[list of theorems](https://en.wikipedia.org/wiki/List_of_theorems) or have a
Wikidata entry listed as an instance of a
[theorem](https://www.wikidata.org/wiki/Q65943). Additions to this list are very
welcome!

<pre class="Agda"><a id="346" class="Keyword">module</a> <a id="353" href="literature.wikipedia-list-of-theorems.html" class="Module">literature.wikipedia-list-of-theorems</a> <a id="391" class="Keyword">where</a>
</pre>
## Formalized theorems

The theorems are ordered alphabetically, omitting leading definite articles
("the").

### Bézout's lemma {#Q513028}

**Author:** [Bryan Lu](https://blu-bird.github.io)

<pre class="Agda"><a id="603" class="Keyword">open</a> <a id="608" class="Keyword">import</a> <a id="615" href="elementary-number-theory.bezouts-lemma-integers.html" class="Module">elementary-number-theory.bezouts-lemma-integers</a> <a id="663" class="Keyword">using</a>
  <a id="671" class="Symbol">(</a> <a id="673" href="elementary-number-theory.bezouts-lemma-integers.html#9652" class="Function">bezouts-lemma-ℤ</a><a id="688" class="Symbol">)</a>
<a id="690" class="Keyword">open</a> <a id="695" class="Keyword">import</a> <a id="702" href="elementary-number-theory.bezouts-lemma-natural-numbers.html" class="Module">elementary-number-theory.bezouts-lemma-natural-numbers</a> <a id="757" class="Keyword">using</a>
  <a id="765" class="Symbol">(</a> <a id="767" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#70534" class="Function">bezouts-lemma-ℕ</a><a id="782" class="Symbol">)</a>
</pre>
### Binomial theorem {#Q26708}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="888" class="Keyword">open</a> <a id="893" class="Keyword">import</a> <a id="900" href="commutative-algebra.binomial-theorem-commutative-rings.html" class="Module">commutative-algebra.binomial-theorem-commutative-rings</a> <a id="955" class="Keyword">using</a>
  <a id="963" class="Symbol">(</a> <a id="965" href="commutative-algebra.binomial-theorem-commutative-rings.html#4353" class="Function">binomial-theorem-Commutative-Ring</a><a id="998" class="Symbol">)</a>
<a id="1000" class="Keyword">open</a> <a id="1005" class="Keyword">import</a> <a id="1012" href="commutative-algebra.binomial-theorem-commutative-semirings.html" class="Module">commutative-algebra.binomial-theorem-commutative-semirings</a> <a id="1071" class="Keyword">using</a>
  <a id="1079" class="Symbol">(</a> <a id="1081" href="commutative-algebra.binomial-theorem-commutative-semirings.html#4543" class="Function">binomial-theorem-Commutative-Semiring</a><a id="1118" class="Symbol">)</a>
<a id="1120" class="Keyword">open</a> <a id="1125" class="Keyword">import</a> <a id="1132" href="ring-theory.binomial-theorem-rings.html" class="Module">ring-theory.binomial-theorem-rings</a> <a id="1167" class="Keyword">using</a>
  <a id="1175" class="Symbol">(</a> <a id="1177" href="ring-theory.binomial-theorem-rings.html#3588" class="Function">binomial-theorem-Ring</a><a id="1198" class="Symbol">)</a>
<a id="1200" class="Keyword">open</a> <a id="1205" class="Keyword">import</a> <a id="1212" href="ring-theory.binomial-theorem-semirings.html" class="Module">ring-theory.binomial-theorem-semirings</a> <a id="1251" class="Keyword">using</a>
  <a id="1259" class="Symbol">(</a> <a id="1261" href="ring-theory.binomial-theorem-semirings.html#13317" class="Function">binomial-theorem-Semiring</a><a id="1286" class="Symbol">)</a>
<a id="1288" class="Keyword">open</a> <a id="1293" class="Keyword">import</a> <a id="1300" href="elementary-number-theory.binomial-theorem-integers.html" class="Module">elementary-number-theory.binomial-theorem-integers</a> <a id="1351" class="Keyword">using</a>
  <a id="1359" class="Symbol">(</a> <a id="1361" href="elementary-number-theory.binomial-theorem-integers.html#2836" class="Function">binomial-theorem-ℤ</a><a id="1379" class="Symbol">)</a>
<a id="1381" class="Keyword">open</a> <a id="1386" class="Keyword">import</a> <a id="1393" href="elementary-number-theory.binomial-theorem-natural-numbers.html" class="Module">elementary-number-theory.binomial-theorem-natural-numbers</a> <a id="1451" class="Keyword">using</a>
  <a id="1459" class="Symbol">(</a> <a id="1461" href="elementary-number-theory.binomial-theorem-natural-numbers.html#2929" class="Function">binomial-theorem-ℕ</a><a id="1479" class="Symbol">)</a>
</pre>
### Cantor–Schröder–Bernstein theorem {#Q1033910}

**Author:** [Elif Uskuplu](https://elifuskuplu.github.io)

**Note:** The formalization of the Cantor-Schröder-Bernstein theorem in
agda-unimath is a generalization of the statement to all types, i.e., it is not
restricted to sets. This generalization is originally due to Martin-Escardó,
hence we refer to the generalization as the Cantor-Schröder-Bernstein-Escardó
theorem.

<pre class="Agda"><a id="1921" class="Keyword">open</a> <a id="1926" class="Keyword">import</a> <a id="1933" href="foundation.cantor-schroder-bernstein-escardo.html" class="Module">foundation.cantor-schroder-bernstein-escardo</a> <a id="1978" class="Keyword">using</a>
  <a id="1986" class="Symbol">(</a> <a id="1988" href="foundation.cantor-schroder-bernstein-escardo.html#6045" class="Function">Cantor-Schröder-Bernstein-Escardó</a> <a id="2022" class="Symbol">;</a>
    <a id="2028" href="foundation.cantor-schroder-bernstein-escardo.html#6399" class="Function">Cantor-Schröder-Bernstein</a><a id="2053" class="Symbol">)</a>
</pre>
### Cantor's theorem {#Q474881}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="2160" class="Keyword">open</a> <a id="2165" class="Keyword">import</a> <a id="2172" href="foundation.cantors-theorem.html" class="Module">foundation.cantors-theorem</a> <a id="2199" class="Keyword">using</a>
  <a id="2207" class="Symbol">(</a> <a id="2209" href="foundation.cantors-theorem.html#2668" class="Function">theorem-Cantor</a><a id="2223" class="Symbol">)</a>
</pre>
### Cayley's theorem {#Q179208}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="2330" class="Keyword">open</a> <a id="2335" class="Keyword">import</a> <a id="2342" href="group-theory.cayleys-theorem.html" class="Module">group-theory.cayleys-theorem</a> <a id="2371" class="Keyword">using</a>
  <a id="2379" class="Symbol">(</a> <a id="2381" href="group-theory.cayleys-theorem.html#1939" class="Function">Cayleys-theorem</a><a id="2396" class="Symbol">)</a>
</pre>
### Diaconescu's theorem {#Q3527059}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

<pre class="Agda"><a id="2524" class="Keyword">open</a> <a id="2529" class="Keyword">import</a> <a id="2536" href="foundation.diaconescus-theorem.html" class="Module">foundation.diaconescus-theorem</a> <a id="2567" class="Keyword">using</a>
  <a id="2575" class="Symbol">(</a> <a id="2577" href="foundation.diaconescus-theorem.html#3012" class="Function">theorem-Diaconescu</a><a id="2595" class="Symbol">)</a>
</pre>
### Euclid's theorem {#Q1506253}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="2703" class="Keyword">open</a> <a id="2708" class="Keyword">import</a> <a id="2715" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a> <a id="2761" class="Keyword">using</a>
  <a id="2769" class="Symbol">(</a> <a id="2771" href="elementary-number-theory.infinitude-of-primes.html#5223" class="Function">infinitude-of-primes-ℕ</a><a id="2793" class="Symbol">)</a>
</pre>
### Fundamental theorem of arithmetic {#Q670235}

**Author:** [Victor Blanchi](https://github.com/VictorBlanchi)

<pre class="Agda"><a id="2922" class="Keyword">open</a> <a id="2927" class="Keyword">import</a> <a id="2934" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html" class="Module">elementary-number-theory.fundamental-theorem-of-arithmetic</a> <a id="2993" class="Keyword">using</a>
  <a id="3001" class="Symbol">(</a> <a id="3003" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#33687" class="Function">fundamental-theorem-arithmetic-list-ℕ</a><a id="3040" class="Symbol">)</a>
</pre>
### Fundamental theorem of equivalence relations

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="3164" class="Keyword">open</a> <a id="3169" class="Keyword">import</a> <a id="3176" href="foundation.fundamental-theorem-of-equivalence-relations.html" class="Module">foundation.fundamental-theorem-of-equivalence-relations</a> <a id="3232" class="Keyword">using</a>
  <a id="3240" class="Symbol">(</a> <a id="3242" href="foundation.fundamental-theorem-of-equivalence-relations.html#13964" class="Function">equiv-equivalence-relation-partition</a><a id="3278" class="Symbol">)</a>
</pre>
### Kleene's fixed point theorem {#Q3527263}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

<pre class="Agda"><a id="3414" class="Keyword">open</a> <a id="3419" class="Keyword">import</a> <a id="3426" href="domain-theory.kleenes-fixed-point-theorem-posets.html" class="Module">domain-theory.kleenes-fixed-point-theorem-posets</a> <a id="3475" class="Keyword">using</a>
  <a id="3483" class="Symbol">(</a> <a id="3485" href="domain-theory.kleenes-fixed-point-theorem-posets.html#10861" class="Function">is-least-fixed-point-theorem-kleene-hom-Poset</a> <a id="3531" class="Symbol">;</a>
    <a id="3537" href="domain-theory.kleenes-fixed-point-theorem-posets.html#11994" class="Function">is-least-fixed-point-theorem-kleene-Poset</a><a id="3578" class="Symbol">)</a>
<a id="3580" class="Keyword">open</a> <a id="3585" class="Keyword">import</a> <a id="3592" href="domain-theory.kleenes-fixed-point-theorem-omega-complete-posets.html" class="Module">domain-theory.kleenes-fixed-point-theorem-omega-complete-posets</a> <a id="3656" class="Keyword">using</a>
  <a id="3664" class="Symbol">(</a> <a id="3666" href="domain-theory.kleenes-fixed-point-theorem-omega-complete-posets.html#8951" class="Function">is-least-fixed-point-theorem-kleene-hom-ω-Complete-Poset</a> <a id="3723" class="Symbol">;</a>
    <a id="3729" href="domain-theory.kleenes-fixed-point-theorem-omega-complete-posets.html#10248" class="Function">is-least-fixed-point-theorem-kleene-ω-Complete-Poset</a><a id="3781" class="Symbol">)</a>
</pre>
### Knaster–Tarski fixed point theorem {#Q609612}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

<pre class="Agda"><a id="3922" class="Keyword">open</a> <a id="3927" class="Keyword">import</a> <a id="3934" href="order-theory.knaster-tarski-fixed-point-theorem.html" class="Module">order-theory.knaster-tarski-fixed-point-theorem</a> <a id="3982" class="Keyword">using</a>
  <a id="3990" class="Symbol">(</a> <a id="3992" href="order-theory.knaster-tarski-fixed-point-theorem.html#6233" class="Function">least-fixed-point-knaster-tarski-Inflattice</a> <a id="4036" class="Symbol">;</a>
    <a id="4042" href="order-theory.knaster-tarski-fixed-point-theorem.html#3478" class="Function">greatest-fixed-point-knaster-tarski-Suplattice</a><a id="4088" class="Symbol">)</a>
</pre>
### Lawvere's fixed point theorem {#Q15809744}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

<pre class="Agda"><a id="4210" class="Keyword">open</a> <a id="4215" class="Keyword">import</a> <a id="4222" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a> <a id="4262" class="Keyword">using</a>
  <a id="4270" class="Symbol">(</a> <a id="4272" href="foundation.lawveres-fixed-point-theorem.html#903" class="Function">fixed-point-theorem-Lawvere</a><a id="4299" class="Symbol">)</a>
</pre>
### Yoneda lemma {#Q320577}

**Author:** [Emily Riehl](https://emilyriehl.github.io/)

<pre class="Agda"><a id="4401" class="Keyword">open</a> <a id="4406" class="Keyword">import</a> <a id="4413" href="category-theory.yoneda-lemma-categories.html" class="Module">category-theory.yoneda-lemma-categories</a> <a id="4453" class="Keyword">using</a>
  <a id="4461" class="Symbol">(</a> <a id="4463" href="category-theory.yoneda-lemma-categories.html#3114" class="Function">lemma-yoneda-Category</a><a id="4484" class="Symbol">)</a>
<a id="4486" class="Keyword">open</a> <a id="4491" class="Keyword">import</a> <a id="4498" href="category-theory.yoneda-lemma-precategories.html" class="Module">category-theory.yoneda-lemma-precategories</a> <a id="4541" class="Keyword">using</a>
  <a id="4549" class="Symbol">(</a> <a id="4551" href="category-theory.yoneda-lemma-precategories.html#4571" class="Function">lemma-yoneda-Precategory</a><a id="4575" class="Symbol">)</a>
</pre>
## External links

- [List of theorems](https://en.wikipedia.org/wiki/List_of_theorems) on
  Wikipedia
- The [1000plus project](https://github.com/1000-plus)'s
  [_1000+ theorems_](https://1000-plus.github.io/) aims to record formalized
  results from Wikipedia's list of theorems in the 6 proof assistants Isabelle,
  HOL Light, Coq/Rocq, Lean, Metamath, and Mizar.
