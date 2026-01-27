# Introduction to homotopy type theory

This file collects references to formalization of constructions, propositions,
theorems and exercises from {{#cite Rij22}}.

<pre class="Agda"><a id="174" class="Keyword">module</a> <a id="181" href="literature.introduction-to-homotopy-type-theory.html" class="Module">literature.introduction-to-homotopy-type-theory</a> <a id="229" class="Keyword">where</a>

<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
The first two sections introduce the metatheory of dependent type theories,
which correspond to built-in features of Agda.

## 3 The natural numbers

### 3.1 The formal specification of the type of natural numbers

<pre class="Agda"><a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a> <a id="556" class="Keyword">using</a>
  <a id="564" class="Symbol">(</a> <a id="566" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="568" class="Comment">-- the ℕ formation rule ⊢ ℕ type</a>
  <a id="603" class="Symbol">;</a> <a id="605" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="612" class="Comment">-- the zero element</a>
  <a id="634" class="Symbol">;</a> <a id="636" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="643" class="Comment">-- the successor function</a>
  <a id="671" class="Symbol">;</a> <a id="673" href="elementary-number-theory.natural-numbers.html#2052" class="Function">ind-ℕ</a> <a id="679" class="Comment">-- the induction principle</a>
  <a id="708" class="Symbol">)</a>
</pre>
### 3.2 Addition on the natural numbers

**Definition 3.2.1.** Addition on the natural numbers.

<pre class="Agda"><a id="820" class="Keyword">open</a> <a id="825" class="Keyword">import</a> <a id="832" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a> <a id="882" class="Keyword">using</a>
  <a id="890" class="Symbol">(</a> <a id="892" href="elementary-number-theory.addition-natural-numbers.html#819" class="Function">add-ℕ</a> <a id="898" class="Symbol">;</a> <a id="900" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">_+ℕ_</a><a id="904" class="Symbol">)</a>
</pre>
### 3.3 Pattern matching

<pre class="Agda"><a id="945" class="Keyword">open</a> <a id="950" class="Keyword">import</a> <a id="957" href="elementary-number-theory.fibonacci-sequence.html" class="Module">elementary-number-theory.fibonacci-sequence</a> <a id="1001" class="Keyword">using</a>
  <a id="1009" class="Symbol">(</a> <a id="1011" href="elementary-number-theory.fibonacci-sequence.html#1381" class="Function">Fibonacci-ℕ</a><a id="1022" class="Symbol">)</a>
</pre>
### Exercises

**Exercise 3.1.** Multiplication and exponentiation.

<pre class="Agda"><a id="1106" class="Comment">-- (a)</a>
<a id="1113" class="Keyword">open</a> <a id="1118" class="Keyword">import</a> <a id="1125" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a> <a id="1181" class="Keyword">using</a>
  <a id="1189" class="Symbol">(</a> <a id="1191" href="elementary-number-theory.multiplication-natural-numbers.html#1312" class="Function">mul-ℕ</a> <a id="1197" class="Symbol">;</a> <a id="1199" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">_*ℕ_</a><a id="1203" class="Symbol">)</a>

<a id="1206" class="Comment">-- (b)</a>
<a id="1213" class="Keyword">open</a> <a id="1218" class="Keyword">import</a> <a id="1225" href="elementary-number-theory.exponentiation-natural-numbers.html" class="Module">elementary-number-theory.exponentiation-natural-numbers</a> <a id="1281" class="Keyword">using</a>
  <a id="1289" class="Symbol">(</a> <a id="1291" href="elementary-number-theory.exponentiation-natural-numbers.html#927" class="Function">exp-ℕ</a><a id="1296" class="Symbol">)</a>
</pre>
**Exercise 3.2.** Minimum and maximum.

<pre class="Agda"><a id="1351" class="Keyword">open</a> <a id="1356" class="Keyword">import</a> <a id="1363" href="elementary-number-theory.minimum-natural-numbers.html" class="Module">elementary-number-theory.minimum-natural-numbers</a> <a id="1412" class="Keyword">using</a>
  <a id="1420" class="Symbol">(</a> <a id="1422" href="elementary-number-theory.minimum-natural-numbers.html#932" class="Function">min-ℕ</a><a id="1427" class="Symbol">)</a>
<a id="1429" class="Keyword">open</a> <a id="1434" class="Keyword">import</a> <a id="1441" href="elementary-number-theory.maximum-natural-numbers.html" class="Module">elementary-number-theory.maximum-natural-numbers</a> <a id="1490" class="Keyword">using</a>
  <a id="1498" class="Symbol">(</a> <a id="1500" href="elementary-number-theory.maximum-natural-numbers.html#958" class="Function">max-ℕ</a><a id="1505" class="Symbol">)</a>
</pre>
**Exercise 3.3.** Triangular numbers and factorial.

<pre class="Agda"><a id="1573" class="Comment">-- (a)</a>
<a id="1580" class="Keyword">open</a> <a id="1585" class="Keyword">import</a> <a id="1592" href="elementary-number-theory.triangular-numbers.html" class="Module">elementary-number-theory.triangular-numbers</a> <a id="1636" class="Keyword">using</a>
  <a id="1644" class="Symbol">(</a> <a id="1646" href="elementary-number-theory.triangular-numbers.html#1223" class="Function">triangular-number-ℕ</a><a id="1665" class="Symbol">)</a>

<a id="1668" class="Comment">-- (b)</a>
<a id="1675" class="Keyword">open</a> <a id="1680" class="Keyword">import</a> <a id="1687" href="elementary-number-theory.factorials.html" class="Module">elementary-number-theory.factorials</a> <a id="1723" class="Keyword">using</a>
  <a id="1731" class="Symbol">(</a> <a id="1733" href="elementary-number-theory.factorials.html#823" class="Function">factorial-ℕ</a><a id="1744" class="Symbol">)</a>
</pre>
**Exercise 3.4.** Binomial coefficients.

<pre class="Agda"><a id="1801" class="Keyword">open</a> <a id="1806" class="Keyword">import</a> <a id="1813" href="elementary-number-theory.binomial-coefficients.html" class="Module">elementary-number-theory.binomial-coefficients</a> <a id="1860" class="Keyword">using</a>
  <a id="1868" class="Symbol">(</a> <a id="1870" href="elementary-number-theory.binomial-coefficients.html#1394" class="Function">binomial-coefficient-ℕ</a>
  <a id="1895" class="Symbol">;</a> <a id="1897" href="elementary-number-theory.binomial-coefficients.html#1981" class="Function">is-zero-binomial-coefficient-ℕ</a><a id="1927" class="Symbol">)</a>
</pre>
**Exercise 3.5.** Fibonacci sequence using the induction principle of natural
numbers.

<pre class="Agda"><a id="2030" class="Keyword">open</a> <a id="2035" class="Keyword">import</a> <a id="2042" href="elementary-number-theory.fibonacci-sequence.html" class="Module">elementary-number-theory.fibonacci-sequence</a> <a id="2086" class="Keyword">using</a>
  <a id="2094" class="Symbol">(</a> <a id="2096" href="elementary-number-theory.fibonacci-sequence.html#2929" class="Function">Fibo</a><a id="2100" class="Symbol">)</a>
</pre>
**Exercise 3.6.** Division by two using pattern matching and induction.

<pre class="Agda"><a id="div-two-pattern-match"></a><a id="2188" href="literature.introduction-to-homotopy-type-theory.html#2188" class="Function">div-two-pattern-match</a> <a id="2210" class="Symbol">:</a> <a id="2212" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2214" class="Symbol">→</a> <a id="2216" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="2218" href="literature.introduction-to-homotopy-type-theory.html#2188" class="Function">div-two-pattern-match</a> <a id="2240" class="Number">0</a> <a id="2242" class="Symbol">=</a> <a id="2244" class="Number">0</a>
<a id="2246" href="literature.introduction-to-homotopy-type-theory.html#2188" class="Function">div-two-pattern-match</a> <a id="2268" class="Number">1</a> <a id="2270" class="Symbol">=</a> <a id="2272" class="Number">0</a>
<a id="2274" href="literature.introduction-to-homotopy-type-theory.html#2188" class="Function">div-two-pattern-match</a> <a id="2296" class="Symbol">(</a><a id="2297" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2304" class="Symbol">(</a><a id="2305" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2312" href="literature.introduction-to-homotopy-type-theory.html#2312" class="Bound">n</a><a id="2313" class="Symbol">))</a> <a id="2316" class="Symbol">=</a> <a id="2318" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2325" class="Symbol">(</a><a id="2326" href="literature.introduction-to-homotopy-type-theory.html#2188" class="Function">div-two-pattern-match</a> <a id="2348" href="literature.introduction-to-homotopy-type-theory.html#2312" class="Bound">n</a><a id="2349" class="Symbol">)</a>
</pre>
For the definition using the induction principle, we think of iterating the
swapping operation `(m, 0) ↦ (m, 1) ; (m, 1) ↦ (m + 1, 0)`, using the same
encoding of pairs with functions as the definition of the Fibonacci sequence.

<pre class="Agda"><a id="2594" class="Keyword">open</a> <a id="2599" class="Keyword">import</a> <a id="2606" href="elementary-number-theory.fibonacci-sequence.html" class="Module">elementary-number-theory.fibonacci-sequence</a> <a id="2650" class="Keyword">using</a>
  <a id="2658" class="Symbol">(</a> <a id="2660" href="elementary-number-theory.fibonacci-sequence.html#2525" class="Function">shift-one</a> <a id="2670" class="Symbol">;</a> <a id="2672" href="elementary-number-theory.fibonacci-sequence.html#2598" class="Function">shift-two</a><a id="2681" class="Symbol">)</a>

<a id="div-two-induction-step"></a><a id="2684" href="literature.introduction-to-homotopy-type-theory.html#2684" class="Function">div-two-induction-step</a> <a id="2707" class="Symbol">:</a> <a id="2709" class="Symbol">(</a><a id="2710" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2712" class="Symbol">→</a> <a id="2714" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2715" class="Symbol">)</a> <a id="2717" class="Symbol">→</a> <a id="2719" class="Symbol">(</a><a id="2720" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2722" class="Symbol">→</a> <a id="2724" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2725" class="Symbol">)</a>
<a id="2727" href="literature.introduction-to-homotopy-type-theory.html#2684" class="Function">div-two-induction-step</a> <a id="2750" href="literature.introduction-to-homotopy-type-theory.html#2750" class="Bound">f</a> <a id="2752" class="Symbol">=</a>
  <a id="2756" href="elementary-number-theory.natural-numbers.html#2052" class="Function">ind-ℕ</a>
    <a id="2766" class="Symbol">(</a> <a id="2768" href="elementary-number-theory.fibonacci-sequence.html#2525" class="Function">shift-one</a> <a id="2778" class="Symbol">(</a><a id="2779" href="literature.introduction-to-homotopy-type-theory.html#2750" class="Bound">f</a> <a id="2781" class="Number">0</a><a id="2782" class="Symbol">)</a> <a id="2784" class="Symbol">(λ</a> <a id="2787" href="literature.introduction-to-homotopy-type-theory.html#2787" class="Bound">_</a> <a id="2789" class="Symbol">→</a> <a id="2791" class="Number">1</a><a id="2792" class="Symbol">))</a>
    <a id="2799" class="Symbol">(</a> <a id="2801" class="Symbol">λ</a> <a id="2803" href="literature.introduction-to-homotopy-type-theory.html#2803" class="Bound">_</a> <a id="2805" href="literature.introduction-to-homotopy-type-theory.html#2805" class="Bound">_</a> <a id="2807" class="Symbol">→</a> <a id="2809" href="elementary-number-theory.fibonacci-sequence.html#2525" class="Function">shift-one</a> <a id="2819" class="Symbol">(</a><a id="2820" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2827" class="Symbol">(</a><a id="2828" href="literature.introduction-to-homotopy-type-theory.html#2750" class="Bound">f</a> <a id="2830" class="Number">0</a><a id="2831" class="Symbol">))</a> <a id="2834" class="Symbol">(λ</a> <a id="2837" href="literature.introduction-to-homotopy-type-theory.html#2837" class="Bound">_</a> <a id="2839" class="Symbol">→</a> <a id="2841" class="Number">0</a><a id="2842" class="Symbol">))</a>
    <a id="2849" class="Symbol">(</a> <a id="2851" href="literature.introduction-to-homotopy-type-theory.html#2750" class="Bound">f</a> <a id="2853" class="Number">1</a><a id="2854" class="Symbol">)</a>

<a id="div-two-induction-zero"></a><a id="2857" href="literature.introduction-to-homotopy-type-theory.html#2857" class="Function">div-two-induction-zero</a> <a id="2880" class="Symbol">:</a> <a id="2882" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2884" class="Symbol">→</a> <a id="2886" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="2888" href="literature.introduction-to-homotopy-type-theory.html#2857" class="Function">div-two-induction-zero</a> <a id="2911" class="Symbol">=</a> <a id="2913" class="Symbol">λ</a> <a id="2915" href="literature.introduction-to-homotopy-type-theory.html#2915" class="Bound">_</a> <a id="2917" class="Symbol">→</a> <a id="2919" class="Number">0</a>

<a id="div-two-induction-function"></a><a id="2922" href="literature.introduction-to-homotopy-type-theory.html#2922" class="Function">div-two-induction-function</a> <a id="2949" class="Symbol">:</a> <a id="2951" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2953" class="Symbol">→</a> <a id="2955" class="Symbol">(</a><a id="2956" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2958" class="Symbol">→</a> <a id="2960" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2961" class="Symbol">)</a>
<a id="2963" href="literature.introduction-to-homotopy-type-theory.html#2922" class="Function">div-two-induction-function</a> <a id="2990" class="Symbol">=</a>
  <a id="2994" href="elementary-number-theory.natural-numbers.html#2052" class="Function">ind-ℕ</a>
    <a id="3004" class="Symbol">(</a> <a id="3006" href="literature.introduction-to-homotopy-type-theory.html#2857" class="Function">div-two-induction-zero</a><a id="3028" class="Symbol">)</a>
    <a id="3034" class="Symbol">(</a> <a id="3036" class="Symbol">λ</a> <a id="3038" href="literature.introduction-to-homotopy-type-theory.html#3038" class="Bound">_</a> <a id="3040" class="Symbol">→</a> <a id="3042" href="literature.introduction-to-homotopy-type-theory.html#2684" class="Function">div-two-induction-step</a><a id="3064" class="Symbol">)</a>

<a id="div-two-induction"></a><a id="3067" href="literature.introduction-to-homotopy-type-theory.html#3067" class="Function">div-two-induction</a> <a id="3085" class="Symbol">:</a> <a id="3087" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="3089" class="Symbol">→</a> <a id="3091" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="3093" href="literature.introduction-to-homotopy-type-theory.html#3067" class="Function">div-two-induction</a> <a id="3111" href="literature.introduction-to-homotopy-type-theory.html#3111" class="Bound">n</a> <a id="3113" class="Symbol">=</a> <a id="3115" href="literature.introduction-to-homotopy-type-theory.html#2922" class="Function">div-two-induction-function</a> <a id="3142" href="literature.introduction-to-homotopy-type-theory.html#3111" class="Bound">n</a> <a id="3144" class="Number">0</a>
</pre>
## 4 More inductive types

### 4.2 The unit type

**Definition 4.2.1.** The unit type.

Note that the unit type in the library is defined as a _record_ type, as opposed
to an inductive type with one constructor. That allows us to have a judmental
eta law, which states that every element of the unit type is judgmentally equal
to `star`. This rule is not assumed in the book.

<pre class="Agda"><a id="3536" class="Keyword">open</a> <a id="3541" class="Keyword">import</a> <a id="3548" href="foundation.unit-type.html" class="Module">foundation.unit-type</a> <a id="3569" class="Keyword">using</a>
  <a id="3577" class="Symbol">(</a> <a id="3579" href="foundation.unit-type.html#950" class="Record">unit</a> <a id="3584" class="Comment">-- 𝟏</a>
  <a id="3591" class="Symbol">;</a> <a id="3593" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a> <a id="3598" class="Comment">-- ⋆</a>
  <a id="3605" class="Symbol">;</a> <a id="3607" href="foundation.unit-type.html#1086" class="Function">ind-unit</a>
  <a id="3618" class="Symbol">;</a> <a id="3620" href="foundation.unit-type.html#1422" class="Function">point</a> <a id="3626" class="Comment">-- pt</a>
  <a id="3634" class="Symbol">)</a>
</pre>
### 4.3 The empty type

**Definition 4.3.1.** The empty type.

<pre class="Agda"><a id="3712" class="Keyword">open</a> <a id="3717" class="Keyword">import</a> <a id="3724" href="foundation.empty-types.html" class="Module">foundation.empty-types</a> <a id="3747" class="Keyword">using</a>
  <a id="3755" class="Symbol">(</a> <a id="3757" href="foundation-core.empty-types.html#801" class="Datatype">empty</a> <a id="3763" class="Comment">-- ∅</a>
  <a id="3770" class="Symbol">;</a> <a id="3772" href="foundation-core.empty-types.html#825" class="Function">ind-empty</a>
  <a id="3784" class="Symbol">;</a> <a id="3786" href="foundation-core.empty-types.html#904" class="Function">ex-falso</a><a id="3794" class="Symbol">)</a>
</pre>
**Definition 4.3.2.** Negation of types.

<pre class="Agda"><a id="3851" class="Keyword">open</a> <a id="3856" class="Keyword">import</a> <a id="3863" href="foundation.negation.html" class="Module">foundation.negation</a> <a id="3883" class="Keyword">using</a>
  <a id="3891" class="Symbol">(</a> <a id="3893" href="foundation-core.negation.html#595" class="Function Operator">¬_</a><a id="3895" class="Symbol">)</a>
<a id="3897" class="Keyword">open</a> <a id="3902" class="Keyword">import</a> <a id="3909" href="foundation.empty-types.html" class="Module">foundation.empty-types</a> <a id="3932" class="Keyword">using</a>
  <a id="3940" class="Symbol">(</a> <a id="3942" href="foundation-core.empty-types.html#972" class="Function">is-empty</a><a id="3950" class="Symbol">)</a>
</pre>
**Proposition 4.3.4** Contrapositives.

<pre class="Agda"><a id="4005" class="Keyword">open</a> <a id="4010" class="Keyword">import</a> <a id="4017" href="foundation.negation.html" class="Module">foundation.negation</a> <a id="4037" class="Keyword">using</a>
  <a id="4045" class="Symbol">(</a> <a id="4047" href="foundation-core.negation.html#643" class="Function">map-neg</a><a id="4054" class="Symbol">)</a>
</pre>
### 4.4 Coproducts

**Definition 4.4.1.** Coproducts of types.

<pre class="Agda"><a id="4133" class="Keyword">open</a> <a id="4138" class="Keyword">import</a> <a id="4145" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a> <a id="4172" class="Keyword">using</a>
  <a id="4180" class="Symbol">(</a> <a id="4182" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">_+_</a>
  <a id="4188" class="Symbol">;</a> <a id="4190" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a>
  <a id="4196" class="Symbol">;</a> <a id="4198" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a>
  <a id="4204" class="Symbol">;</a> <a id="4206" href="foundation-core.coproduct-types.html#554" class="Function">ind-coproduct</a>
  <a id="4222" class="Symbol">;</a> <a id="4224" href="foundation-core.coproduct-types.html#837" class="Function">rec-coproduct</a><a id="4237" class="Symbol">)</a>
</pre>
**Remark 4.4.2.** Coproducts of functions.

<pre class="Agda"><a id="4296" class="Keyword">open</a> <a id="4301" class="Keyword">import</a> <a id="4308" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a> <a id="4349" class="Keyword">using</a>
  <a id="4357" class="Symbol">(</a> <a id="4359" href="foundation.functoriality-coproduct-types.html#2021" class="Function">map-coproduct</a> <a id="4373" class="Comment">-- f + g : A + B → A&#39; + B&#39;</a>
  <a id="4402" class="Symbol">)</a>
</pre>
**Proposition 4.4.3.** Projections from coproducts with an empty type.

<pre class="Agda"><a id="4489" class="Keyword">open</a> <a id="4494" class="Keyword">import</a> <a id="4501" href="foundation.type-arithmetic-empty-type.html" class="Module">foundation.type-arithmetic-empty-type</a> <a id="4539" class="Keyword">using</a>
  <a id="4547" class="Symbol">(</a> <a id="4549" href="foundation.type-arithmetic-empty-type.html#10422" class="Function">map-right-unit-law-coproduct-is-empty</a> <a id="4587" class="Comment">-- is-empty B → (A + B) → A</a>
  <a id="4617" class="Symbol">)</a>
</pre>
### 4.5 The type of integers

**Definition 4.5.1.** The integers.

<pre class="Agda"><a id="4699" class="Keyword">open</a> <a id="4704" class="Keyword">import</a> <a id="4711" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a> <a id="4745" class="Keyword">using</a>
  <a id="4753" class="Symbol">(</a> <a id="4755" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a>
  <a id="4759" class="Symbol">;</a> <a id="4761" href="elementary-number-theory.integers.html#1809" class="Function">in-pos-ℤ</a>
  <a id="4772" class="Symbol">;</a> <a id="4774" href="elementary-number-theory.integers.html#1405" class="Function">in-neg-ℤ</a>
  <a id="4785" class="Symbol">;</a> <a id="4787" href="elementary-number-theory.integers.html#1442" class="Function">neg-one-ℤ</a> <a id="4797" class="Comment">-- -1</a>
  <a id="4805" class="Symbol">;</a> <a id="4807" href="elementary-number-theory.integers.html#1569" class="Function">zero-ℤ</a> <a id="4814" class="Comment">-- 0</a>
  <a id="4821" class="Symbol">;</a> <a id="4823" href="elementary-number-theory.integers.html#1852" class="Function">one-ℤ</a> <a id="4829" class="Comment">-- 1</a>
  <a id="4836" class="Symbol">)</a>
</pre>
**Remark 4.5.2.** The induction principle of integers.

<pre class="Agda"><a id="4907" class="Keyword">open</a> <a id="4912" class="Keyword">import</a> <a id="4919" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a> <a id="4953" class="Keyword">using</a>
  <a id="4961" class="Symbol">(</a> <a id="4963" href="elementary-number-theory.integers.html#2258" class="Function">ind-ℤ</a><a id="4968" class="Symbol">)</a>
</pre>
**Definition 4.5.3.** The successor function on integers.

<pre class="Agda"><a id="5042" class="Keyword">open</a> <a id="5047" class="Keyword">import</a> <a id="5054" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a> <a id="5088" class="Keyword">using</a>
  <a id="5096" class="Symbol">(</a> <a id="5098" href="elementary-number-theory.integers.html#2848" class="Function">succ-ℤ</a><a id="5104" class="Symbol">)</a>
</pre>
### 4.6 Dependent pair types

**Definition 4.6.1.** The dependent pair type.

Note that similarly to the unit type, dependent pair types are defined as a
record and enjoy a judgmental eta law in the library.

<pre class="Agda"><a id="5328" class="Keyword">open</a> <a id="5333" class="Keyword">import</a> <a id="5340" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a> <a id="5372" class="Keyword">using</a>
  <a id="5380" class="Symbol">(</a> <a id="5382" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a>
  <a id="5386" class="Symbol">;</a> <a id="5388" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="5393" class="Symbol">;</a> <a id="5395" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">_,_</a>
  <a id="5401" class="Symbol">;</a> <a id="5403" href="foundation.dependent-pair-types.html#873" class="Function">ind-Σ</a><a id="5408" class="Symbol">)</a>
</pre>
**Definition 4.6.2.** Projection maps.

<pre class="Agda"><a id="5463" class="Keyword">open</a> <a id="5468" class="Keyword">import</a> <a id="5475" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a> <a id="5507" class="Keyword">using</a>
  <a id="5515" class="Symbol">(</a> <a id="5517" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>
  <a id="5523" class="Symbol">;</a> <a id="5525" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a><a id="5528" class="Symbol">)</a>
</pre>
**Remark 4.6.3.** Currying.

<pre class="Agda"><a id="5572" class="Keyword">open</a> <a id="5577" class="Keyword">import</a> <a id="5584" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a> <a id="5616" class="Keyword">using</a>
  <a id="5624" class="Symbol">(</a> <a id="5626" href="foundation.dependent-pair-types.html#1278" class="Function">ev-pair</a><a id="5633" class="Symbol">)</a>
</pre>
**Definition 4.6.4.** The cartesian product.

<pre class="Agda"><a id="5694" class="Keyword">open</a> <a id="5699" class="Keyword">import</a> <a id="5706" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a> <a id="5741" class="Keyword">using</a>
  <a id="5749" class="Symbol">(</a> <a id="5751" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">_×_</a>
  <a id="5757" class="Symbol">;</a> <a id="5759" href="foundation-core.cartesian-product-types.html#733" class="Function">ind-product</a><a id="5770" class="Symbol">)</a>
</pre>
### Exercises

**Exercise 4.1.** Predecessor, addition, negation and multiplication on
integers.

<pre class="Agda"><a id="5883" class="Comment">-- (a)</a>
<a id="5890" class="Keyword">open</a> <a id="5895" class="Keyword">import</a> <a id="5902" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a> <a id="5936" class="Keyword">using</a>
  <a id="5944" class="Symbol">(</a> <a id="5946" href="elementary-number-theory.integers.html#3001" class="Function">pred-ℤ</a><a id="5952" class="Symbol">)</a>

<a id="5955" class="Comment">-- (b)</a>
<a id="5962" class="Keyword">open</a> <a id="5967" class="Keyword">import</a> <a id="5974" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a> <a id="6017" class="Keyword">using</a>
  <a id="6025" class="Symbol">(</a> <a id="6027" href="elementary-number-theory.addition-integers.html#1312" class="Function">add-ℤ</a><a id="6032" class="Symbol">)</a>
<a id="6034" class="Keyword">open</a> <a id="6039" class="Keyword">import</a> <a id="6046" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a> <a id="6080" class="Keyword">using</a>
  <a id="6088" class="Symbol">(</a> <a id="6090" href="elementary-number-theory.integers.html#3345" class="Function">neg-ℤ</a><a id="6095" class="Symbol">)</a>

<a id="6098" class="Comment">-- (c)</a>
<a id="6105" class="Keyword">open</a> <a id="6110" class="Keyword">import</a> <a id="6117" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a> <a id="6166" class="Keyword">using</a>
  <a id="6174" class="Symbol">(</a> <a id="6176" href="elementary-number-theory.multiplication-integers.html#1728" class="Function">mul-ℤ</a><a id="6181" class="Symbol">)</a>
</pre>
**Exercise 4.2.** Boolean negation, conjunction and disjunction.

<pre class="Agda"><a id="6262" class="Keyword">open</a> <a id="6267" class="Keyword">import</a> <a id="6274" href="foundation.booleans.html" class="Module">foundation.booleans</a> <a id="6294" class="Keyword">using</a>
  <a id="6302" class="Symbol">(</a> <a id="6304" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="6311" class="Symbol">;</a> <a id="6313" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a>
  <a id="6321" class="Symbol">;</a> <a id="6323" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a>
  <a id="6330" class="Symbol">;</a> <a id="6332" href="foundation.booleans.html#1789" class="Function">ind-bool</a><a id="6340" class="Symbol">)</a>

<a id="6343" class="Comment">-- (a)</a>
<a id="6350" class="Keyword">open</a> <a id="6355" class="Keyword">import</a> <a id="6362" href="foundation.logical-operations-booleans.html" class="Module">foundation.logical-operations-booleans</a> <a id="6401" class="Keyword">using</a>
  <a id="6409" class="Symbol">(</a> <a id="6411" href="foundation.logical-operations-booleans.html#1428" class="Function">neg-bool</a><a id="6419" class="Symbol">)</a>

<a id="6422" class="Comment">-- (b)</a>
<a id="6429" class="Keyword">open</a> <a id="6434" class="Keyword">import</a> <a id="6441" href="foundation.logical-operations-booleans.html" class="Module">foundation.logical-operations-booleans</a> <a id="6480" class="Keyword">using</a>
  <a id="6488" class="Symbol">(</a> <a id="6490" href="foundation.logical-operations-booleans.html#1525" class="Function">and-bool</a><a id="6498" class="Symbol">)</a>

<a id="6501" class="Comment">-- (c)</a>
<a id="6508" class="Keyword">open</a> <a id="6513" class="Keyword">import</a> <a id="6520" href="foundation.logical-operations-booleans.html" class="Module">foundation.logical-operations-booleans</a> <a id="6559" class="Keyword">using</a>
  <a id="6567" class="Symbol">(</a> <a id="6569" href="foundation.logical-operations-booleans.html#1630" class="Function">or-bool</a><a id="6576" class="Symbol">)</a>
</pre>
**Exercise 4.3.** Double negation.

Note that we call bi-implications _logical equivalences_ in the library.

A type `X` for which we can show `¬¬X` is called _irrefutable_.

<pre class="Agda"><a id="6766" class="Keyword">open</a> <a id="6771" class="Keyword">import</a> <a id="6778" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a> <a id="6810" class="Keyword">using</a>
  <a id="6818" class="Symbol">(</a> <a id="6820" href="foundation.logical-equivalences.html#2096" class="Function Operator">_↔_</a><a id="6823" class="Symbol">)</a>

<a id="6826" class="Comment">-- (a)</a>
<a id="6833" href="literature.introduction-to-homotopy-type-theory.html#6833" class="Function">_</a> <a id="6835" class="Symbol">:</a> <a id="6837" class="Symbol">{</a><a id="6838" href="literature.introduction-to-homotopy-type-theory.html#6838" class="Bound">l</a> <a id="6840" class="Symbol">:</a> <a id="6842" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6847" class="Symbol">}</a> <a id="6849" class="Symbol">(</a><a id="6850" href="literature.introduction-to-homotopy-type-theory.html#6850" class="Bound">P</a> <a id="6852" class="Symbol">:</a> <a id="6854" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6857" href="literature.introduction-to-homotopy-type-theory.html#6838" class="Bound">l</a><a id="6858" class="Symbol">)</a> <a id="6860" class="Symbol">→</a> <a id="6862" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="6864" class="Symbol">(</a><a id="6865" href="literature.introduction-to-homotopy-type-theory.html#6850" class="Bound">P</a> <a id="6867" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="6869" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="6871" href="literature.introduction-to-homotopy-type-theory.html#6850" class="Bound">P</a><a id="6872" class="Symbol">)</a>
<a id="6874" class="Symbol">_</a> <a id="6876" class="Symbol">=</a> <a id="6878" class="Symbol">λ</a> <a id="6880" href="literature.introduction-to-homotopy-type-theory.html#6880" class="Bound">P</a> <a id="6882" class="Symbol">(</a><a id="6883" href="literature.introduction-to-homotopy-type-theory.html#6883" class="Bound">p</a> <a id="6885" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="6887" href="literature.introduction-to-homotopy-type-theory.html#6887" class="Bound">np</a><a id="6889" class="Symbol">)</a> <a id="6891" class="Symbol">→</a> <a id="6893" href="literature.introduction-to-homotopy-type-theory.html#6887" class="Bound">np</a> <a id="6896" href="literature.introduction-to-homotopy-type-theory.html#6883" class="Bound">p</a>
<a id="6898" class="Keyword">open</a> <a id="6903" class="Keyword">import</a> <a id="6910" href="foundation.negation.html" class="Module">foundation.negation</a> <a id="6930" class="Keyword">using</a>
  <a id="6938" class="Symbol">(</a> <a id="6940" href="foundation.negation.html#2085" class="Function">no-fixed-points-neg</a> <a id="6960" class="Comment">-- ¬(P ↔ ¬P)</a>
  <a id="6975" class="Symbol">)</a>

<a id="6978" class="Comment">-- (b)</a>
<a id="6985" class="Keyword">open</a> <a id="6990" class="Keyword">import</a> <a id="6997" href="foundation.double-negation.html" class="Module">foundation.double-negation</a> <a id="7024" class="Keyword">using</a>
  <a id="7032" class="Symbol">(</a> <a id="7034" href="foundation.double-negation.html#572" class="Function Operator">¬¬_</a>
  <a id="7040" class="Symbol">;</a> <a id="7042" href="foundation.double-negation.html#782" class="Function">intro-double-negation</a> <a id="7064" class="Comment">-- P → ¬¬P</a>
  <a id="7077" class="Symbol">;</a> <a id="7079" href="foundation.double-negation.html#873" class="Function">map-double-negation</a> <a id="7099" class="Comment">-- (P → Q) → (¬¬P → ¬¬Q)</a>
  <a id="7126" class="Symbol">;</a> <a id="7128" href="foundation.double-negation.html#2738" class="Function">extend-double-negation</a> <a id="7151" class="Comment">-- (P → ¬¬Q) → (¬¬P → ¬¬Q)</a>
  <a id="7180" class="Symbol">)</a>

<a id="7183" class="Comment">-- (c)</a>
<a id="7190" class="Keyword">open</a> <a id="7195" class="Keyword">import</a> <a id="7202" href="foundation.double-negation.html" class="Module">foundation.double-negation</a> <a id="7229" class="Keyword">using</a>
  <a id="7237" class="Symbol">(</a> <a id="7239" href="foundation.double-negation.html#1882" class="Function">double-negation-double-negation-elim</a> <a id="7276" class="Comment">-- ¬¬(¬¬P → P)</a>
  <a id="7293" class="Symbol">;</a> <a id="7295" href="foundation.double-negation.html#2111" class="Function">double-negation-Peirces-law</a> <a id="7323" class="Comment">-- ¬¬(((P → Q) → P) → P)</a>
  <a id="7350" class="Symbol">;</a> <a id="7352" href="foundation.double-negation.html#2334" class="Function">double-negation-linearity-implication</a> <a id="7390" class="Comment">-- ¬¬((P → Q) + (Q → P))</a>
  <a id="7417" class="Symbol">)</a>
<a id="7419" class="Keyword">open</a> <a id="7424" class="Keyword">import</a> <a id="7431" href="logic.irrefutable-types.html" class="Module">logic.irrefutable-types</a> <a id="7455" class="Keyword">using</a>
  <a id="7463" class="Symbol">(</a> <a id="7465" href="logic.irrefutable-types.html#3389" class="Function">is-irrefutable-is-decidable</a> <a id="7493" class="Comment">-- ¬¬(P + ¬P)</a>
  <a id="7509" class="Symbol">)</a>

<a id="7512" class="Comment">-- (d)</a>
<a id="7519" class="Keyword">open</a> <a id="7524" class="Keyword">import</a> <a id="7531" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a> <a id="7558" class="Keyword">using</a>
  <a id="7566" class="Symbol">(</a> <a id="7568" href="foundation.decidable-types.html#7806" class="Function">double-negation-elim-is-decidable</a> <a id="7602" class="Comment">-- (P + ¬P) → (¬¬P → P)</a>
  <a id="7628" class="Symbol">)</a>

<a id="7631" href="literature.introduction-to-homotopy-type-theory.html#7631" class="Function">_</a> <a id="7633" class="Symbol">:</a> <a id="7635" class="Symbol">{</a><a id="7636" href="literature.introduction-to-homotopy-type-theory.html#7636" class="Bound">l1</a> <a id="7639" href="literature.introduction-to-homotopy-type-theory.html#7639" class="Bound">l2</a> <a id="7642" class="Symbol">:</a> <a id="7644" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7649" class="Symbol">}</a> <a id="7651" class="Symbol">(</a><a id="7652" href="literature.introduction-to-homotopy-type-theory.html#7652" class="Bound">P</a> <a id="7654" class="Symbol">:</a> <a id="7656" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="7659" href="literature.introduction-to-homotopy-type-theory.html#7636" class="Bound">l1</a><a id="7661" class="Symbol">)</a> <a id="7663" class="Symbol">(</a><a id="7664" href="literature.introduction-to-homotopy-type-theory.html#7664" class="Bound">Q</a> <a id="7666" class="Symbol">:</a> <a id="7668" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="7671" href="literature.introduction-to-homotopy-type-theory.html#7639" class="Bound">l2</a><a id="7673" class="Symbol">)</a> <a id="7675" class="Symbol">→</a> <a id="7677" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="7680" class="Symbol">(</a><a id="7681" href="literature.introduction-to-homotopy-type-theory.html#7664" class="Bound">Q</a> <a id="7683" class="Symbol">→</a> <a id="7685" href="literature.introduction-to-homotopy-type-theory.html#7652" class="Bound">P</a><a id="7686" class="Symbol">)</a> <a id="7688" class="Symbol">→</a> <a id="7690" class="Symbol">((</a><a id="7692" href="literature.introduction-to-homotopy-type-theory.html#7652" class="Bound">P</a> <a id="7694" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="7696" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="7698" href="literature.introduction-to-homotopy-type-theory.html#7652" class="Bound">P</a><a id="7699" class="Symbol">)</a> <a id="7701" class="Symbol">→</a> <a id="7703" href="literature.introduction-to-homotopy-type-theory.html#7664" class="Bound">Q</a> <a id="7705" class="Symbol">→</a> <a id="7707" href="literature.introduction-to-homotopy-type-theory.html#7652" class="Bound">P</a><a id="7708" class="Symbol">)</a>
<a id="7710" class="Symbol">_</a> <a id="7712" class="Symbol">=</a>
  <a id="7716" class="Symbol">λ</a> <a id="7718" href="literature.introduction-to-homotopy-type-theory.html#7718" class="Bound">P</a> <a id="7720" href="literature.introduction-to-homotopy-type-theory.html#7720" class="Bound">Q</a> <a id="7722" href="literature.introduction-to-homotopy-type-theory.html#7722" class="Bound">nnqp</a> <a id="7727" class="Symbol">→</a>
    <a id="7733" href="foundation-core.coproduct-types.html#837" class="Function">rec-coproduct</a> <a id="7747" class="Symbol">(λ</a> <a id="7750" href="literature.introduction-to-homotopy-type-theory.html#7750" class="Bound">p</a> <a id="7752" href="literature.introduction-to-homotopy-type-theory.html#7752" class="Bound">q</a> <a id="7754" class="Symbol">→</a> <a id="7756" href="literature.introduction-to-homotopy-type-theory.html#7750" class="Bound">p</a><a id="7757" class="Symbol">)</a> <a id="7759" class="Symbol">(λ</a> <a id="7762" href="literature.introduction-to-homotopy-type-theory.html#7762" class="Bound">np</a> <a id="7765" href="literature.introduction-to-homotopy-type-theory.html#7765" class="Bound">q</a> <a id="7767" class="Symbol">→</a> <a id="7769" href="foundation-core.empty-types.html#904" class="Function">ex-falso</a> <a id="7778" class="Symbol">(</a><a id="7779" href="literature.introduction-to-homotopy-type-theory.html#7722" class="Bound">nnqp</a> <a id="7784" class="Symbol">(λ</a> <a id="7787" href="literature.introduction-to-homotopy-type-theory.html#7787" class="Bound">qp</a> <a id="7790" class="Symbol">→</a> <a id="7792" href="literature.introduction-to-homotopy-type-theory.html#7762" class="Bound">np</a> <a id="7795" class="Symbol">(</a><a id="7796" href="literature.introduction-to-homotopy-type-theory.html#7787" class="Bound">qp</a> <a id="7799" href="literature.introduction-to-homotopy-type-theory.html#7765" class="Bound">q</a><a id="7800" class="Symbol">))))</a>

<a id="7806" href="literature.introduction-to-homotopy-type-theory.html#7806" class="Function">_</a> <a id="7808" class="Symbol">:</a> <a id="7810" class="Symbol">{</a><a id="7811" href="literature.introduction-to-homotopy-type-theory.html#7811" class="Bound">l1</a> <a id="7814" href="literature.introduction-to-homotopy-type-theory.html#7814" class="Bound">l2</a> <a id="7817" class="Symbol">:</a> <a id="7819" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7824" class="Symbol">}</a> <a id="7826" class="Symbol">(</a><a id="7827" href="literature.introduction-to-homotopy-type-theory.html#7827" class="Bound">P</a> <a id="7829" class="Symbol">:</a> <a id="7831" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="7834" href="literature.introduction-to-homotopy-type-theory.html#7811" class="Bound">l1</a><a id="7836" class="Symbol">)</a> <a id="7838" class="Symbol">(</a><a id="7839" href="literature.introduction-to-homotopy-type-theory.html#7839" class="Bound">Q</a> <a id="7841" class="Symbol">:</a> <a id="7843" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="7846" href="literature.introduction-to-homotopy-type-theory.html#7814" class="Bound">l2</a><a id="7848" class="Symbol">)</a> <a id="7850" class="Symbol">→</a> <a id="7852" class="Symbol">((</a><a id="7854" href="literature.introduction-to-homotopy-type-theory.html#7827" class="Bound">P</a> <a id="7856" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="7858" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="7860" href="literature.introduction-to-homotopy-type-theory.html#7827" class="Bound">P</a><a id="7861" class="Symbol">)</a> <a id="7863" class="Symbol">→</a> <a id="7865" href="literature.introduction-to-homotopy-type-theory.html#7839" class="Bound">Q</a> <a id="7867" class="Symbol">→</a> <a id="7869" href="literature.introduction-to-homotopy-type-theory.html#7827" class="Bound">P</a><a id="7870" class="Symbol">)</a> <a id="7872" class="Symbol">→</a> <a id="7874" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="7877" class="Symbol">(</a><a id="7878" href="literature.introduction-to-homotopy-type-theory.html#7839" class="Bound">Q</a> <a id="7880" class="Symbol">→</a> <a id="7882" href="literature.introduction-to-homotopy-type-theory.html#7827" class="Bound">P</a><a id="7883" class="Symbol">)</a>
<a id="7885" class="Symbol">_</a> <a id="7887" class="Symbol">=</a>
  <a id="7891" class="Symbol">λ</a> <a id="7893" href="literature.introduction-to-homotopy-type-theory.html#7893" class="Bound">P</a> <a id="7895" href="literature.introduction-to-homotopy-type-theory.html#7895" class="Bound">Q</a> <a id="7897" href="literature.introduction-to-homotopy-type-theory.html#7897" class="Bound">pnpqp</a> <a id="7903" href="literature.introduction-to-homotopy-type-theory.html#7903" class="Bound">nqp</a> <a id="7907" class="Symbol">→</a>
    <a id="7913" class="Symbol">(</a> <a id="7915" class="Symbol">λ</a> <a id="7917" class="Symbol">(</a><a id="7918" href="literature.introduction-to-homotopy-type-theory.html#7918" class="Bound">np</a> <a id="7921" class="Symbol">:</a> <a id="7923" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="7925" href="literature.introduction-to-homotopy-type-theory.html#7893" class="Bound">P</a><a id="7926" class="Symbol">)</a> <a id="7928" class="Symbol">→</a> <a id="7930" href="literature.introduction-to-homotopy-type-theory.html#7903" class="Bound">nqp</a> <a id="7934" class="Symbol">(</a><a id="7935" href="literature.introduction-to-homotopy-type-theory.html#7897" class="Bound">pnpqp</a> <a id="7941" class="Symbol">(</a><a id="7942" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="7946" href="literature.introduction-to-homotopy-type-theory.html#7918" class="Bound">np</a><a id="7948" class="Symbol">)))</a>
    <a id="7956" class="Symbol">(</a> <a id="7958" class="Symbol">λ</a> <a id="7960" class="Symbol">(</a><a id="7961" href="literature.introduction-to-homotopy-type-theory.html#7961" class="Bound">p</a> <a id="7963" class="Symbol">:</a> <a id="7965" href="literature.introduction-to-homotopy-type-theory.html#7893" class="Bound">P</a><a id="7966" class="Symbol">)</a> <a id="7968" class="Symbol">→</a> <a id="7970" href="literature.introduction-to-homotopy-type-theory.html#7903" class="Bound">nqp</a> <a id="7974" class="Symbol">(λ</a> <a id="7977" href="literature.introduction-to-homotopy-type-theory.html#7977" class="Bound">_</a> <a id="7979" class="Symbol">→</a> <a id="7981" href="literature.introduction-to-homotopy-type-theory.html#7961" class="Bound">p</a><a id="7982" class="Symbol">))</a>

<a id="7986" class="Comment">-- (e)</a>
<a id="7993" class="Keyword">open</a> <a id="7998" class="Keyword">import</a> <a id="8005" href="logic.double-negation-elimination.html" class="Module">logic.double-negation-elimination</a> <a id="8039" class="Keyword">using</a>
  <a id="8047" class="Symbol">(</a> <a id="8049" href="logic.double-negation-elimination.html#4755" class="Function">double-negation-elim-neg</a> <a id="8074" class="Comment">-- ¬¬(¬ P) → P</a>
  <a id="8091" class="Symbol">;</a> <a id="8093" href="logic.double-negation-elimination.html#8246" class="Function">double-negation-elim-exp-neg-neg</a> <a id="8126" class="Comment">-- ¬¬(P → ¬¬Q) → (P → ¬¬Q)</a>
  <a id="8155" class="Symbol">;</a> <a id="8157" href="logic.double-negation-elimination.html#7310" class="Function">double-negation-elim-product</a>
  <a id="8188" class="Symbol">)</a>

<a id="8191" href="literature.introduction-to-homotopy-type-theory.html#8191" class="Function">_</a> <a id="8193" class="Symbol">:</a>
  <a id="8197" class="Symbol">{</a><a id="8198" href="literature.introduction-to-homotopy-type-theory.html#8198" class="Bound">l1</a> <a id="8201" href="literature.introduction-to-homotopy-type-theory.html#8201" class="Bound">l2</a> <a id="8204" class="Symbol">:</a> <a id="8206" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8211" class="Symbol">}</a> <a id="8213" class="Symbol">(</a><a id="8214" href="literature.introduction-to-homotopy-type-theory.html#8214" class="Bound">P</a> <a id="8216" class="Symbol">:</a> <a id="8218" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="8221" href="literature.introduction-to-homotopy-type-theory.html#8198" class="Bound">l1</a><a id="8223" class="Symbol">)</a> <a id="8225" class="Symbol">(</a><a id="8226" href="literature.introduction-to-homotopy-type-theory.html#8226" class="Bound">Q</a> <a id="8228" class="Symbol">:</a> <a id="8230" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="8233" href="literature.introduction-to-homotopy-type-theory.html#8201" class="Bound">l2</a><a id="8235" class="Symbol">)</a> <a id="8237" class="Symbol">→</a>
  <a id="8241" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8244" class="Symbol">((</a><a id="8246" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8249" href="literature.introduction-to-homotopy-type-theory.html#8214" class="Bound">P</a><a id="8250" class="Symbol">)</a> <a id="8252" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="8254" class="Symbol">(</a><a id="8255" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8258" href="literature.introduction-to-homotopy-type-theory.html#8226" class="Bound">Q</a><a id="8259" class="Symbol">))</a> <a id="8262" class="Symbol">→</a> <a id="8264" class="Symbol">(</a><a id="8265" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8268" href="literature.introduction-to-homotopy-type-theory.html#8214" class="Bound">P</a><a id="8269" class="Symbol">)</a> <a id="8271" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="8273" class="Symbol">(</a><a id="8274" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8277" href="literature.introduction-to-homotopy-type-theory.html#8226" class="Bound">Q</a><a id="8278" class="Symbol">)</a>
<a id="8280" class="Symbol">_</a> <a id="8282" class="Symbol">=</a>
  <a id="8286" class="Symbol">λ</a> <a id="8288" href="literature.introduction-to-homotopy-type-theory.html#8288" class="Bound">P</a> <a id="8290" href="literature.introduction-to-homotopy-type-theory.html#8290" class="Bound">Q</a> <a id="8292" class="Symbol">→</a>
    <a id="8298" href="logic.double-negation-elimination.html#7310" class="Function">double-negation-elim-product</a>
      <a id="8333" class="Symbol">(</a> <a id="8335" href="logic.double-negation-elimination.html#4755" class="Function">double-negation-elim-neg</a> <a id="8360" class="Symbol">(</a><a id="8361" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="8363" href="literature.introduction-to-homotopy-type-theory.html#8288" class="Bound">P</a><a id="8364" class="Symbol">))</a>
      <a id="8373" class="Symbol">(</a> <a id="8375" href="logic.double-negation-elimination.html#4755" class="Function">double-negation-elim-neg</a> <a id="8400" class="Symbol">(</a><a id="8401" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="8403" href="literature.introduction-to-homotopy-type-theory.html#8290" class="Bound">Q</a><a id="8404" class="Symbol">))</a>

<a id="8408" class="Comment">-- (f)</a>
<a id="8415" class="Keyword">open</a> <a id="8420" class="Keyword">import</a> <a id="8427" href="logic.irrefutable-types.html" class="Module">logic.irrefutable-types</a> <a id="8451" class="Keyword">using</a>
  <a id="8459" class="Symbol">(</a> <a id="8461" href="logic.irrefutable-types.html#4184" class="Function">is-irrefutable-product</a> <a id="8484" class="Comment">-- ¬¬A → ¬¬B → ¬¬(A × B)</a>
  <a id="8511" class="Symbol">)</a>

<a id="8514" class="Keyword">module</a> <a id="8521" href="literature.introduction-to-homotopy-type-theory.html#8521" class="Module">_</a>
  <a id="8525" class="Symbol">{</a><a id="8526" href="literature.introduction-to-homotopy-type-theory.html#8526" class="Bound">l1</a> <a id="8529" href="literature.introduction-to-homotopy-type-theory.html#8529" class="Bound">l2</a> <a id="8532" class="Symbol">:</a> <a id="8534" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8539" class="Symbol">}</a> <a id="8541" class="Symbol">{</a><a id="8542" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8544" class="Symbol">:</a> <a id="8546" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="8549" href="literature.introduction-to-homotopy-type-theory.html#8526" class="Bound">l1</a><a id="8551" class="Symbol">}</a> <a id="8553" class="Symbol">{</a><a id="8554" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a> <a id="8556" class="Symbol">:</a> <a id="8558" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="8561" href="literature.introduction-to-homotopy-type-theory.html#8529" class="Bound">l2</a><a id="8563" class="Symbol">}</a>
  <a id="8567" class="Keyword">where</a>
  <a id="8575" href="literature.introduction-to-homotopy-type-theory.html#8575" class="Function">_</a> <a id="8577" class="Symbol">:</a> <a id="8579" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8582" class="Symbol">(</a><a id="8583" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8585" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="8587" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="8588" class="Symbol">)</a> <a id="8590" class="Symbol">→</a> <a id="8592" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8595" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8597" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="8599" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8602" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a>
  <a id="8606" class="Symbol">_</a> <a id="8608" class="Symbol">=</a>
    <a id="8614" class="Symbol">λ</a> <a id="8616" href="literature.introduction-to-homotopy-type-theory.html#8616" class="Bound">nnpq</a> <a id="8621" class="Symbol">→</a> <a id="8623" class="Symbol">(λ</a> <a id="8626" href="literature.introduction-to-homotopy-type-theory.html#8626" class="Bound">np</a> <a id="8629" class="Symbol">→</a> <a id="8631" href="literature.introduction-to-homotopy-type-theory.html#8616" class="Bound">nnpq</a> <a id="8636" class="Symbol">(λ</a> <a id="8639" class="Symbol">(</a><a id="8640" href="literature.introduction-to-homotopy-type-theory.html#8640" class="Bound">p</a> <a id="8642" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="8644" href="literature.introduction-to-homotopy-type-theory.html#8644" class="Bound">q</a><a id="8645" class="Symbol">)</a> <a id="8647" class="Symbol">→</a> <a id="8649" href="literature.introduction-to-homotopy-type-theory.html#8626" class="Bound">np</a> <a id="8652" href="literature.introduction-to-homotopy-type-theory.html#8640" class="Bound">p</a><a id="8653" class="Symbol">))</a> <a id="8656" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="8658" class="Symbol">(λ</a> <a id="8661" href="literature.introduction-to-homotopy-type-theory.html#8661" class="Bound">nq</a> <a id="8664" class="Symbol">→</a> <a id="8666" href="literature.introduction-to-homotopy-type-theory.html#8616" class="Bound">nnpq</a> <a id="8671" class="Symbol">(λ</a> <a id="8674" class="Symbol">(</a><a id="8675" href="literature.introduction-to-homotopy-type-theory.html#8675" class="Bound">p</a> <a id="8677" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="8679" href="literature.introduction-to-homotopy-type-theory.html#8679" class="Bound">q</a><a id="8680" class="Symbol">)</a> <a id="8682" class="Symbol">→</a> <a id="8684" href="literature.introduction-to-homotopy-type-theory.html#8661" class="Bound">nq</a> <a id="8687" href="literature.introduction-to-homotopy-type-theory.html#8679" class="Bound">q</a><a id="8688" class="Symbol">))</a>

  <a id="8694" href="literature.introduction-to-homotopy-type-theory.html#8694" class="Function">_</a> <a id="8696" class="Symbol">:</a> <a id="8698" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8701" class="Symbol">(</a><a id="8702" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8704" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="8706" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="8707" class="Symbol">)</a> <a id="8709" class="Symbol">→</a> <a id="8711" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="8713" class="Symbol">(</a><a id="8714" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="8716" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8718" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="8720" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="8722" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="8723" class="Symbol">)</a>
  <a id="8727" class="Symbol">_</a> <a id="8729" class="Symbol">=</a>
    <a id="8735" class="Symbol">λ</a> <a id="8737" href="literature.introduction-to-homotopy-type-theory.html#8737" class="Bound">nnpq</a> <a id="8742" class="Symbol">(</a><a id="8743" href="literature.introduction-to-homotopy-type-theory.html#8743" class="Bound">np</a> <a id="8746" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="8748" href="literature.introduction-to-homotopy-type-theory.html#8748" class="Bound">nq</a><a id="8750" class="Symbol">)</a> <a id="8752" class="Symbol">→</a> <a id="8754" href="literature.introduction-to-homotopy-type-theory.html#8737" class="Bound">nnpq</a> <a id="8759" class="Symbol">(</a><a id="8760" href="foundation-core.coproduct-types.html#837" class="Function">rec-coproduct</a> <a id="8774" href="literature.introduction-to-homotopy-type-theory.html#8743" class="Bound">np</a> <a id="8777" href="literature.introduction-to-homotopy-type-theory.html#8748" class="Bound">nq</a><a id="8779" class="Symbol">)</a>
  <a id="8783" href="literature.introduction-to-homotopy-type-theory.html#8783" class="Function">_</a> <a id="8785" class="Symbol">:</a> <a id="8787" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="8789" class="Symbol">(</a><a id="8790" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="8792" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8794" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="8796" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="8798" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="8799" class="Symbol">)</a> <a id="8801" class="Symbol">→</a> <a id="8803" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8806" class="Symbol">(</a><a id="8807" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8809" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="8811" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="8812" class="Symbol">)</a>
  <a id="8816" class="Symbol">_</a> <a id="8818" class="Symbol">=</a> <a id="8820" class="Symbol">λ</a> <a id="8822" href="literature.introduction-to-homotopy-type-theory.html#8822" class="Bound">nnpnq</a> <a id="8828" href="literature.introduction-to-homotopy-type-theory.html#8828" class="Bound">npq</a> <a id="8832" class="Symbol">→</a> <a id="8834" href="literature.introduction-to-homotopy-type-theory.html#8822" class="Bound">nnpnq</a> <a id="8840" class="Symbol">((λ</a> <a id="8844" href="literature.introduction-to-homotopy-type-theory.html#8844" class="Bound">p</a> <a id="8846" class="Symbol">→</a> <a id="8848" href="literature.introduction-to-homotopy-type-theory.html#8828" class="Bound">npq</a> <a id="8852" class="Symbol">(</a><a id="8853" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="8857" href="literature.introduction-to-homotopy-type-theory.html#8844" class="Bound">p</a><a id="8858" class="Symbol">))</a> <a id="8861" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="8863" class="Symbol">(λ</a> <a id="8866" href="literature.introduction-to-homotopy-type-theory.html#8866" class="Bound">q</a> <a id="8868" class="Symbol">→</a> <a id="8870" href="literature.introduction-to-homotopy-type-theory.html#8828" class="Bound">npq</a> <a id="8874" class="Symbol">(</a><a id="8875" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="8879" href="literature.introduction-to-homotopy-type-theory.html#8866" class="Bound">q</a><a id="8880" class="Symbol">)))</a>

  <a id="8887" href="literature.introduction-to-homotopy-type-theory.html#8887" class="Function">_</a> <a id="8889" class="Symbol">:</a> <a id="8891" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8894" class="Symbol">(</a><a id="8895" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8897" class="Symbol">→</a> <a id="8899" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="8900" class="Symbol">)</a> <a id="8902" class="Symbol">→</a> <a id="8904" class="Symbol">(</a><a id="8905" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8908" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8910" class="Symbol">→</a> <a id="8912" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8915" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="8916" class="Symbol">)</a>
  <a id="8920" class="Symbol">_</a> <a id="8922" class="Symbol">=</a> <a id="8924" class="Symbol">λ</a> <a id="8926" href="literature.introduction-to-homotopy-type-theory.html#8926" class="Bound">nnpq</a> <a id="8931" href="literature.introduction-to-homotopy-type-theory.html#8931" class="Bound">nnp</a> <a id="8935" href="literature.introduction-to-homotopy-type-theory.html#8935" class="Bound">nq</a> <a id="8938" class="Symbol">→</a> <a id="8940" href="literature.introduction-to-homotopy-type-theory.html#8931" class="Bound">nnp</a> <a id="8944" class="Symbol">(λ</a> <a id="8947" href="literature.introduction-to-homotopy-type-theory.html#8947" class="Bound">p</a> <a id="8949" class="Symbol">→</a> <a id="8951" href="literature.introduction-to-homotopy-type-theory.html#8926" class="Bound">nnpq</a> <a id="8956" class="Symbol">(λ</a> <a id="8959" href="literature.introduction-to-homotopy-type-theory.html#8959" class="Bound">pq</a> <a id="8962" class="Symbol">→</a> <a id="8964" href="literature.introduction-to-homotopy-type-theory.html#8935" class="Bound">nq</a> <a id="8967" class="Symbol">(</a><a id="8968" href="literature.introduction-to-homotopy-type-theory.html#8959" class="Bound">pq</a> <a id="8971" href="literature.introduction-to-homotopy-type-theory.html#8947" class="Bound">p</a><a id="8972" class="Symbol">)))</a>

  <a id="8979" href="literature.introduction-to-homotopy-type-theory.html#8979" class="Function">_</a> <a id="8981" class="Symbol">:</a> <a id="8983" class="Symbol">(</a><a id="8984" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8987" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="8989" class="Symbol">→</a> <a id="8991" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="8994" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="8995" class="Symbol">)</a> <a id="8997" class="Symbol">→</a> <a id="8999" href="foundation.double-negation.html#572" class="Function Operator">¬¬</a> <a id="9002" class="Symbol">(</a><a id="9003" href="literature.introduction-to-homotopy-type-theory.html#8542" class="Bound">P</a> <a id="9005" class="Symbol">→</a> <a id="9007" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="9008" class="Symbol">)</a>
  <a id="9012" class="Symbol">_</a> <a id="9014" class="Symbol">=</a>
    <a id="9020" class="Symbol">λ</a> <a id="9022" href="literature.introduction-to-homotopy-type-theory.html#9022" class="Bound">nnpnnq</a> <a id="9029" href="literature.introduction-to-homotopy-type-theory.html#9029" class="Bound">npq</a> <a id="9033" class="Symbol">→</a>
      <a id="9041" class="Symbol">(</a> <a id="9043" class="Symbol">λ</a> <a id="9045" class="Symbol">(</a><a id="9046" href="literature.introduction-to-homotopy-type-theory.html#9046" class="Bound">nq</a> <a id="9049" class="Symbol">:</a> <a id="9051" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="9053" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="9054" class="Symbol">)</a> <a id="9056" class="Symbol">→</a>
        <a id="9066" href="literature.introduction-to-homotopy-type-theory.html#9029" class="Bound">npq</a> <a id="9070" class="Symbol">(λ</a> <a id="9073" href="literature.introduction-to-homotopy-type-theory.html#9073" class="Bound">p</a> <a id="9075" class="Symbol">→</a> <a id="9077" href="foundation-core.empty-types.html#904" class="Function">ex-falso</a> <a id="9086" class="Symbol">(</a><a id="9087" href="literature.introduction-to-homotopy-type-theory.html#9022" class="Bound">nnpnnq</a> <a id="9094" class="Symbol">(</a><a id="9095" href="foundation.double-negation.html#782" class="Function">intro-double-negation</a> <a id="9117" href="literature.introduction-to-homotopy-type-theory.html#9073" class="Bound">p</a><a id="9118" class="Symbol">)</a> <a id="9120" href="literature.introduction-to-homotopy-type-theory.html#9046" class="Bound">nq</a><a id="9122" class="Symbol">)))</a>
      <a id="9132" class="Symbol">(</a> <a id="9134" class="Symbol">λ</a> <a id="9136" class="Symbol">(</a><a id="9137" href="literature.introduction-to-homotopy-type-theory.html#9137" class="Bound">q</a> <a id="9139" class="Symbol">:</a> <a id="9141" href="literature.introduction-to-homotopy-type-theory.html#8554" class="Bound">Q</a><a id="9142" class="Symbol">)</a> <a id="9144" class="Symbol">→</a> <a id="9146" href="literature.introduction-to-homotopy-type-theory.html#9029" class="Bound">npq</a> <a id="9150" class="Symbol">(λ</a> <a id="9153" href="literature.introduction-to-homotopy-type-theory.html#9153" class="Bound">_</a> <a id="9155" class="Symbol">→</a> <a id="9157" href="literature.introduction-to-homotopy-type-theory.html#9137" class="Bound">q</a><a id="9158" class="Symbol">))</a>
</pre>
**Exercise 4.4.** Lists.

<pre class="Agda"><a id="9200" class="Keyword">open</a> <a id="9205" class="Keyword">import</a> <a id="9212" href="lists.lists.html" class="Module">lists.lists</a> <a id="9224" class="Keyword">using</a>
  <a id="9232" class="Symbol">(</a> <a id="9234" href="lists.lists.html#1328" class="Datatype">list</a>
  <a id="9241" class="Symbol">;</a> <a id="9243" href="lists.lists.html#1371" class="InductiveConstructor">nil</a>
  <a id="9249" class="Symbol">;</a> <a id="9251" href="lists.lists.html#1386" class="InductiveConstructor">cons</a><a id="9255" class="Symbol">)</a>

<a id="9258" class="Comment">-- (a)</a>
<a id="9265" class="Keyword">open</a> <a id="9270" class="Keyword">import</a> <a id="9277" href="lists.lists.html" class="Module">lists.lists</a> <a id="9289" class="Keyword">using</a>
  <a id="9297" class="Symbol">(</a> <a id="9299" href="lists.lists.html#1920" class="Function">ind-list</a><a id="9307" class="Symbol">)</a>

<a id="9310" class="Comment">-- (b)</a>
<a id="9317" class="Keyword">open</a> <a id="9322" class="Keyword">import</a> <a id="9329" href="lists.lists.html" class="Module">lists.lists</a> <a id="9341" class="Keyword">using</a>
  <a id="9349" class="Symbol">(</a> <a id="9351" href="lists.lists.html#2158" class="Function">fold-list</a><a id="9360" class="Symbol">)</a>

<a id="9363" class="Comment">-- (c)</a>
<a id="9370" class="Keyword">open</a> <a id="9375" class="Keyword">import</a> <a id="9382" href="lists.functoriality-lists.html" class="Module">lists.functoriality-lists</a> <a id="9408" class="Keyword">using</a>
  <a id="9416" class="Symbol">(</a> <a id="9418" href="lists.functoriality-lists.html#934" class="Function">map-list</a><a id="9426" class="Symbol">)</a>

<a id="9429" class="Comment">-- (d)</a>
<a id="9436" class="Keyword">open</a> <a id="9441" class="Keyword">import</a> <a id="9448" href="lists.lists.html" class="Module">lists.lists</a> <a id="9460" class="Keyword">using</a>
  <a id="9468" class="Symbol">(</a> <a id="9470" href="lists.lists.html#2619" class="Function">length-list</a><a id="9481" class="Symbol">)</a>

<a id="9484" class="Comment">-- (e)</a>
<a id="9491" class="Keyword">open</a> <a id="9496" class="Keyword">import</a> <a id="9503" href="elementary-number-theory.sums-of-natural-numbers.html" class="Module">elementary-number-theory.sums-of-natural-numbers</a> <a id="9552" class="Keyword">using</a>
  <a id="9560" class="Symbol">(</a> <a id="9562" href="elementary-number-theory.sums-of-natural-numbers.html#1149" class="Function">sum-list-ℕ</a><a id="9572" class="Symbol">)</a>
<a id="9574" class="Keyword">open</a> <a id="9579" class="Keyword">import</a> <a id="9586" href="elementary-number-theory.products-of-natural-numbers.html" class="Module">elementary-number-theory.products-of-natural-numbers</a> <a id="9639" class="Keyword">using</a>
  <a id="9647" class="Symbol">(</a> <a id="9649" href="elementary-number-theory.products-of-natural-numbers.html#754" class="Function">product-list-ℕ</a><a id="9663" class="Symbol">)</a>

<a id="9666" class="Comment">-- (f)</a>
<a id="9673" class="Keyword">open</a> <a id="9678" class="Keyword">import</a> <a id="9685" href="lists.concatenation-lists.html" class="Module">lists.concatenation-lists</a> <a id="9711" class="Keyword">using</a>
  <a id="9719" class="Symbol">(</a> <a id="9721" href="lists.concatenation-lists.html#648" class="Function">concat-list</a><a id="9732" class="Symbol">)</a>

<a id="9735" class="Comment">-- (g)</a>
<a id="9742" class="Keyword">open</a> <a id="9747" class="Keyword">import</a> <a id="9754" href="lists.flattening-lists.html" class="Module">lists.flattening-lists</a> <a id="9777" class="Keyword">using</a>
  <a id="9785" class="Symbol">(</a> <a id="9787" href="lists.flattening-lists.html#617" class="Function">flatten-list</a><a id="9799" class="Symbol">)</a>

<a id="9802" class="Comment">-- (h)</a>
<a id="9809" class="Keyword">open</a> <a id="9814" class="Keyword">import</a> <a id="9821" href="lists.reversing-lists.html" class="Module">lists.reversing-lists</a> <a id="9843" class="Keyword">using</a>
  <a id="9851" class="Symbol">(</a> <a id="9853" href="lists.reversing-lists.html#617" class="Function">reverse-list</a><a id="9865" class="Symbol">)</a>
</pre>
## 5 Identity types

### 5.1 The inductive definition of identity types

**Definition 5.1.1.** The identity type.

<pre class="Agda"><a id="9995" class="Keyword">open</a> <a id="10000" class="Keyword">import</a> <a id="10007" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="10033" class="Keyword">using</a>
  <a id="10041" class="Symbol">(</a> <a id="10043" href="foundation-core.identity-types.html#2713" class="Function Operator">_＝_</a> <a id="10047" class="Symbol">;</a> <a id="10049" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a>
  <a id="10054" class="Symbol">;</a> <a id="10056" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
  <a id="10063" class="Symbol">;</a> <a id="10065" href="foundation-core.identity-types.html#3722" class="Function">ind-Id</a><a id="10071" class="Symbol">)</a>
</pre>
### 5.2 The groupoidal structure of types

**Definition 5.2.1.** Concatenation of identifications.

<pre class="Agda"><a id="10186" class="Keyword">open</a> <a id="10191" class="Keyword">import</a> <a id="10198" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="10224" class="Keyword">using</a>
  <a id="10232" class="Symbol">(</a> <a id="10234" href="foundation-core.identity-types.html#6114" class="Function">concat</a> <a id="10241" class="Symbol">;</a> <a id="10243" href="foundation-core.identity-types.html#6054" class="Function Operator">_∙_</a><a id="10246" class="Symbol">)</a>
</pre>
**Definition 5.2.2.** Inverse operation.

<pre class="Agda"><a id="10303" class="Keyword">open</a> <a id="10308" class="Keyword">import</a> <a id="10315" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="10341" class="Keyword">using</a>
  <a id="10349" class="Symbol">(</a> <a id="10351" href="foundation-core.identity-types.html#6358" class="Function">inv</a><a id="10354" class="Symbol">)</a>
</pre>
**Definition 5.2.4.** Associator.

<pre class="Agda"><a id="10404" class="Keyword">open</a> <a id="10409" class="Keyword">import</a> <a id="10416" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="10442" class="Keyword">using</a>
  <a id="10450" class="Symbol">(</a> <a id="10452" href="foundation-core.identity-types.html#7454" class="Function">assoc</a> <a id="10458" class="Comment">-- (p ∙ q) ∙ r = p ∙ (q ∙ r)</a>
  <a id="10489" class="Symbol">)</a>
</pre>
**Definition 5.2.5.** Unit law operations.

<pre class="Agda"><a id="10548" class="Keyword">open</a> <a id="10553" class="Keyword">import</a> <a id="10560" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="10586" class="Keyword">using</a>
  <a id="10594" class="Symbol">(</a> <a id="10596" href="foundation-core.identity-types.html#8369" class="Function">left-unit</a> <a id="10606" class="Comment">-- refl ∙ p = p</a>
  <a id="10624" class="Symbol">;</a> <a id="10626" href="foundation-core.identity-types.html#8440" class="Function">right-unit</a> <a id="10637" class="Comment">-- p ∙ refl = p</a>
  <a id="10655" class="Symbol">)</a>
</pre>
**Definition 5.2.5.** Inverse law operations.

<pre class="Agda"><a id="10717" class="Keyword">open</a> <a id="10722" class="Keyword">import</a> <a id="10729" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="10755" class="Keyword">using</a>
  <a id="10763" class="Symbol">(</a> <a id="10765" href="foundation-core.identity-types.html#8619" class="Function">left-inv</a> <a id="10774" class="Comment">-- inv p ∙ p = refl</a>
  <a id="10796" class="Symbol">;</a> <a id="10798" href="foundation-core.identity-types.html#8697" class="Function">right-inv</a> <a id="10808" class="Comment">-- p ∙ inv p = refl</a>
  <a id="10830" class="Symbol">)</a>
</pre>
### 5.3 The action on identifications of functions

**Definition 5.3.1.** Action on paths.

Note that the operations `ap-id` and `ap-comp` provide identifications in the
inverse direction from the ones in the book.

<pre class="Agda"><a id="11061" class="Keyword">open</a> <a id="11066" class="Keyword">import</a> <a id="11073" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a> <a id="11120" class="Keyword">using</a>
  <a id="11128" class="Symbol">(</a> <a id="11130" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
  <a id="11135" class="Symbol">;</a> <a id="11137" href="foundation.action-on-identifications-functions.html#931" class="Function">ap-id</a> <a id="11143" class="Comment">-- ap id p = p</a>
  <a id="11160" class="Symbol">;</a> <a id="11162" href="foundation.action-on-identifications-functions.html#1124" class="Function">ap-comp</a> <a id="11170" class="Comment">-- ap (g ∘ f) p = ap g (ap f (p))</a>
  <a id="11206" class="Symbol">)</a>
</pre>
**Definition 5.3.2.** Preservation rules.

<pre class="Agda"><a id="11264" class="Keyword">open</a> <a id="11269" class="Keyword">import</a> <a id="11276" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a> <a id="11323" class="Keyword">using</a>
  <a id="11331" class="Symbol">(</a> <a id="11333" href="foundation.action-on-identifications-functions.html#1603" class="Function">ap-refl</a> <a id="11341" class="Comment">-- ap f refl = refl</a>
  <a id="11363" class="Symbol">;</a> <a id="11365" href="foundation.action-on-identifications-functions.html#2258" class="Function">ap-inv</a> <a id="11372" class="Comment">-- ap f (inv p) = inv (ap f p)</a>
  <a id="11405" class="Symbol">;</a> <a id="11407" href="foundation.action-on-identifications-functions.html#1903" class="Function">ap-concat</a> <a id="11417" class="Comment">-- ap f (p ∙ q) = ap f p ∙ ap f q</a>
  <a id="11453" class="Symbol">)</a>
</pre>
### 5.4 Transport

**Definition 5.4.1.** Transport.

<pre class="Agda"><a id="11521" class="Keyword">open</a> <a id="11526" class="Keyword">import</a> <a id="11533" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a> <a id="11576" class="Keyword">using</a>
  <a id="11584" class="Symbol">(</a> <a id="11586" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a><a id="11588" class="Symbol">)</a>
</pre>
**Definition 5.4.2.** Dependent action on paths.

<pre class="Agda"><a id="11653" class="Keyword">open</a> <a id="11658" class="Keyword">import</a> <a id="11665" href="foundation.action-on-identifications-dependent-functions.html" class="Module">foundation.action-on-identifications-dependent-functions</a> <a id="11722" class="Keyword">using</a>
  <a id="11730" class="Symbol">(</a> <a id="11732" href="foundation.action-on-identifications-dependent-functions.html#1181" class="Function">apd</a><a id="11735" class="Symbol">)</a>
</pre>
### 5.5 The uniqueness of `refl`

**Proposition 5.5.1.** Contractibility of singletons.

<pre class="Agda"><a id="11839" class="Keyword">open</a> <a id="11844" class="Keyword">import</a> <a id="11851" href="foundation.torsorial-type-families.html" class="Module">foundation.torsorial-type-families</a> <a id="11886" class="Keyword">using</a>
  <a id="11894" class="Symbol">(</a> <a id="11896" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a><a id="11911" class="Symbol">)</a>
<a id="11913" class="Keyword">open</a> <a id="11918" class="Keyword">import</a> <a id="11925" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a> <a id="11955" class="Keyword">using</a>
  <a id="11963" class="Symbol">(</a> <a id="11965" href="foundation-core.contractible-types.html#1073" class="Function">eq-is-contr&#39;</a><a id="11977" class="Symbol">)</a>

<a id="11980" href="literature.introduction-to-homotopy-type-theory.html#11980" class="Function">_</a> <a id="11982" class="Symbol">:</a> <a id="11984" class="Symbol">{</a><a id="11985" href="literature.introduction-to-homotopy-type-theory.html#11985" class="Bound">l</a> <a id="11987" class="Symbol">:</a> <a id="11989" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="11994" class="Symbol">}</a> <a id="11996" class="Symbol">{</a><a id="11997" href="literature.introduction-to-homotopy-type-theory.html#11997" class="Bound">A</a> <a id="11999" class="Symbol">:</a> <a id="12001" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="12004" href="literature.introduction-to-homotopy-type-theory.html#11985" class="Bound">l</a><a id="12005" class="Symbol">}</a> <a id="12007" class="Symbol">(</a><a id="12008" href="literature.introduction-to-homotopy-type-theory.html#12008" class="Bound">a</a> <a id="12010" class="Symbol">:</a> <a id="12012" href="literature.introduction-to-homotopy-type-theory.html#11997" class="Bound">A</a><a id="12013" class="Symbol">)</a> <a id="12015" class="Symbol">(</a><a id="12016" href="literature.introduction-to-homotopy-type-theory.html#12016" class="Bound">y</a> <a id="12018" class="Symbol">:</a> <a id="12020" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="12022" href="literature.introduction-to-homotopy-type-theory.html#11997" class="Bound">A</a> <a id="12024" class="Symbol">(λ</a> <a id="12027" href="literature.introduction-to-homotopy-type-theory.html#12027" class="Bound">x</a> <a id="12029" class="Symbol">→</a> <a id="12031" href="literature.introduction-to-homotopy-type-theory.html#12008" class="Bound">a</a> <a id="12033" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="12035" href="literature.introduction-to-homotopy-type-theory.html#12027" class="Bound">x</a><a id="12036" class="Symbol">))</a> <a id="12039" class="Symbol">→</a> <a id="12041" class="Symbol">(</a><a id="12042" href="literature.introduction-to-homotopy-type-theory.html#12008" class="Bound">a</a> <a id="12044" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="12046" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="12050" class="Symbol">)</a> <a id="12052" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="12054" href="literature.introduction-to-homotopy-type-theory.html#12016" class="Bound">y</a>
<a id="12056" class="Symbol">_</a> <a id="12058" class="Symbol">=</a> <a id="12060" class="Symbol">λ</a> <a id="12062" href="literature.introduction-to-homotopy-type-theory.html#12062" class="Bound">a</a> <a id="12064" class="Symbol">→</a> <a id="12066" href="foundation-core.contractible-types.html#1073" class="Function">eq-is-contr&#39;</a> <a id="12079" class="Symbol">(</a><a id="12080" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a> <a id="12096" href="literature.introduction-to-homotopy-type-theory.html#12062" class="Bound">a</a><a id="12097" class="Symbol">)</a> <a id="12099" class="Symbol">(</a><a id="12100" href="literature.introduction-to-homotopy-type-theory.html#12062" class="Bound">a</a> <a id="12102" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="12104" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="12108" class="Symbol">)</a>
</pre>
### 5.6 The laws of addition on ℕ

**Proposition 5.6.1.** Unit laws.

<pre class="Agda"><a id="12193" class="Keyword">open</a> <a id="12198" class="Keyword">import</a> <a id="12205" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a> <a id="12255" class="Keyword">using</a>
  <a id="12263" class="Symbol">(</a> <a id="12265" href="elementary-number-theory.addition-natural-numbers.html#1240" class="Function">left-unit-law-add-ℕ</a> <a id="12285" class="Comment">-- 0 + n = n</a>
  <a id="12300" class="Symbol">;</a> <a id="12302" href="elementary-number-theory.addition-natural-numbers.html#1158" class="Function">right-unit-law-add-ℕ</a> <a id="12323" class="Comment">-- n + 0 = n</a>
  <a id="12338" class="Symbol">)</a>
</pre>
**Proposition 5.6.2.** Successor laws.

<pre class="Agda"><a id="12393" class="Keyword">open</a> <a id="12398" class="Keyword">import</a> <a id="12405" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a> <a id="12455" class="Keyword">using</a>
  <a id="12463" class="Symbol">(</a> <a id="12465" href="elementary-number-theory.addition-natural-numbers.html#1454" class="Function">left-successor-law-add-ℕ</a> <a id="12490" class="Comment">-- succ m + n = succ (m + n)</a>
  <a id="12521" class="Symbol">;</a> <a id="12523" href="elementary-number-theory.addition-natural-numbers.html#1662" class="Function">right-successor-law-add-ℕ</a> <a id="12549" class="Comment">-- m + succ n = succ (m + n)</a>
  <a id="12580" class="Symbol">)</a>
</pre>
**Proposition 5.6.3.** Associativity.

<pre class="Agda"><a id="12634" class="Keyword">open</a> <a id="12639" class="Keyword">import</a> <a id="12646" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a> <a id="12696" class="Keyword">using</a>
  <a id="12704" class="Symbol">(</a> <a id="12706" href="elementary-number-theory.addition-natural-numbers.html#1828" class="Function">associative-add-ℕ</a> <a id="12724" class="Comment">-- (m + n) + k = m + (n + k)</a>
  <a id="12755" class="Symbol">)</a>
</pre>
**Proposition 5.6.4.** Commutativity.

<pre class="Agda"><a id="12809" class="Keyword">open</a> <a id="12814" class="Keyword">import</a> <a id="12821" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a> <a id="12871" class="Keyword">using</a>
  <a id="12879" class="Symbol">(</a> <a id="12881" href="elementary-number-theory.addition-natural-numbers.html#2060" class="Function">commutative-add-ℕ</a> <a id="12899" class="Comment">-- m + n = n + m</a>
  <a id="12918" class="Symbol">)</a>
</pre>
### Exercises

**Exercise 5.1.** Distributivity of inversion over concatenation.

<pre class="Agda"><a id="13015" class="Keyword">open</a> <a id="13020" class="Keyword">import</a> <a id="13027" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="13053" class="Keyword">using</a>
  <a id="13061" class="Symbol">(</a> <a id="13063" href="foundation-core.identity-types.html#9072" class="Function">distributive-inv-concat</a> <a id="13087" class="Comment">-- inv (p ∙ q) = inv q ∙ inv p</a>
  <a id="13120" class="Symbol">)</a>
</pre>
**Exercise 5.2.** Transposing concatenation.

<pre class="Agda"><a id="13181" class="Keyword">open</a> <a id="13186" class="Keyword">import</a> <a id="13193" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="13219" class="Keyword">using</a>
  <a id="13227" class="Symbol">(</a> <a id="13229" href="foundation-core.identity-types.html#10922" class="Function">left-transpose-eq-concat</a> <a id="13254" class="Comment">-- (p ∙ q = r) → (q = inv p ∙ r)</a>
  <a id="13289" class="Symbol">;</a> <a id="13291" href="foundation-core.identity-types.html#11254" class="Function">right-transpose-eq-concat</a> <a id="13317" class="Comment">-- (p ∙ q = r) → (p = r ∙ inv q)</a>
  <a id="13352" class="Symbol">)</a>
</pre>
**Exercise 5.3.** Path lifting.

<pre class="Agda"><a id="13400" class="Keyword">open</a> <a id="13405" class="Keyword">import</a> <a id="13412" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a> <a id="13453" class="Keyword">using</a>
  <a id="13461" class="Symbol">(</a> <a id="13463" href="foundation-core.equality-dependent-pair-types.html#1669" class="Function">eq-pair-eq-base</a><a id="13478" class="Symbol">)</a>
</pre>
**Exercise 5.4.** Mac Lane pentagon.

<pre class="Agda"><a id="13531" class="Keyword">open</a> <a id="13536" class="Keyword">import</a> <a id="13543" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="13569" class="Keyword">using</a>
  <a id="13577" class="Symbol">(</a> <a id="13579" href="foundation.identity-types.html#1324" class="Function">mac-lane-pentagon</a><a id="13596" class="Symbol">)</a>
</pre>
**Exercise 5.5.** Semiring laws for addition and multiplication of natural
numbers.

<pre class="Agda"><a id="13696" class="Comment">-- (a)</a>
<a id="13703" class="Keyword">open</a> <a id="13708" class="Keyword">import</a> <a id="13715" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a> <a id="13771" class="Keyword">using</a>
  <a id="13779" class="Symbol">(</a> <a id="13781" href="elementary-number-theory.multiplication-natural-numbers.html#1794" class="Function">right-zero-law-mul-ℕ</a> <a id="13802" class="Comment">-- m * 0 = 0</a>
  <a id="13817" class="Symbol">;</a> <a id="13819" href="elementary-number-theory.multiplication-natural-numbers.html#1703" class="Function">left-zero-law-mul-ℕ</a> <a id="13839" class="Comment">-- 0 * m = 0</a>
  <a id="13854" class="Symbol">;</a> <a id="13856" href="elementary-number-theory.multiplication-natural-numbers.html#2006" class="Function">right-unit-law-mul-ℕ</a> <a id="13877" class="Comment">-- m * 1 = m</a>
  <a id="13892" class="Symbol">;</a> <a id="13894" href="elementary-number-theory.multiplication-natural-numbers.html#2165" class="Function">left-unit-law-mul-ℕ</a> <a id="13914" class="Comment">-- 1 * m = m</a>
  <a id="13929" class="Symbol">;</a> <a id="13931" href="elementary-number-theory.multiplication-natural-numbers.html#2445" class="Function">right-successor-law-mul-ℕ</a> <a id="13957" class="Comment">-- m * (succ n) = m + m * n</a>
  <a id="13987" class="Symbol">;</a> <a id="13989" href="elementary-number-theory.multiplication-natural-numbers.html#2329" class="Function">left-successor-law-mul-ℕ</a> <a id="14014" class="Comment">-- (succ m) * n = m * n + n</a>
  <a id="14044" class="Symbol">)</a>

<a id="14047" class="Comment">-- (b)</a>
<a id="14054" class="Keyword">open</a> <a id="14059" class="Keyword">import</a> <a id="14066" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a> <a id="14122" class="Keyword">using</a>
  <a id="14130" class="Symbol">(</a> <a id="14132" href="elementary-number-theory.multiplication-natural-numbers.html#2801" class="Function">commutative-mul-ℕ</a> <a id="14150" class="Comment">-- m * n = n * m</a>
  <a id="14169" class="Symbol">)</a>

<a id="14172" class="Comment">-- (c)</a>
<a id="14179" class="Keyword">open</a> <a id="14184" class="Keyword">import</a> <a id="14191" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a> <a id="14247" class="Keyword">using</a>
  <a id="14255" class="Symbol">(</a> <a id="14257" href="elementary-number-theory.multiplication-natural-numbers.html#3090" class="Function">left-distributive-mul-add-ℕ</a> <a id="14285" class="Comment">-- m * (n + k) = m * n + m * k</a>
  <a id="14318" class="Symbol">;</a> <a id="14320" href="elementary-number-theory.multiplication-natural-numbers.html#3735" class="Function">right-distributive-mul-add-ℕ</a> <a id="14349" class="Comment">-- (m + n) * k = m * k + n * k</a>
  <a id="14382" class="Symbol">)</a>

<a id="14385" class="Comment">-- (d)</a>
<a id="14392" class="Keyword">open</a> <a id="14397" class="Keyword">import</a> <a id="14404" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a> <a id="14460" class="Keyword">using</a>
  <a id="14468" class="Symbol">(</a> <a id="14470" href="elementary-number-theory.multiplication-natural-numbers.html#4065" class="Function">associative-mul-ℕ</a> <a id="14488" class="Comment">-- (m * n) * k = m * (n * k)</a>
  <a id="14519" class="Symbol">)</a>
</pre>
**Exercise 5.6.** Successor and predecessor operations on integers are mutual
inverses.

<pre class="Agda"><a id="14623" class="Keyword">open</a> <a id="14628" class="Keyword">import</a> <a id="14635" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a> <a id="14669" class="Keyword">using</a>
  <a id="14677" class="Symbol">(</a> <a id="14679" href="elementary-number-theory.integers.html#4066" class="Function">is-section-pred-ℤ</a> <a id="14697" class="Comment">-- (succ (pred k)) = k</a>
  <a id="14722" class="Symbol">;</a> <a id="14724" href="elementary-number-theory.integers.html#3776" class="Function">is-retraction-pred-ℤ</a> <a id="14745" class="Comment">-- (pred (succ k)) = k</a>
  <a id="14770" class="Symbol">)</a>
</pre>
**Exercise 5.7.** Abelian group laws for addition of integers.

<pre class="Agda"><a id="14849" class="Comment">-- (a)</a>
<a id="14856" class="Keyword">open</a> <a id="14861" class="Keyword">import</a> <a id="14868" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a> <a id="14911" class="Keyword">using</a>
  <a id="14919" class="Symbol">(</a> <a id="14921" href="elementary-number-theory.addition-integers.html#1774" class="Function">left-unit-law-add-ℤ</a> <a id="14941" class="Comment">-- 0 + x = x</a>
  <a id="14956" class="Symbol">;</a> <a id="14958" href="elementary-number-theory.addition-integers.html#1856" class="Function">right-unit-law-add-ℤ</a> <a id="14979" class="Comment">-- x + 0 = x</a>
  <a id="14994" class="Symbol">)</a>

<a id="14997" class="Comment">-- (b)</a>
<a id="15004" class="Keyword">open</a> <a id="15009" class="Keyword">import</a> <a id="15016" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a> <a id="15059" class="Keyword">using</a>
  <a id="15067" class="Symbol">(</a> <a id="15069" href="elementary-number-theory.addition-integers.html#2291" class="Function">left-predecessor-law-add-ℤ</a> <a id="15096" class="Comment">-- pred x + y = pred (x + y)</a>
  <a id="15127" class="Symbol">;</a> <a id="15129" href="elementary-number-theory.addition-integers.html#2665" class="Function">right-predecessor-law-add-ℤ</a> <a id="15157" class="Comment">-- x + pred y = pred (x + y)</a>
  <a id="15188" class="Symbol">;</a> <a id="15190" href="elementary-number-theory.addition-integers.html#3632" class="Function">left-successor-law-add-ℤ</a> <a id="15215" class="Comment">-- succ x + y = succ (x + y)</a>
  <a id="15246" class="Symbol">;</a> <a id="15248" href="elementary-number-theory.addition-integers.html#4167" class="Function">right-successor-law-add-ℤ</a> <a id="15274" class="Comment">-- x + succ y = succ (x + y)</a>
  <a id="15305" class="Symbol">)</a>

<a id="15308" class="Comment">-- (c)</a>
<a id="15315" class="Keyword">open</a> <a id="15320" class="Keyword">import</a> <a id="15327" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a> <a id="15370" class="Keyword">using</a>
  <a id="15378" class="Symbol">(</a> <a id="15380" href="elementary-number-theory.addition-integers.html#6486" class="Function">associative-add-ℤ</a> <a id="15398" class="Comment">-- (x + y) + z = x + (y + z)</a>
  <a id="15429" class="Symbol">;</a> <a id="15431" href="elementary-number-theory.addition-integers.html#8333" class="Function">commutative-add-ℤ</a> <a id="15449" class="Comment">-- x + y = y + x</a>
  <a id="15468" class="Symbol">)</a>

<a id="15471" class="Comment">-- (d)</a>
<a id="15478" class="Keyword">open</a> <a id="15483" class="Keyword">import</a> <a id="15490" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a> <a id="15533" class="Keyword">using</a>
  <a id="15541" class="Symbol">(</a> <a id="15543" href="elementary-number-theory.addition-integers.html#9634" class="Function">left-inverse-law-add-ℤ</a> <a id="15566" class="Comment">-- (-x) + x = 0</a>
  <a id="15584" class="Symbol">;</a> <a id="15586" href="elementary-number-theory.addition-integers.html#10412" class="Function">right-inverse-law-add-ℤ</a> <a id="15610" class="Comment">-- x + (-x) = 0</a>
  <a id="15628" class="Symbol">)</a>
</pre>
**Exercise 5.8.** Ring laws for multiplication of integers.

<pre class="Agda"><a id="15704" class="Comment">-- (a)</a>
<a id="15711" class="Keyword">open</a> <a id="15716" class="Keyword">import</a> <a id="15723" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a> <a id="15772" class="Keyword">using</a>
  <a id="15780" class="Symbol">(</a> <a id="15782" href="elementary-number-theory.multiplication-integers.html#3107" class="Function">left-zero-law-mul-ℤ</a> <a id="15802" class="Comment">-- 0 * x = x</a>
  <a id="15817" class="Symbol">;</a> <a id="15819" href="elementary-number-theory.multiplication-integers.html#3190" class="Function">right-zero-law-mul-ℤ</a> <a id="15840" class="Comment">-- x * 0 = x</a>
  <a id="15855" class="Symbol">;</a> <a id="15857" href="elementary-number-theory.multiplication-integers.html#3559" class="Function">left-unit-law-mul-ℤ</a> <a id="15877" class="Comment">-- 1 * x = x</a>
  <a id="15892" class="Symbol">;</a> <a id="15894" href="elementary-number-theory.multiplication-integers.html#3636" class="Function">right-unit-law-mul-ℤ</a> <a id="15915" class="Comment">-- x * 1 = x</a>
  <a id="15930" class="Symbol">)</a>

<a id="15933" class="Comment">-- (b)</a>
<a id="15940" class="Keyword">open</a> <a id="15945" class="Keyword">import</a> <a id="15952" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a> <a id="16001" class="Keyword">using</a>
  <a id="16009" class="Symbol">(</a> <a id="16011" href="elementary-number-theory.multiplication-integers.html#5880" class="Function">left-predecessor-law-mul-ℤ&#39;</a> <a id="16039" class="Comment">-- pred x * y = x * y - y</a>
  <a id="16067" class="Symbol">;</a> <a id="16069" href="elementary-number-theory.multiplication-integers.html#9858" class="Function">right-predecessor-law-mul-ℤ&#39;</a> <a id="16098" class="Comment">-- x * pred y = x * y - x</a>
  <a id="16126" class="Symbol">;</a> <a id="16128" href="elementary-number-theory.multiplication-integers.html#5187" class="Function">left-successor-law-mul-ℤ&#39;</a> <a id="16154" class="Comment">-- succ x * y = x * y + y</a>
  <a id="16182" class="Symbol">;</a> <a id="16184" href="elementary-number-theory.multiplication-integers.html#7956" class="Function">right-successor-law-mul-ℤ&#39;</a> <a id="16211" class="Comment">-- x * succ y = x * y + x</a>
  <a id="16239" class="Symbol">)</a>

<a id="16242" class="Comment">-- (c)</a>
<a id="16249" class="Keyword">open</a> <a id="16254" class="Keyword">import</a> <a id="16261" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a> <a id="16310" class="Keyword">using</a>
  <a id="16318" class="Symbol">(</a> <a id="16320" href="elementary-number-theory.multiplication-integers.html#13327" class="Function">left-distributive-mul-add-ℤ</a> <a id="16348" class="Comment">-- x * (y + z) = x * y + x * z</a>
  <a id="16381" class="Symbol">;</a> <a id="16383" href="elementary-number-theory.multiplication-integers.html#10141" class="Function">right-distributive-mul-add-ℤ</a> <a id="16412" class="Comment">-- (x + y) * z = x * z + y * z</a>
  <a id="16445" class="Symbol">)</a>

<a id="16448" class="Comment">-- (d)</a>
<a id="16455" class="Keyword">open</a> <a id="16460" class="Keyword">import</a> <a id="16467" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a> <a id="16516" class="Keyword">using</a>
  <a id="16524" class="Symbol">(</a> <a id="16526" href="elementary-number-theory.multiplication-integers.html#11976" class="Function">associative-mul-ℤ</a> <a id="16544" class="Comment">-- (x * y) * z = x * (y * z)</a>
  <a id="16575" class="Symbol">;</a> <a id="16577" href="elementary-number-theory.multiplication-integers.html#12689" class="Function">commutative-mul-ℤ</a> <a id="16595" class="Comment">-- x * y = y * x</a>
  <a id="16614" class="Symbol">)</a>
</pre>
## 6 Universes

### 6.1 Specification of type theoretic universes

**Definition 6.1.1** Universes.

The book's metatheory uses universes _à la Tarski_, which considers a universe
`𝒰` a type of _codes_, such that for every code `X : 𝒰` we may derive
`𝒯(X) type`. In contrast, Agda uses universes _à la Russell_, where the elements
`X : 𝒰` are themselves types.

The only exception is the universe types themselves — we have the type `Level`
of codes for universes, and for every code `l : Level` we have the judgment
`UU l type`.

Universes are called `UU` in the library, which stands for _univalent universe_.

Closure of universes under various type constructors is guaranteed by Agda's
[sort system](https://agda.readthedocs.io/en/latest/language/sort-system.html).

<pre class="Agda"><a id="17399" class="Keyword">open</a> <a id="17404" class="Keyword">import</a> <a id="17411" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a> <a id="17438" class="Keyword">using</a>
  <a id="17446" class="Symbol">(</a> <a id="17448" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="17454" class="Comment">-- type of codes for universes</a>
  <a id="17487" class="Symbol">;</a> <a id="17489" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="17492" class="Comment">-- the universal family decoding universes</a>
  <a id="17537" class="Symbol">)</a>
</pre>
### 6.2 Assuming enough universes

**Postulate 6.2.1.** There are enough universes.

The postulate is metatheoretical, so it doesn't have a corresponding term.
Instead we are guaranteed to have enough universes by Agda's implementation.

**Definition 6.2.2.** The base universe.

<pre class="Agda"><a id="17832" class="Keyword">open</a> <a id="17837" class="Keyword">import</a> <a id="17844" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a> <a id="17871" class="Keyword">using</a>
  <a id="17879" class="Symbol">(</a> <a id="17881" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="17886" class="Symbol">)</a>
</pre>
**Definition 6.2.3.** The successor universe.

<pre class="Agda"><a id="17948" class="Keyword">open</a> <a id="17953" class="Keyword">import</a> <a id="17960" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a> <a id="17987" class="Keyword">using</a>
  <a id="17995" class="Symbol">(</a> <a id="17997" href="Agda.Primitive.html#931" class="Primitive">lsuc</a><a id="18001" class="Symbol">)</a>
</pre>
**Remark 6.2.4.** Inclusions into the successor universe.

<pre class="Agda"><a id="18075" class="Keyword">open</a> <a id="18080" class="Keyword">import</a> <a id="18087" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a> <a id="18122" class="Keyword">using</a>
  <a id="18130" class="Symbol">(</a> <a id="18132" href="foundation.raising-universe-levels.html#1034" class="Datatype">raise</a><a id="18137" class="Symbol">)</a>

<a id="18140" href="literature.introduction-to-homotopy-type-theory.html#18140" class="Function">_</a> <a id="18142" class="Symbol">:</a> <a id="18144" class="Symbol">(</a><a id="18145" href="literature.introduction-to-homotopy-type-theory.html#18145" class="Bound">l</a> <a id="18147" class="Symbol">:</a> <a id="18149" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="18154" class="Symbol">)</a> <a id="18156" class="Symbol">→</a> <a id="18158" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="18161" href="literature.introduction-to-homotopy-type-theory.html#18145" class="Bound">l</a> <a id="18163" class="Symbol">→</a> <a id="18165" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="18168" class="Symbol">(</a><a id="18169" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="18174" href="literature.introduction-to-homotopy-type-theory.html#18145" class="Bound">l</a><a id="18175" class="Symbol">)</a>
<a id="18177" class="Symbol">_</a> <a id="18179" class="Symbol">=</a> <a id="18181" class="Symbol">λ</a> <a id="18183" href="literature.introduction-to-homotopy-type-theory.html#18183" class="Bound">l</a> <a id="18185" class="Symbol">→</a> <a id="18187" href="foundation.raising-universe-levels.html#1034" class="Datatype">raise</a> <a id="18193" class="Symbol">(</a><a id="18194" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="18199" href="literature.introduction-to-homotopy-type-theory.html#18183" class="Bound">l</a><a id="18200" class="Symbol">)</a>
</pre>
**Definition 6.2.5.** The join of two universes.

<pre class="Agda"><a id="18265" class="Keyword">open</a> <a id="18270" class="Keyword">import</a> <a id="18277" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a> <a id="18304" class="Keyword">using</a>
  <a id="18312" class="Symbol">(</a> <a id="18314" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="18317" class="Symbol">)</a>
</pre>
**Remark 6.2.6.** Universe arithmetic.

Note that while in the book `(𝒰 ⊔ 𝒱) ⊔ 𝒲` and `𝒰 ⊔ (𝒱 ⊔ 𝒲)` are a priori
unrelated, Agda considers them equal. Other universe equalities may be found in
[the documentation](https://agda.readthedocs.io/en/latest/language/universe-levels.html#intrinsic-level-properties).

### 6.3 Observational equality of the natural numbers

**Definition 6.3.1.** Observational equality of ℕ.

<pre class="Agda"><a id="18750" class="Keyword">open</a> <a id="18755" class="Keyword">import</a> <a id="18762" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a> <a id="18812" class="Keyword">using</a>
  <a id="18820" class="Symbol">(</a> <a id="18822" href="elementary-number-theory.equality-natural-numbers.html#1096" class="Function">Eq-ℕ</a><a id="18826" class="Symbol">)</a>
</pre>
**Lemma 6.3.2.** Observational equality of ℕ is reflexive.

<pre class="Agda"><a id="18901" class="Keyword">open</a> <a id="18906" class="Keyword">import</a> <a id="18913" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a> <a id="18963" class="Keyword">using</a>
  <a id="18971" class="Symbol">(</a> <a id="18973" href="elementary-number-theory.equality-natural-numbers.html#1576" class="Function">refl-Eq-ℕ</a><a id="18982" class="Symbol">)</a>
</pre>
**Proposition 6.3.3.** Logical equivalence of observational equality of ℕ and
identifications.

<pre class="Agda"><a id="19093" class="Keyword">open</a> <a id="19098" class="Keyword">import</a> <a id="19105" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a> <a id="19155" class="Keyword">using</a>
  <a id="19163" class="Symbol">(</a> <a id="19165" href="elementary-number-theory.equality-natural-numbers.html#1667" class="Function">Eq-eq-ℕ</a>
  <a id="19175" class="Symbol">;</a> <a id="19177" href="elementary-number-theory.equality-natural-numbers.html#1743" class="Function">eq-Eq-ℕ</a><a id="19184" class="Symbol">)</a>

<a id="19187" href="literature.introduction-to-homotopy-type-theory.html#19187" class="Function">_</a> <a id="19189" class="Symbol">:</a> <a id="19191" class="Symbol">(</a><a id="19192" href="literature.introduction-to-homotopy-type-theory.html#19192" class="Bound">m</a> <a id="19194" href="literature.introduction-to-homotopy-type-theory.html#19194" class="Bound">n</a> <a id="19196" class="Symbol">:</a> <a id="19198" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="19199" class="Symbol">)</a> <a id="19201" class="Symbol">→</a> <a id="19203" class="Symbol">(</a><a id="19204" href="literature.introduction-to-homotopy-type-theory.html#19192" class="Bound">m</a> <a id="19206" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19208" href="literature.introduction-to-homotopy-type-theory.html#19194" class="Bound">n</a><a id="19209" class="Symbol">)</a> <a id="19211" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="19213" href="elementary-number-theory.equality-natural-numbers.html#1096" class="Function">Eq-ℕ</a> <a id="19218" href="literature.introduction-to-homotopy-type-theory.html#19192" class="Bound">m</a> <a id="19220" href="literature.introduction-to-homotopy-type-theory.html#19194" class="Bound">n</a>
<a id="19222" class="Symbol">_</a> <a id="19224" class="Symbol">=</a> <a id="19226" class="Symbol">λ</a> <a id="19228" href="literature.introduction-to-homotopy-type-theory.html#19228" class="Bound">m</a> <a id="19230" href="literature.introduction-to-homotopy-type-theory.html#19230" class="Bound">n</a> <a id="19232" class="Symbol">→</a> <a id="19234" class="Symbol">(</a><a id="19235" href="elementary-number-theory.equality-natural-numbers.html#1667" class="Function">Eq-eq-ℕ</a> <a id="19243" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="19245" class="Symbol">(</a><a id="19246" href="elementary-number-theory.equality-natural-numbers.html#1743" class="Function">eq-Eq-ℕ</a> <a id="19254" href="literature.introduction-to-homotopy-type-theory.html#19228" class="Bound">m</a> <a id="19256" href="literature.introduction-to-homotopy-type-theory.html#19230" class="Bound">n</a><a id="19257" class="Symbol">))</a>
</pre>
### 6.4 Peano's seventh and eighth axioms

**Theorem 6.4.1.** Peano's seventh axiom.

<pre class="Agda"><a id="19359" class="Keyword">open</a> <a id="19364" class="Keyword">import</a> <a id="19371" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a> <a id="19412" class="Keyword">using</a>
  <a id="19420" class="Symbol">(</a> <a id="19422" href="elementary-number-theory.natural-numbers.html#2424" class="Function">is-injective-succ-ℕ</a><a id="19441" class="Symbol">)</a>

<a id="19444" href="literature.introduction-to-homotopy-type-theory.html#19444" class="Function">_</a> <a id="19446" class="Symbol">:</a> <a id="19448" class="Symbol">(</a><a id="19449" href="literature.introduction-to-homotopy-type-theory.html#19449" class="Bound">m</a> <a id="19451" href="literature.introduction-to-homotopy-type-theory.html#19451" class="Bound">n</a> <a id="19453" class="Symbol">:</a> <a id="19455" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="19456" class="Symbol">)</a> <a id="19458" class="Symbol">→</a> <a id="19460" class="Symbol">(</a><a id="19461" href="literature.introduction-to-homotopy-type-theory.html#19449" class="Bound">m</a> <a id="19463" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19465" href="literature.introduction-to-homotopy-type-theory.html#19451" class="Bound">n</a><a id="19466" class="Symbol">)</a> <a id="19468" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="19470" class="Symbol">(</a><a id="19471" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="19478" href="literature.introduction-to-homotopy-type-theory.html#19449" class="Bound">m</a> <a id="19480" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19482" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="19489" href="literature.introduction-to-homotopy-type-theory.html#19451" class="Bound">n</a><a id="19490" class="Symbol">)</a>
<a id="19492" class="Symbol">_</a> <a id="19494" class="Symbol">=</a> <a id="19496" class="Symbol">λ</a> <a id="19498" href="literature.introduction-to-homotopy-type-theory.html#19498" class="Bound">m</a> <a id="19500" href="literature.introduction-to-homotopy-type-theory.html#19500" class="Bound">n</a> <a id="19502" class="Symbol">→</a> <a id="19504" class="Symbol">(</a><a id="19505" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="19508" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="19515" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="19517" href="elementary-number-theory.natural-numbers.html#2424" class="Function">is-injective-succ-ℕ</a><a id="19536" class="Symbol">)</a>
</pre>
**Theorem 6.4.2.** Peano's eighth axiom.

<pre class="Agda"><a id="19593" class="Keyword">open</a> <a id="19598" class="Keyword">import</a> <a id="19605" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a> <a id="19646" class="Keyword">using</a>
  <a id="19654" class="Symbol">(</a> <a id="19656" href="elementary-number-theory.natural-numbers.html#2539" class="Function">is-nonzero-succ-ℕ</a> <a id="19674" class="Comment">-- succ n ≠ 0</a>
  <a id="19690" class="Symbol">)</a>
</pre>
The above proof uses Agda's built-in mechanism for recognizing that two elements
of an inductive type built out of different constructors cannot be equal (the
"no confusion" principle). The proof from the book follows:

<pre class="Agda"><a id="19925" href="literature.introduction-to-homotopy-type-theory.html#19925" class="Function">_</a> <a id="19927" class="Symbol">:</a> <a id="19929" class="Symbol">(</a><a id="19930" href="literature.introduction-to-homotopy-type-theory.html#19930" class="Bound">n</a> <a id="19932" class="Symbol">:</a> <a id="19934" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="19935" class="Symbol">)</a> <a id="19937" class="Symbol">→</a> <a id="19939" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="19941" class="Symbol">(</a><a id="19942" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="19949" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="19951" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="19958" href="literature.introduction-to-homotopy-type-theory.html#19930" class="Bound">n</a><a id="19959" class="Symbol">)</a>
<a id="19961" class="Symbol">_</a> <a id="19963" class="Symbol">=</a> <a id="19965" class="Symbol">λ</a> <a id="19967" href="literature.introduction-to-homotopy-type-theory.html#19967" class="Bound">n</a> <a id="19969" class="Symbol">→</a> <a id="19971" href="elementary-number-theory.equality-natural-numbers.html#1667" class="Function">Eq-eq-ℕ</a>
</pre>
### Exercises

**Exercise 6.1.** Addition and multiplication by a positive natural number are
injective functions.

<pre class="Agda"><a id="20108" class="Comment">-- (a)</a>
<a id="20115" class="Keyword">open</a> <a id="20120" class="Keyword">import</a> <a id="20127" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a> <a id="20177" class="Keyword">using</a>
  <a id="20185" class="Symbol">(</a> <a id="20187" href="elementary-number-theory.addition-natural-numbers.html#3304" class="Function">is-injective-right-add-ℕ</a><a id="20211" class="Symbol">)</a>

<a id="20214" href="literature.introduction-to-homotopy-type-theory.html#20214" class="Function">_</a> <a id="20216" class="Symbol">:</a> <a id="20218" class="Symbol">(</a><a id="20219" href="literature.introduction-to-homotopy-type-theory.html#20219" class="Bound">m</a> <a id="20221" href="literature.introduction-to-homotopy-type-theory.html#20221" class="Bound">n</a> <a id="20223" href="literature.introduction-to-homotopy-type-theory.html#20223" class="Bound">k</a> <a id="20225" class="Symbol">:</a> <a id="20227" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="20228" class="Symbol">)</a> <a id="20230" class="Symbol">→</a> <a id="20232" class="Symbol">(</a><a id="20233" href="literature.introduction-to-homotopy-type-theory.html#20219" class="Bound">m</a> <a id="20235" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20237" href="literature.introduction-to-homotopy-type-theory.html#20221" class="Bound">n</a><a id="20238" class="Symbol">)</a> <a id="20240" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="20242" class="Symbol">(</a><a id="20243" href="literature.introduction-to-homotopy-type-theory.html#20219" class="Bound">m</a> <a id="20245" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="20248" href="literature.introduction-to-homotopy-type-theory.html#20223" class="Bound">k</a> <a id="20250" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20252" href="literature.introduction-to-homotopy-type-theory.html#20221" class="Bound">n</a> <a id="20254" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="20257" href="literature.introduction-to-homotopy-type-theory.html#20223" class="Bound">k</a><a id="20258" class="Symbol">)</a>
<a id="20260" class="Symbol">_</a> <a id="20262" class="Symbol">=</a> <a id="20264" class="Symbol">λ</a> <a id="20266" href="literature.introduction-to-homotopy-type-theory.html#20266" class="Bound">m</a> <a id="20268" href="literature.introduction-to-homotopy-type-theory.html#20268" class="Bound">n</a> <a id="20270" href="literature.introduction-to-homotopy-type-theory.html#20270" class="Bound">k</a> <a id="20272" class="Symbol">→</a> <a id="20274" class="Symbol">(</a><a id="20275" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="20278" class="Symbol">(λ</a> <a id="20281" href="literature.introduction-to-homotopy-type-theory.html#20281" class="Bound">x</a> <a id="20283" class="Symbol">→</a> <a id="20285" href="literature.introduction-to-homotopy-type-theory.html#20281" class="Bound">x</a> <a id="20287" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="20290" href="literature.introduction-to-homotopy-type-theory.html#20270" class="Bound">k</a><a id="20291" class="Symbol">)</a> <a id="20293" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="20295" href="elementary-number-theory.addition-natural-numbers.html#3304" class="Function">is-injective-right-add-ℕ</a> <a id="20320" href="literature.introduction-to-homotopy-type-theory.html#20270" class="Bound">k</a><a id="20321" class="Symbol">)</a>

<a id="20324" class="Keyword">open</a> <a id="20329" class="Keyword">import</a> <a id="20336" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a> <a id="20392" class="Keyword">using</a>
  <a id="20400" class="Symbol">(</a> <a id="20402" href="elementary-number-theory.multiplication-natural-numbers.html#4798" class="Function">is-injective-right-mul-succ-ℕ</a><a id="20431" class="Symbol">)</a>

<a id="20434" href="literature.introduction-to-homotopy-type-theory.html#20434" class="Function">_</a> <a id="20436" class="Symbol">:</a> <a id="20438" class="Symbol">(</a><a id="20439" href="literature.introduction-to-homotopy-type-theory.html#20439" class="Bound">m</a> <a id="20441" href="literature.introduction-to-homotopy-type-theory.html#20441" class="Bound">n</a> <a id="20443" href="literature.introduction-to-homotopy-type-theory.html#20443" class="Bound">k</a> <a id="20445" class="Symbol">:</a> <a id="20447" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="20448" class="Symbol">)</a> <a id="20450" class="Symbol">→</a> <a id="20452" class="Symbol">(</a><a id="20453" href="literature.introduction-to-homotopy-type-theory.html#20439" class="Bound">m</a> <a id="20455" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20457" href="literature.introduction-to-homotopy-type-theory.html#20441" class="Bound">n</a><a id="20458" class="Symbol">)</a> <a id="20460" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="20462" class="Symbol">(</a><a id="20463" href="literature.introduction-to-homotopy-type-theory.html#20439" class="Bound">m</a> <a id="20465" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="20468" class="Symbol">(</a><a id="20469" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="20476" href="literature.introduction-to-homotopy-type-theory.html#20443" class="Bound">k</a><a id="20477" class="Symbol">)</a> <a id="20479" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20481" href="literature.introduction-to-homotopy-type-theory.html#20441" class="Bound">n</a> <a id="20483" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="20486" class="Symbol">(</a><a id="20487" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="20494" href="literature.introduction-to-homotopy-type-theory.html#20443" class="Bound">k</a><a id="20495" class="Symbol">))</a>
<a id="20498" class="Symbol">_</a> <a id="20500" class="Symbol">=</a>
  <a id="20504" class="Symbol">λ</a> <a id="20506" href="literature.introduction-to-homotopy-type-theory.html#20506" class="Bound">m</a> <a id="20508" href="literature.introduction-to-homotopy-type-theory.html#20508" class="Bound">n</a> <a id="20510" href="literature.introduction-to-homotopy-type-theory.html#20510" class="Bound">k</a> <a id="20512" class="Symbol">→</a> <a id="20514" class="Symbol">(</a><a id="20515" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="20518" class="Symbol">(λ</a> <a id="20521" href="literature.introduction-to-homotopy-type-theory.html#20521" class="Bound">x</a> <a id="20523" class="Symbol">→</a> <a id="20525" href="literature.introduction-to-homotopy-type-theory.html#20521" class="Bound">x</a> <a id="20527" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="20530" class="Symbol">(</a><a id="20531" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="20538" href="literature.introduction-to-homotopy-type-theory.html#20510" class="Bound">k</a><a id="20539" class="Symbol">))</a> <a id="20542" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="20544" href="elementary-number-theory.multiplication-natural-numbers.html#4798" class="Function">is-injective-right-mul-succ-ℕ</a> <a id="20574" href="literature.introduction-to-homotopy-type-theory.html#20510" class="Bound">k</a><a id="20575" class="Symbol">)</a>

<a id="20578" class="Keyword">open</a> <a id="20583" class="Keyword">import</a> <a id="20590" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a> <a id="20640" class="Keyword">using</a>
  <a id="20648" class="Symbol">(</a> <a id="20650" href="elementary-number-theory.addition-natural-numbers.html#4539" class="Function">is-zero-summand-is-zero-sum-ℕ</a>
  <a id="20682" class="Symbol">;</a> <a id="20684" href="elementary-number-theory.addition-natural-numbers.html#4761" class="Function">is-zero-sum-is-zero-summand-ℕ</a><a id="20713" class="Symbol">)</a>

<a id="20716" href="literature.introduction-to-homotopy-type-theory.html#20716" class="Function">_</a> <a id="20718" class="Symbol">:</a> <a id="20720" class="Symbol">(</a><a id="20721" href="literature.introduction-to-homotopy-type-theory.html#20721" class="Bound">m</a> <a id="20723" href="literature.introduction-to-homotopy-type-theory.html#20723" class="Bound">n</a> <a id="20725" class="Symbol">:</a> <a id="20727" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="20728" class="Symbol">)</a> <a id="20730" class="Symbol">→</a> <a id="20732" class="Symbol">(</a><a id="20733" href="literature.introduction-to-homotopy-type-theory.html#20721" class="Bound">m</a> <a id="20735" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="20738" href="literature.introduction-to-homotopy-type-theory.html#20723" class="Bound">n</a> <a id="20740" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20742" class="Number">0</a><a id="20743" class="Symbol">)</a> <a id="20745" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="20747" class="Symbol">(</a><a id="20748" href="literature.introduction-to-homotopy-type-theory.html#20721" class="Bound">m</a> <a id="20750" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20752" class="Number">0</a><a id="20753" class="Symbol">)</a> <a id="20755" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="20757" class="Symbol">(</a><a id="20758" href="literature.introduction-to-homotopy-type-theory.html#20723" class="Bound">n</a> <a id="20760" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="20762" class="Number">0</a><a id="20763" class="Symbol">)</a>
<a id="20765" class="Symbol">_</a> <a id="20767" class="Symbol">=</a>
  <a id="20771" class="Symbol">λ</a> <a id="20773" href="literature.introduction-to-homotopy-type-theory.html#20773" class="Bound">m</a> <a id="20775" href="literature.introduction-to-homotopy-type-theory.html#20775" class="Bound">n</a> <a id="20777" class="Symbol">→</a>
    <a id="20783" class="Symbol">(</a> <a id="20785" href="elementary-number-theory.addition-natural-numbers.html#4539" class="Function">is-zero-summand-is-zero-sum-ℕ</a> <a id="20815" href="literature.introduction-to-homotopy-type-theory.html#20773" class="Bound">m</a> <a id="20817" href="literature.introduction-to-homotopy-type-theory.html#20775" class="Bound">n</a> <a id="20819" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="20821" href="elementary-number-theory.addition-natural-numbers.html#4761" class="Function">is-zero-sum-is-zero-summand-ℕ</a> <a id="20851" href="literature.introduction-to-homotopy-type-theory.html#20773" class="Bound">m</a> <a id="20853" href="literature.introduction-to-homotopy-type-theory.html#20775" class="Bound">n</a><a id="20854" class="Symbol">)</a>

<a id="20857" class="Keyword">open</a> <a id="20862" class="Keyword">import</a> <a id="20869" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a> <a id="20925" class="Keyword">using</a>
  <a id="20933" class="Symbol">(</a> <a id="20935" href="elementary-number-theory.multiplication-natural-numbers.html#8187" class="Function">is-zero-summand-is-zero-mul-ℕ</a>
  <a id="20967" class="Symbol">;</a> <a id="20969" href="elementary-number-theory.multiplication-natural-numbers.html#8695" class="Function">is-zero-mul-ℕ-is-zero-summand</a>
  <a id="21001" class="Symbol">;</a> <a id="21003" href="elementary-number-theory.multiplication-natural-numbers.html#7699" class="Function">is-one-mul-ℕ</a>
  <a id="21018" class="Symbol">;</a> <a id="21020" href="elementary-number-theory.multiplication-natural-numbers.html#7533" class="Function">is-one-left-is-one-mul-ℕ</a>
  <a id="21047" class="Symbol">;</a> <a id="21049" href="elementary-number-theory.multiplication-natural-numbers.html#7122" class="Function">is-one-right-is-one-mul-ℕ</a><a id="21074" class="Symbol">)</a>

<a id="21077" href="literature.introduction-to-homotopy-type-theory.html#21077" class="Function">_</a> <a id="21079" class="Symbol">:</a> <a id="21081" class="Symbol">(</a><a id="21082" href="literature.introduction-to-homotopy-type-theory.html#21082" class="Bound">m</a> <a id="21084" href="literature.introduction-to-homotopy-type-theory.html#21084" class="Bound">n</a> <a id="21086" class="Symbol">:</a> <a id="21088" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="21089" class="Symbol">)</a> <a id="21091" class="Symbol">→</a> <a id="21093" class="Symbol">(</a><a id="21094" href="literature.introduction-to-homotopy-type-theory.html#21082" class="Bound">m</a> <a id="21096" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="21099" href="literature.introduction-to-homotopy-type-theory.html#21084" class="Bound">n</a> <a id="21101" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="21103" class="Number">0</a><a id="21104" class="Symbol">)</a> <a id="21106" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="21108" class="Symbol">(</a><a id="21109" href="literature.introduction-to-homotopy-type-theory.html#21082" class="Bound">m</a> <a id="21111" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="21113" class="Number">0</a><a id="21114" class="Symbol">)</a> <a id="21116" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="21118" class="Symbol">(</a><a id="21119" href="literature.introduction-to-homotopy-type-theory.html#21084" class="Bound">n</a> <a id="21121" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="21123" class="Number">0</a><a id="21124" class="Symbol">)</a>
<a id="21126" class="Symbol">_</a> <a id="21128" class="Symbol">=</a>
  <a id="21132" class="Symbol">λ</a> <a id="21134" href="literature.introduction-to-homotopy-type-theory.html#21134" class="Bound">m</a> <a id="21136" href="literature.introduction-to-homotopy-type-theory.html#21136" class="Bound">n</a> <a id="21138" class="Symbol">→</a>
    <a id="21144" href="elementary-number-theory.multiplication-natural-numbers.html#8187" class="Function">is-zero-summand-is-zero-mul-ℕ</a> <a id="21174" href="literature.introduction-to-homotopy-type-theory.html#21134" class="Bound">m</a> <a id="21176" href="literature.introduction-to-homotopy-type-theory.html#21136" class="Bound">n</a> <a id="21178" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="21180" href="elementary-number-theory.multiplication-natural-numbers.html#8695" class="Function">is-zero-mul-ℕ-is-zero-summand</a> <a id="21210" href="literature.introduction-to-homotopy-type-theory.html#21134" class="Bound">m</a> <a id="21212" href="literature.introduction-to-homotopy-type-theory.html#21136" class="Bound">n</a>

<a id="21215" href="literature.introduction-to-homotopy-type-theory.html#21215" class="Function">_</a> <a id="21217" class="Symbol">:</a> <a id="21219" class="Symbol">(</a><a id="21220" href="literature.introduction-to-homotopy-type-theory.html#21220" class="Bound">m</a> <a id="21222" href="literature.introduction-to-homotopy-type-theory.html#21222" class="Bound">n</a> <a id="21224" class="Symbol">:</a> <a id="21226" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="21227" class="Symbol">)</a> <a id="21229" class="Symbol">→</a> <a id="21231" class="Symbol">(</a><a id="21232" href="literature.introduction-to-homotopy-type-theory.html#21220" class="Bound">m</a> <a id="21234" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="21237" href="literature.introduction-to-homotopy-type-theory.html#21222" class="Bound">n</a> <a id="21239" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="21241" class="Number">1</a><a id="21242" class="Symbol">)</a> <a id="21244" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="21246" class="Symbol">(</a><a id="21247" href="literature.introduction-to-homotopy-type-theory.html#21220" class="Bound">m</a> <a id="21249" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="21251" class="Number">1</a><a id="21252" class="Symbol">)</a> <a id="21254" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="21256" class="Symbol">(</a><a id="21257" href="literature.introduction-to-homotopy-type-theory.html#21222" class="Bound">n</a> <a id="21259" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="21261" class="Number">1</a><a id="21262" class="Symbol">)</a>
<a id="21264" class="Symbol">_</a> <a id="21266" class="Symbol">=</a>
  <a id="21270" class="Symbol">λ</a> <a id="21272" href="literature.introduction-to-homotopy-type-theory.html#21272" class="Bound">m</a> <a id="21274" href="literature.introduction-to-homotopy-type-theory.html#21274" class="Bound">n</a> <a id="21276" class="Symbol">→</a>
    <a id="21282" class="Symbol">(</a> <a id="21284" class="Symbol">λ</a> <a id="21286" href="literature.introduction-to-homotopy-type-theory.html#21286" class="Bound">H</a> <a id="21288" class="Symbol">→</a> <a id="21290" href="elementary-number-theory.multiplication-natural-numbers.html#7533" class="Function">is-one-left-is-one-mul-ℕ</a> <a id="21315" href="literature.introduction-to-homotopy-type-theory.html#21272" class="Bound">m</a> <a id="21317" href="literature.introduction-to-homotopy-type-theory.html#21274" class="Bound">n</a> <a id="21319" href="literature.introduction-to-homotopy-type-theory.html#21286" class="Bound">H</a> <a id="21321" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="21323" href="elementary-number-theory.multiplication-natural-numbers.html#7122" class="Function">is-one-right-is-one-mul-ℕ</a> <a id="21349" href="literature.introduction-to-homotopy-type-theory.html#21272" class="Bound">m</a> <a id="21351" href="literature.introduction-to-homotopy-type-theory.html#21274" class="Bound">n</a> <a id="21353" href="literature.introduction-to-homotopy-type-theory.html#21286" class="Bound">H</a><a id="21354" class="Symbol">)</a> <a id="21356" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="21362" class="Symbol">(</a> <a id="21364" class="Symbol">λ</a> <a id="21366" class="Symbol">(</a><a id="21367" href="literature.introduction-to-homotopy-type-theory.html#21367" class="Bound">H</a> <a id="21369" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="21371" href="literature.introduction-to-homotopy-type-theory.html#21371" class="Bound">K</a><a id="21372" class="Symbol">)</a> <a id="21374" class="Symbol">→</a> <a id="21376" href="elementary-number-theory.multiplication-natural-numbers.html#7699" class="Function">is-one-mul-ℕ</a> <a id="21389" href="literature.introduction-to-homotopy-type-theory.html#21272" class="Bound">m</a> <a id="21391" href="literature.introduction-to-homotopy-type-theory.html#21274" class="Bound">n</a> <a id="21393" href="literature.introduction-to-homotopy-type-theory.html#21367" class="Bound">H</a> <a id="21395" href="literature.introduction-to-homotopy-type-theory.html#21371" class="Bound">K</a><a id="21396" class="Symbol">)</a>

<a id="21399" class="Comment">-- (c)</a>
<a id="21406" class="Keyword">open</a> <a id="21411" class="Keyword">import</a> <a id="21418" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a> <a id="21468" class="Keyword">using</a>
  <a id="21476" class="Symbol">(</a> <a id="21478" href="elementary-number-theory.addition-natural-numbers.html#4977" class="Function">neq-add-ℕ</a> <a id="21488" class="Comment">-- m ≠ m + (n + 1)</a>
  <a id="21509" class="Symbol">)</a>
<a id="21511" class="Keyword">open</a> <a id="21516" class="Keyword">import</a> <a id="21523" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a> <a id="21579" class="Keyword">using</a>
  <a id="21587" class="Symbol">(</a> <a id="21589" href="elementary-number-theory.multiplication-natural-numbers.html#7809" class="Function">neq-mul-ℕ</a> <a id="21599" class="Comment">-- m + 1 ≠ (m + 1) * (n + 2)</a>
  <a id="21630" class="Symbol">)</a>
</pre>
**Exercise 6.2.** Observational equality of booleans.

<pre class="Agda"><a id="21700" class="Comment">-- (a)</a>
<a id="21707" class="Keyword">open</a> <a id="21712" class="Keyword">import</a> <a id="21719" href="foundation.booleans.html" class="Module">foundation.booleans</a> <a id="21739" class="Keyword">using</a>
  <a id="21747" class="Symbol">(</a> <a id="21749" href="foundation.booleans.html#2864" class="Function">Eq-bool</a><a id="21756" class="Symbol">)</a>

<a id="21759" class="Comment">-- (b)</a>
<a id="21766" class="Keyword">open</a> <a id="21771" class="Keyword">import</a> <a id="21778" href="foundation.booleans.html" class="Module">foundation.booleans</a> <a id="21798" class="Keyword">using</a>
  <a id="21806" class="Symbol">(</a> <a id="21808" href="foundation.booleans.html#3096" class="Function">Eq-eq-bool</a>
  <a id="21821" class="Symbol">;</a> <a id="21823" href="foundation.booleans.html#3188" class="Function">eq-Eq-bool</a><a id="21833" class="Symbol">)</a>

<a id="21836" href="literature.introduction-to-homotopy-type-theory.html#21836" class="Function">_</a> <a id="21838" class="Symbol">:</a> <a id="21840" class="Symbol">(</a><a id="21841" href="literature.introduction-to-homotopy-type-theory.html#21841" class="Bound">x</a> <a id="21843" href="literature.introduction-to-homotopy-type-theory.html#21843" class="Bound">y</a> <a id="21845" class="Symbol">:</a> <a id="21847" href="foundation.booleans.html#1556" class="Datatype">bool</a><a id="21851" class="Symbol">)</a> <a id="21853" class="Symbol">→</a> <a id="21855" class="Symbol">(</a><a id="21856" href="literature.introduction-to-homotopy-type-theory.html#21841" class="Bound">x</a> <a id="21858" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="21860" href="literature.introduction-to-homotopy-type-theory.html#21843" class="Bound">y</a><a id="21861" class="Symbol">)</a> <a id="21863" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="21865" href="foundation.booleans.html#2864" class="Function">Eq-bool</a> <a id="21873" href="literature.introduction-to-homotopy-type-theory.html#21841" class="Bound">x</a> <a id="21875" href="literature.introduction-to-homotopy-type-theory.html#21843" class="Bound">y</a>
<a id="21877" class="Symbol">_</a> <a id="21879" class="Symbol">=</a> <a id="21881" class="Symbol">λ</a> <a id="21883" href="literature.introduction-to-homotopy-type-theory.html#21883" class="Bound">x</a> <a id="21885" href="literature.introduction-to-homotopy-type-theory.html#21885" class="Bound">y</a> <a id="21887" class="Symbol">→</a> <a id="21889" class="Symbol">(</a><a id="21890" href="foundation.booleans.html#3096" class="Function">Eq-eq-bool</a> <a id="21901" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="21903" href="foundation.booleans.html#3188" class="Function">eq-Eq-bool</a><a id="21913" class="Symbol">)</a>

<a id="21916" class="Comment">-- (c)</a>
<a id="21923" class="Keyword">open</a> <a id="21928" class="Keyword">import</a> <a id="21935" href="foundation.logical-operations-booleans.html" class="Module">foundation.logical-operations-booleans</a> <a id="21974" class="Keyword">using</a>
  <a id="21982" class="Symbol">(</a> <a id="21984" href="foundation.logical-operations-booleans.html#2116" class="Function">neq-neg-bool</a> <a id="21997" class="Comment">-- b ≠ neg-bool b</a>
  <a id="22017" class="Symbol">)</a>
<a id="22019" href="literature.introduction-to-homotopy-type-theory.html#22019" class="Function">_</a> <a id="22021" class="Symbol">:</a> <a id="22023" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="22025" class="Symbol">(</a><a id="22026" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="22032" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="22034" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a><a id="22038" class="Symbol">)</a>
<a id="22040" class="Symbol">_</a> <a id="22042" class="Symbol">=</a> <a id="22044" href="foundation.logical-operations-booleans.html#2116" class="Function">neq-neg-bool</a> <a id="22057" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a>
</pre>
**Exercise 6.3.** Standard linear order on ℕ.

<pre class="Agda"><a id="22123" class="Keyword">open</a> <a id="22128" class="Keyword">import</a> <a id="22135" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a> <a id="22187" class="Keyword">using</a>
  <a id="22195" class="Symbol">(</a> <a id="22197" href="elementary-number-theory.inequality-natural-numbers.html#1411" class="Function Operator">_≤-ℕ_</a><a id="22202" class="Symbol">)</a>

<a id="22205" class="Comment">-- (a)</a>
<a id="22212" class="Keyword">open</a> <a id="22217" class="Keyword">import</a> <a id="22224" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a> <a id="22276" class="Keyword">using</a>
  <a id="22284" class="Symbol">(</a> <a id="22286" href="elementary-number-theory.inequality-natural-numbers.html#2898" class="Function">refl-leq-ℕ</a>
  <a id="22299" class="Symbol">;</a> <a id="22301" href="elementary-number-theory.inequality-natural-numbers.html#3363" class="Function">antisymmetric-leq-ℕ</a>
  <a id="22323" class="Symbol">;</a> <a id="22325" href="elementary-number-theory.inequality-natural-numbers.html#3131" class="Function">transitive-leq-ℕ</a><a id="22341" class="Symbol">)</a>

<a id="22344" class="Comment">-- (b)</a>
<a id="22351" class="Keyword">open</a> <a id="22356" class="Keyword">import</a> <a id="22363" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a> <a id="22415" class="Keyword">using</a>
  <a id="22423" class="Symbol">(</a> <a id="22425" href="elementary-number-theory.inequality-natural-numbers.html#4160" class="Function">linear-leq-ℕ</a> <a id="22438" class="Comment">-- (m ≤ n) + (n ≤ m)</a>
  <a id="22461" class="Symbol">)</a>

<a id="22464" class="Comment">-- (c)</a>
<a id="22471" class="Keyword">open</a> <a id="22476" class="Keyword">import</a> <a id="22483" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a> <a id="22535" class="Keyword">using</a>
  <a id="22543" class="Symbol">(</a> <a id="22545" href="elementary-number-theory.inequality-natural-numbers.html#8432" class="Function">preserves-leq-left-add-ℕ</a>
  <a id="22572" class="Symbol">;</a> <a id="22574" href="elementary-number-theory.inequality-natural-numbers.html#9207" class="Function">reflects-leq-left-add-ℕ</a><a id="22597" class="Symbol">)</a>

<a id="22600" href="literature.introduction-to-homotopy-type-theory.html#22600" class="Function">_</a> <a id="22602" class="Symbol">:</a> <a id="22604" class="Symbol">(</a><a id="22605" href="literature.introduction-to-homotopy-type-theory.html#22605" class="Bound">m</a> <a id="22607" href="literature.introduction-to-homotopy-type-theory.html#22607" class="Bound">n</a> <a id="22609" href="literature.introduction-to-homotopy-type-theory.html#22609" class="Bound">k</a> <a id="22611" class="Symbol">:</a> <a id="22613" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="22614" class="Symbol">)</a> <a id="22616" class="Symbol">→</a> <a id="22618" class="Symbol">(</a><a id="22619" href="literature.introduction-to-homotopy-type-theory.html#22605" class="Bound">m</a> <a id="22621" href="elementary-number-theory.inequality-natural-numbers.html#1411" class="Function Operator">≤-ℕ</a> <a id="22625" href="literature.introduction-to-homotopy-type-theory.html#22607" class="Bound">n</a><a id="22626" class="Symbol">)</a> <a id="22628" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="22630" class="Symbol">(</a><a id="22631" href="literature.introduction-to-homotopy-type-theory.html#22605" class="Bound">m</a> <a id="22633" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="22636" href="literature.introduction-to-homotopy-type-theory.html#22609" class="Bound">k</a> <a id="22638" href="elementary-number-theory.inequality-natural-numbers.html#1411" class="Function Operator">≤-ℕ</a> <a id="22642" href="literature.introduction-to-homotopy-type-theory.html#22607" class="Bound">n</a> <a id="22644" href="elementary-number-theory.addition-natural-numbers.html#907" class="Primitive Operator">+ℕ</a> <a id="22647" href="literature.introduction-to-homotopy-type-theory.html#22609" class="Bound">k</a><a id="22648" class="Symbol">)</a>
<a id="22650" class="Symbol">_</a> <a id="22652" class="Symbol">=</a>
  <a id="22656" class="Symbol">λ</a> <a id="22658" href="literature.introduction-to-homotopy-type-theory.html#22658" class="Bound">m</a> <a id="22660" href="literature.introduction-to-homotopy-type-theory.html#22660" class="Bound">n</a> <a id="22662" href="literature.introduction-to-homotopy-type-theory.html#22662" class="Bound">k</a> <a id="22664" class="Symbol">→</a> <a id="22666" class="Symbol">(</a><a id="22667" href="elementary-number-theory.inequality-natural-numbers.html#8432" class="Function">preserves-leq-left-add-ℕ</a> <a id="22692" href="literature.introduction-to-homotopy-type-theory.html#22662" class="Bound">k</a> <a id="22694" href="literature.introduction-to-homotopy-type-theory.html#22658" class="Bound">m</a> <a id="22696" href="literature.introduction-to-homotopy-type-theory.html#22660" class="Bound">n</a> <a id="22698" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="22700" href="elementary-number-theory.inequality-natural-numbers.html#9207" class="Function">reflects-leq-left-add-ℕ</a> <a id="22724" href="literature.introduction-to-homotopy-type-theory.html#22662" class="Bound">k</a> <a id="22726" href="literature.introduction-to-homotopy-type-theory.html#22658" class="Bound">m</a> <a id="22728" href="literature.introduction-to-homotopy-type-theory.html#22660" class="Bound">n</a><a id="22729" class="Symbol">)</a>

<a id="22732" class="Comment">-- (d)</a>
<a id="22739" class="Keyword">open</a> <a id="22744" class="Keyword">import</a> <a id="22751" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a> <a id="22803" class="Keyword">using</a>
  <a id="22811" class="Symbol">(</a> <a id="22813" href="elementary-number-theory.inequality-natural-numbers.html#10651" class="Function">preserves-leq-left-mul-ℕ</a>
  <a id="22840" class="Symbol">;</a> <a id="22842" href="elementary-number-theory.inequality-natural-numbers.html#11531" class="Function">reflects-order-mul-ℕ</a><a id="22862" class="Symbol">)</a>

<a id="22865" href="literature.introduction-to-homotopy-type-theory.html#22865" class="Function">_</a> <a id="22867" class="Symbol">:</a> <a id="22869" class="Symbol">(</a><a id="22870" href="literature.introduction-to-homotopy-type-theory.html#22870" class="Bound">m</a> <a id="22872" href="literature.introduction-to-homotopy-type-theory.html#22872" class="Bound">n</a> <a id="22874" href="literature.introduction-to-homotopy-type-theory.html#22874" class="Bound">k</a> <a id="22876" class="Symbol">:</a> <a id="22878" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="22879" class="Symbol">)</a> <a id="22881" class="Symbol">→</a> <a id="22883" class="Symbol">(</a><a id="22884" href="literature.introduction-to-homotopy-type-theory.html#22870" class="Bound">m</a> <a id="22886" href="elementary-number-theory.inequality-natural-numbers.html#1411" class="Function Operator">≤-ℕ</a> <a id="22890" href="literature.introduction-to-homotopy-type-theory.html#22872" class="Bound">n</a><a id="22891" class="Symbol">)</a> <a id="22893" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="22895" class="Symbol">(</a><a id="22896" href="literature.introduction-to-homotopy-type-theory.html#22870" class="Bound">m</a> <a id="22898" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="22901" class="Symbol">(</a><a id="22902" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="22909" href="literature.introduction-to-homotopy-type-theory.html#22874" class="Bound">k</a><a id="22910" class="Symbol">)</a> <a id="22912" href="elementary-number-theory.inequality-natural-numbers.html#1411" class="Function Operator">≤-ℕ</a> <a id="22916" href="literature.introduction-to-homotopy-type-theory.html#22872" class="Bound">n</a> <a id="22918" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="22921" class="Symbol">(</a><a id="22922" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="22929" href="literature.introduction-to-homotopy-type-theory.html#22874" class="Bound">k</a><a id="22930" class="Symbol">))</a>
<a id="22933" class="Symbol">_</a> <a id="22935" class="Symbol">=</a>
  <a id="22939" class="Symbol">λ</a> <a id="22941" href="literature.introduction-to-homotopy-type-theory.html#22941" class="Bound">m</a> <a id="22943" href="literature.introduction-to-homotopy-type-theory.html#22943" class="Bound">n</a> <a id="22945" href="literature.introduction-to-homotopy-type-theory.html#22945" class="Bound">k</a> <a id="22947" class="Symbol">→</a>
    <a id="22953" class="Symbol">(</a><a id="22954" href="elementary-number-theory.inequality-natural-numbers.html#10651" class="Function">preserves-leq-left-mul-ℕ</a> <a id="22979" class="Symbol">(</a><a id="22980" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="22987" href="literature.introduction-to-homotopy-type-theory.html#22945" class="Bound">k</a><a id="22988" class="Symbol">)</a> <a id="22990" href="literature.introduction-to-homotopy-type-theory.html#22941" class="Bound">m</a> <a id="22992" href="literature.introduction-to-homotopy-type-theory.html#22943" class="Bound">n</a> <a id="22994" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="22996" href="elementary-number-theory.inequality-natural-numbers.html#11531" class="Function">reflects-order-mul-ℕ</a> <a id="23017" href="literature.introduction-to-homotopy-type-theory.html#22945" class="Bound">k</a> <a id="23019" href="literature.introduction-to-homotopy-type-theory.html#22941" class="Bound">m</a> <a id="23021" href="literature.introduction-to-homotopy-type-theory.html#22943" class="Bound">n</a><a id="23022" class="Symbol">)</a>

<a id="23025" class="Comment">-- (e)</a>
<a id="23032" class="Keyword">open</a> <a id="23037" class="Keyword">import</a> <a id="23044" href="elementary-number-theory.minimum-natural-numbers.html" class="Module">elementary-number-theory.minimum-natural-numbers</a> <a id="23093" class="Keyword">using</a>
  <a id="23101" class="Symbol">(</a> <a id="23103" href="elementary-number-theory.minimum-natural-numbers.html#2452" class="Function">is-greatest-lower-bound-min-ℕ</a> <a id="23133" class="Comment">-- (k ≤ min m n) ↔ (k ≤ m) × (k ≤ n)</a>
  <a id="23172" class="Symbol">)</a>
<a id="23174" class="Keyword">open</a> <a id="23179" class="Keyword">import</a> <a id="23186" href="elementary-number-theory.maximum-natural-numbers.html" class="Module">elementary-number-theory.maximum-natural-numbers</a> <a id="23235" class="Keyword">using</a>
  <a id="23243" class="Symbol">(</a> <a id="23245" href="elementary-number-theory.maximum-natural-numbers.html#2663" class="Function">is-least-upper-bound-max-ℕ</a> <a id="23272" class="Comment">-- (max m n ≤ k) ↔ (m ≤ k) × (n ≤ k)</a>
  <a id="23311" class="Symbol">)</a>
</pre>
**Exercise 6.4.** Standard strict order on ℕ.

<pre class="Agda"><a id="23373" class="Keyword">open</a> <a id="23378" class="Keyword">import</a> <a id="23385" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a> <a id="23444" class="Keyword">using</a>
  <a id="23452" class="Symbol">(</a> <a id="23454" href="elementary-number-theory.strict-inequality-natural-numbers.html#1861" class="Function Operator">_&lt;-ℕ_</a><a id="23459" class="Symbol">)</a>

<a id="23462" class="Comment">-- (a)</a>
<a id="23469" class="Keyword">open</a> <a id="23474" class="Keyword">import</a> <a id="23481" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a> <a id="23540" class="Keyword">using</a>
  <a id="23548" class="Symbol">(</a> <a id="23550" href="elementary-number-theory.strict-inequality-natural-numbers.html#3766" class="Function">anti-reflexive-le-ℕ</a>
  <a id="23572" class="Symbol">;</a> <a id="23574" href="elementary-number-theory.strict-inequality-natural-numbers.html#4188" class="Function">antisymmetric-le-ℕ</a>
  <a id="23595" class="Symbol">;</a> <a id="23597" href="elementary-number-theory.strict-inequality-natural-numbers.html#4414" class="Function">transitive-le-ℕ</a><a id="23612" class="Symbol">)</a>

<a id="23615" class="Comment">-- (b)</a>
<a id="23622" class="Keyword">open</a> <a id="23627" class="Keyword">import</a> <a id="23634" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a> <a id="23693" class="Keyword">using</a>
  <a id="23701" class="Symbol">(</a> <a id="23703" href="elementary-number-theory.strict-inequality-natural-numbers.html#6630" class="Function">succ-le-ℕ</a> <a id="23713" class="Comment">-- n &lt; n + 1</a>
  <a id="23728" class="Symbol">;</a> <a id="23730" href="elementary-number-theory.strict-inequality-natural-numbers.html#6811" class="Function">preserves-le-succ-ℕ</a> <a id="23750" class="Comment">-- m &lt; n → m &lt; n + 1</a>
  <a id="23773" class="Symbol">)</a>

<a id="23776" class="Comment">-- (c)</a>
<a id="23783" class="Keyword">open</a> <a id="23788" class="Keyword">import</a> <a id="23795" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a> <a id="23854" class="Keyword">using</a>
  <a id="23862" class="Symbol">(</a> <a id="23864" href="elementary-number-theory.strict-inequality-natural-numbers.html#8897" class="Function">leq-succ-le-ℕ</a>
  <a id="23880" class="Symbol">;</a> <a id="23882" href="elementary-number-theory.strict-inequality-natural-numbers.html#9104" class="Function">le-leq-succ-ℕ</a>
  <a id="23898" class="Symbol">;</a> <a id="23900" href="elementary-number-theory.strict-inequality-natural-numbers.html#7585" class="Function">contradiction-le-ℕ</a>
  <a id="23921" class="Symbol">;</a> <a id="23923" href="elementary-number-theory.strict-inequality-natural-numbers.html#8233" class="Function">le-not-leq-ℕ</a><a id="23935" class="Symbol">)</a>

<a id="23938" href="literature.introduction-to-homotopy-type-theory.html#23938" class="Function">_</a> <a id="23940" class="Symbol">:</a> <a id="23942" class="Symbol">(</a><a id="23943" href="literature.introduction-to-homotopy-type-theory.html#23943" class="Bound">m</a> <a id="23945" href="literature.introduction-to-homotopy-type-theory.html#23945" class="Bound">n</a> <a id="23947" class="Symbol">:</a> <a id="23949" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="23950" class="Symbol">)</a> <a id="23952" class="Symbol">→</a> <a id="23954" class="Symbol">(</a><a id="23955" href="literature.introduction-to-homotopy-type-theory.html#23943" class="Bound">m</a> <a id="23957" href="elementary-number-theory.strict-inequality-natural-numbers.html#1861" class="Function Operator">&lt;-ℕ</a> <a id="23961" href="literature.introduction-to-homotopy-type-theory.html#23945" class="Bound">n</a><a id="23962" class="Symbol">)</a> <a id="23964" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="23966" class="Symbol">(</a><a id="23967" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="23974" href="literature.introduction-to-homotopy-type-theory.html#23943" class="Bound">m</a> <a id="23976" href="elementary-number-theory.inequality-natural-numbers.html#1411" class="Function Operator">≤-ℕ</a> <a id="23980" href="literature.introduction-to-homotopy-type-theory.html#23945" class="Bound">n</a><a id="23981" class="Symbol">)</a>
<a id="23983" class="Symbol">_</a> <a id="23985" class="Symbol">=</a> <a id="23987" class="Symbol">λ</a> <a id="23989" href="literature.introduction-to-homotopy-type-theory.html#23989" class="Bound">m</a> <a id="23991" href="literature.introduction-to-homotopy-type-theory.html#23991" class="Bound">n</a> <a id="23993" class="Symbol">→</a> <a id="23995" href="elementary-number-theory.strict-inequality-natural-numbers.html#8897" class="Function">leq-succ-le-ℕ</a> <a id="24009" href="literature.introduction-to-homotopy-type-theory.html#23989" class="Bound">m</a> <a id="24011" href="literature.introduction-to-homotopy-type-theory.html#23991" class="Bound">n</a> <a id="24013" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="24015" href="elementary-number-theory.strict-inequality-natural-numbers.html#9104" class="Function">le-leq-succ-ℕ</a> <a id="24029" href="literature.introduction-to-homotopy-type-theory.html#23989" class="Bound">m</a> <a id="24031" href="literature.introduction-to-homotopy-type-theory.html#23991" class="Bound">n</a>

<a id="24034" href="literature.introduction-to-homotopy-type-theory.html#24034" class="Function">_</a> <a id="24036" class="Symbol">:</a> <a id="24038" class="Symbol">(</a><a id="24039" href="literature.introduction-to-homotopy-type-theory.html#24039" class="Bound">m</a> <a id="24041" href="literature.introduction-to-homotopy-type-theory.html#24041" class="Bound">n</a> <a id="24043" class="Symbol">:</a> <a id="24045" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="24046" class="Symbol">)</a> <a id="24048" class="Symbol">→</a> <a id="24050" class="Symbol">(</a><a id="24051" href="literature.introduction-to-homotopy-type-theory.html#24039" class="Bound">m</a> <a id="24053" href="elementary-number-theory.strict-inequality-natural-numbers.html#1861" class="Function Operator">&lt;-ℕ</a> <a id="24057" href="literature.introduction-to-homotopy-type-theory.html#24041" class="Bound">n</a><a id="24058" class="Symbol">)</a> <a id="24060" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="24062" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="24064" class="Symbol">(</a><a id="24065" href="literature.introduction-to-homotopy-type-theory.html#24041" class="Bound">n</a> <a id="24067" href="elementary-number-theory.inequality-natural-numbers.html#1411" class="Function Operator">≤-ℕ</a> <a id="24071" href="literature.introduction-to-homotopy-type-theory.html#24039" class="Bound">m</a><a id="24072" class="Symbol">)</a>
<a id="24074" class="Symbol">_</a> <a id="24076" class="Symbol">=</a> <a id="24078" class="Symbol">λ</a> <a id="24080" href="literature.introduction-to-homotopy-type-theory.html#24080" class="Bound">m</a> <a id="24082" href="literature.introduction-to-homotopy-type-theory.html#24082" class="Bound">n</a> <a id="24084" class="Symbol">→</a> <a id="24086" href="elementary-number-theory.strict-inequality-natural-numbers.html#7585" class="Function">contradiction-le-ℕ</a> <a id="24105" href="literature.introduction-to-homotopy-type-theory.html#24080" class="Bound">m</a> <a id="24107" href="literature.introduction-to-homotopy-type-theory.html#24082" class="Bound">n</a> <a id="24109" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="24111" href="elementary-number-theory.strict-inequality-natural-numbers.html#8233" class="Function">le-not-leq-ℕ</a> <a id="24124" href="literature.introduction-to-homotopy-type-theory.html#24080" class="Bound">m</a> <a id="24126" href="literature.introduction-to-homotopy-type-theory.html#24082" class="Bound">n</a>
</pre>
**Exercise 6.5.** Distance function on ℕ.

<pre class="Agda"><a id="24184" class="Keyword">open</a> <a id="24189" class="Keyword">import</a> <a id="24196" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a> <a id="24246" class="Keyword">using</a>
  <a id="24254" class="Symbol">(</a> <a id="24256" href="elementary-number-theory.distance-natural-numbers.html#1461" class="Function">dist-ℕ</a><a id="24262" class="Symbol">)</a>

<a id="24265" class="Comment">-- (a)</a>
<a id="24272" class="Keyword">open</a> <a id="24277" class="Keyword">import</a> <a id="24284" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a> <a id="24334" class="Keyword">using</a>
  <a id="24342" class="Symbol">(</a> <a id="24344" href="elementary-number-theory.distance-natural-numbers.html#2101" class="Function">dist-eq-ℕ</a>
  <a id="24356" class="Symbol">;</a> <a id="24358" href="elementary-number-theory.distance-natural-numbers.html#1839" class="Function">eq-dist-ℕ</a>
  <a id="24370" class="Symbol">;</a> <a id="24372" href="elementary-number-theory.distance-natural-numbers.html#2777" class="Function">symmetric-dist-ℕ</a> <a id="24389" class="Comment">-- dist m n = dist n m</a>
  <a id="24414" class="Symbol">;</a> <a id="24416" href="elementary-number-theory.distance-natural-numbers.html#3362" class="Function">triangle-inequality-dist-ℕ</a> <a id="24443" class="Comment">-- dist m n ≤ dist m k + dist k n</a>
  <a id="24479" class="Symbol">)</a>

<a id="24482" href="literature.introduction-to-homotopy-type-theory.html#24482" class="Function">_</a> <a id="24484" class="Symbol">:</a> <a id="24486" class="Symbol">(</a><a id="24487" href="literature.introduction-to-homotopy-type-theory.html#24487" class="Bound">m</a> <a id="24489" href="literature.introduction-to-homotopy-type-theory.html#24489" class="Bound">n</a> <a id="24491" class="Symbol">:</a> <a id="24493" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="24494" class="Symbol">)</a> <a id="24496" class="Symbol">→</a> <a id="24498" class="Symbol">(</a><a id="24499" href="literature.introduction-to-homotopy-type-theory.html#24487" class="Bound">m</a> <a id="24501" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="24503" href="literature.introduction-to-homotopy-type-theory.html#24489" class="Bound">n</a><a id="24504" class="Symbol">)</a> <a id="24506" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="24508" class="Symbol">(</a><a id="24509" href="elementary-number-theory.distance-natural-numbers.html#1461" class="Function">dist-ℕ</a> <a id="24516" href="literature.introduction-to-homotopy-type-theory.html#24487" class="Bound">m</a> <a id="24518" href="literature.introduction-to-homotopy-type-theory.html#24489" class="Bound">n</a> <a id="24520" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="24522" class="Number">0</a><a id="24523" class="Symbol">)</a>
<a id="24525" class="Symbol">_</a> <a id="24527" class="Symbol">=</a> <a id="24529" class="Symbol">λ</a> <a id="24531" href="literature.introduction-to-homotopy-type-theory.html#24531" class="Bound">m</a> <a id="24533" href="literature.introduction-to-homotopy-type-theory.html#24533" class="Bound">n</a> <a id="24535" class="Symbol">→</a> <a id="24537" class="Symbol">(</a><a id="24538" href="elementary-number-theory.distance-natural-numbers.html#2101" class="Function">dist-eq-ℕ</a> <a id="24548" href="literature.introduction-to-homotopy-type-theory.html#24531" class="Bound">m</a> <a id="24550" href="literature.introduction-to-homotopy-type-theory.html#24533" class="Bound">n</a> <a id="24552" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="24554" href="elementary-number-theory.distance-natural-numbers.html#1839" class="Function">eq-dist-ℕ</a> <a id="24564" href="literature.introduction-to-homotopy-type-theory.html#24531" class="Bound">m</a> <a id="24566" href="literature.introduction-to-homotopy-type-theory.html#24533" class="Bound">n</a><a id="24567" class="Symbol">)</a>

<a id="24570" class="Comment">-- TODO: b</a>

<a id="24582" class="Comment">-- (c)</a>
<a id="24589" class="Keyword">open</a> <a id="24594" class="Keyword">import</a> <a id="24601" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a> <a id="24651" class="Keyword">using</a>
  <a id="24659" class="Symbol">(</a> <a id="24661" href="elementary-number-theory.distance-natural-numbers.html#11174" class="Function">translation-invariant-dist-ℕ</a> <a id="24690" class="Comment">-- dist (a + m) (a + n) = dist m n</a>
  <a id="24727" class="Symbol">;</a> <a id="24729" href="elementary-number-theory.distance-natural-numbers.html#12950" class="Function">left-distributive-mul-dist-ℕ&#39;</a> <a id="24759" class="Comment">-- dist (k * m) (k * n) = k * (dist m n)</a>
  <a id="24802" class="Symbol">)</a>

<a id="24805" class="Comment">-- (d)</a>
<a id="24812" class="Keyword">open</a> <a id="24817" class="Keyword">import</a> <a id="24824" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a> <a id="24874" class="Keyword">using</a>
  <a id="24882" class="Symbol">(</a> <a id="24884" href="elementary-number-theory.distance-natural-numbers.html#5282" class="Function">is-additive-right-inverse-dist-ℕ</a> <a id="24917" class="Comment">-- x + dist x y = y for x ≤ y</a>
  <a id="24949" class="Symbol">)</a>
</pre>
**Exercise 6.6.** The absolute value function.

<pre class="Agda"><a id="25012" class="Keyword">open</a> <a id="25017" class="Keyword">import</a> <a id="25024" href="elementary-number-theory.absolute-value-integers.html" class="Module">elementary-number-theory.absolute-value-integers</a> <a id="25073" class="Keyword">using</a>
  <a id="25081" class="Symbol">(</a> <a id="25083" href="elementary-number-theory.absolute-value-integers.html#1126" class="Function">abs-ℤ</a>
  <a id="25091" class="Symbol">;</a> <a id="25093" href="elementary-number-theory.absolute-value-integers.html#1903" class="Function">eq-abs-ℤ</a>
  <a id="25104" class="Symbol">;</a> <a id="25106" href="elementary-number-theory.absolute-value-integers.html#1994" class="Function">abs-eq-ℤ</a>
  <a id="25117" class="Symbol">;</a> <a id="25119" href="elementary-number-theory.absolute-value-integers.html#2885" class="Function">subadditive-abs-ℤ</a> <a id="25137" class="Comment">-- |x + y| ≤ |x| + |y|</a>
  <a id="25162" class="Symbol">;</a> <a id="25164" href="elementary-number-theory.absolute-value-integers.html#5634" class="Function">multiplicative-abs-ℤ</a> <a id="25185" class="Comment">-- |x * y| = |x| * |y|</a>
  <a id="25210" class="Symbol">)</a>

<a id="25213" href="literature.introduction-to-homotopy-type-theory.html#25213" class="Function">_</a> <a id="25215" class="Symbol">:</a> <a id="25217" class="Symbol">(</a><a id="25218" href="literature.introduction-to-homotopy-type-theory.html#25218" class="Bound">x</a> <a id="25220" class="Symbol">:</a> <a id="25222" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a><a id="25223" class="Symbol">)</a> <a id="25225" class="Symbol">→</a> <a id="25227" class="Symbol">(</a><a id="25228" href="literature.introduction-to-homotopy-type-theory.html#25218" class="Bound">x</a> <a id="25230" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="25232" href="elementary-number-theory.integers.html#1569" class="Function">zero-ℤ</a><a id="25238" class="Symbol">)</a> <a id="25240" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="25242" class="Symbol">(</a><a id="25243" href="elementary-number-theory.absolute-value-integers.html#1126" class="Function">abs-ℤ</a> <a id="25249" href="literature.introduction-to-homotopy-type-theory.html#25218" class="Bound">x</a> <a id="25251" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="25253" class="Number">0</a><a id="25254" class="Symbol">)</a>
<a id="25256" class="Symbol">_</a> <a id="25258" class="Symbol">=</a> <a id="25260" class="Symbol">λ</a> <a id="25262" href="literature.introduction-to-homotopy-type-theory.html#25262" class="Bound">x</a> <a id="25264" class="Symbol">→</a> <a id="25266" class="Symbol">(</a><a id="25267" href="elementary-number-theory.absolute-value-integers.html#1994" class="Function">abs-eq-ℤ</a> <a id="25276" href="literature.introduction-to-homotopy-type-theory.html#25262" class="Bound">x</a> <a id="25278" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="25280" href="elementary-number-theory.absolute-value-integers.html#1903" class="Function">eq-abs-ℤ</a> <a id="25289" href="literature.introduction-to-homotopy-type-theory.html#25262" class="Bound">x</a><a id="25290" class="Symbol">)</a>
</pre>
## 7 Modular arithmetic via the Curry-Howard interpretation

### 7.1 The Curry-Howard interpretation

**Definition 7.1.2.** The divisibility relation.

Note that the library's division relation uses the property `k * d = n`, as
opposed to the book's `d * k = n`.

<pre class="Agda"><a id="25569" class="Keyword">open</a> <a id="25574" class="Keyword">import</a> <a id="25581" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a> <a id="25635" class="Keyword">using</a>
  <a id="25643" class="Symbol">(</a> <a id="25645" href="elementary-number-theory.divisibility-natural-numbers.html#1683" class="Function">div-ℕ</a><a id="25650" class="Symbol">)</a>
</pre>
**Example 7.1.4.** Divisibility by one.

<pre class="Agda"><a id="25706" class="Keyword">open</a> <a id="25711" class="Keyword">import</a> <a id="25718" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a> <a id="25772" class="Keyword">using</a>
  <a id="25780" class="Symbol">(</a> <a id="25782" href="elementary-number-theory.divisibility-natural-numbers.html#5926" class="Function">div-one-ℕ</a> <a id="25792" class="Comment">-- 1 | x</a>
  <a id="25803" class="Symbol">)</a>
</pre>
**Proposition 7.1.5.** A 3-for-2 property of division.
<a id="proposition-7.1.5"></a>

<pre class="Agda"><a id="25905" class="Keyword">open</a> <a id="25910" class="Keyword">import</a> <a id="25917" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a> <a id="25971" class="Keyword">using</a>
  <a id="25979" class="Symbol">(</a> <a id="25981" href="elementary-number-theory.divisibility-natural-numbers.html#8043" class="Function">div-add-ℕ</a> <a id="25991" class="Comment">-- d | x → d | y → d | (x + y)</a>
  <a id="26024" class="Symbol">)</a>
</pre>
The other other two claims are shown in Exercise [7.1](#exercise-7.1).

### 7.2 The congruence relations on ℕ

**Definition 7.2.1.** Typal binary relations.

<pre class="Agda"><a id="26197" class="Keyword">open</a> <a id="26202" class="Keyword">import</a> <a id="26209" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a> <a id="26237" class="Keyword">using</a>
  <a id="26245" class="Symbol">(</a> <a id="26247" href="foundation.binary-relations.html#1220" class="Function">Relation</a>
  <a id="26258" class="Symbol">;</a> <a id="26260" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a>
  <a id="26275" class="Symbol">;</a> <a id="26277" href="foundation.binary-relations.html#3402" class="Function">is-symmetric</a>
  <a id="26292" class="Symbol">;</a> <a id="26294" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a><a id="26307" class="Symbol">)</a>
<a id="26309" class="Comment">-- TODO: there is no is-equivalence, and equivalence relations are only Prop-valued. Why?</a>
</pre>
**Definition 7.2.2.** Congruence relations on ℕ.

<pre class="Agda"><a id="26462" class="Keyword">open</a> <a id="26467" class="Keyword">import</a> <a id="26474" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a> <a id="26526" class="Keyword">using</a>
  <a id="26534" class="Symbol">(</a> <a id="26536" href="elementary-number-theory.congruence-natural-numbers.html#1093" class="Function Operator">_≡_mod_</a><a id="26543" class="Symbol">)</a>
</pre>
**Example 7.2.3.** The modulus is congruent to zero.

<pre class="Agda"><a id="26612" class="Keyword">open</a> <a id="26617" class="Keyword">import</a> <a id="26624" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a> <a id="26676" class="Keyword">using</a>
  <a id="26684" class="Symbol">(</a> <a id="26686" href="elementary-number-theory.congruence-natural-numbers.html#1839" class="Function">cong-zero-ℕ</a> <a id="26698" class="Comment">-- k ≡ 0 mod k</a>
  <a id="26715" class="Symbol">)</a>
</pre>
**Proposition 7.2.4.** Congruence modulo `k` is an equivalence relation.

<pre class="Agda"><a id="26804" class="Keyword">open</a> <a id="26809" class="Keyword">import</a> <a id="26816" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a> <a id="26868" class="Keyword">using</a>
  <a id="26876" class="Symbol">(</a> <a id="26878" href="elementary-number-theory.congruence-natural-numbers.html#1990" class="Function">refl-cong-ℕ</a>
  <a id="26892" class="Symbol">;</a> <a id="26894" href="elementary-number-theory.congruence-natural-numbers.html#2277" class="Function">symmetric-cong-ℕ</a>
  <a id="26913" class="Symbol">;</a> <a id="26915" href="elementary-number-theory.congruence-natural-numbers.html#2551" class="Function">transitive-cong-ℕ</a><a id="26932" class="Symbol">)</a>
</pre>
### 7.3 The standard finite types

**Definition 7.3.2.** The standard finite types.

The point `⋆` is called `neg-one-Fin` because it represents the element `k - 1`
under the inclusion into ℕ.

<pre class="Agda"><a id="27141" class="Keyword">open</a> <a id="27146" class="Keyword">import</a> <a id="27153" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="27199" class="Keyword">using</a>
  <a id="27207" class="Symbol">(</a> <a id="27209" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a>
  <a id="27215" class="Symbol">;</a> <a id="27217" href="univalent-combinatorics.standard-finite-types.html#2323" class="Function">inl-Fin</a> <a id="27225" class="Comment">-- inclusion Fin k → Fin (k + 1)</a>
  <a id="27260" class="Symbol">;</a> <a id="27262" href="univalent-combinatorics.standard-finite-types.html#2498" class="Function">neg-one-Fin</a> <a id="27274" class="Comment">-- point Fin (k + 1)</a>
  <a id="27297" class="Symbol">)</a>
</pre>
**Definition 7.3.4.** Inclusion into ℕ.

<pre class="Agda"><a id="27353" class="Keyword">open</a> <a id="27358" class="Keyword">import</a> <a id="27365" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="27411" class="Keyword">using</a>
  <a id="27419" class="Symbol">(</a> <a id="27421" href="univalent-combinatorics.standard-finite-types.html#6914" class="Function">nat-Fin</a><a id="27428" class="Symbol">)</a>
</pre>
**Lemma 7.3.5.** The inclusion into ℕ is bounded.

<pre class="Agda"><a id="27494" class="Keyword">open</a> <a id="27499" class="Keyword">import</a> <a id="27506" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="27552" class="Keyword">using</a>
  <a id="27560" class="Symbol">(</a> <a id="27562" href="univalent-combinatorics.standard-finite-types.html#7161" class="Function">strict-upper-bound-nat-Fin</a> <a id="27589" class="Comment">-- ι x &lt; k</a>
  <a id="27602" class="Symbol">)</a>
</pre>
**Proposition 7.3.6.** The inclusion into ℕ is injective.

<pre class="Agda"><a id="27676" class="Keyword">open</a> <a id="27681" class="Keyword">import</a> <a id="27688" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="27734" class="Keyword">using</a>
  <a id="27742" class="Symbol">(</a> <a id="27744" href="univalent-combinatorics.standard-finite-types.html#7936" class="Function">is-injective-nat-Fin</a><a id="27764" class="Symbol">)</a>
</pre>
### 7.4 The natural numbers modulo `k + 1`

**Definition 7.4.1.** Split surjective functions.

<pre class="Agda"><a id="27874" class="Keyword">open</a> <a id="27879" class="Keyword">import</a> <a id="27886" href="foundation.split-surjective-maps.html" class="Module">foundation.split-surjective-maps</a> <a id="27919" class="Keyword">using</a>
  <a id="27927" class="Symbol">(</a> <a id="27929" href="foundation.split-surjective-maps.html#1417" class="Function">is-split-surjective</a><a id="27948" class="Symbol">)</a>
</pre>
**Definition 7.4.2.** Zero and successor on standard finite types.

<pre class="Agda"><a id="28031" class="Keyword">open</a> <a id="28036" class="Keyword">import</a> <a id="28043" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="28089" class="Keyword">using</a>
  <a id="28097" class="Symbol">(</a> <a id="28099" href="univalent-combinatorics.standard-finite-types.html#5750" class="Function">zero-Fin</a>
  <a id="28110" class="Symbol">;</a> <a id="28112" href="univalent-combinatorics.standard-finite-types.html#6196" class="Function">skip-zero-Fin</a>
  <a id="28128" class="Symbol">;</a> <a id="28130" href="univalent-combinatorics.standard-finite-types.html#6352" class="Function">succ-Fin</a><a id="28138" class="Symbol">)</a>
</pre>
**Definition 7.4.3.** The surjection from ℕ into standard finite types.

<pre class="Agda"><a id="28226" class="Keyword">open</a> <a id="28231" class="Keyword">import</a> <a id="28238" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="28304" class="Keyword">using</a>
  <a id="28312" class="Symbol">(</a> <a id="28314" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#1517" class="Function">mod-succ-ℕ</a> <a id="28325" class="Comment">-- [-]ₖ₊₁</a>
  <a id="28337" class="Symbol">)</a>
</pre>
**Lemma 7.4.4.** Preservation of zero and successor `mod k`.

<pre class="Agda"><a id="28414" class="Keyword">open</a> <a id="28419" class="Keyword">import</a> <a id="28426" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="28472" class="Keyword">using</a>
  <a id="28480" class="Symbol">(</a> <a id="28482" href="univalent-combinatorics.standard-finite-types.html#8616" class="Function">is-zero-nat-zero-Fin</a> <a id="28503" class="Comment">-- ι(zero) = 0</a>
  <a id="28520" class="Symbol">;</a> <a id="28522" href="univalent-combinatorics.standard-finite-types.html#8790" class="Function">nat-skip-zero-Fin</a> <a id="28540" class="Comment">-- ι(skip-zero x) = ι(x) + 1</a>
  <a id="28571" class="Symbol">)</a>
<a id="28573" class="Keyword">open</a> <a id="28578" class="Keyword">import</a> <a id="28585" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="28651" class="Keyword">using</a>
  <a id="28659" class="Symbol">(</a> <a id="28661" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#1867" class="Function">cong-nat-succ-Fin</a> <a id="28679" class="Comment">-- ι(succ x) ≡ ι(x) + 1 mod k</a>
  <a id="28711" class="Symbol">)</a>
</pre>
**Proposition 7.4.5.**

<pre class="Agda"><a id="28750" class="Keyword">open</a> <a id="28755" class="Keyword">import</a> <a id="28762" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="28828" class="Keyword">using</a>
  <a id="28836" class="Symbol">(</a> <a id="28838" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#2371" class="Function">cong-nat-mod-succ-ℕ</a> <a id="28858" class="Comment">-- ι[x]ₖ₊₁ ≡ x mod (k + 1)</a>
  <a id="28887" class="Symbol">)</a>
</pre>
**Proposition 7.4.6.**

<pre class="Agda"><a id="28926" class="Keyword">open</a> <a id="28931" class="Keyword">import</a> <a id="28938" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a> <a id="28992" class="Keyword">using</a>
  <a id="29000" class="Symbol">(</a> <a id="29002" href="elementary-number-theory.divisibility-natural-numbers.html#7355" class="Function">is-zero-div-ℕ</a>
  <a id="29018" class="Symbol">;</a> <a id="29020" href="elementary-number-theory.divisibility-natural-numbers.html#6415" class="Function">div-is-zero-ℕ</a><a id="29033" class="Symbol">)</a>

<a id="29036" href="literature.introduction-to-homotopy-type-theory.html#29036" class="Function">_</a> <a id="29038" class="Symbol">:</a> <a id="29040" class="Symbol">(</a><a id="29041" href="literature.introduction-to-homotopy-type-theory.html#29041" class="Bound">d</a> <a id="29043" href="literature.introduction-to-homotopy-type-theory.html#29043" class="Bound">x</a> <a id="29045" class="Symbol">:</a> <a id="29047" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="29048" class="Symbol">)</a> <a id="29050" class="Symbol">→</a> <a id="29052" href="literature.introduction-to-homotopy-type-theory.html#29043" class="Bound">x</a> <a id="29054" href="elementary-number-theory.strict-inequality-natural-numbers.html#1861" class="Function Operator">&lt;-ℕ</a> <a id="29058" href="literature.introduction-to-homotopy-type-theory.html#29041" class="Bound">d</a> <a id="29060" class="Symbol">→</a> <a id="29062" href="elementary-number-theory.divisibility-natural-numbers.html#1683" class="Function">div-ℕ</a> <a id="29068" href="literature.introduction-to-homotopy-type-theory.html#29041" class="Bound">d</a> <a id="29070" href="literature.introduction-to-homotopy-type-theory.html#29043" class="Bound">x</a> <a id="29072" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="29074" class="Symbol">(</a><a id="29075" href="literature.introduction-to-homotopy-type-theory.html#29043" class="Bound">x</a> <a id="29077" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="29079" class="Number">0</a><a id="29080" class="Symbol">)</a>
<a id="29082" class="Symbol">_</a> <a id="29084" class="Symbol">=</a> <a id="29086" class="Symbol">λ</a> <a id="29088" href="literature.introduction-to-homotopy-type-theory.html#29088" class="Bound">d</a> <a id="29090" href="literature.introduction-to-homotopy-type-theory.html#29090" class="Bound">x</a> <a id="29092" href="literature.introduction-to-homotopy-type-theory.html#29092" class="Bound">x&lt;d</a> <a id="29096" class="Symbol">→</a> <a id="29098" class="Symbol">(</a><a id="29099" href="elementary-number-theory.divisibility-natural-numbers.html#7355" class="Function">is-zero-div-ℕ</a> <a id="29113" href="literature.introduction-to-homotopy-type-theory.html#29088" class="Bound">d</a> <a id="29115" href="literature.introduction-to-homotopy-type-theory.html#29090" class="Bound">x</a> <a id="29117" href="literature.introduction-to-homotopy-type-theory.html#29092" class="Bound">x&lt;d</a> <a id="29121" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="29123" href="elementary-number-theory.divisibility-natural-numbers.html#6415" class="Function">div-is-zero-ℕ</a> <a id="29137" href="literature.introduction-to-homotopy-type-theory.html#29088" class="Bound">d</a> <a id="29139" href="literature.introduction-to-homotopy-type-theory.html#29090" class="Bound">x</a><a id="29140" class="Symbol">)</a>

<a id="29143" class="Keyword">open</a> <a id="29148" class="Keyword">import</a> <a id="29155" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a> <a id="29207" class="Keyword">using</a>
  <a id="29215" class="Symbol">(</a> <a id="29217" href="elementary-number-theory.congruence-natural-numbers.html#3534" class="Function">eq-cong-le-dist-ℕ</a>
  <a id="29237" class="Symbol">;</a> <a id="29239" href="elementary-number-theory.congruence-natural-numbers.html#2158" class="Function">cong-identification-ℕ</a><a id="29260" class="Symbol">)</a>

<a id="29263" href="literature.introduction-to-homotopy-type-theory.html#29263" class="Function">_</a> <a id="29265" class="Symbol">:</a> <a id="29267" class="Symbol">(</a><a id="29268" href="literature.introduction-to-homotopy-type-theory.html#29268" class="Bound">k</a> <a id="29270" href="literature.introduction-to-homotopy-type-theory.html#29270" class="Bound">x</a> <a id="29272" href="literature.introduction-to-homotopy-type-theory.html#29272" class="Bound">y</a> <a id="29274" class="Symbol">:</a> <a id="29276" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="29277" class="Symbol">)</a> <a id="29279" class="Symbol">→</a> <a id="29281" href="elementary-number-theory.distance-natural-numbers.html#1461" class="Function">dist-ℕ</a> <a id="29288" href="literature.introduction-to-homotopy-type-theory.html#29270" class="Bound">x</a> <a id="29290" href="literature.introduction-to-homotopy-type-theory.html#29272" class="Bound">y</a> <a id="29292" href="elementary-number-theory.strict-inequality-natural-numbers.html#1861" class="Function Operator">&lt;-ℕ</a> <a id="29296" href="literature.introduction-to-homotopy-type-theory.html#29268" class="Bound">k</a> <a id="29298" class="Symbol">→</a> <a id="29300" href="literature.introduction-to-homotopy-type-theory.html#29270" class="Bound">x</a> <a id="29302" href="elementary-number-theory.congruence-natural-numbers.html#1093" class="Function Operator">≡</a> <a id="29304" href="literature.introduction-to-homotopy-type-theory.html#29272" class="Bound">y</a> <a id="29306" href="elementary-number-theory.congruence-natural-numbers.html#1093" class="Function Operator">mod</a> <a id="29310" href="literature.introduction-to-homotopy-type-theory.html#29268" class="Bound">k</a> <a id="29312" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="29314" class="Symbol">(</a><a id="29315" href="literature.introduction-to-homotopy-type-theory.html#29270" class="Bound">x</a> <a id="29317" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="29319" href="literature.introduction-to-homotopy-type-theory.html#29272" class="Bound">y</a><a id="29320" class="Symbol">)</a>
<a id="29322" class="Symbol">_</a> <a id="29324" class="Symbol">=</a> <a id="29326" class="Symbol">λ</a> <a id="29328" href="literature.introduction-to-homotopy-type-theory.html#29328" class="Bound">k</a> <a id="29330" href="literature.introduction-to-homotopy-type-theory.html#29330" class="Bound">x</a> <a id="29332" href="literature.introduction-to-homotopy-type-theory.html#29332" class="Bound">y</a> <a id="29334" href="literature.introduction-to-homotopy-type-theory.html#29334" class="Bound">dist&lt;d</a> <a id="29341" class="Symbol">→</a> <a id="29343" class="Symbol">(</a><a id="29344" href="elementary-number-theory.congruence-natural-numbers.html#3534" class="Function">eq-cong-le-dist-ℕ</a> <a id="29362" href="literature.introduction-to-homotopy-type-theory.html#29328" class="Bound">k</a> <a id="29364" href="literature.introduction-to-homotopy-type-theory.html#29330" class="Bound">x</a> <a id="29366" href="literature.introduction-to-homotopy-type-theory.html#29332" class="Bound">y</a> <a id="29368" href="literature.introduction-to-homotopy-type-theory.html#29334" class="Bound">dist&lt;d</a> <a id="29375" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="29377" href="elementary-number-theory.congruence-natural-numbers.html#2158" class="Function">cong-identification-ℕ</a> <a id="29399" href="literature.introduction-to-homotopy-type-theory.html#29328" class="Bound">k</a><a id="29400" class="Symbol">)</a>
</pre>
**Theorem 7.4.7.** Equality modulo `k + 1` corresponds to equality after
inclusion to `Fin (k + 1)`.

<pre class="Agda"><a id="29517" class="Keyword">open</a> <a id="29522" class="Keyword">import</a> <a id="29529" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="29595" class="Keyword">using</a>
  <a id="29603" class="Symbol">(</a> <a id="29605" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#2928" class="Function">cong-eq-mod-succ-ℕ</a>
  <a id="29626" class="Symbol">;</a> <a id="29628" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#3383" class="Function">eq-mod-succ-cong-ℕ</a><a id="29646" class="Symbol">)</a>

<a id="29649" href="literature.introduction-to-homotopy-type-theory.html#29649" class="Function">_</a> <a id="29651" class="Symbol">:</a> <a id="29653" class="Symbol">(</a><a id="29654" href="literature.introduction-to-homotopy-type-theory.html#29654" class="Bound">k</a> <a id="29656" href="literature.introduction-to-homotopy-type-theory.html#29656" class="Bound">x</a> <a id="29658" href="literature.introduction-to-homotopy-type-theory.html#29658" class="Bound">y</a> <a id="29660" class="Symbol">:</a> <a id="29662" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="29663" class="Symbol">)</a> <a id="29665" class="Symbol">→</a> <a id="29667" class="Symbol">(</a><a id="29668" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#1517" class="Function">mod-succ-ℕ</a> <a id="29679" href="literature.introduction-to-homotopy-type-theory.html#29654" class="Bound">k</a> <a id="29681" href="literature.introduction-to-homotopy-type-theory.html#29656" class="Bound">x</a> <a id="29683" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="29685" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#1517" class="Function">mod-succ-ℕ</a> <a id="29696" href="literature.introduction-to-homotopy-type-theory.html#29654" class="Bound">k</a> <a id="29698" href="literature.introduction-to-homotopy-type-theory.html#29658" class="Bound">y</a><a id="29699" class="Symbol">)</a> <a id="29701" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="29703" class="Symbol">(</a><a id="29704" href="literature.introduction-to-homotopy-type-theory.html#29656" class="Bound">x</a> <a id="29706" href="elementary-number-theory.congruence-natural-numbers.html#1093" class="Function Operator">≡</a> <a id="29708" href="literature.introduction-to-homotopy-type-theory.html#29658" class="Bound">y</a> <a id="29710" href="elementary-number-theory.congruence-natural-numbers.html#1093" class="Function Operator">mod</a> <a id="29714" class="Symbol">(</a><a id="29715" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="29722" href="literature.introduction-to-homotopy-type-theory.html#29654" class="Bound">k</a><a id="29723" class="Symbol">))</a>
<a id="29726" class="Symbol">_</a> <a id="29728" class="Symbol">=</a> <a id="29730" class="Symbol">λ</a> <a id="29732" href="literature.introduction-to-homotopy-type-theory.html#29732" class="Bound">k</a> <a id="29734" href="literature.introduction-to-homotopy-type-theory.html#29734" class="Bound">x</a> <a id="29736" href="literature.introduction-to-homotopy-type-theory.html#29736" class="Bound">y</a> <a id="29738" class="Symbol">→</a> <a id="29740" class="Symbol">(</a><a id="29741" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#2928" class="Function">cong-eq-mod-succ-ℕ</a> <a id="29760" href="literature.introduction-to-homotopy-type-theory.html#29732" class="Bound">k</a> <a id="29762" href="literature.introduction-to-homotopy-type-theory.html#29734" class="Bound">x</a> <a id="29764" href="literature.introduction-to-homotopy-type-theory.html#29736" class="Bound">y</a> <a id="29766" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="29768" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#3383" class="Function">eq-mod-succ-cong-ℕ</a> <a id="29787" href="literature.introduction-to-homotopy-type-theory.html#29732" class="Bound">k</a> <a id="29789" href="literature.introduction-to-homotopy-type-theory.html#29734" class="Bound">x</a> <a id="29791" href="literature.introduction-to-homotopy-type-theory.html#29736" class="Bound">y</a><a id="29792" class="Symbol">)</a>
</pre>
**Theorem 7.4.8.** The map from natural numbers is split surjective.

<pre class="Agda"><a id="29877" class="Keyword">open</a> <a id="29882" class="Keyword">import</a> <a id="29889" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="29955" class="Keyword">using</a>
  <a id="29963" class="Symbol">(</a> <a id="29965" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#5101" class="Function">is-split-surjective-mod-succ-ℕ</a><a id="29995" class="Symbol">)</a>
</pre>
### 7.5 The cyclic groups

**Definition 7.5.1.** The cyclic groups.

<pre class="Agda"><a id="30079" class="Keyword">open</a> <a id="30084" class="Keyword">import</a> <a id="30091" href="elementary-number-theory.modular-arithmetic.html" class="Module">elementary-number-theory.modular-arithmetic</a> <a id="30135" class="Keyword">using</a>
  <a id="30143" class="Symbol">(</a> <a id="30145" href="elementary-number-theory.modular-arithmetic.html#2573" class="Function">ℤ-Mod</a> <a id="30151" class="Comment">-- ℤ/k</a>
  <a id="30160" class="Symbol">)</a>
</pre>
**Definition 7.5.2.** Addition on `ℤ/(k + 1)` and additive inverse.

<pre class="Agda"><a id="30244" class="Keyword">open</a> <a id="30249" class="Keyword">import</a> <a id="30256" href="elementary-number-theory.modular-arithmetic.html" class="Module">elementary-number-theory.modular-arithmetic</a> <a id="30300" class="Keyword">using</a>
  <a id="30308" class="Symbol">(</a> <a id="30310" href="elementary-number-theory.modular-arithmetic.html#6928" class="Function">add-ℤ-Mod</a>
  <a id="30322" class="Symbol">;</a> <a id="30324" href="elementary-number-theory.modular-arithmetic.html#8494" class="Function">neg-ℤ-Mod</a><a id="30333" class="Symbol">)</a>
</pre>
**Remark 7.5.3.**

The lemmas are proven for all natural numbers `k`, not just positive ones.

<pre class="Agda"><a id="30443" class="Keyword">open</a> <a id="30448" class="Keyword">import</a> <a id="30455" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a> <a id="30507" class="Keyword">using</a>
  <a id="30515" class="Symbol">(</a> <a id="30517" href="elementary-number-theory.congruence-natural-numbers.html#4240" class="Function">cong-is-zero-nat-zero-Fin</a> <a id="30543" class="Comment">-- ι(0) ≡ 0 mod (k + 1)</a>
  <a id="30569" class="Symbol">)</a>
<a id="30571" class="Keyword">open</a> <a id="30576" class="Keyword">import</a> <a id="30583" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="30649" class="Keyword">using</a>
  <a id="30657" class="Symbol">(</a> <a id="30659" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#6470" class="Function">cong-add-Fin</a> <a id="30672" class="Comment">-- ι(x + y) ≡ ι(x) + ι(y) mod (k + 1)</a>
  <a id="30712" class="Symbol">;</a> <a id="30714" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#9956" class="Function">cong-neg-Fin</a> <a id="30727" class="Comment">-- ι(-x) ≡ dist(ι(x), k + 1) mod (k + 1)</a>
  <a id="30770" class="Symbol">)</a>
</pre>
**Proposition 7.5.4.** A 3-for-2 property of congruences.

<pre class="Agda"><a id="30844" class="Keyword">open</a> <a id="30849" class="Keyword">import</a> <a id="30856" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="30922" class="Keyword">using</a>
  <a id="30930" class="Symbol">(</a> <a id="30932" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#7434" class="Function">congruence-add-ℕ</a> <a id="30949" class="Comment">-- x ≡ x&#39; → y ≡ y&#39; → (x + y ≡ x&#39; + y&#39;)</a>
  <a id="30990" class="Symbol">;</a> <a id="30992" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#7736" class="Function">cong-right-summand-ℕ</a> <a id="31013" class="Comment">-- x ≡ x&#39; → (x + y ≡ x&#39; + y&#39;) → y ≡ y&#39;</a>
  <a id="31054" class="Symbol">;</a> <a id="31056" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#8101" class="Function">cong-left-summand-ℕ</a> <a id="31076" class="Comment">-- y ≡ y&#39; → (x + y ≡ x&#39; + y&#39;) → x ≡ x&#39;</a>
  <a id="31117" class="Symbol">)</a>
</pre>
**Theorem 7.5.5.** ℤ/k with addition and negation form an Abelian group.

<pre class="Agda"><a id="31206" class="Keyword">open</a> <a id="31211" class="Keyword">import</a> <a id="31218" href="elementary-number-theory.modular-arithmetic.html" class="Module">elementary-number-theory.modular-arithmetic</a> <a id="31262" class="Keyword">using</a>
  <a id="31270" class="Symbol">(</a> <a id="31272" href="elementary-number-theory.modular-arithmetic.html#9391" class="Function">left-unit-law-add-ℤ-Mod</a> <a id="31296" class="Comment">-- 0 + x = x</a>
  <a id="31311" class="Symbol">;</a> <a id="31313" href="elementary-number-theory.modular-arithmetic.html#9591" class="Function">right-unit-law-add-ℤ-Mod</a> <a id="31338" class="Comment">-- x + 0 = x</a>
  <a id="31353" class="Symbol">;</a> <a id="31355" href="elementary-number-theory.modular-arithmetic.html#9796" class="Function">left-inverse-law-add-ℤ-Mod</a> <a id="31382" class="Comment">-- (-x) + x = 0</a>
  <a id="31400" class="Symbol">;</a> <a id="31402" href="elementary-number-theory.modular-arithmetic.html#10023" class="Function">right-inverse-law-add-ℤ-Mod</a> <a id="31430" class="Comment">-- x + (-x) = 0</a>
  <a id="31448" class="Symbol">;</a> <a id="31450" href="elementary-number-theory.modular-arithmetic.html#8951" class="Function">associative-add-ℤ-Mod</a> <a id="31472" class="Comment">-- (x + y) + z = x + (y + z)</a>
  <a id="31503" class="Symbol">;</a> <a id="31505" href="elementary-number-theory.modular-arithmetic.html#9189" class="Function">commutative-add-ℤ-Mod</a> <a id="31527" class="Comment">-- x + y = y + x</a>
  <a id="31546" class="Symbol">)</a>
</pre>
### Exercises

**Exercise 7.1.** The rest of Proposition [7.1.5](#proposition-7.1.5)
<a id="exercise-7.1"></a>

<pre class="Agda"><a id="31673" class="Keyword">open</a> <a id="31678" class="Keyword">import</a> <a id="31685" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a> <a id="31739" class="Keyword">using</a>
  <a id="31747" class="Symbol">(</a> <a id="31749" href="elementary-number-theory.divisibility-natural-numbers.html#9173" class="Function">div-right-summand-ℕ</a> <a id="31769" class="Comment">-- d | x → d | x + y → d | y</a>
  <a id="31800" class="Symbol">;</a> <a id="31802" href="elementary-number-theory.divisibility-natural-numbers.html#8272" class="Function">div-left-summand-ℕ</a> <a id="31821" class="Comment">-- d | y → d | x + y → d | x</a>
  <a id="31852" class="Symbol">)</a>
</pre>
**Exercise 7.2.** Divisibility is a partial order.

<pre class="Agda"><a id="31919" class="Keyword">open</a> <a id="31924" class="Keyword">import</a> <a id="31931" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a> <a id="31985" class="Keyword">using</a>
  <a id="31993" class="Symbol">(</a> <a id="31995" href="elementary-number-theory.divisibility-natural-numbers.html#3643" class="Function">refl-div-ℕ</a>
  <a id="32008" class="Symbol">;</a> <a id="32010" href="elementary-number-theory.divisibility-natural-numbers.html#3818" class="Function">antisymmetric-div-ℕ</a>
  <a id="32032" class="Symbol">;</a> <a id="32034" href="elementary-number-theory.divisibility-natural-numbers.html#4430" class="Function">transitive-div-ℕ</a><a id="32050" class="Symbol">)</a>
</pre>
**Exercise 7.3.** `n!` is divisible by all `0 < x ≤ n`

<pre class="Agda"><a id="32121" class="Keyword">open</a> <a id="32126" class="Keyword">import</a> <a id="32133" href="elementary-number-theory.factorials.html" class="Module">elementary-number-theory.factorials</a> <a id="32169" class="Keyword">using</a>
  <a id="32177" class="Symbol">(</a> <a id="32179" href="elementary-number-theory.factorials.html#944" class="Function">div-factorial-ℕ</a><a id="32194" class="Symbol">)</a>
</pre>
**Exercise 7.4.** The successor on `Fin (k + 1)` adds one.

<pre class="Agda"><a id="32269" class="Keyword">open</a> <a id="32274" class="Keyword">import</a> <a id="32281" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="32347" class="Keyword">using</a>
  <a id="32355" class="Symbol">(</a> <a id="32357" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#14924" class="Function">is-add-one-succ-Fin&#39;</a><a id="32377" class="Symbol">)</a>
</pre>
**Exercise 7.5.** Observational equality of `Fin k`.

<pre class="Agda"><a id="32446" class="Keyword">open</a> <a id="32451" class="Keyword">import</a> <a id="32458" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a> <a id="32513" class="Keyword">using</a>
  <a id="32521" class="Symbol">(</a> <a id="32523" href="univalent-combinatorics.equality-standard-finite-types.html#1479" class="Function">Eq-Fin</a><a id="32529" class="Symbol">)</a>

<a id="32532" class="Comment">-- (a)</a>
<a id="32539" class="Keyword">open</a> <a id="32544" class="Keyword">import</a> <a id="32551" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a> <a id="32606" class="Keyword">using</a>
  <a id="32614" class="Symbol">(</a> <a id="32616" href="univalent-combinatorics.equality-standard-finite-types.html#2152" class="Function">Eq-Fin-eq</a>
  <a id="32628" class="Symbol">;</a> <a id="32630" href="univalent-combinatorics.equality-standard-finite-types.html#2246" class="Function">eq-Eq-Fin</a><a id="32639" class="Symbol">)</a>

<a id="32642" href="literature.introduction-to-homotopy-type-theory.html#32642" class="Function">_</a> <a id="32644" class="Symbol">:</a> <a id="32646" class="Symbol">(</a><a id="32647" href="literature.introduction-to-homotopy-type-theory.html#32647" class="Bound">k</a> <a id="32649" class="Symbol">:</a> <a id="32651" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="32652" class="Symbol">)</a> <a id="32654" class="Symbol">→</a> <a id="32656" class="Symbol">{</a><a id="32657" href="literature.introduction-to-homotopy-type-theory.html#32657" class="Bound">x</a> <a id="32659" href="literature.introduction-to-homotopy-type-theory.html#32659" class="Bound">y</a> <a id="32661" class="Symbol">:</a> <a id="32663" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="32667" href="literature.introduction-to-homotopy-type-theory.html#32647" class="Bound">k</a><a id="32668" class="Symbol">}</a> <a id="32670" class="Symbol">→</a> <a id="32672" class="Symbol">(</a><a id="32673" href="literature.introduction-to-homotopy-type-theory.html#32657" class="Bound">x</a> <a id="32675" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="32677" href="literature.introduction-to-homotopy-type-theory.html#32659" class="Bound">y</a><a id="32678" class="Symbol">)</a> <a id="32680" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="32682" href="univalent-combinatorics.equality-standard-finite-types.html#1479" class="Function">Eq-Fin</a> <a id="32689" href="literature.introduction-to-homotopy-type-theory.html#32647" class="Bound">k</a> <a id="32691" href="literature.introduction-to-homotopy-type-theory.html#32657" class="Bound">x</a> <a id="32693" href="literature.introduction-to-homotopy-type-theory.html#32659" class="Bound">y</a>
<a id="32695" class="Symbol">_</a> <a id="32697" class="Symbol">=</a> <a id="32699" class="Symbol">λ</a> <a id="32701" href="literature.introduction-to-homotopy-type-theory.html#32701" class="Bound">k</a> <a id="32703" class="Symbol">→</a> <a id="32705" class="Symbol">(</a><a id="32706" href="univalent-combinatorics.equality-standard-finite-types.html#2152" class="Function">Eq-Fin-eq</a> <a id="32716" href="literature.introduction-to-homotopy-type-theory.html#32701" class="Bound">k</a> <a id="32718" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="32720" href="univalent-combinatorics.equality-standard-finite-types.html#2246" class="Function">eq-Eq-Fin</a> <a id="32730" href="literature.introduction-to-homotopy-type-theory.html#32701" class="Bound">k</a><a id="32731" class="Symbol">)</a>

<a id="32734" class="Comment">-- (b)</a>
<a id="32741" class="Keyword">open</a> <a id="32746" class="Keyword">import</a> <a id="32753" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="32799" class="Keyword">using</a>
  <a id="32807" class="Symbol">(</a> <a id="32809" href="univalent-combinatorics.standard-finite-types.html#9882" class="Function">is-injective-inl-Fin</a><a id="32829" class="Symbol">)</a>

<a id="32832" class="Comment">-- (c)</a>
<a id="32839" class="Keyword">open</a> <a id="32844" class="Keyword">import</a> <a id="32851" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="32897" class="Keyword">using</a>
  <a id="32905" class="Symbol">(</a> <a id="32907" href="univalent-combinatorics.standard-finite-types.html#10231" class="Function">neq-zero-succ-Fin</a><a id="32924" class="Symbol">)</a>

<a id="32927" class="Comment">-- (d)</a>
<a id="32934" class="Keyword">open</a> <a id="32939" class="Keyword">import</a> <a id="32946" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="32992" class="Keyword">using</a>
  <a id="33000" class="Symbol">(</a> <a id="33002" href="univalent-combinatorics.standard-finite-types.html#10908" class="Function">is-injective-succ-Fin</a><a id="33023" class="Symbol">)</a>
</pre>
**Exercise 7.6.** The predecessor function on `Fin k`.

<pre class="Agda"><a id="33094" class="Keyword">open</a> <a id="33099" class="Keyword">import</a> <a id="33106" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a> <a id="33152" class="Keyword">using</a>
  <a id="33160" class="Symbol">(</a> <a id="33162" href="univalent-combinatorics.standard-finite-types.html#2656" class="Function">neg-two-Fin</a>
  <a id="33176" class="Symbol">;</a> <a id="33178" href="univalent-combinatorics.standard-finite-types.html#11460" class="Function">skip-neg-two-Fin</a>
  <a id="33197" class="Symbol">;</a> <a id="33199" href="univalent-combinatorics.standard-finite-types.html#11686" class="Function">pred-Fin</a>
  <a id="33210" class="Symbol">;</a> <a id="33212" href="univalent-combinatorics.standard-finite-types.html#12369" class="Function">is-section-pred-Fin</a> <a id="33232" class="Comment">-- succ (pred x) = x</a>
  <a id="33255" class="Symbol">;</a> <a id="33257" href="univalent-combinatorics.standard-finite-types.html#12710" class="Function">is-retraction-pred-Fin</a> <a id="33280" class="Comment">-- pred (succ x) = x</a>
  <a id="33303" class="Symbol">)</a>
</pre>
**Exercise 7.7.** Classical finite types.

<pre class="Agda"><a id="33361" class="Keyword">open</a> <a id="33366" class="Keyword">import</a> <a id="33373" href="univalent-combinatorics.classical-finite-types.html" class="Module">univalent-combinatorics.classical-finite-types</a> <a id="33420" class="Keyword">using</a>
  <a id="33428" class="Symbol">(</a> <a id="33430" href="univalent-combinatorics.classical-finite-types.html#1322" class="Function">classical-Fin</a><a id="33443" class="Symbol">)</a>

<a id="33446" class="Comment">-- (a)</a>
<a id="33453" class="Keyword">open</a> <a id="33458" class="Keyword">import</a> <a id="33465" href="univalent-combinatorics.classical-finite-types.html" class="Module">univalent-combinatorics.classical-finite-types</a> <a id="33512" class="Keyword">using</a>
  <a id="33520" class="Symbol">(</a> <a id="33522" href="univalent-combinatorics.classical-finite-types.html#1586" class="Function">Eq-classical-Fin</a>
  <a id="33541" class="Symbol">;</a> <a id="33543" href="univalent-combinatorics.classical-finite-types.html#2344" class="Function">Eq-eq-classical-Fin</a>
  <a id="33565" class="Symbol">;</a> <a id="33567" href="univalent-combinatorics.classical-finite-types.html#1973" class="Function">eq-Eq-classical-Fin</a><a id="33586" class="Symbol">)</a>

<a id="33589" href="literature.introduction-to-homotopy-type-theory.html#33589" class="Function">_</a> <a id="33591" class="Symbol">:</a> <a id="33593" class="Symbol">(</a><a id="33594" href="literature.introduction-to-homotopy-type-theory.html#33594" class="Bound">k</a> <a id="33596" class="Symbol">:</a> <a id="33598" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="33599" class="Symbol">)</a> <a id="33601" class="Symbol">→</a> <a id="33603" class="Symbol">(</a><a id="33604" href="literature.introduction-to-homotopy-type-theory.html#33604" class="Bound">x</a> <a id="33606" href="literature.introduction-to-homotopy-type-theory.html#33606" class="Bound">y</a> <a id="33608" class="Symbol">:</a> <a id="33610" href="univalent-combinatorics.classical-finite-types.html#1322" class="Function">classical-Fin</a> <a id="33624" href="literature.introduction-to-homotopy-type-theory.html#33594" class="Bound">k</a><a id="33625" class="Symbol">)</a> <a id="33627" class="Symbol">→</a> <a id="33629" class="Symbol">(</a><a id="33630" href="literature.introduction-to-homotopy-type-theory.html#33604" class="Bound">x</a> <a id="33632" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="33634" href="literature.introduction-to-homotopy-type-theory.html#33606" class="Bound">y</a><a id="33635" class="Symbol">)</a> <a id="33637" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="33639" href="univalent-combinatorics.classical-finite-types.html#1586" class="Function">Eq-classical-Fin</a> <a id="33656" href="literature.introduction-to-homotopy-type-theory.html#33594" class="Bound">k</a> <a id="33658" href="literature.introduction-to-homotopy-type-theory.html#33604" class="Bound">x</a> <a id="33660" href="literature.introduction-to-homotopy-type-theory.html#33606" class="Bound">y</a>
<a id="33662" class="Symbol">_</a> <a id="33664" class="Symbol">=</a> <a id="33666" class="Symbol">λ</a> <a id="33668" href="literature.introduction-to-homotopy-type-theory.html#33668" class="Bound">k</a> <a id="33670" href="literature.introduction-to-homotopy-type-theory.html#33670" class="Bound">x</a> <a id="33672" href="literature.introduction-to-homotopy-type-theory.html#33672" class="Bound">y</a> <a id="33674" class="Symbol">→</a> <a id="33676" class="Symbol">(</a><a id="33677" href="univalent-combinatorics.classical-finite-types.html#2344" class="Function">Eq-eq-classical-Fin</a> <a id="33697" href="literature.introduction-to-homotopy-type-theory.html#33668" class="Bound">k</a> <a id="33699" href="literature.introduction-to-homotopy-type-theory.html#33670" class="Bound">x</a> <a id="33701" href="literature.introduction-to-homotopy-type-theory.html#33672" class="Bound">y</a> <a id="33703" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="33705" href="univalent-combinatorics.classical-finite-types.html#1973" class="Function">eq-Eq-classical-Fin</a> <a id="33725" href="literature.introduction-to-homotopy-type-theory.html#33668" class="Bound">k</a> <a id="33727" href="literature.introduction-to-homotopy-type-theory.html#33670" class="Bound">x</a> <a id="33729" href="literature.introduction-to-homotopy-type-theory.html#33672" class="Bound">y</a><a id="33730" class="Symbol">)</a>

<a id="33733" class="Comment">-- (b)</a>
<a id="33740" class="Keyword">open</a> <a id="33745" class="Keyword">import</a> <a id="33752" href="univalent-combinatorics.classical-finite-types.html" class="Module">univalent-combinatorics.classical-finite-types</a> <a id="33799" class="Keyword">using</a>
  <a id="33807" class="Symbol">(</a> <a id="33809" href="univalent-combinatorics.classical-finite-types.html#2783" class="Function">classical-standard-Fin</a> <a id="33832" class="Comment">-- ι</a>
  <a id="33839" class="Symbol">;</a> <a id="33841" href="univalent-combinatorics.classical-finite-types.html#2661" class="Function">standard-classical-Fin</a> <a id="33864" class="Comment">-- α</a>
  <a id="33871" class="Symbol">;</a> <a id="33873" href="univalent-combinatorics.classical-finite-types.html#3020" class="Function">is-section-classical-standard-Fin</a> <a id="33907" class="Comment">-- α (ι x) = x</a>
  <a id="33924" class="Symbol">;</a> <a id="33926" href="univalent-combinatorics.classical-finite-types.html#3216" class="Function">is-retraction-classical-standard-Fin</a> <a id="33963" class="Comment">-- ι (α y) = y</a>
  <a id="33980" class="Symbol">)</a>
</pre>
**Exercise 7.8.** Multiplication on `ℤ/(k + 1)`.

<pre class="Agda"><a id="34045" class="Keyword">open</a> <a id="34050" class="Keyword">import</a> <a id="34057" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="34123" class="Keyword">using</a>
  <a id="34131" class="Symbol">(</a> <a id="34133" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#10213" class="Function">mul-Fin</a><a id="34140" class="Symbol">)</a>

<a id="34143" class="Comment">-- (a)</a>
<a id="34150" class="Keyword">open</a> <a id="34155" class="Keyword">import</a> <a id="34162" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="34228" class="Keyword">using</a>
  <a id="34236" class="Symbol">(</a> <a id="34238" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#10569" class="Function">cong-mul-Fin</a> <a id="34251" class="Comment">-- ι(x * y) ≡ ι x * ι y mod (k + 1)</a>
  <a id="34289" class="Symbol">)</a>

<a id="34292" class="Comment">-- (b)</a>
<a id="34299" class="Keyword">open</a> <a id="34304" class="Keyword">import</a> <a id="34311" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a> <a id="34363" class="Keyword">using</a>
  <a id="34371" class="Symbol">(</a> <a id="34373" href="elementary-number-theory.congruence-natural-numbers.html#5425" class="Function">congruence-mul-ℕ</a> <a id="34390" class="Comment">-- x ≡ x&#39; → y ≡ y&#39; → (x * y) ≡ (x&#39; * y&#39;)</a>
  <a id="34433" class="Symbol">)</a>

<a id="34436" class="Comment">-- (c)</a>
<a id="34443" class="Keyword">open</a> <a id="34448" class="Keyword">import</a> <a id="34455" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="34521" class="Keyword">using</a>
  <a id="34529" class="Symbol">(</a> <a id="34531" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#16315" class="Function">associative-mul-Fin</a> <a id="34551" class="Comment">-- (x * y) * z = x * (y * z)</a>
  <a id="34582" class="Symbol">;</a> <a id="34584" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#17966" class="Function">commutative-mul-Fin</a> <a id="34604" class="Comment">-- x * y = y * x</a>
  <a id="34623" class="Symbol">;</a> <a id="34625" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#18337" class="Function">left-unit-law-mul-Fin</a> <a id="34647" class="Comment">-- 1 * x = x</a>
  <a id="34662" class="Symbol">;</a> <a id="34664" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#18944" class="Function">right-unit-law-mul-Fin</a> <a id="34687" class="Comment">-- x * 1 = x</a>
  <a id="34702" class="Symbol">;</a> <a id="34704" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#19949" class="Function">left-distributive-mul-add-Fin</a> <a id="34734" class="Comment">-- x * (y + z) = x * y + x * z</a>
  <a id="34767" class="Symbol">;</a> <a id="34769" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#22069" class="Function">right-distributive-mul-add-Fin</a> <a id="34800" class="Comment">-- (x + y) * z = x * z + y * z</a>
  <a id="34833" class="Symbol">)</a>
</pre>
**Exercise 7.9.** Euclidean division.

<pre class="Agda"><a id="34887" class="Comment">-- (a)</a>
<a id="34894" class="Keyword">open</a> <a id="34899" class="Keyword">import</a> <a id="34906" href="elementary-number-theory.euclidean-division-natural-numbers.html" class="Module">elementary-number-theory.euclidean-division-natural-numbers</a> <a id="34966" class="Keyword">using</a>
  <a id="34974" class="Symbol">(</a> <a id="34976" href="elementary-number-theory.euclidean-division-natural-numbers.html#2581" class="Function">euclidean-division-ℕ</a><a id="34996" class="Symbol">)</a>

<a id="34999" class="Comment">-- TODO: b</a>
</pre>
**Exercise 7.10.** `k`-ary natural numbers.

<pre class="Agda"><a id="35068" class="Keyword">open</a> <a id="35073" class="Keyword">import</a> <a id="35080" href="elementary-number-theory.finitary-natural-numbers.html" class="Module">elementary-number-theory.finitary-natural-numbers</a> <a id="35130" class="Keyword">using</a>
  <a id="35138" class="Symbol">(</a> <a id="35140" href="elementary-number-theory.finitary-natural-numbers.html#1033" class="Datatype">based-ℕ</a> <a id="35148" class="Comment">-- ℕₖ</a>
  <a id="35156" class="Symbol">;</a> <a id="35158" href="elementary-number-theory.finitary-natural-numbers.html#1401" class="Function">convert-based-ℕ</a> <a id="35174" class="Comment">-- fₖ</a>
  <a id="35182" class="Symbol">)</a>

<a id="35185" class="Comment">-- (a)</a>
<a id="35192" class="Keyword">open</a> <a id="35197" class="Keyword">import</a> <a id="35204" href="elementary-number-theory.finitary-natural-numbers.html" class="Module">elementary-number-theory.finitary-natural-numbers</a> <a id="35254" class="Keyword">using</a>
  <a id="35262" class="Symbol">(</a> <a id="35264" href="elementary-number-theory.finitary-natural-numbers.html#1652" class="Function">is-empty-based-zero-ℕ</a><a id="35285" class="Symbol">)</a>

<a id="35288" class="Comment">-- (b)</a>
<a id="35295" class="Keyword">open</a> <a id="35300" class="Keyword">import</a> <a id="35307" href="elementary-number-theory.finitary-natural-numbers.html" class="Module">elementary-number-theory.finitary-natural-numbers</a> <a id="35357" class="Keyword">using</a>
  <a id="35365" class="Symbol">(</a> <a id="35367" href="elementary-number-theory.finitary-natural-numbers.html#2852" class="Function">is-injective-convert-based-ℕ</a><a id="35395" class="Symbol">)</a>

<a id="35398" class="Comment">-- (c)</a>
<a id="35405" class="Keyword">open</a> <a id="35410" class="Keyword">import</a> <a id="35417" href="elementary-number-theory.finitary-natural-numbers.html" class="Module">elementary-number-theory.finitary-natural-numbers</a> <a id="35467" class="Keyword">using</a>
  <a id="35475" class="Symbol">(</a> <a id="35477" href="elementary-number-theory.finitary-natural-numbers.html#5648" class="Function">inv-convert-based-ℕ</a> <a id="35497" class="Comment">-- gₖ</a>
  <a id="35505" class="Symbol">;</a> <a id="35507" href="elementary-number-theory.finitary-natural-numbers.html#7003" class="Function">is-section-inv-convert-based-ℕ</a> <a id="35538" class="Comment">-- fₖ₊₁ (gₖ n) = n</a>
  <a id="35559" class="Symbol">;</a> <a id="35561" href="elementary-number-theory.finitary-natural-numbers.html#7344" class="Function">is-retraction-inv-convert-based-ℕ</a> <a id="35595" class="Comment">-- gₖ (fₖ₊₁ x) = x</a>
  <a id="35616" class="Symbol">)</a>
</pre>
## 8 Decidability in elementary number theory

### 8.1 Decidability and decidable equality

**Definition 8.1.1.** Decidable types.

<pre class="Agda"><a id="35763" class="Keyword">open</a> <a id="35768" class="Keyword">import</a> <a id="35775" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a> <a id="35802" class="Keyword">using</a>
  <a id="35810" class="Symbol">(</a> <a id="35812" href="foundation.decidable-types.html#1859" class="Function">is-decidable</a><a id="35824" class="Symbol">)</a>
</pre>
**Example 8.1.2.** The unit type and the empty type are decidable

<pre class="Agda"><a id="35906" class="Keyword">open</a> <a id="35911" class="Keyword">import</a> <a id="35918" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a> <a id="35945" class="Keyword">using</a>
  <a id="35953" class="Symbol">(</a> <a id="35955" href="foundation.decidable-types.html#2009" class="Function">is-decidable-unit</a>
  <a id="35975" class="Symbol">;</a> <a id="35977" href="foundation.decidable-types.html#2077" class="Function">is-decidable-empty</a><a id="35995" class="Symbol">)</a>
</pre>
**Example 8.1.3.** Decidability of coproducts, products and functions.

<pre class="Agda"><a id="36082" class="Keyword">open</a> <a id="36087" class="Keyword">import</a> <a id="36094" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a> <a id="36121" class="Keyword">using</a>
  <a id="36129" class="Symbol">(</a> <a id="36131" href="foundation.decidable-types.html#2222" class="Function">is-decidable-coproduct</a> <a id="36154" class="Comment">-- if A and B are decidable, then A + B is decidable</a>
  <a id="36209" class="Symbol">;</a> <a id="36211" href="foundation.decidable-types.html#2588" class="Function">is-decidable-product</a> <a id="36232" class="Comment">-- if A and B are decidable, then A × B is decidable</a>
  <a id="36287" class="Symbol">;</a> <a id="36289" href="foundation.decidable-types.html#3721" class="Function">is-decidable-function-type</a> <a id="36316" class="Comment">-- if A and B are decidable, then A → B is decidable</a>
  <a id="36371" class="Symbol">;</a> <a id="36373" href="foundation.decidable-types.html#4418" class="Function">is-decidable-neg</a> <a id="36390" class="Comment">-- if A is decidable, then ¬A is decidable</a>
  <a id="36435" class="Symbol">)</a>
</pre>
**Example 8.1.4.** Decidability of observational equality and inequality on ℕ.

<pre class="Agda"><a id="36530" class="Keyword">open</a> <a id="36535" class="Keyword">import</a> <a id="36542" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a> <a id="36592" class="Keyword">using</a>
  <a id="36600" class="Symbol">(</a> <a id="36602" href="elementary-number-theory.equality-natural-numbers.html#2613" class="Function">is-decidable-Eq-ℕ</a><a id="36619" class="Symbol">)</a>
<a id="36621" class="Keyword">open</a> <a id="36626" class="Keyword">import</a> <a id="36633" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a> <a id="36685" class="Keyword">using</a>
  <a id="36693" class="Symbol">(</a> <a id="36695" href="elementary-number-theory.inequality-natural-numbers.html#2159" class="Function">is-decidable-leq-ℕ</a><a id="36713" class="Symbol">)</a>
<a id="36715" class="Keyword">open</a> <a id="36720" class="Keyword">import</a> <a id="36727" href="elementary-number-theory.strict-inequality-natural-numbers.html" class="Module">elementary-number-theory.strict-inequality-natural-numbers</a> <a id="36786" class="Keyword">using</a>
  <a id="36794" class="Symbol">(</a> <a id="36796" href="elementary-number-theory.strict-inequality-natural-numbers.html#2342" class="Function">is-decidable-le-ℕ</a><a id="36813" class="Symbol">)</a>
</pre>
**Definition 8.1.5.** Decidable equality.

<pre class="Agda"><a id="36871" class="Keyword">open</a> <a id="36876" class="Keyword">import</a> <a id="36883" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a> <a id="36913" class="Keyword">using</a>
  <a id="36921" class="Symbol">(</a> <a id="36923" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a><a id="36945" class="Symbol">)</a>
</pre>
**Lemma 8.1.6.** Decidability of logically equivalent types is logically
equivalent.

<pre class="Agda"><a id="37046" class="Keyword">open</a> <a id="37051" class="Keyword">import</a> <a id="37058" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a> <a id="37085" class="Keyword">using</a>
  <a id="37093" class="Symbol">(</a> <a id="37095" href="foundation.decidable-types.html#5105" class="Function">is-decidable-iff&#39;</a><a id="37112" class="Symbol">)</a>
</pre>
**Proposition 8.1.7.** Equality on ℕ is decidable.

<pre class="Agda"><a id="37179" class="Keyword">open</a> <a id="37184" class="Keyword">import</a> <a id="37191" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a> <a id="37241" class="Keyword">using</a>
  <a id="37249" class="Symbol">(</a> <a id="37251" href="elementary-number-theory.equality-natural-numbers.html#2869" class="Function">has-decidable-equality-ℕ</a><a id="37275" class="Symbol">)</a>
</pre>
**Proposition 8.1.8.** Equality on `Fin k` is decidable.

<pre class="Agda"><a id="37348" class="Keyword">open</a> <a id="37353" class="Keyword">import</a> <a id="37360" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a> <a id="37415" class="Keyword">using</a>
  <a id="37423" class="Symbol">(</a> <a id="37425" href="univalent-combinatorics.equality-standard-finite-types.html#2684" class="Function">is-decidable-Eq-Fin</a>
  <a id="37447" class="Symbol">;</a> <a id="37449" href="univalent-combinatorics.equality-standard-finite-types.html#3037" class="Function">has-decidable-equality-Fin</a><a id="37475" class="Symbol">)</a>
</pre>
**Theorem 8.1.9.** Divisibility is decidable.

<pre class="Agda"><a id="37537" class="Keyword">open</a> <a id="37542" class="Keyword">import</a> <a id="37549" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a> <a id="37615" class="Keyword">using</a>
  <a id="37623" class="Symbol">(</a> <a id="37625" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html#35054" class="Function">is-decidable-div-ℕ</a><a id="37643" class="Symbol">)</a>
</pre>
### 8.2 Constructions by case analysis

**Definition 8.2.1.** The Collatz function.

Note that we don't store the helper function `h` in a separate definition.
Instead we use Agda's `with` abstraction to do case analysis on the result of
`is-decidable-div-ℕ 2 n`, as explained in Remark 8.2.2.

<pre class="Agda"><a id="37953" class="Keyword">open</a> <a id="37958" class="Keyword">import</a> <a id="37965" href="elementary-number-theory.collatz-conjecture.html" class="Module">elementary-number-theory.collatz-conjecture</a> <a id="38009" class="Keyword">using</a>
  <a id="38017" class="Symbol">(</a> <a id="38019" href="elementary-number-theory.collatz-conjecture.html#503" class="Function">collatz</a><a id="38026" class="Symbol">)</a>
</pre>
**Proposition 8.2.3.** Decidability of products and function types with weaker
assumptions.

<pre class="Agda"><a id="38134" class="Keyword">open</a> <a id="38139" class="Keyword">import</a> <a id="38146" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a> <a id="38173" class="Keyword">using</a>
  <a id="38181" class="Symbol">(</a> <a id="38183" href="foundation.decidable-types.html#2923" class="Function">is-decidable-product&#39;</a>
  <a id="38207" class="Symbol">;</a> <a id="38209" href="foundation.decidable-types.html#4039" class="Function">is-decidable-function-type&#39;</a><a id="38236" class="Symbol">)</a>
</pre>
**Proposition 8.2.4.**

<pre class="Agda"><a id="38275" class="Keyword">open</a> <a id="38280" class="Keyword">import</a> <a id="38287" href="elementary-number-theory.decidable-types.html" class="Module">elementary-number-theory.decidable-types</a> <a id="38328" class="Keyword">using</a>
  <a id="38336" class="Symbol">(</a> <a id="38338" href="elementary-number-theory.decidable-types.html#3557" class="Function">is-decidable-Π-ℕ</a><a id="38354" class="Symbol">)</a>
</pre>
**Corollary 8.2.5.**

<pre class="Agda"><a id="38391" class="Keyword">open</a> <a id="38396" class="Keyword">import</a> <a id="38403" href="elementary-number-theory.decidable-types.html" class="Module">elementary-number-theory.decidable-types</a> <a id="38444" class="Keyword">using</a>
  <a id="38452" class="Symbol">(</a> <a id="38454" href="elementary-number-theory.decidable-types.html#4323" class="Function">is-decidable-bounded-Π-ℕ</a><a id="38478" class="Symbol">)</a>
</pre>
### 8.3 The well-ordering principle of ℕ

**Definition 8.3.1.** Bounds for families over ℕ.

<pre class="Agda"><a id="38586" class="Keyword">open</a> <a id="38591" class="Keyword">import</a> <a id="38598" href="elementary-number-theory.lower-bounds-natural-numbers.html" class="Module">elementary-number-theory.lower-bounds-natural-numbers</a> <a id="38652" class="Keyword">using</a>
  <a id="38660" class="Symbol">(</a> <a id="38662" href="elementary-number-theory.lower-bounds-natural-numbers.html#927" class="Function">is-lower-bound-ℕ</a><a id="38678" class="Symbol">)</a>
<a id="38680" class="Keyword">open</a> <a id="38685" class="Keyword">import</a> <a id="38692" href="elementary-number-theory.upper-bounds-natural-numbers.html" class="Module">elementary-number-theory.upper-bounds-natural-numbers</a> <a id="38746" class="Keyword">using</a>
  <a id="38754" class="Symbol">(</a> <a id="38756" href="elementary-number-theory.upper-bounds-natural-numbers.html#648" class="Function">is-upper-bound-ℕ</a><a id="38772" class="Symbol">)</a>
<a id="38774" class="Keyword">open</a> <a id="38779" class="Keyword">import</a> <a id="38786" href="elementary-number-theory.well-ordering-principle-natural-numbers.html" class="Module">elementary-number-theory.well-ordering-principle-natural-numbers</a> <a id="38851" class="Keyword">using</a>
  <a id="38859" class="Symbol">(</a> <a id="38861" href="elementary-number-theory.well-ordering-principle-natural-numbers.html#1244" class="Function">minimal-element-ℕ</a><a id="38878" class="Symbol">)</a>
</pre>
**Theorem 8.3.2.** Well-ordering principle of ℕ.

<pre class="Agda"><a id="38943" class="Keyword">open</a> <a id="38948" class="Keyword">import</a> <a id="38955" href="elementary-number-theory.well-ordering-principle-natural-numbers.html" class="Module">elementary-number-theory.well-ordering-principle-natural-numbers</a> <a id="39020" class="Keyword">using</a>
  <a id="39028" class="Symbol">(</a> <a id="39030" href="elementary-number-theory.well-ordering-principle-natural-numbers.html#3137" class="Function">well-ordering-principle-ℕ</a><a id="39055" class="Symbol">)</a>
</pre>
### 8.4 The greatest common divisor

**Definition 8.4.1.** The type of greatest common divisors.

<pre class="Agda"><a id="39168" class="Keyword">open</a> <a id="39173" class="Keyword">import</a> <a id="39180" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="39245" class="Keyword">using</a>
  <a id="39253" class="Symbol">(</a> <a id="39255" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#2236" class="Function">is-gcd-ℕ</a><a id="39263" class="Symbol">)</a>
</pre>
**Proposition 8.4.2.** Uniqueness of the greatest common divisor.

<pre class="Agda"><a id="39345" class="Keyword">open</a> <a id="39350" class="Keyword">import</a> <a id="39357" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="39422" class="Keyword">using</a>
  <a id="39430" class="Symbol">(</a> <a id="39432" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#3366" class="Function">uniqueness-is-gcd-ℕ</a><a id="39451" class="Symbol">)</a>
</pre>
**Definition 8.4.3.** Multiples of the greatest common divisor.

<pre class="Agda"><a id="39531" class="Keyword">open</a> <a id="39536" class="Keyword">import</a> <a id="39543" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="39608" class="Keyword">using</a>
  <a id="39616" class="Symbol">(</a> <a id="39618" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#2422" class="Function">is-multiple-of-gcd-ℕ</a><a id="39638" class="Symbol">)</a>
</pre>
**Proposition 8.4.4.** Decidability of multiples of the greatest common divisor.

<pre class="Agda"><a id="39735" class="Keyword">open</a> <a id="39740" class="Keyword">import</a> <a id="39747" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="39812" class="Keyword">using</a>
  <a id="39820" class="Symbol">(</a> <a id="39822" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#4423" class="Function">is-decidable-is-multiple-of-gcd-ℕ</a><a id="39855" class="Symbol">)</a>
</pre>
**Lemma 8.4.5.** `a + b` is a multiple of `gcd(a, b)`.

<pre class="Agda"><a id="39926" class="Keyword">open</a> <a id="39931" class="Keyword">import</a> <a id="39938" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="40003" class="Keyword">using</a>
  <a id="40011" class="Symbol">(</a> <a id="40013" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#5117" class="Function">sum-is-multiple-of-gcd-ℕ</a><a id="40037" class="Symbol">)</a>
</pre>
**Definition 8.4.6.** The greatest common divisor.

<pre class="Agda"><a id="40104" class="Keyword">open</a> <a id="40109" class="Keyword">import</a> <a id="40116" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="40181" class="Keyword">using</a>
  <a id="40189" class="Symbol">(</a> <a id="40191" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#5618" class="Function">gcd-ℕ</a><a id="40196" class="Symbol">)</a>
</pre>
**Lemma 8.4.7.** `gcd(a, b)` is zero if and only if `a + b` = 0.

<pre class="Agda"><a id="40277" class="Keyword">open</a> <a id="40282" class="Keyword">import</a> <a id="40289" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="40354" class="Keyword">using</a>
  <a id="40362" class="Symbol">(</a> <a id="40364" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#5996" class="Function">is-zero-gcd-ℕ</a>
  <a id="40380" class="Symbol">;</a> <a id="40382" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#6398" class="Function">is-zero-add-is-zero-gcd-ℕ</a><a id="40407" class="Symbol">)</a>

<a id="40410" href="literature.introduction-to-homotopy-type-theory.html#40410" class="Function">_</a> <a id="40412" class="Symbol">:</a> <a id="40414" class="Symbol">(</a><a id="40415" href="literature.introduction-to-homotopy-type-theory.html#40415" class="Bound">a</a> <a id="40417" href="literature.introduction-to-homotopy-type-theory.html#40417" class="Bound">b</a> <a id="40419" class="Symbol">:</a> <a id="40421" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="40422" class="Symbol">)</a> <a id="40424" class="Symbol">→</a> <a id="40426" class="Symbol">(</a><a id="40427" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#5618" class="Function">gcd-ℕ</a> <a id="40433" href="literature.introduction-to-homotopy-type-theory.html#40415" class="Bound">a</a> <a id="40435" href="literature.introduction-to-homotopy-type-theory.html#40417" class="Bound">b</a> <a id="40437" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="40439" class="Number">0</a><a id="40440" class="Symbol">)</a> <a id="40442" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="40444" class="Symbol">(</a><a id="40445" href="elementary-number-theory.addition-natural-numbers.html#819" class="Function">add-ℕ</a> <a id="40451" href="literature.introduction-to-homotopy-type-theory.html#40415" class="Bound">a</a> <a id="40453" href="literature.introduction-to-homotopy-type-theory.html#40417" class="Bound">b</a> <a id="40455" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="40457" class="Number">0</a><a id="40458" class="Symbol">)</a>
<a id="40460" class="Symbol">_</a> <a id="40462" class="Symbol">=</a> <a id="40464" class="Symbol">λ</a> <a id="40466" href="literature.introduction-to-homotopy-type-theory.html#40466" class="Bound">a</a> <a id="40468" href="literature.introduction-to-homotopy-type-theory.html#40468" class="Bound">b</a> <a id="40470" class="Symbol">→</a> <a id="40472" class="Symbol">(</a><a id="40473" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#6398" class="Function">is-zero-add-is-zero-gcd-ℕ</a> <a id="40499" href="literature.introduction-to-homotopy-type-theory.html#40466" class="Bound">a</a> <a id="40501" href="literature.introduction-to-homotopy-type-theory.html#40468" class="Bound">b</a> <a id="40503" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="40505" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#5996" class="Function">is-zero-gcd-ℕ</a> <a id="40519" href="literature.introduction-to-homotopy-type-theory.html#40466" class="Bound">a</a> <a id="40521" href="literature.introduction-to-homotopy-type-theory.html#40468" class="Bound">b</a><a id="40522" class="Symbol">)</a>
</pre>
**Theorem 8.4.8.** `gcd(a, b)` is a greatest common divisor.

<pre class="Agda"><a id="40599" class="Keyword">open</a> <a id="40604" class="Keyword">import</a> <a id="40611" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a> <a id="40676" class="Keyword">using</a>
  <a id="40684" class="Symbol">(</a> <a id="40686" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#10885" class="Function">is-gcd-gcd-ℕ</a><a id="40698" class="Symbol">)</a>
</pre>
### 8.5 The infinitude of primes

**Definition 8.5.1.** Proper divisors and primes.

<pre class="Agda"><a id="40798" class="Keyword">open</a> <a id="40803" class="Keyword">import</a> <a id="40810" href="elementary-number-theory.proper-divisors-natural-numbers.html" class="Module">elementary-number-theory.proper-divisors-natural-numbers</a> <a id="40867" class="Keyword">using</a>
  <a id="40875" class="Symbol">(</a> <a id="40877" href="elementary-number-theory.proper-divisors-natural-numbers.html#1152" class="Function">is-proper-divisor-ℕ</a><a id="40896" class="Symbol">)</a>
<a id="40898" class="Keyword">open</a> <a id="40903" class="Keyword">import</a> <a id="40910" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a> <a id="40949" class="Keyword">using</a>
  <a id="40957" class="Symbol">(</a> <a id="40959" href="elementary-number-theory.prime-numbers.html#1562" class="Function">is-prime-ℕ</a><a id="40969" class="Symbol">)</a>
</pre>
**Proposition 8.5.2.** Being a prime is decidable.

<pre class="Agda"><a id="41036" class="Keyword">open</a> <a id="41041" class="Keyword">import</a> <a id="41048" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a> <a id="41087" class="Keyword">using</a>
  <a id="41095" class="Symbol">(</a> <a id="41097" href="elementary-number-theory.prime-numbers.html#5554" class="Function">is-decidable-is-prime-ℕ</a><a id="41120" class="Symbol">)</a>
</pre>
**Definition 8.5.3.** Sieve of Erathostenes.

<pre class="Agda"><a id="41181" class="Keyword">open</a> <a id="41186" class="Keyword">import</a> <a id="41193" href="elementary-number-theory.sieve-of-eratosthenes.html" class="Module">elementary-number-theory.sieve-of-eratosthenes</a> <a id="41240" class="Keyword">using</a>
  <a id="41248" class="Symbol">(</a> <a id="41250" href="elementary-number-theory.sieve-of-eratosthenes.html#1353" class="Function">in-sieve-of-eratosthenes-ℕ</a><a id="41276" class="Symbol">)</a>
</pre>
**Lemma 8.5.4.** Being in the sieve of Erathostenes is decidable.

<pre class="Agda"><a id="41358" class="Keyword">open</a> <a id="41363" class="Keyword">import</a> <a id="41370" href="elementary-number-theory.sieve-of-eratosthenes.html" class="Module">elementary-number-theory.sieve-of-eratosthenes</a> <a id="41417" class="Keyword">using</a>
  <a id="41425" class="Symbol">(</a> <a id="41427" href="elementary-number-theory.sieve-of-eratosthenes.html#1689" class="Function">is-decidable-in-sieve-of-eratosthenes-ℕ</a><a id="41466" class="Symbol">)</a>
</pre>
**Lemma 8.5.5.** `n! + 1` is above `n` in the sieve.

<pre class="Agda"><a id="41535" class="Keyword">open</a> <a id="41540" class="Keyword">import</a> <a id="41547" href="elementary-number-theory.sieve-of-eratosthenes.html" class="Module">elementary-number-theory.sieve-of-eratosthenes</a> <a id="41594" class="Keyword">using</a>
  <a id="41602" class="Symbol">(</a> <a id="41604" href="elementary-number-theory.sieve-of-eratosthenes.html#2253" class="Function">in-sieve-of-eratosthenes-succ-factorial-ℕ</a><a id="41645" class="Symbol">)</a>
</pre>
**Theorem 8.5.6.** Infinitude of primes.

<pre class="Agda"><a id="41702" class="Keyword">open</a> <a id="41707" class="Keyword">import</a> <a id="41714" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a> <a id="41760" class="Keyword">using</a>
  <a id="41768" class="Symbol">(</a> <a id="41770" href="elementary-number-theory.infinitude-of-primes.html#5223" class="Function">infinitude-of-primes-ℕ</a><a id="41792" class="Symbol">)</a>
</pre>
### 8.6 Boolean reflection

**Definition 8.6.1.** Booleanization.

<pre class="Agda"><a id="41874" class="Keyword">open</a> <a id="41879" class="Keyword">import</a> <a id="41886" href="reflection.boolean-reflection.html" class="Module">reflection.boolean-reflection</a> <a id="41916" class="Keyword">using</a>
  <a id="41924" class="Symbol">(</a> <a id="41926" href="reflection.boolean-reflection.html#1218" class="Function">booleanization</a><a id="41940" class="Symbol">)</a>
</pre>
**Theorem 8.6.2.** Boolean reflection principle.

<pre class="Agda"><a id="42005" class="Keyword">open</a> <a id="42010" class="Keyword">import</a> <a id="42017" href="reflection.boolean-reflection.html" class="Module">reflection.boolean-reflection</a> <a id="42047" class="Keyword">using</a>
  <a id="42055" class="Symbol">(</a> <a id="42057" href="reflection.boolean-reflection.html#1536" class="Function">boolean-reflection</a> <a id="42076" class="Comment">-- reflect</a>
  <a id="42089" class="Symbol">)</a>

<a id="42092" href="literature.introduction-to-homotopy-type-theory.html#42092" class="Function">_</a> <a id="42094" class="Symbol">:</a> <a id="42096" href="elementary-number-theory.prime-numbers.html#1562" class="Function">is-prime-ℕ</a> <a id="42107" class="Number">37</a>
<a id="42110" class="Symbol">_</a> <a id="42112" class="Symbol">=</a> <a id="42114" href="reflection.boolean-reflection.html#1536" class="Function">boolean-reflection</a> <a id="42133" class="Symbol">(</a><a id="42134" href="elementary-number-theory.prime-numbers.html#5554" class="Function">is-decidable-is-prime-ℕ</a> <a id="42158" class="Number">37</a><a id="42160" class="Symbol">)</a> <a id="42162" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### Exercises

**Exercise 8.1.** Statements of famous conjectures.

<pre class="Agda"><a id="42248" class="Comment">-- (a)</a>
<a id="42255" class="Keyword">open</a> <a id="42260" class="Keyword">import</a> <a id="42267" href="elementary-number-theory.goldbach-conjecture.html" class="Module">elementary-number-theory.goldbach-conjecture</a> <a id="42312" class="Keyword">using</a>
  <a id="42320" class="Symbol">(</a> <a id="42322" href="elementary-number-theory.goldbach-conjecture.html#1131" class="Function">Goldbach-conjecture</a><a id="42341" class="Symbol">)</a>

<a id="42344" class="Comment">-- (b)</a>
<a id="42351" class="Keyword">open</a> <a id="42356" class="Keyword">import</a> <a id="42363" href="elementary-number-theory.twin-prime-conjecture.html" class="Module">elementary-number-theory.twin-prime-conjecture</a> <a id="42410" class="Keyword">using</a>
  <a id="42418" class="Symbol">(</a> <a id="42420" href="elementary-number-theory.twin-prime-conjecture.html#794" class="Function">twin-prime-conjecture</a><a id="42441" class="Symbol">)</a>

<a id="42444" class="Comment">-- (c)</a>
<a id="42451" class="Keyword">open</a> <a id="42456" class="Keyword">import</a> <a id="42463" href="elementary-number-theory.collatz-conjecture.html" class="Module">elementary-number-theory.collatz-conjecture</a> <a id="42507" class="Keyword">using</a>
  <a id="42515" class="Symbol">(</a> <a id="42517" href="elementary-number-theory.collatz-conjecture.html#732" class="Function">Collatz-conjecture</a><a id="42535" class="Symbol">)</a>
</pre>
**Exercise 8.2.** `is-decidable` is idempotent.

<pre class="Agda"><a id="42599" class="Keyword">open</a> <a id="42604" class="Keyword">import</a> <a id="42611" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a> <a id="42638" class="Keyword">using</a>
  <a id="42646" class="Symbol">(</a> <a id="42648" href="foundation.decidable-types.html#8491" class="Function">map-idempotent-is-decidable</a> <a id="42676" class="Comment">-- is-decidable (is-decidable P) → is-decidable P</a>
  <a id="42728" class="Symbol">)</a>
</pre>
**Exercise 8.3.** Markov's principle over finite types.

<pre class="Agda"><a id="42800" class="Keyword">open</a> <a id="42805" class="Keyword">import</a> <a id="42812" href="elementary-number-theory.well-ordering-principle-standard-finite-types.html" class="Module">elementary-number-theory.well-ordering-principle-standard-finite-types</a> <a id="42883" class="Keyword">using</a>
  <a id="42891" class="Symbol">(</a> <a id="42893" href="elementary-number-theory.well-ordering-principle-standard-finite-types.html#2079" class="Function">exists-not-not-for-all-Fin</a> <a id="42920" class="Comment">-- ¬((x : Fin k) → P x) → Σ (x : Fin k) ¬(P x)</a>
  <a id="42969" class="Symbol">)</a>
</pre>
**Exercise 8.4.** Prime functions.

<pre class="Agda"><a id="43020" class="Keyword">open</a> <a id="43025" class="Keyword">import</a> <a id="43032" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a> <a id="43078" class="Keyword">using</a>
  <a id="43086" class="Symbol">(</a> <a id="43088" href="elementary-number-theory.infinitude-of-primes.html#5642" class="Function">prime-ℕ</a> <a id="43096" class="Comment">-- n-th prime</a>
  <a id="43112" class="Symbol">;</a> <a id="43114" href="elementary-number-theory.infinitude-of-primes.html#6235" class="Function">prime-counting-ℕ</a> <a id="43131" class="Comment">-- number of primes less than or equal `n`</a>
  <a id="43176" class="Symbol">)</a>
</pre>
**Exercise 8.5.** Alternative definition of prime numbers.

TODO

**Exercise 8.6.** Products have decidable equality if and only if factors have
decidable equality, assuming the other factor is pointed.

<pre class="Agda"><a id="43395" class="Keyword">open</a> <a id="43400" class="Keyword">import</a> <a id="43407" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a> <a id="43437" class="Keyword">using</a>
  <a id="43445" class="Symbol">(</a> <a id="43447" href="foundation.decidable-equality.html#2073" class="Function">has-decidable-equality-product&#39;</a>
  <a id="43481" class="Symbol">;</a> <a id="43483" href="foundation.decidable-equality.html#2983" class="Function">has-decidable-equality-left-factor</a>
  <a id="43520" class="Symbol">;</a> <a id="43522" href="foundation.decidable-equality.html#3284" class="Function">has-decidable-equality-right-factor</a><a id="43557" class="Symbol">)</a>

<a id="43560" href="literature.introduction-to-homotopy-type-theory.html#43560" class="Function">_</a> <a id="43562" class="Symbol">:</a>
  <a id="43566" class="Symbol">{</a><a id="43567" href="literature.introduction-to-homotopy-type-theory.html#43567" class="Bound">l1</a> <a id="43570" href="literature.introduction-to-homotopy-type-theory.html#43570" class="Bound">l2</a> <a id="43573" class="Symbol">:</a> <a id="43575" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="43580" class="Symbol">}</a> <a id="43582" class="Symbol">{</a><a id="43583" href="literature.introduction-to-homotopy-type-theory.html#43583" class="Bound">A</a> <a id="43585" class="Symbol">:</a> <a id="43587" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="43590" href="literature.introduction-to-homotopy-type-theory.html#43567" class="Bound">l1</a><a id="43592" class="Symbol">}</a> <a id="43594" class="Symbol">{</a><a id="43595" href="literature.introduction-to-homotopy-type-theory.html#43595" class="Bound">B</a> <a id="43597" class="Symbol">:</a> <a id="43599" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="43602" href="literature.introduction-to-homotopy-type-theory.html#43570" class="Bound">l2</a><a id="43604" class="Symbol">}</a> <a id="43606" class="Symbol">→</a>
  <a id="43610" class="Symbol">(</a><a id="43611" href="literature.introduction-to-homotopy-type-theory.html#43595" class="Bound">B</a> <a id="43613" class="Symbol">→</a> <a id="43615" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="43638" href="literature.introduction-to-homotopy-type-theory.html#43583" class="Bound">A</a><a id="43639" class="Symbol">)</a> <a id="43641" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="43643" class="Symbol">(</a><a id="43644" href="literature.introduction-to-homotopy-type-theory.html#43583" class="Bound">A</a> <a id="43646" class="Symbol">→</a> <a id="43648" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="43671" href="literature.introduction-to-homotopy-type-theory.html#43595" class="Bound">B</a><a id="43672" class="Symbol">)</a> <a id="43674" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a>
  <a id="43678" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="43701" class="Symbol">(</a><a id="43702" href="literature.introduction-to-homotopy-type-theory.html#43583" class="Bound">A</a> <a id="43704" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="43706" href="literature.introduction-to-homotopy-type-theory.html#43595" class="Bound">B</a><a id="43707" class="Symbol">)</a>
<a id="43709" class="Symbol">_</a> <a id="43711" class="Symbol">=</a>
  <a id="43715" class="Symbol">(</a> <a id="43717" class="Symbol">λ</a> <a id="43719" class="Symbol">(</a><a id="43720" href="literature.introduction-to-homotopy-type-theory.html#43720" class="Bound">eqA</a> <a id="43724" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="43726" href="literature.introduction-to-homotopy-type-theory.html#43726" class="Bound">eqB</a><a id="43729" class="Symbol">)</a> <a id="43731" class="Symbol">→</a> <a id="43733" href="foundation.decidable-equality.html#2073" class="Function">has-decidable-equality-product&#39;</a> <a id="43765" href="literature.introduction-to-homotopy-type-theory.html#43720" class="Bound">eqA</a> <a id="43769" href="literature.introduction-to-homotopy-type-theory.html#43726" class="Bound">eqB</a><a id="43772" class="Symbol">)</a> <a id="43774" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
  <a id="43778" class="Symbol">(</a> <a id="43780" class="Symbol">λ</a> <a id="43782" href="literature.introduction-to-homotopy-type-theory.html#43782" class="Bound">eqAB</a> <a id="43787" class="Symbol">→</a>
    <a id="43793" href="foundation.decidable-equality.html#2983" class="Function">has-decidable-equality-left-factor</a> <a id="43828" href="literature.introduction-to-homotopy-type-theory.html#43782" class="Bound">eqAB</a> <a id="43833" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="43839" href="foundation.decidable-equality.html#3284" class="Function">has-decidable-equality-right-factor</a> <a id="43875" href="literature.introduction-to-homotopy-type-theory.html#43782" class="Bound">eqAB</a><a id="43879" class="Symbol">)</a>

<a id="43882" class="Keyword">open</a> <a id="43887" class="Keyword">import</a> <a id="43894" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a> <a id="43924" class="Keyword">using</a>
  <a id="43932" class="Symbol">(</a> <a id="43934" href="foundation.decidable-equality.html#2537" class="Function">has-decidable-equality-product</a><a id="43964" class="Symbol">)</a>
</pre>
**Exercise 8.7.** Observational equality of coproducts.

Note that observational equality of coproducts is defined as a bespoke inductive
type, because the book definition requires raising universe levels: if `A : 𝒰`
and `B : 𝒱` aren't assumed to be in the same universe, then we need to raise the
identity type of `A`, the identity type of `B`, and the empty type to `𝒰 ⊔ 𝒱`.

<pre class="Agda"><a id="44357" class="Keyword">open</a> <a id="44362" class="Keyword">import</a> <a id="44369" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a> <a id="44405" class="Keyword">using</a>
  <a id="44413" class="Symbol">(</a> <a id="44415" href="foundation.equality-coproduct-types.html#1498" class="Datatype">Eq-coproduct</a><a id="44427" class="Symbol">)</a>

<a id="44430" class="Comment">-- (a)</a>
<a id="44437" class="Keyword">open</a> <a id="44442" class="Keyword">import</a> <a id="44449" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a> <a id="44485" class="Keyword">using</a>
  <a id="44493" class="Symbol">(</a> <a id="44495" href="foundation.equality-coproduct-types.html#2071" class="Function">Eq-eq-coproduct</a>
  <a id="44513" class="Symbol">;</a> <a id="44515" href="foundation.equality-coproduct-types.html#2183" class="Function">eq-Eq-coproduct</a><a id="44530" class="Symbol">)</a>

<a id="44533" href="literature.introduction-to-homotopy-type-theory.html#44533" class="Function">_</a> <a id="44535" class="Symbol">:</a>
  <a id="44539" class="Symbol">{</a><a id="44540" href="literature.introduction-to-homotopy-type-theory.html#44540" class="Bound">l1</a> <a id="44543" href="literature.introduction-to-homotopy-type-theory.html#44543" class="Bound">l2</a> <a id="44546" class="Symbol">:</a> <a id="44548" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="44553" class="Symbol">}</a> <a id="44555" class="Symbol">{</a><a id="44556" href="literature.introduction-to-homotopy-type-theory.html#44556" class="Bound">A</a> <a id="44558" class="Symbol">:</a> <a id="44560" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="44563" href="literature.introduction-to-homotopy-type-theory.html#44540" class="Bound">l1</a><a id="44565" class="Symbol">}</a> <a id="44567" class="Symbol">{</a><a id="44568" href="literature.introduction-to-homotopy-type-theory.html#44568" class="Bound">B</a> <a id="44570" class="Symbol">:</a> <a id="44572" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="44575" href="literature.introduction-to-homotopy-type-theory.html#44543" class="Bound">l2</a><a id="44577" class="Symbol">}</a> <a id="44579" class="Symbol">→</a>
  <a id="44583" class="Symbol">(</a><a id="44584" href="literature.introduction-to-homotopy-type-theory.html#44584" class="Bound">x</a> <a id="44586" href="literature.introduction-to-homotopy-type-theory.html#44586" class="Bound">y</a> <a id="44588" class="Symbol">:</a> <a id="44590" href="literature.introduction-to-homotopy-type-theory.html#44556" class="Bound">A</a> <a id="44592" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="44594" href="literature.introduction-to-homotopy-type-theory.html#44568" class="Bound">B</a><a id="44595" class="Symbol">)</a> <a id="44597" class="Symbol">→</a> <a id="44599" class="Symbol">(</a><a id="44600" href="literature.introduction-to-homotopy-type-theory.html#44584" class="Bound">x</a> <a id="44602" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="44604" href="literature.introduction-to-homotopy-type-theory.html#44586" class="Bound">y</a><a id="44605" class="Symbol">)</a> <a id="44607" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="44609" href="foundation.equality-coproduct-types.html#1498" class="Datatype">Eq-coproduct</a> <a id="44622" href="literature.introduction-to-homotopy-type-theory.html#44584" class="Bound">x</a> <a id="44624" href="literature.introduction-to-homotopy-type-theory.html#44586" class="Bound">y</a>
<a id="44626" class="Symbol">_</a> <a id="44628" class="Symbol">=</a> <a id="44630" class="Symbol">λ</a> <a id="44632" href="literature.introduction-to-homotopy-type-theory.html#44632" class="Bound">x</a> <a id="44634" href="literature.introduction-to-homotopy-type-theory.html#44634" class="Bound">y</a> <a id="44636" class="Symbol">→</a> <a id="44638" class="Symbol">(</a><a id="44639" href="foundation.equality-coproduct-types.html#2071" class="Function">Eq-eq-coproduct</a> <a id="44655" href="literature.introduction-to-homotopy-type-theory.html#44632" class="Bound">x</a> <a id="44657" href="literature.introduction-to-homotopy-type-theory.html#44634" class="Bound">y</a> <a id="44659" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="44661" href="foundation.equality-coproduct-types.html#2183" class="Function">eq-Eq-coproduct</a> <a id="44677" href="literature.introduction-to-homotopy-type-theory.html#44632" class="Bound">x</a> <a id="44679" href="literature.introduction-to-homotopy-type-theory.html#44634" class="Bound">y</a><a id="44680" class="Symbol">)</a>

<a id="44683" class="Comment">-- (b)</a>
<a id="44690" class="Keyword">open</a> <a id="44695" class="Keyword">import</a> <a id="44702" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a> <a id="44732" class="Keyword">using</a>
  <a id="44740" class="Symbol">(</a> <a id="44742" href="foundation.decidable-equality.html#10504" class="Function">has-decidable-equality-coproduct</a>
  <a id="44777" class="Symbol">;</a> <a id="44779" href="foundation.decidable-equality.html#11013" class="Function">has-decidable-equality-left-summand</a>
  <a id="44817" class="Symbol">;</a> <a id="44819" href="foundation.decidable-equality.html#11229" class="Function">has-decidable-equality-right-summand</a><a id="44855" class="Symbol">)</a>

<a id="44858" href="literature.introduction-to-homotopy-type-theory.html#44858" class="Function">_</a> <a id="44860" class="Symbol">:</a>
  <a id="44864" class="Symbol">{</a><a id="44865" href="literature.introduction-to-homotopy-type-theory.html#44865" class="Bound">l1</a> <a id="44868" href="literature.introduction-to-homotopy-type-theory.html#44868" class="Bound">l2</a> <a id="44871" class="Symbol">:</a> <a id="44873" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="44878" class="Symbol">}</a> <a id="44880" class="Symbol">{</a><a id="44881" href="literature.introduction-to-homotopy-type-theory.html#44881" class="Bound">A</a> <a id="44883" class="Symbol">:</a> <a id="44885" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="44888" href="literature.introduction-to-homotopy-type-theory.html#44865" class="Bound">l1</a><a id="44890" class="Symbol">}</a> <a id="44892" class="Symbol">{</a><a id="44893" href="literature.introduction-to-homotopy-type-theory.html#44893" class="Bound">B</a> <a id="44895" class="Symbol">:</a> <a id="44897" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="44900" href="literature.introduction-to-homotopy-type-theory.html#44868" class="Bound">l2</a><a id="44902" class="Symbol">}</a> <a id="44904" class="Symbol">→</a>
  <a id="44908" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="44931" href="literature.introduction-to-homotopy-type-theory.html#44881" class="Bound">A</a> <a id="44933" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="44935" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="44958" href="literature.introduction-to-homotopy-type-theory.html#44893" class="Bound">B</a> <a id="44960" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a>
  <a id="44964" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="44987" class="Symbol">(</a><a id="44988" href="literature.introduction-to-homotopy-type-theory.html#44881" class="Bound">A</a> <a id="44990" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="44992" href="literature.introduction-to-homotopy-type-theory.html#44893" class="Bound">B</a><a id="44993" class="Symbol">)</a>
<a id="44995" class="Symbol">_</a> <a id="44997" class="Symbol">=</a>
  <a id="45001" class="Symbol">(</a> <a id="45003" class="Symbol">λ</a> <a id="45005" class="Symbol">(</a><a id="45006" href="literature.introduction-to-homotopy-type-theory.html#45006" class="Bound">eqA</a> <a id="45010" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="45012" href="literature.introduction-to-homotopy-type-theory.html#45012" class="Bound">eqB</a><a id="45015" class="Symbol">)</a> <a id="45017" class="Symbol">→</a> <a id="45019" href="foundation.decidable-equality.html#10504" class="Function">has-decidable-equality-coproduct</a> <a id="45052" href="literature.introduction-to-homotopy-type-theory.html#45006" class="Bound">eqA</a> <a id="45056" href="literature.introduction-to-homotopy-type-theory.html#45012" class="Bound">eqB</a><a id="45059" class="Symbol">)</a> <a id="45061" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
  <a id="45065" class="Symbol">(</a> <a id="45067" class="Symbol">λ</a> <a id="45069" href="literature.introduction-to-homotopy-type-theory.html#45069" class="Bound">eqAB</a> <a id="45074" class="Symbol">→</a>
    <a id="45080" href="foundation.decidable-equality.html#11013" class="Function">has-decidable-equality-left-summand</a> <a id="45116" href="literature.introduction-to-homotopy-type-theory.html#45069" class="Bound">eqAB</a> <a id="45121" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="45127" href="foundation.decidable-equality.html#11229" class="Function">has-decidable-equality-right-summand</a> <a id="45164" href="literature.introduction-to-homotopy-type-theory.html#45069" class="Bound">eqAB</a><a id="45168" class="Symbol">)</a>

<a id="45171" class="Keyword">open</a> <a id="45176" class="Keyword">import</a> <a id="45183" href="elementary-number-theory.equality-integers.html" class="Module">elementary-number-theory.equality-integers</a> <a id="45226" class="Keyword">using</a>
  <a id="45234" class="Symbol">(</a> <a id="45236" href="elementary-number-theory.equality-integers.html#1937" class="Function">has-decidable-equality-ℤ</a><a id="45260" class="Symbol">)</a>
</pre>
**Exercise 8.8.** Decidable equality in dependent pair types.

<pre class="Agda"><a id="45338" class="Keyword">open</a> <a id="45343" class="Keyword">import</a> <a id="45350" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a> <a id="45380" class="Keyword">using</a>
  <a id="45388" class="Symbol">(</a> <a id="45390" href="foundation.decidable-equality.html#8310" class="Function">has-decidable-equality-Σ</a>
  <a id="45417" class="Symbol">;</a> <a id="45419" href="foundation.decidable-equality.html#9027" class="Function">has-decidable-equality-fiber-has-decidable-equality-Σ</a><a id="45472" class="Symbol">)</a>

<a id="45475" href="literature.introduction-to-homotopy-type-theory.html#45475" class="Function">_</a> <a id="45477" class="Symbol">:</a>
  <a id="45481" class="Symbol">{</a><a id="45482" href="literature.introduction-to-homotopy-type-theory.html#45482" class="Bound">l1</a> <a id="45485" href="literature.introduction-to-homotopy-type-theory.html#45485" class="Bound">l2</a> <a id="45488" class="Symbol">:</a> <a id="45490" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="45495" class="Symbol">}</a> <a id="45497" class="Symbol">{</a><a id="45498" href="literature.introduction-to-homotopy-type-theory.html#45498" class="Bound">A</a> <a id="45500" class="Symbol">:</a> <a id="45502" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="45505" href="literature.introduction-to-homotopy-type-theory.html#45482" class="Bound">l1</a><a id="45507" class="Symbol">}</a> <a id="45509" class="Symbol">{</a><a id="45510" href="literature.introduction-to-homotopy-type-theory.html#45510" class="Bound">B</a> <a id="45512" class="Symbol">:</a> <a id="45514" href="literature.introduction-to-homotopy-type-theory.html#45498" class="Bound">A</a> <a id="45516" class="Symbol">→</a> <a id="45518" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="45521" href="literature.introduction-to-homotopy-type-theory.html#45485" class="Bound">l2</a><a id="45523" class="Symbol">}</a> <a id="45525" class="Symbol">→</a> <a id="45527" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="45550" href="literature.introduction-to-homotopy-type-theory.html#45498" class="Bound">A</a> <a id="45552" class="Symbol">→</a>
  <a id="45556" class="Symbol">((</a><a id="45558" href="literature.introduction-to-homotopy-type-theory.html#45558" class="Bound">x</a> <a id="45560" class="Symbol">:</a> <a id="45562" href="literature.introduction-to-homotopy-type-theory.html#45498" class="Bound">A</a><a id="45563" class="Symbol">)</a> <a id="45565" class="Symbol">→</a> <a id="45567" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="45590" class="Symbol">(</a><a id="45591" href="literature.introduction-to-homotopy-type-theory.html#45510" class="Bound">B</a> <a id="45593" href="literature.introduction-to-homotopy-type-theory.html#45558" class="Bound">x</a><a id="45594" class="Symbol">))</a> <a id="45597" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a>
  <a id="45601" href="foundation.decidable-equality.html#1307" class="Function">has-decidable-equality</a> <a id="45624" class="Symbol">(</a><a id="45625" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="45627" href="literature.introduction-to-homotopy-type-theory.html#45498" class="Bound">A</a> <a id="45629" href="literature.introduction-to-homotopy-type-theory.html#45510" class="Bound">B</a><a id="45630" class="Symbol">)</a>
<a id="45632" class="Symbol">_</a> <a id="45634" class="Symbol">=</a>
  <a id="45638" class="Symbol">λ</a> <a id="45640" href="literature.introduction-to-homotopy-type-theory.html#45640" class="Bound">eqA</a> <a id="45644" class="Symbol">→</a>
    <a id="45650" href="foundation.decidable-equality.html#8310" class="Function">has-decidable-equality-Σ</a> <a id="45675" href="literature.introduction-to-homotopy-type-theory.html#45640" class="Bound">eqA</a> <a id="45679" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="45685" href="foundation.decidable-equality.html#9027" class="Function">has-decidable-equality-fiber-has-decidable-equality-Σ</a> <a id="45739" href="literature.introduction-to-homotopy-type-theory.html#45640" class="Bound">eqA</a>

<a id="45744" class="Keyword">open</a> <a id="45749" class="Keyword">import</a> <a id="45756" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a> <a id="45786" class="Keyword">using</a>
  <a id="45794" class="Symbol">(</a> <a id="45796" href="foundation.decidable-equality.html#9717" class="Function">has-decidable-equality-base-has-decidable-equality-Σ</a><a id="45848" class="Symbol">)</a>
</pre>
**Exercise 8.9.** Decidability and decidable equality of dependent function out
of `Fin k`

<pre class="Agda"><a id="45955" class="Keyword">open</a> <a id="45960" class="Keyword">import</a> <a id="45967" href="univalent-combinatorics.decidable-dependent-function-types.html" class="Module">univalent-combinatorics.decidable-dependent-function-types</a> <a id="46026" class="Keyword">using</a>
  <a id="46034" class="Symbol">(</a> <a id="46036" href="univalent-combinatorics.decidable-dependent-function-types.html#1000" class="Function">is-decidable-Π-Fin</a><a id="46054" class="Symbol">)</a>

<a id="46057" class="Comment">-- TODO: b</a>
</pre>
**Exercise 8.10.** Definition of the greatest common divisor as the maximal
element of common divisors.

TODO

**Exercise 8.11.** Bézout's identity.

<pre class="Agda"><a id="46231" class="Keyword">open</a> <a id="46236" class="Keyword">import</a> <a id="46243" href="elementary-number-theory.bezouts-lemma-natural-numbers.html" class="Module">elementary-number-theory.bezouts-lemma-natural-numbers</a> <a id="46298" class="Keyword">using</a>
  <a id="46306" class="Symbol">(</a> <a id="46308" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#28442" class="Function">is-decidable-is-distance-between-multiples-ℕ</a>
    <a id="46357" class="Comment">--^ Σ (k : ℕ) Σ (l : ℕ) dist(k*x, l*x) = z is decidable</a>
  <a id="46415" class="Symbol">;</a> <a id="46417" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#32602" class="Function">minimal-positive-distance-x-coeff</a>
  <a id="46453" class="Symbol">;</a> <a id="46455" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#33047" class="Function">minimal-positive-distance-y-coeff</a>
  <a id="46491" class="Symbol">;</a> <a id="46493" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#70831" class="Function">bezouts-lemma-eqn-ℕ</a>
  <a id="46515" class="Symbol">)</a>
<a id="46517" class="Comment">-- TODO: handle a+b=0</a>
<a id="46539" href="literature.introduction-to-homotopy-type-theory.html#46539" class="Function">_</a> <a id="46541" class="Symbol">:</a>
  <a id="46545" class="Symbol">(</a><a id="46546" href="literature.introduction-to-homotopy-type-theory.html#46546" class="Bound">x</a> <a id="46548" href="literature.introduction-to-homotopy-type-theory.html#46548" class="Bound">y</a> <a id="46550" class="Symbol">:</a> <a id="46552" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="46553" class="Symbol">)</a> <a id="46555" class="Symbol">→</a> <a id="46557" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="46559" class="Symbol">(</a><a id="46560" href="elementary-number-theory.addition-natural-numbers.html#819" class="Function">add-ℕ</a> <a id="46566" href="literature.introduction-to-homotopy-type-theory.html#46546" class="Bound">x</a> <a id="46568" href="literature.introduction-to-homotopy-type-theory.html#46548" class="Bound">y</a> <a id="46570" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="46572" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="46578" class="Symbol">)</a> <a id="46580" class="Symbol">→</a>
  <a id="46584" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="46586" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="46588" class="Symbol">(λ</a> <a id="46591" href="literature.introduction-to-homotopy-type-theory.html#46591" class="Bound">k</a> <a id="46593" class="Symbol">→</a> <a id="46595" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="46597" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="46599" class="Symbol">(λ</a> <a id="46602" href="literature.introduction-to-homotopy-type-theory.html#46602" class="Bound">l</a> <a id="46604" class="Symbol">→</a> <a id="46606" href="elementary-number-theory.distance-natural-numbers.html#1461" class="Function">dist-ℕ</a> <a id="46613" class="Symbol">(</a><a id="46614" href="elementary-number-theory.multiplication-natural-numbers.html#1312" class="Function">mul-ℕ</a> <a id="46620" href="literature.introduction-to-homotopy-type-theory.html#46591" class="Bound">k</a> <a id="46622" href="literature.introduction-to-homotopy-type-theory.html#46546" class="Bound">x</a><a id="46623" class="Symbol">)</a> <a id="46625" class="Symbol">(</a><a id="46626" href="elementary-number-theory.multiplication-natural-numbers.html#1312" class="Function">mul-ℕ</a> <a id="46632" href="literature.introduction-to-homotopy-type-theory.html#46602" class="Bound">l</a> <a id="46634" href="literature.introduction-to-homotopy-type-theory.html#46548" class="Bound">y</a><a id="46635" class="Symbol">)</a> <a id="46637" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="46639" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html#5618" class="Function">gcd-ℕ</a> <a id="46645" href="literature.introduction-to-homotopy-type-theory.html#46546" class="Bound">x</a> <a id="46647" href="literature.introduction-to-homotopy-type-theory.html#46548" class="Bound">y</a><a id="46648" class="Symbol">))</a>
<a id="46651" class="Symbol">_</a> <a id="46653" class="Symbol">=</a>
  <a id="46657" class="Symbol">λ</a> <a id="46659" href="literature.introduction-to-homotopy-type-theory.html#46659" class="Bound">x</a> <a id="46661" href="literature.introduction-to-homotopy-type-theory.html#46661" class="Bound">y</a> <a id="46663" href="literature.introduction-to-homotopy-type-theory.html#46663" class="Bound">possum</a> <a id="46670" class="Symbol">→</a>
    <a id="46676" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#32602" class="Function">minimal-positive-distance-x-coeff</a> <a id="46710" href="literature.introduction-to-homotopy-type-theory.html#46659" class="Bound">x</a> <a id="46712" href="literature.introduction-to-homotopy-type-theory.html#46661" class="Bound">y</a> <a id="46714" href="literature.introduction-to-homotopy-type-theory.html#46663" class="Bound">possum</a> <a id="46721" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="46727" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#33047" class="Function">minimal-positive-distance-y-coeff</a> <a id="46761" href="literature.introduction-to-homotopy-type-theory.html#46659" class="Bound">x</a> <a id="46763" href="literature.introduction-to-homotopy-type-theory.html#46661" class="Bound">y</a> <a id="46765" href="literature.introduction-to-homotopy-type-theory.html#46663" class="Bound">possum</a> <a id="46772" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
    <a id="46778" href="elementary-number-theory.bezouts-lemma-natural-numbers.html#70831" class="Function">bezouts-lemma-eqn-ℕ</a> <a id="46798" href="literature.introduction-to-homotopy-type-theory.html#46659" class="Bound">x</a> <a id="46800" href="literature.introduction-to-homotopy-type-theory.html#46661" class="Bound">y</a> <a id="46802" href="literature.introduction-to-homotopy-type-theory.html#46663" class="Bound">possum</a>
</pre>
**Exercise 8.12.** Prime factor decomposition.

<pre class="Agda"><a id="46870" class="Keyword">open</a> <a id="46875" class="Keyword">import</a> <a id="46882" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html" class="Module">elementary-number-theory.fundamental-theorem-of-arithmetic</a> <a id="46941" class="Keyword">using</a>
  <a id="46949" class="Symbol">(</a> <a id="46951" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#10558" class="Function">nat-least-nontrivial-divisor-ℕ</a> <a id="46982" class="Comment">-- for every 1 &lt; n a number...</a>
  <a id="47015" class="Symbol">;</a> <a id="47017" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#12060" class="Function">is-prime-least-nontrivial-divisor-ℕ</a> <a id="47053" class="Comment">-- which is a prime...</a>
  <a id="47078" class="Symbol">;</a> <a id="47080" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#11136" class="Function">div-least-nontrivial-divisor-ℕ</a> <a id="47111" class="Comment">-- and divides n</a>
  <a id="47130" class="Symbol">)</a>
<a id="47132" class="Keyword">open</a> <a id="47137" class="Keyword">import</a> <a id="47144" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html" class="Module">elementary-number-theory.fundamental-theorem-of-arithmetic</a> <a id="47203" class="Keyword">using</a>
  <a id="47211" class="Symbol">(</a> <a id="47213" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#15218" class="Function">list-fundamental-theorem-arithmetic-ℕ</a> <a id="47251" class="Comment">-- for every 1 &lt; n a list of numbers...</a>
  <a id="47293" class="Symbol">;</a> <a id="47295" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#24791" class="Function">is-sorted-list-fundamental-theorem-arithmetic-ℕ</a> <a id="47343" class="Comment">-- which is sorted...</a>
  <a id="47367" class="Symbol">;</a> <a id="47369" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#18951" class="Function">is-prime-list-fundamental-theorem-arithmetic-ℕ</a> <a id="47416" class="Comment">-- only contains primes...</a>
  <a id="47445" class="Symbol">;</a> <a id="47447" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#19220" class="Function">is-decomposition-list-fundamental-theorem-arithmetic-ℕ</a> <a id="47502" class="Comment">-- and multiplies up to n</a>
  <a id="47530" class="Symbol">)</a>
<a id="47532" class="Keyword">open</a> <a id="47537" class="Keyword">import</a> <a id="47544" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html" class="Module">elementary-number-theory.fundamental-theorem-of-arithmetic</a> <a id="47603" class="Keyword">using</a>
  <a id="47611" class="Symbol">(</a> <a id="47613" href="elementary-number-theory.fundamental-theorem-of-arithmetic.html#31091" class="Function">eq-prime-decomposition-list-ℕ</a> <a id="47643" class="Comment">-- prime decompositions of a fixed number are equal</a>
  <a id="47697" class="Symbol">)</a>
</pre>
**Exercise 8.13.** There are infinitely many primes `p ≡ 3 mod 4`.

TODO.

**Exercise 8.14.** Prime fields.

TODO.

**Exercise 8.15.** The cofibonacci sequenece.

<pre class="Agda"><a id="47875" class="Keyword">open</a> <a id="47880" class="Keyword">import</a> <a id="47887" href="elementary-number-theory.cofibonacci.html" class="Module">elementary-number-theory.cofibonacci</a> <a id="47924" class="Keyword">using</a>
  <a id="47932" class="Symbol">(</a> <a id="47934" href="elementary-number-theory.cofibonacci.html#2522" class="Function">cofibonacci</a>
  <a id="47948" class="Symbol">;</a> <a id="47950" href="elementary-number-theory.cofibonacci.html#3326" class="Function">forward-is-left-adjoint-cofibonacci</a><a id="47985" class="Symbol">)</a>

<a id="47988" class="Comment">-- TODO: backward direction of the adjointness equivalence</a>
</pre>