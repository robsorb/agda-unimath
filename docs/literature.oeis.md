# Sequences of the online encyclopedia of integer sequences

This file records formalized sequences of the
[Online Encyclopedia of Integer Sequences](https://oeis.org) {{#cite oeis}}.

<pre class="Agda"><a id="194" class="Keyword">module</a> <a id="201" href="literature.oeis.html" class="Module">literature.oeis</a> <a id="217" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="elementary-number-theory.exponentiation-natural-numbers.html" class="Module">elementary-number-theory.exponentiation-natural-numbers</a>
<a id="341" class="Keyword">open</a> <a id="346" class="Keyword">import</a> <a id="353" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="foundation.function-types.html" class="Module">foundation.function-types</a>
</pre>
</details>

## Sequences

### The number of groups of order `n`

OEIS: [A000001](https://oeis.org/A000001)

<pre class="Agda"><a id="554" class="Keyword">open</a> <a id="559" class="Keyword">import</a> <a id="566" href="finite-group-theory.finite-groups.html" class="Module">finite-group-theory.finite-groups</a> <a id="600" class="Keyword">using</a>
  <a id="608" class="Symbol">(</a> <a id="610" href="finite-group-theory.finite-groups.html#15617" class="Function">number-of-groups-of-order</a><a id="635" class="Symbol">)</a>
</pre>
### The Kolakoski sequence

OEIS: [A000002](https://oeis.org/A000002)

<pre class="Agda"><a id="721" class="Keyword">open</a> <a id="726" class="Keyword">import</a> <a id="733" href="elementary-number-theory.kolakoski-sequence.html" class="Module">elementary-number-theory.kolakoski-sequence</a> <a id="777" class="Keyword">using</a>
  <a id="785" class="Symbol">(</a> <a id="787" href="elementary-number-theory.kolakoski-sequence.html#1866" class="Function">kolakoski</a><a id="796" class="Symbol">)</a>
</pre>
### The zero sequence

OEIS: [A000004](https://oeis.org/A000004)

<pre class="Agda"><a id="A000004"></a><a id="877" href="literature.oeis.html#877" class="Function">A000004</a> <a id="885" class="Symbol">:</a> <a id="887" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="889" class="Symbol">→</a> <a id="891" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="893" href="literature.oeis.html#877" class="Function">A000004</a> <a id="901" class="Symbol">_</a> <a id="903" class="Symbol">=</a> <a id="905" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a>
</pre>
### The characteristic function for 0

OEIS: [A000007](https://oeis.org/A000007)

<pre class="Agda"><a id="A000007"></a><a id="1007" href="literature.oeis.html#1007" class="Function">A000007</a> <a id="1015" class="Symbol">:</a> <a id="1017" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1019" class="Symbol">→</a> <a id="1021" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1023" href="literature.oeis.html#1007" class="Function">A000007</a> <a id="1031" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="1038" class="Symbol">=</a> <a id="1040" class="Number">1</a>
<a id="1042" href="literature.oeis.html#1007" class="Function">A000007</a> <a id="1050" class="Symbol">(</a><a id="1051" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1058" class="Symbol">_)</a> <a id="1061" class="Symbol">=</a> <a id="1063" class="Number">0</a>
</pre>
### Euler's totient function

OEIS: [A000010](https://oeis.org/A000010)

<pre class="Agda"><a id="1151" class="Keyword">open</a> <a id="1156" class="Keyword">import</a> <a id="1163" href="elementary-number-theory.eulers-totient-function.html" class="Module">elementary-number-theory.eulers-totient-function</a> <a id="1212" class="Keyword">using</a>
  <a id="1220" class="Symbol">(</a> <a id="1222" href="elementary-number-theory.eulers-totient-function.html#1842" class="Function">eulers-totient-function-relatively-prime</a><a id="1262" class="Symbol">)</a>
</pre>
### All 1's sequence

OEIS: [A000012](https://oeis.org/A000012)

<pre class="Agda"><a id="A000012"></a><a id="1342" href="literature.oeis.html#1342" class="Function">A000012</a> <a id="1350" class="Symbol">:</a> <a id="1352" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1354" class="Symbol">→</a> <a id="1356" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1358" href="literature.oeis.html#1342" class="Function">A000012</a> <a id="1366" class="Symbol">_</a> <a id="1368" class="Symbol">=</a> <a id="1370" class="Number">1</a>
</pre>
### The positive integers

OEIS: [A000027](https://oeis.org/A000027)

<pre class="Agda"><a id="A000027"></a><a id="1455" href="literature.oeis.html#1455" class="Function">A000027</a> <a id="1463" class="Symbol">:</a> <a id="1465" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1467" class="Symbol">→</a> <a id="1469" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1471" href="literature.oeis.html#1455" class="Function">A000027</a> <a id="1479" class="Symbol">=</a> <a id="1481" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a>
</pre>
### The prime numbers

OEIS: [A000040](https://oeis.org/A000040)

<pre class="Agda"><a id="1567" class="Keyword">open</a> <a id="1572" class="Keyword">import</a> <a id="1579" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a> <a id="1625" class="Keyword">using</a>
  <a id="1633" class="Symbol">(</a> <a id="1635" href="elementary-number-theory.infinitude-of-primes.html#5642" class="Function">prime-ℕ</a><a id="1642" class="Symbol">)</a>
</pre>
### The Fibonacci sequence

OEIS: [A000045](https://oeis.org/A000045)

<pre class="Agda"><a id="1728" class="Keyword">open</a> <a id="1733" class="Keyword">import</a> <a id="1740" href="elementary-number-theory.fibonacci-sequence.html" class="Module">elementary-number-theory.fibonacci-sequence</a> <a id="1784" class="Keyword">using</a>
  <a id="1792" class="Symbol">(</a> <a id="1794" href="elementary-number-theory.fibonacci-sequence.html#1381" class="Function">Fibonacci-ℕ</a><a id="1805" class="Symbol">)</a>
</pre>
### Sylvester's sequence

OEIS: [A000058](https://oeis.org/A000058)

<pre class="Agda"><a id="1889" class="Keyword">open</a> <a id="1894" class="Keyword">import</a> <a id="1901" href="elementary-number-theory.sylvesters-sequence.html" class="Module">elementary-number-theory.sylvesters-sequence</a> <a id="1946" class="Keyword">using</a>
  <a id="1954" class="Symbol">(</a> <a id="1956" href="elementary-number-theory.sylvesters-sequence.html#1062" class="Function">sylvesters-sequence-ℕ</a><a id="1977" class="Symbol">)</a>
</pre>
### Powers of `2`

OEIS: [A000079](https://oeis.org/A000079)

<pre class="Agda"><a id="A000079"></a><a id="2054" href="literature.oeis.html#2054" class="Function">A000079</a> <a id="2062" class="Symbol">:</a> <a id="2064" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2066" class="Symbol">→</a> <a id="2068" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="2070" href="literature.oeis.html#2054" class="Function">A000079</a> <a id="2078" class="Symbol">=</a> <a id="2080" href="elementary-number-theory.exponentiation-natural-numbers.html#927" class="Function">exp-ℕ</a> <a id="2086" class="Number">2</a>
</pre>
### The Catalan numbers

OEIS: [A000108](https://oeis.org/A000108)

<pre class="Agda"><a id="2169" class="Keyword">open</a> <a id="2174" class="Keyword">import</a> <a id="2181" href="elementary-number-theory.catalan-numbers.html" class="Module">elementary-number-theory.catalan-numbers</a> <a id="2222" class="Keyword">using</a>
  <a id="2230" class="Symbol">(</a> <a id="2232" href="elementary-number-theory.catalan-numbers.html#1724" class="Function">catalan-numbers</a><a id="2247" class="Symbol">)</a>
</pre>
### The Bell numbers

OEIS: [A000110](https://oeis.org/A000110)

<pre class="Agda"><a id="2327" class="Keyword">open</a> <a id="2332" class="Keyword">import</a> <a id="2339" href="elementary-number-theory.bell-numbers.html" class="Module">elementary-number-theory.bell-numbers</a> <a id="2377" class="Keyword">using</a>
  <a id="2385" class="Symbol">(</a> <a id="2387" href="elementary-number-theory.bell-numbers.html#1059" class="Function">bell-number-ℕ</a><a id="2400" class="Symbol">)</a>
</pre>
### Factorials

OEIS: [A000142](https://oeis.org/A000142)

<pre class="Agda"><a id="2474" class="Keyword">open</a> <a id="2479" class="Keyword">import</a> <a id="2486" href="elementary-number-theory.factorials.html" class="Module">elementary-number-theory.factorials</a> <a id="2522" class="Keyword">using</a>
  <a id="2530" class="Symbol">(</a> <a id="2532" href="elementary-number-theory.factorials.html#823" class="Function">factorial-ℕ</a><a id="2543" class="Symbol">)</a>
</pre>
### The Fermat numbers

OEIS: [A000215](https://oeis.org/A000215)

<pre class="Agda"><a id="2625" class="Keyword">open</a> <a id="2630" class="Keyword">import</a> <a id="2637" href="elementary-number-theory.fermat-numbers.html" class="Module">elementary-number-theory.fermat-numbers</a> <a id="2677" class="Keyword">using</a>
  <a id="2685" class="Symbol">(</a> <a id="2687" href="elementary-number-theory.fermat-numbers.html#1674" class="Function">fermat-number-ℕ</a><a id="2702" class="Symbol">)</a>
</pre>
### Powers of `3`

OEIS: [A000244](https://oeis.org/A000244)

<pre class="Agda"><a id="A000244"></a><a id="2779" href="literature.oeis.html#2779" class="Function">A000244</a> <a id="2787" class="Symbol">:</a> <a id="2789" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2791" class="Symbol">→</a> <a id="2793" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="2795" href="literature.oeis.html#2779" class="Function">A000244</a> <a id="2803" class="Symbol">=</a> <a id="2805" href="elementary-number-theory.exponentiation-natural-numbers.html#927" class="Function">exp-ℕ</a> <a id="2811" class="Number">3</a>
</pre>
### The prime counting function

OEIS: [A000720](https://oeis.org/A000720)

<pre class="Agda"><a id="2902" class="Keyword">open</a> <a id="2907" class="Keyword">import</a> <a id="2914" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a> <a id="2960" class="Keyword">using</a>
  <a id="2968" class="Symbol">(</a> <a id="2970" href="elementary-number-theory.infinitude-of-primes.html#6235" class="Function">prime-counting-ℕ</a><a id="2986" class="Symbol">)</a>
</pre>
### The Euclid–Mullin sequence

OEIS: [A000945](https://oeis.org/A000945)

<pre class="Agda"><a id="3076" class="Keyword">open</a> <a id="3081" class="Keyword">import</a> <a id="3088" href="elementary-number-theory.euclid-mullin-sequence.html" class="Module">elementary-number-theory.euclid-mullin-sequence</a> <a id="3136" class="Keyword">using</a>
  <a id="3144" class="Symbol">(</a> <a id="3146" href="elementary-number-theory.euclid-mullin-sequence.html#1270" class="Function">euclid-mullin-ℕ</a><a id="3161" class="Symbol">)</a>
</pre>
### Pisano periods

OEIS: [A001175](https://oeis.org/A001175)

<pre class="Agda"><a id="3239" class="Keyword">open</a> <a id="3244" class="Keyword">import</a> <a id="3251" href="elementary-number-theory.pisano-periods.html" class="Module">elementary-number-theory.pisano-periods</a> <a id="3291" class="Keyword">using</a>
  <a id="3299" class="Symbol">(</a> <a id="3301" href="elementary-number-theory.pisano-periods.html#5555" class="Function">pisano-period</a><a id="3314" class="Symbol">)</a>
</pre>
### The cofibonacci sequence

OEIS: [A001177](https://oeis.org/A001177)

<pre class="Agda"><a id="3402" class="Keyword">open</a> <a id="3407" class="Keyword">import</a> <a id="3414" href="elementary-number-theory.cofibonacci.html" class="Module">elementary-number-theory.cofibonacci</a> <a id="3451" class="Keyword">using</a>
  <a id="3459" class="Symbol">(</a> <a id="3461" href="elementary-number-theory.cofibonacci.html#2522" class="Function">cofibonacci</a><a id="3472" class="Symbol">)</a>
</pre>
### The natural numbers

OEIS: [A001477](https://oeis.org/A001477)

<pre class="Agda"><a id="A001477"></a><a id="3555" href="literature.oeis.html#3555" class="Function">A001477</a> <a id="3563" class="Symbol">:</a> <a id="3565" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="3567" class="Symbol">→</a> <a id="3569" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="3571" href="literature.oeis.html#3555" class="Function">A001477</a> <a id="3579" class="Symbol">=</a> <a id="3581" href="foundation-core.function-types.html#307" class="Function">id</a>
</pre>
### The number of main classes of Latin squares of order `n`

OEIS: [A003090](https://oeis.org/A003090)

<pre class="Agda"><a id="3702" class="Keyword">open</a> <a id="3707" class="Keyword">import</a> <a id="3714" href="univalent-combinatorics.main-classes-of-latin-squares.html" class="Module">univalent-combinatorics.main-classes-of-latin-squares</a> <a id="3768" class="Keyword">using</a>
  <a id="3776" class="Symbol">(</a> <a id="3778" href="univalent-combinatorics.main-classes-of-latin-squares.html#2462" class="Function">number-of-main-classes-of-Latin-squares-of-order</a><a id="3826" class="Symbol">)</a>
</pre>
### Collatz' bijection

OEIS: [A006369](https://oeis.org/A006369)

<pre class="Agda"><a id="3908" class="Keyword">open</a> <a id="3913" class="Keyword">import</a> <a id="3920" href="elementary-number-theory.collatz-bijection.html" class="Module">elementary-number-theory.collatz-bijection</a> <a id="3963" class="Keyword">using</a>
  <a id="3971" class="Symbol">(</a> <a id="3973" href="elementary-number-theory.collatz-bijection.html#982" class="Function">map-collatz-bijection</a><a id="3994" class="Symbol">)</a>
</pre>
### The number of semigroups of order `n` up to isomorphism

OEIS: [A027851](https://oeis.org/A027851)

<pre class="Agda"><a id="4113" class="Keyword">open</a> <a id="4118" class="Keyword">import</a> <a id="4125" href="finite-group-theory.finite-semigroups.html" class="Module">finite-group-theory.finite-semigroups</a> <a id="4163" class="Keyword">using</a>
  <a id="4171" class="Symbol">(</a> <a id="4173" href="finite-group-theory.finite-semigroups.html#7225" class="Function">number-of-semigroups-of-order</a><a id="4202" class="Symbol">)</a>
</pre>
### The main diagonal of the Ackermann–Péter function

OEIS: [A046859](https://oeis.org/A046859)

<pre class="Agda"><a id="4315" class="Keyword">open</a> <a id="4320" class="Keyword">import</a> <a id="4327" href="elementary-number-theory.ackermann-function.html" class="Module">elementary-number-theory.ackermann-function</a> <a id="4371" class="Keyword">using</a>
  <a id="4379" class="Symbol">(</a> <a id="4381" href="elementary-number-theory.ackermann-function.html#770" class="Function">simplified-ackermann-ℕ</a><a id="4403" class="Symbol">)</a>
</pre>
### The number of monoids of order `n` up to isomorphism

OEIS: [A058129](https://oeis.org/A058129)

<pre class="Agda"><a id="4519" class="Keyword">open</a> <a id="4524" class="Keyword">import</a> <a id="4531" href="finite-group-theory.finite-monoids.html" class="Module">finite-group-theory.finite-monoids</a> <a id="4566" class="Keyword">using</a>
  <a id="4574" class="Symbol">(</a> <a id="4576" href="finite-group-theory.finite-monoids.html#7528" class="Function">number-of-monoids-of-order</a><a id="4602" class="Symbol">)</a>
</pre>
## References

{{#bibliography}}
