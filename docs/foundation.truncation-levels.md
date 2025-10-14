# Truncation levels

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a> <a id="66" class="Keyword">where</a>

<a id="73" class="Keyword">open</a> <a id="78" class="Keyword">import</a> <a id="85" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a> <a id="119" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>

<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Definitions

### Inclusions of the natural numbers into the truncation levels

<pre class="Agda"><a id="truncation-level-minus-two-ℕ"></a><a id="522" href="foundation.truncation-levels.html#522" class="Function">truncation-level-minus-two-ℕ</a> <a id="551" class="Symbol">:</a> <a id="553" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="555" class="Symbol">→</a> <a id="557" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
<a id="559" href="foundation.truncation-levels.html#522" class="Function">truncation-level-minus-two-ℕ</a> <a id="588" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="595" class="Symbol">=</a> <a id="597" href="foundation-core.truncation-levels.html#542" class="InductiveConstructor">neg-two-𝕋</a>
<a id="607" href="foundation.truncation-levels.html#522" class="Function">truncation-level-minus-two-ℕ</a> <a id="636" class="Symbol">(</a><a id="637" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="644" href="foundation.truncation-levels.html#644" class="Bound">n</a><a id="645" class="Symbol">)</a> <a id="647" class="Symbol">=</a>
  <a id="651" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="658" class="Symbol">(</a><a id="659" href="foundation.truncation-levels.html#522" class="Function">truncation-level-minus-two-ℕ</a> <a id="688" href="foundation.truncation-levels.html#644" class="Bound">n</a><a id="689" class="Symbol">)</a>

<a id="truncation-level-minus-one-ℕ"></a><a id="692" href="foundation.truncation-levels.html#692" class="Function">truncation-level-minus-one-ℕ</a> <a id="721" class="Symbol">:</a> <a id="723" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="725" class="Symbol">→</a> <a id="727" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
<a id="729" href="foundation.truncation-levels.html#692" class="Function">truncation-level-minus-one-ℕ</a> <a id="758" class="Symbol">=</a> <a id="760" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="767" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="769" href="foundation.truncation-levels.html#522" class="Function">truncation-level-minus-two-ℕ</a>

<a id="truncation-level-ℕ"></a><a id="799" href="foundation.truncation-levels.html#799" class="Function">truncation-level-ℕ</a> <a id="818" class="Symbol">:</a> <a id="820" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="822" class="Symbol">→</a> <a id="824" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a>
<a id="826" href="foundation.truncation-levels.html#799" class="Function">truncation-level-ℕ</a> <a id="845" class="Symbol">=</a> <a id="847" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="854" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="856" href="foundation.truncation-levels.html#692" class="Function">truncation-level-minus-one-ℕ</a>
</pre>
### Inclusion of the double successors of truncation levels into the natural numbers

<pre class="Agda"><a id="nat+2-𝕋"></a><a id="984" href="foundation.truncation-levels.html#984" class="Function">nat+2-𝕋</a> <a id="992" class="Symbol">:</a> <a id="994" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a> <a id="996" class="Symbol">→</a> <a id="998" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="1000" href="foundation.truncation-levels.html#984" class="Function">nat+2-𝕋</a> <a id="1008" href="foundation-core.truncation-levels.html#542" class="InductiveConstructor">neg-two-𝕋</a> <a id="1018" class="Symbol">=</a> <a id="1020" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a>
<a id="1027" href="foundation.truncation-levels.html#984" class="Function">nat+2-𝕋</a> <a id="1035" class="Symbol">(</a><a id="1036" href="foundation-core.truncation-levels.html#558" class="InductiveConstructor">succ-𝕋</a> <a id="1043" href="foundation.truncation-levels.html#1043" class="Bound">k</a><a id="1044" class="Symbol">)</a> <a id="1046" class="Symbol">=</a> <a id="1048" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1055" class="Symbol">(</a><a id="1056" href="foundation.truncation-levels.html#984" class="Function">nat+2-𝕋</a> <a id="1064" href="foundation.truncation-levels.html#1043" class="Bound">k</a><a id="1065" class="Symbol">)</a>
</pre>