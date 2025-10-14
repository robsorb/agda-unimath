# Function H-spaces

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="structured-types.function-h-spaces.html" class="Module">structured-types.function-h-spaces</a> <a id="72" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.unital-binary-operations.html" class="Module">foundation.unital-binary-operations</a>
<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="structured-types.dependent-products-h-spaces.html" class="Module">structured-types.dependent-products-h-spaces</a>
<a id="311" class="Keyword">open</a> <a id="316" class="Keyword">import</a> <a id="323" href="structured-types.h-spaces.html" class="Module">structured-types.h-spaces</a>
<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

Given a [H-space](structured-types.h-spaces.md) `M` and a type `I`, the
**function H-space** `M^I` consists of functions from `I` to the underlying type
of `M`. Every component of the structure is given pointwise.

## Definition

<pre class="Agda"><a id="656" class="Keyword">module</a> <a id="663" href="structured-types.function-h-spaces.html#663" class="Module">_</a>
  <a id="667" class="Symbol">{</a><a id="668" href="structured-types.function-h-spaces.html#668" class="Bound">l1</a> <a id="671" href="structured-types.function-h-spaces.html#671" class="Bound">l2</a> <a id="674" class="Symbol">:</a> <a id="676" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="681" class="Symbol">}</a> <a id="683" class="Symbol">(</a><a id="684" href="structured-types.function-h-spaces.html#684" class="Bound">I</a> <a id="686" class="Symbol">:</a> <a id="688" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="691" href="structured-types.function-h-spaces.html#668" class="Bound">l1</a><a id="693" class="Symbol">)</a> <a id="695" class="Symbol">(</a><a id="696" href="structured-types.function-h-spaces.html#696" class="Bound">M</a> <a id="698" class="Symbol">:</a> <a id="700" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="708" href="structured-types.function-h-spaces.html#671" class="Bound">l2</a><a id="710" class="Symbol">)</a>
  <a id="714" class="Keyword">where</a>

  <a id="723" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a> <a id="740" class="Symbol">:</a> <a id="742" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="750" class="Symbol">(</a><a id="751" href="structured-types.function-h-spaces.html#668" class="Bound">l1</a> <a id="754" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="756" href="structured-types.function-h-spaces.html#671" class="Bound">l2</a><a id="758" class="Symbol">)</a>
  <a id="762" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a> <a id="779" class="Symbol">=</a> <a id="781" href="structured-types.dependent-products-h-spaces.html#3091" class="Function">Π-H-Space</a> <a id="791" href="structured-types.function-h-spaces.html#684" class="Bound">I</a> <a id="793" class="Symbol">(λ</a> <a id="796" href="structured-types.function-h-spaces.html#796" class="Bound">_</a> <a id="798" class="Symbol">→</a> <a id="800" href="structured-types.function-h-spaces.html#696" class="Bound">M</a><a id="801" class="Symbol">)</a>

  <a id="806" href="structured-types.function-h-spaces.html#806" class="Function">pointed-type-function-H-Space</a> <a id="836" class="Symbol">:</a> <a id="838" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="851" class="Symbol">(</a><a id="852" href="structured-types.function-h-spaces.html#668" class="Bound">l1</a> <a id="855" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="857" href="structured-types.function-h-spaces.html#671" class="Bound">l2</a><a id="859" class="Symbol">)</a>
  <a id="863" href="structured-types.function-h-spaces.html#806" class="Function">pointed-type-function-H-Space</a> <a id="893" class="Symbol">=</a>
    <a id="899" href="structured-types.h-spaces.html#2808" class="Function">pointed-type-H-Space</a> <a id="920" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="940" href="structured-types.function-h-spaces.html#940" class="Function">type-function-H-Space</a> <a id="962" class="Symbol">:</a> <a id="964" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="967" class="Symbol">(</a><a id="968" href="structured-types.function-h-spaces.html#668" class="Bound">l1</a> <a id="971" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="973" href="structured-types.function-h-spaces.html#671" class="Bound">l2</a><a id="975" class="Symbol">)</a>
  <a id="979" href="structured-types.function-h-spaces.html#940" class="Function">type-function-H-Space</a> <a id="1001" class="Symbol">=</a>
    <a id="1007" href="structured-types.h-spaces.html#2880" class="Function">type-H-Space</a> <a id="1020" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="1040" href="structured-types.function-h-spaces.html#1040" class="Function">unit-function-H-Space</a> <a id="1062" class="Symbol">:</a> <a id="1064" href="structured-types.function-h-spaces.html#940" class="Function">type-function-H-Space</a>
  <a id="1088" href="structured-types.function-h-spaces.html#1040" class="Function">unit-function-H-Space</a> <a id="1110" class="Symbol">=</a>
    <a id="1116" href="structured-types.h-spaces.html#2959" class="Function">unit-H-Space</a> <a id="1129" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="1149" href="structured-types.function-h-spaces.html#1149" class="Function">mul-function-H-Space</a> <a id="1170" class="Symbol">:</a>
    <a id="1176" href="structured-types.function-h-spaces.html#940" class="Function">type-function-H-Space</a> <a id="1198" class="Symbol">→</a>
    <a id="1204" href="structured-types.function-h-spaces.html#940" class="Function">type-function-H-Space</a> <a id="1226" class="Symbol">→</a>
    <a id="1232" href="structured-types.function-h-spaces.html#940" class="Function">type-function-H-Space</a>
  <a id="1256" href="structured-types.function-h-spaces.html#1149" class="Function">mul-function-H-Space</a> <a id="1277" class="Symbol">=</a> <a id="1279" href="structured-types.h-spaces.html#3176" class="Function">mul-H-Space</a> <a id="1291" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="1311" href="structured-types.function-h-spaces.html#1311" class="Function">left-unit-law-mul-function-H-Space</a> <a id="1346" class="Symbol">:</a>
    <a id="1352" class="Symbol">(</a><a id="1353" href="structured-types.function-h-spaces.html#1353" class="Bound">f</a> <a id="1355" class="Symbol">:</a> <a id="1357" href="structured-types.function-h-spaces.html#940" class="Function">type-function-H-Space</a><a id="1378" class="Symbol">)</a> <a id="1380" class="Symbol">→</a>
    <a id="1386" href="structured-types.function-h-spaces.html#1149" class="Function">mul-function-H-Space</a> <a id="1407" href="structured-types.function-h-spaces.html#1040" class="Function">unit-function-H-Space</a> <a id="1429" href="structured-types.function-h-spaces.html#1353" class="Bound">f</a> <a id="1431" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1433" href="structured-types.function-h-spaces.html#1353" class="Bound">f</a>
  <a id="1437" href="structured-types.function-h-spaces.html#1311" class="Function">left-unit-law-mul-function-H-Space</a> <a id="1472" class="Symbol">=</a>
    <a id="1478" href="structured-types.h-spaces.html#3802" class="Function">left-unit-law-mul-H-Space</a> <a id="1504" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="1524" href="structured-types.function-h-spaces.html#1524" class="Function">right-unit-law-mul-function-H-Space</a> <a id="1560" class="Symbol">:</a>
    <a id="1566" class="Symbol">(</a><a id="1567" href="structured-types.function-h-spaces.html#1567" class="Bound">f</a> <a id="1569" class="Symbol">:</a> <a id="1571" href="structured-types.function-h-spaces.html#940" class="Function">type-function-H-Space</a><a id="1592" class="Symbol">)</a> <a id="1594" class="Symbol">→</a>
    <a id="1600" href="structured-types.function-h-spaces.html#1149" class="Function">mul-function-H-Space</a> <a id="1621" href="structured-types.function-h-spaces.html#1567" class="Bound">f</a> <a id="1623" href="structured-types.function-h-spaces.html#1040" class="Function">unit-function-H-Space</a> <a id="1645" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1647" href="structured-types.function-h-spaces.html#1567" class="Bound">f</a>
  <a id="1651" href="structured-types.function-h-spaces.html#1524" class="Function">right-unit-law-mul-function-H-Space</a> <a id="1687" class="Symbol">=</a>
    <a id="1693" href="structured-types.h-spaces.html#3965" class="Function">right-unit-law-mul-H-Space</a> <a id="1720" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="1740" href="structured-types.function-h-spaces.html#1740" class="Function">is-unital-mul-function-H-Space</a> <a id="1771" class="Symbol">:</a>
    <a id="1777" href="foundation.unital-binary-operations.html#1413" class="Function">is-unital</a> <a id="1787" href="structured-types.function-h-spaces.html#1149" class="Function">mul-function-H-Space</a>
  <a id="1810" href="structured-types.function-h-spaces.html#1740" class="Function">is-unital-mul-function-H-Space</a> <a id="1841" class="Symbol">=</a>
    <a id="1847" href="structured-types.h-spaces.html#4525" class="Function">is-unital-mul-H-Space</a> <a id="1869" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="1889" href="structured-types.function-h-spaces.html#1889" class="Function">coh-unit-laws-mul-function-H-Space</a> <a id="1924" class="Symbol">:</a>
    <a id="1930" href="foundation.unital-binary-operations.html#1102" class="Function">coh-unit-laws</a>
      <a id="1950" class="Symbol">(</a> <a id="1952" href="structured-types.function-h-spaces.html#1149" class="Function">mul-function-H-Space</a><a id="1972" class="Symbol">)</a>
      <a id="1980" class="Symbol">(</a> <a id="1982" href="structured-types.function-h-spaces.html#1040" class="Function">unit-function-H-Space</a><a id="2003" class="Symbol">)</a>
      <a id="2011" class="Symbol">(</a> <a id="2013" href="structured-types.function-h-spaces.html#1311" class="Function">left-unit-law-mul-function-H-Space</a><a id="2047" class="Symbol">)</a>
      <a id="2055" class="Symbol">(</a> <a id="2057" href="structured-types.function-h-spaces.html#1524" class="Function">right-unit-law-mul-function-H-Space</a><a id="2092" class="Symbol">)</a>
  <a id="2096" href="structured-types.function-h-spaces.html#1889" class="Function">coh-unit-laws-mul-function-H-Space</a> <a id="2131" class="Symbol">=</a>
    <a id="2137" href="structured-types.h-spaces.html#4136" class="Function">coh-unit-laws-mul-H-Space</a> <a id="2163" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="2183" href="structured-types.function-h-spaces.html#2183" class="Function">coherent-unit-laws-mul-function-H-Space</a> <a id="2223" class="Symbol">:</a>
    <a id="2229" href="foundation.unital-binary-operations.html#1258" class="Function">coherent-unit-laws</a>
      <a id="2254" class="Symbol">(</a> <a id="2256" href="structured-types.function-h-spaces.html#1149" class="Function">mul-function-H-Space</a><a id="2276" class="Symbol">)</a>
      <a id="2284" class="Symbol">(</a> <a id="2286" href="structured-types.function-h-spaces.html#1040" class="Function">unit-function-H-Space</a><a id="2307" class="Symbol">)</a>
  <a id="2311" href="structured-types.function-h-spaces.html#2183" class="Function">coherent-unit-laws-mul-function-H-Space</a> <a id="2351" class="Symbol">=</a>
    <a id="2357" href="structured-types.h-spaces.html#3647" class="Function">coherent-unit-laws-mul-H-Space</a> <a id="2388" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="2408" href="structured-types.function-h-spaces.html#2408" class="Function">is-coherently-unital-mul-function-H-Space</a> <a id="2450" class="Symbol">:</a>
    <a id="2456" href="foundation.unital-binary-operations.html#1565" class="Function">is-coherently-unital</a> <a id="2477" href="structured-types.function-h-spaces.html#1149" class="Function">mul-function-H-Space</a>
  <a id="2500" href="structured-types.function-h-spaces.html#2408" class="Function">is-coherently-unital-mul-function-H-Space</a> <a id="2542" class="Symbol">=</a>
    <a id="2548" href="structured-types.h-spaces.html#4669" class="Function">is-coherently-unital-mul-H-Space</a> <a id="2581" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>

  <a id="2601" href="structured-types.function-h-spaces.html#2601" class="Function">coherent-unital-mul-function-H-Space</a> <a id="2638" class="Symbol">:</a>
    <a id="2644" href="structured-types.h-spaces.html#1659" class="Function">coherent-unital-mul-Pointed-Type</a> <a id="2677" href="structured-types.function-h-spaces.html#806" class="Function">pointed-type-function-H-Space</a>
  <a id="2709" href="structured-types.function-h-spaces.html#2601" class="Function">coherent-unital-mul-function-H-Space</a> <a id="2746" class="Symbol">=</a>
    <a id="2752" href="structured-types.h-spaces.html#3047" class="Function">coherent-unital-mul-H-Space</a> <a id="2780" href="structured-types.function-h-spaces.html#723" class="Function">function-H-Space</a>
</pre>