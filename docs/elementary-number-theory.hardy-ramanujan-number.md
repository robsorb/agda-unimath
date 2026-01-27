# The Hardy-Ramanujan number

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="elementary-number-theory.hardy-ramanujan-number.html" class="Module">elementary-number-theory.hardy-ramanujan-number</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="elementary-number-theory.taxicab-numbers.html" class="Module">elementary-number-theory.taxicab-numbers</a>

<a id="257" class="Keyword">open</a> <a id="262" class="Keyword">import</a> <a id="269" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
</pre>
</details>

## Idea

The
{{#concept "Hardy-Ramanujan number" Agda=Hardy-Ramanujan-ℕ WD="1729" WDID=Q825176 Agda=Hardy-Ramanujan-ℕ}}
is the number `1729`. This number is the second
[taxicab number](elementary-number-theory.taxicab-numbers.md), i.e., it is the
least natural number that can be written as a sum of cubes of positive natural
numbers in exactly two distinct ways. Specifically, we have the identifications

```text
  1³ + 12³ ＝ 1729    and    9³ + 10³ ＝ 1729.
```

## Definition

### The Hardy-Ramanujan number

<pre class="Agda"><a id="Hardy-Ramanujan-ℕ"></a><a id="909" href="elementary-number-theory.hardy-ramanujan-number.html#909" class="Function">Hardy-Ramanujan-ℕ</a> <a id="927" class="Symbol">:</a> <a id="929" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="931" href="elementary-number-theory.hardy-ramanujan-number.html#909" class="Function">Hardy-Ramanujan-ℕ</a> <a id="949" class="Symbol">=</a> <a id="951" class="Number">1729</a>
</pre>
## Properties

### Two decompositions of the Hardy-Ramanujan number into sums of cubes of two positive natural numbers

<pre class="Agda"><a id="first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ"></a><a id="1089" href="elementary-number-theory.hardy-ramanujan-number.html#1089" class="Function">first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a> <a id="1140" class="Symbol">:</a>
  <a id="1144" href="elementary-number-theory.taxicab-numbers.html#2015" class="Function">sum-of-cubes-decomposition-ℕ</a> <a id="1173" href="elementary-number-theory.hardy-ramanujan-number.html#909" class="Function">Hardy-Ramanujan-ℕ</a>
<a id="1191" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1195" href="elementary-number-theory.hardy-ramanujan-number.html#1089" class="Function">first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a> <a id="1246" class="Symbol">=</a>
  <a id="1250" class="Symbol">(</a><a id="1251" class="Number">1</a> <a id="1253" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1255" href="elementary-number-theory.natural-numbers.html#3087" class="Function">is-nonzero-one-ℕ</a><a id="1271" class="Symbol">)</a>
<a id="1273" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1277" class="Symbol">(</a><a id="1278" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1282" href="elementary-number-theory.hardy-ramanujan-number.html#1089" class="Function">first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a><a id="1332" class="Symbol">)</a> <a id="1334" class="Symbol">=</a>
  <a id="1338" class="Symbol">(</a><a id="1339" class="Number">12</a> <a id="1342" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1344" href="elementary-number-theory.natural-numbers.html#2539" class="Function">is-nonzero-succ-ℕ</a> <a id="1362" class="Number">11</a><a id="1364" class="Symbol">)</a>
<a id="1366" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1370" class="Symbol">(</a><a id="1371" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1375" class="Symbol">(</a><a id="1376" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1380" href="elementary-number-theory.hardy-ramanujan-number.html#1089" class="Function">first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a><a id="1430" class="Symbol">))</a> <a id="1433" class="Symbol">=</a>
  <a id="1437" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a>
<a id="1442" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1446" class="Symbol">(</a><a id="1447" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1451" class="Symbol">(</a><a id="1452" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1456" href="elementary-number-theory.hardy-ramanujan-number.html#1089" class="Function">first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a><a id="1506" class="Symbol">))</a> <a id="1509" class="Symbol">=</a>
  <a id="1513" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ"></a><a id="1519" href="elementary-number-theory.hardy-ramanujan-number.html#1519" class="Function">second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a> <a id="1571" class="Symbol">:</a>
  <a id="1575" href="elementary-number-theory.taxicab-numbers.html#2015" class="Function">sum-of-cubes-decomposition-ℕ</a> <a id="1604" href="elementary-number-theory.hardy-ramanujan-number.html#909" class="Function">Hardy-Ramanujan-ℕ</a>
<a id="1622" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1626" href="elementary-number-theory.hardy-ramanujan-number.html#1519" class="Function">second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a> <a id="1678" class="Symbol">=</a>
  <a id="1682" class="Symbol">(</a><a id="1683" class="Number">9</a> <a id="1685" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1687" href="elementary-number-theory.natural-numbers.html#2539" class="Function">is-nonzero-succ-ℕ</a> <a id="1705" class="Number">8</a><a id="1706" class="Symbol">)</a>
<a id="1708" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1712" class="Symbol">(</a><a id="1713" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1717" href="elementary-number-theory.hardy-ramanujan-number.html#1519" class="Function">second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a><a id="1768" class="Symbol">)</a> <a id="1770" class="Symbol">=</a>
  <a id="1774" class="Symbol">(</a><a id="1775" class="Number">10</a> <a id="1778" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1780" href="elementary-number-theory.natural-numbers.html#2539" class="Function">is-nonzero-succ-ℕ</a> <a id="1798" class="Number">9</a><a id="1799" class="Symbol">)</a>
<a id="1801" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1805" class="Symbol">(</a><a id="1806" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1810" class="Symbol">(</a><a id="1811" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1815" href="elementary-number-theory.hardy-ramanujan-number.html#1519" class="Function">second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a><a id="1866" class="Symbol">))</a> <a id="1869" class="Symbol">=</a>
  <a id="1873" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a>
<a id="1878" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1882" class="Symbol">(</a><a id="1883" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1887" class="Symbol">(</a><a id="1888" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1892" href="elementary-number-theory.hardy-ramanujan-number.html#1519" class="Function">second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ</a><a id="1943" class="Symbol">))</a> <a id="1946" class="Symbol">=</a>
  <a id="1950" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
## External links

- [1729 (number)](<https://en.wikipedia.org/wiki/1729_(number)>) at Wikipedia
