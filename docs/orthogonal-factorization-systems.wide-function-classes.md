# Wide function classes

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="orthogonal-factorization-systems.wide-function-classes.html" class="Module">orthogonal-factorization-systems.wide-function-classes</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="357" class="Keyword">open</a> <a id="362" class="Keyword">import</a> <a id="369" href="orthogonal-factorization-systems.function-classes.html" class="Module">orthogonal-factorization-systems.function-classes</a>
</pre>
</details>

## Idea

We say a
[(small) function class](orthogonal-factorization-systems.function-classes.md)
is **wide** if it contains all [equivalences](foundation-core.equivalences.md)
and is composition closed. This means it is morally a wide sub-∞-category of the
∞-category of types at a fixed universe level.

## Definition

### The predicate on small function classes of being wide

<pre class="Agda"><a id="823" class="Keyword">module</a> <a id="830" href="orthogonal-factorization-systems.wide-function-classes.html#830" class="Module">_</a>
  <a id="834" class="Symbol">{</a><a id="835" href="orthogonal-factorization-systems.wide-function-classes.html#835" class="Bound">l1</a> <a id="838" href="orthogonal-factorization-systems.wide-function-classes.html#838" class="Bound">l2</a> <a id="841" class="Symbol">:</a> <a id="843" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="848" class="Symbol">}</a> <a id="850" class="Symbol">(</a><a id="851" href="orthogonal-factorization-systems.wide-function-classes.html#851" class="Bound">P</a> <a id="853" class="Symbol">:</a> <a id="855" href="orthogonal-factorization-systems.function-classes.html#984" class="Function">function-class</a> <a id="870" href="orthogonal-factorization-systems.wide-function-classes.html#835" class="Bound">l1</a> <a id="873" href="orthogonal-factorization-systems.wide-function-classes.html#835" class="Bound">l1</a> <a id="876" href="orthogonal-factorization-systems.wide-function-classes.html#838" class="Bound">l2</a><a id="878" class="Symbol">)</a>
  <a id="882" class="Keyword">where</a>

  <a id="891" href="orthogonal-factorization-systems.wide-function-classes.html#891" class="Function">is-wide-function-class</a> <a id="914" class="Symbol">:</a> <a id="916" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="919" class="Symbol">(</a><a id="920" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="925" href="orthogonal-factorization-systems.wide-function-classes.html#835" class="Bound">l1</a> <a id="928" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="930" href="orthogonal-factorization-systems.wide-function-classes.html#838" class="Bound">l2</a><a id="932" class="Symbol">)</a>
  <a id="936" href="orthogonal-factorization-systems.wide-function-classes.html#891" class="Function">is-wide-function-class</a> <a id="959" class="Symbol">=</a>
    <a id="965" class="Symbol">(</a> <a id="967" href="orthogonal-factorization-systems.function-classes.html#2788" class="Function">has-equivalences-function-class</a> <a id="999" href="orthogonal-factorization-systems.wide-function-classes.html#851" class="Bound">P</a><a id="1000" class="Symbol">)</a> <a id="1002" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
    <a id="1008" class="Symbol">(</a> <a id="1010" href="orthogonal-factorization-systems.function-classes.html#3666" class="Function">is-closed-under-composition-function-class</a> <a id="1053" href="orthogonal-factorization-systems.wide-function-classes.html#851" class="Bound">P</a><a id="1054" class="Symbol">)</a>

  <a id="1059" href="orthogonal-factorization-systems.wide-function-classes.html#1059" class="Function">is-wide-function-class-Prop</a> <a id="1087" class="Symbol">:</a> <a id="1089" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1094" class="Symbol">(</a><a id="1095" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1100" href="orthogonal-factorization-systems.wide-function-classes.html#835" class="Bound">l1</a> <a id="1103" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1105" href="orthogonal-factorization-systems.wide-function-classes.html#838" class="Bound">l2</a><a id="1107" class="Symbol">)</a>
  <a id="1111" href="orthogonal-factorization-systems.wide-function-classes.html#1059" class="Function">is-wide-function-class-Prop</a> <a id="1139" class="Symbol">=</a>
    <a id="1145" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a>
      <a id="1164" class="Symbol">(</a> <a id="1166" href="orthogonal-factorization-systems.function-classes.html#3217" class="Function">has-equivalences-function-class-Prop</a> <a id="1203" href="orthogonal-factorization-systems.wide-function-classes.html#851" class="Bound">P</a><a id="1204" class="Symbol">)</a>
      <a id="1212" class="Symbol">(</a> <a id="1214" href="orthogonal-factorization-systems.function-classes.html#4230" class="Function">is-closed-under-composition-function-class-Prop</a> <a id="1262" href="orthogonal-factorization-systems.wide-function-classes.html#851" class="Bound">P</a><a id="1263" class="Symbol">)</a>

  <a id="1268" href="orthogonal-factorization-systems.wide-function-classes.html#1268" class="Function">is-prop-is-wide-function-class</a> <a id="1299" class="Symbol">:</a> <a id="1301" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1309" href="orthogonal-factorization-systems.wide-function-classes.html#891" class="Function">is-wide-function-class</a>
  <a id="1334" href="orthogonal-factorization-systems.wide-function-classes.html#1268" class="Function">is-prop-is-wide-function-class</a> <a id="1365" class="Symbol">=</a> <a id="1367" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1385" href="orthogonal-factorization-systems.wide-function-classes.html#1059" class="Function">is-wide-function-class-Prop</a>

  <a id="1416" href="orthogonal-factorization-systems.wide-function-classes.html#1416" class="Function">has-equivalences-is-wide-function-class</a> <a id="1456" class="Symbol">:</a>
    <a id="1462" href="orthogonal-factorization-systems.wide-function-classes.html#891" class="Function">is-wide-function-class</a> <a id="1485" class="Symbol">→</a> <a id="1487" href="orthogonal-factorization-systems.function-classes.html#2788" class="Function">has-equivalences-function-class</a> <a id="1519" href="orthogonal-factorization-systems.wide-function-classes.html#851" class="Bound">P</a>
  <a id="1523" href="orthogonal-factorization-systems.wide-function-classes.html#1416" class="Function">has-equivalences-is-wide-function-class</a> <a id="1563" class="Symbol">=</a> <a id="1565" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="1572" href="orthogonal-factorization-systems.wide-function-classes.html#1572" class="Function">is-closed-under-composition-is-wide-function-class</a> <a id="1623" class="Symbol">:</a>
    <a id="1629" href="orthogonal-factorization-systems.wide-function-classes.html#891" class="Function">is-wide-function-class</a> <a id="1652" class="Symbol">→</a> <a id="1654" href="orthogonal-factorization-systems.function-classes.html#3666" class="Function">is-closed-under-composition-function-class</a> <a id="1697" href="orthogonal-factorization-systems.wide-function-classes.html#851" class="Bound">P</a>
  <a id="1701" href="orthogonal-factorization-systems.wide-function-classes.html#1572" class="Function">is-closed-under-composition-is-wide-function-class</a> <a id="1752" class="Symbol">=</a> <a id="1754" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>
### The type of small wide function classes

<pre class="Agda"><a id="wide-function-class"></a><a id="1816" href="orthogonal-factorization-systems.wide-function-classes.html#1816" class="Function">wide-function-class</a> <a id="1836" class="Symbol">:</a> <a id="1838" class="Symbol">(</a><a id="1839" href="orthogonal-factorization-systems.wide-function-classes.html#1839" class="Bound">l1</a> <a id="1842" href="orthogonal-factorization-systems.wide-function-classes.html#1842" class="Bound">l2</a> <a id="1845" class="Symbol">:</a> <a id="1847" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1852" class="Symbol">)</a> <a id="1854" class="Symbol">→</a> <a id="1856" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1859" class="Symbol">(</a><a id="1860" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1865" href="orthogonal-factorization-systems.wide-function-classes.html#1839" class="Bound">l1</a> <a id="1868" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1870" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1875" href="orthogonal-factorization-systems.wide-function-classes.html#1842" class="Bound">l2</a><a id="1877" class="Symbol">)</a>
<a id="1879" href="orthogonal-factorization-systems.wide-function-classes.html#1816" class="Function">wide-function-class</a> <a id="1899" href="orthogonal-factorization-systems.wide-function-classes.html#1899" class="Bound">l1</a> <a id="1902" href="orthogonal-factorization-systems.wide-function-classes.html#1902" class="Bound">l2</a> <a id="1905" class="Symbol">=</a>
  <a id="1909" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1911" class="Symbol">(</a><a id="1912" href="orthogonal-factorization-systems.function-classes.html#984" class="Function">function-class</a> <a id="1927" href="orthogonal-factorization-systems.wide-function-classes.html#1899" class="Bound">l1</a> <a id="1930" href="orthogonal-factorization-systems.wide-function-classes.html#1899" class="Bound">l1</a> <a id="1933" href="orthogonal-factorization-systems.wide-function-classes.html#1902" class="Bound">l2</a><a id="1935" class="Symbol">)</a> <a id="1937" class="Symbol">(</a><a id="1938" href="orthogonal-factorization-systems.wide-function-classes.html#891" class="Function">is-wide-function-class</a><a id="1960" class="Symbol">)</a>

<a id="1963" class="Keyword">module</a> <a id="1970" href="orthogonal-factorization-systems.wide-function-classes.html#1970" class="Module">_</a>
  <a id="1974" class="Symbol">{</a><a id="1975" href="orthogonal-factorization-systems.wide-function-classes.html#1975" class="Bound">l1</a> <a id="1978" href="orthogonal-factorization-systems.wide-function-classes.html#1978" class="Bound">l2</a> <a id="1981" class="Symbol">:</a> <a id="1983" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1988" class="Symbol">}</a> <a id="1990" class="Symbol">(</a><a id="1991" href="orthogonal-factorization-systems.wide-function-classes.html#1991" class="Bound">P</a> <a id="1993" class="Symbol">:</a> <a id="1995" href="orthogonal-factorization-systems.wide-function-classes.html#1816" class="Function">wide-function-class</a> <a id="2015" href="orthogonal-factorization-systems.wide-function-classes.html#1975" class="Bound">l1</a> <a id="2018" href="orthogonal-factorization-systems.wide-function-classes.html#1978" class="Bound">l2</a><a id="2020" class="Symbol">)</a>
  <a id="2024" class="Keyword">where</a>

  <a id="2033" href="orthogonal-factorization-systems.wide-function-classes.html#2033" class="Function">function-class-wide-function-class</a> <a id="2068" class="Symbol">:</a> <a id="2070" href="orthogonal-factorization-systems.function-classes.html#984" class="Function">function-class</a> <a id="2085" href="orthogonal-factorization-systems.wide-function-classes.html#1975" class="Bound">l1</a> <a id="2088" href="orthogonal-factorization-systems.wide-function-classes.html#1975" class="Bound">l1</a> <a id="2091" href="orthogonal-factorization-systems.wide-function-classes.html#1978" class="Bound">l2</a>
  <a id="2096" href="orthogonal-factorization-systems.wide-function-classes.html#2033" class="Function">function-class-wide-function-class</a> <a id="2131" class="Symbol">=</a> <a id="2133" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2137" href="orthogonal-factorization-systems.wide-function-classes.html#1991" class="Bound">P</a>

  <a id="2142" href="orthogonal-factorization-systems.wide-function-classes.html#2142" class="Function">is-wide-wide-function-class</a> <a id="2170" class="Symbol">:</a>
    <a id="2176" href="orthogonal-factorization-systems.wide-function-classes.html#891" class="Function">is-wide-function-class</a> <a id="2199" href="orthogonal-factorization-systems.wide-function-classes.html#2033" class="Function">function-class-wide-function-class</a>
  <a id="2236" href="orthogonal-factorization-systems.wide-function-classes.html#2142" class="Function">is-wide-wide-function-class</a> <a id="2264" class="Symbol">=</a> <a id="2266" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2270" href="orthogonal-factorization-systems.wide-function-classes.html#1991" class="Bound">P</a>

  <a id="2275" href="orthogonal-factorization-systems.wide-function-classes.html#2275" class="Function">has-equivalences-wide-function-class</a> <a id="2312" class="Symbol">:</a>
    <a id="2318" href="orthogonal-factorization-systems.function-classes.html#2788" class="Function">has-equivalences-function-class</a> <a id="2350" href="orthogonal-factorization-systems.wide-function-classes.html#2033" class="Function">function-class-wide-function-class</a>
  <a id="2387" href="orthogonal-factorization-systems.wide-function-classes.html#2275" class="Function">has-equivalences-wide-function-class</a> <a id="2424" class="Symbol">=</a>
    <a id="2430" href="orthogonal-factorization-systems.wide-function-classes.html#1416" class="Function">has-equivalences-is-wide-function-class</a>
      <a id="2476" class="Symbol">(</a> <a id="2478" href="orthogonal-factorization-systems.wide-function-classes.html#2033" class="Function">function-class-wide-function-class</a><a id="2512" class="Symbol">)</a>
      <a id="2520" class="Symbol">(</a> <a id="2522" href="orthogonal-factorization-systems.wide-function-classes.html#2142" class="Function">is-wide-wide-function-class</a><a id="2549" class="Symbol">)</a>

  <a id="2554" href="orthogonal-factorization-systems.wide-function-classes.html#2554" class="Function">is-closed-under-composition-wide-function-class</a> <a id="2602" class="Symbol">:</a>
    <a id="2608" href="orthogonal-factorization-systems.function-classes.html#3666" class="Function">is-closed-under-composition-function-class</a>
      <a id="2657" class="Symbol">(</a> <a id="2659" href="orthogonal-factorization-systems.wide-function-classes.html#2033" class="Function">function-class-wide-function-class</a><a id="2693" class="Symbol">)</a>
  <a id="2697" href="orthogonal-factorization-systems.wide-function-classes.html#2554" class="Function">is-closed-under-composition-wide-function-class</a> <a id="2745" class="Symbol">=</a>
    <a id="2751" href="orthogonal-factorization-systems.wide-function-classes.html#1572" class="Function">is-closed-under-composition-is-wide-function-class</a>
      <a id="2808" class="Symbol">(</a> <a id="2810" href="orthogonal-factorization-systems.wide-function-classes.html#2033" class="Function">function-class-wide-function-class</a><a id="2844" class="Symbol">)</a>
      <a id="2852" class="Symbol">(</a> <a id="2854" href="orthogonal-factorization-systems.wide-function-classes.html#2142" class="Function">is-wide-wide-function-class</a><a id="2881" class="Symbol">)</a>
</pre>