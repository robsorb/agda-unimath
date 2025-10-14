# Homomorphisms of ring extensions of the rational numbers

<pre class="Agda"><a id="69" class="Symbol">{-#</a> <a id="73" class="Keyword">OPTIONS</a> <a id="81" class="Pragma">--lossy-unification</a> <a id="101" class="Symbol">#-}</a>

<a id="106" class="Keyword">module</a> <a id="113" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html" class="Module">ring-theory.homomorphisms-ring-extensions-rational-numbers</a> <a id="172" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="ring-theory.homomorphisms-rings.html" class="Module">ring-theory.homomorphisms-rings</a>
<a id="312" class="Keyword">open</a> <a id="317" class="Keyword">import</a> <a id="324" href="ring-theory.ring-extensions-rational-numbers.html" class="Module">ring-theory.ring-extensions-rational-numbers</a>
</pre>
</details>

## Idea

{{#concept "Homomorphisms" Disambiguation="of ring extensions of ℚ" Agda=hom-Rational-Extension-Ring}}
of [rational extensions of ℚ](ring-theory.ring-extensions-rational-numbers.md)
are [homomorphisms](ring-theory.homomorphisms-rings.md) between their underlying
[rings](ring-theory.rings.md).

## Definitions

### Homorphisms of ring extensions of ℚ

<pre class="Agda"><a id="755" class="Keyword">module</a> <a id="762" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#762" class="Module">_</a>
  <a id="766" class="Symbol">{</a><a id="767" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#767" class="Bound">l1</a> <a id="770" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#770" class="Bound">l2</a> <a id="773" class="Symbol">:</a> <a id="775" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="780" class="Symbol">}</a>
  <a id="784" class="Symbol">(</a><a id="785" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#785" class="Bound">A</a> <a id="787" class="Symbol">:</a> <a id="789" href="ring-theory.ring-extensions-rational-numbers.html#3568" class="Function">Rational-Extension-Ring</a> <a id="813" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#767" class="Bound">l1</a><a id="815" class="Symbol">)</a>
  <a id="819" class="Symbol">(</a><a id="820" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#820" class="Bound">B</a> <a id="822" class="Symbol">:</a> <a id="824" href="ring-theory.ring-extensions-rational-numbers.html#3568" class="Function">Rational-Extension-Ring</a> <a id="848" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#770" class="Bound">l2</a><a id="850" class="Symbol">)</a>
  <a id="854" class="Keyword">where</a>

  <a id="863" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#863" class="Function">hom-Rational-Extension-Ring</a> <a id="891" class="Symbol">:</a> <a id="893" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="896" class="Symbol">(</a><a id="897" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#767" class="Bound">l1</a> <a id="900" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="902" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#770" class="Bound">l2</a><a id="904" class="Symbol">)</a>
  <a id="908" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#863" class="Function">hom-Rational-Extension-Ring</a> <a id="936" class="Symbol">=</a>
    <a id="942" href="ring-theory.homomorphisms-rings.html#3643" class="Function">hom-Ring</a>
      <a id="957" class="Symbol">(</a> <a id="959" href="ring-theory.ring-extensions-rational-numbers.html#3753" class="Function">ring-Rational-Extension-Ring</a> <a id="988" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#785" class="Bound">A</a><a id="989" class="Symbol">)</a>
      <a id="997" class="Symbol">(</a> <a id="999" href="ring-theory.ring-extensions-rational-numbers.html#3753" class="Function">ring-Rational-Extension-Ring</a> <a id="1028" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#820" class="Bound">B</a><a id="1029" class="Symbol">)</a>

  <a id="1034" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#1034" class="Function">map-hom-Rational-Extension-Ring</a> <a id="1066" class="Symbol">:</a>
    <a id="1072" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#863" class="Function">hom-Rational-Extension-Ring</a> <a id="1100" class="Symbol">→</a>
    <a id="1106" href="ring-theory.ring-extensions-rational-numbers.html#3833" class="Function">type-Rational-Extension-Ring</a> <a id="1135" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#785" class="Bound">A</a> <a id="1137" class="Symbol">→</a>
    <a id="1143" href="ring-theory.ring-extensions-rational-numbers.html#3833" class="Function">type-Rational-Extension-Ring</a> <a id="1172" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#820" class="Bound">B</a>
  <a id="1176" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#1034" class="Function">map-hom-Rational-Extension-Ring</a> <a id="1208" class="Symbol">=</a>
    <a id="1214" href="ring-theory.homomorphisms-rings.html#4297" class="Function">map-hom-Ring</a>
      <a id="1233" class="Symbol">(</a> <a id="1235" href="ring-theory.ring-extensions-rational-numbers.html#3753" class="Function">ring-Rational-Extension-Ring</a> <a id="1264" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#785" class="Bound">A</a><a id="1265" class="Symbol">)</a>
      <a id="1273" class="Symbol">(</a> <a id="1275" href="ring-theory.ring-extensions-rational-numbers.html#3753" class="Function">ring-Rational-Extension-Ring</a> <a id="1304" href="ring-theory.homomorphisms-ring-extensions-rational-numbers.html#820" class="Bound">B</a><a id="1305" class="Symbol">)</a>
</pre>