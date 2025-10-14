# Function wild monoids

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="structured-types.function-wild-monoids.html" class="Module">structured-types.function-wild-monoids</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="174" class="Keyword">open</a> <a id="179" class="Keyword">import</a> <a id="186" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="structured-types.dependent-products-wild-monoids.html" class="Module">structured-types.dependent-products-wild-monoids</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="structured-types.h-spaces.html" class="Module">structured-types.h-spaces</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="structured-types.wild-monoids.html" class="Module">structured-types.wild-monoids</a>
</pre>
</details>

## Idea

Given a [wild monoid](structured-types.wild-monoids.md) `M` and a type `I`, the
**function wild monoid** `M^I` consists of functions from `I` to the underlying
type of `M`. Every component of the structure is given pointwise.

## Definition

<pre class="Agda"><a id="674" class="Keyword">module</a> <a id="681" href="structured-types.function-wild-monoids.html#681" class="Module">_</a>
  <a id="685" class="Symbol">{</a><a id="686" href="structured-types.function-wild-monoids.html#686" class="Bound">l1</a> <a id="689" href="structured-types.function-wild-monoids.html#689" class="Bound">l2</a> <a id="692" class="Symbol">:</a> <a id="694" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="699" class="Symbol">}</a> <a id="701" class="Symbol">(</a><a id="702" href="structured-types.function-wild-monoids.html#702" class="Bound">I</a> <a id="704" class="Symbol">:</a> <a id="706" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="709" href="structured-types.function-wild-monoids.html#686" class="Bound">l1</a><a id="711" class="Symbol">)</a> <a id="713" class="Symbol">(</a><a id="714" href="structured-types.function-wild-monoids.html#714" class="Bound">M</a> <a id="716" class="Symbol">:</a> <a id="718" href="structured-types.wild-monoids.html#3571" class="Function">Wild-Monoid</a> <a id="730" href="structured-types.function-wild-monoids.html#689" class="Bound">l2</a><a id="732" class="Symbol">)</a>
  <a id="736" class="Keyword">where</a>

  <a id="745" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a> <a id="766" class="Symbol">:</a> <a id="768" href="structured-types.wild-monoids.html#3571" class="Function">Wild-Monoid</a> <a id="780" class="Symbol">(</a><a id="781" href="structured-types.function-wild-monoids.html#686" class="Bound">l1</a> <a id="784" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="786" href="structured-types.function-wild-monoids.html#689" class="Bound">l2</a><a id="788" class="Symbol">)</a>
  <a id="792" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a> <a id="813" class="Symbol">=</a> <a id="815" href="structured-types.dependent-products-wild-monoids.html#4299" class="Function">Π-Wild-Monoid</a> <a id="829" href="structured-types.function-wild-monoids.html#702" class="Bound">I</a> <a id="831" class="Symbol">(λ</a> <a id="834" href="structured-types.function-wild-monoids.html#834" class="Bound">_</a> <a id="836" class="Symbol">→</a> <a id="838" href="structured-types.function-wild-monoids.html#714" class="Bound">M</a><a id="839" class="Symbol">)</a>

  <a id="844" href="structured-types.function-wild-monoids.html#844" class="Function">h-space-function-Wild-Monoid</a> <a id="873" class="Symbol">:</a> <a id="875" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="883" class="Symbol">(</a><a id="884" href="structured-types.function-wild-monoids.html#686" class="Bound">l1</a> <a id="887" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="889" href="structured-types.function-wild-monoids.html#689" class="Bound">l2</a><a id="891" class="Symbol">)</a>
  <a id="895" href="structured-types.function-wild-monoids.html#844" class="Function">h-space-function-Wild-Monoid</a> <a id="924" class="Symbol">=</a>
      <a id="932" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a> <a id="952" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>

  <a id="976" href="structured-types.function-wild-monoids.html#976" class="Function">pointed-type-function-Wild-Monoid</a> <a id="1010" class="Symbol">:</a> <a id="1012" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1025" class="Symbol">(</a><a id="1026" href="structured-types.function-wild-monoids.html#686" class="Bound">l1</a> <a id="1029" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1031" href="structured-types.function-wild-monoids.html#689" class="Bound">l2</a><a id="1033" class="Symbol">)</a>
  <a id="1037" href="structured-types.function-wild-monoids.html#976" class="Function">pointed-type-function-Wild-Monoid</a> <a id="1071" class="Symbol">=</a>
    <a id="1077" href="structured-types.wild-monoids.html#3955" class="Function">pointed-type-Wild-Monoid</a> <a id="1102" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>

  <a id="1126" href="structured-types.function-wild-monoids.html#1126" class="Function">type-function-Wild-Monoid</a> <a id="1152" class="Symbol">:</a> <a id="1154" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1157" class="Symbol">(</a><a id="1158" href="structured-types.function-wild-monoids.html#686" class="Bound">l1</a> <a id="1161" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1163" href="structured-types.function-wild-monoids.html#689" class="Bound">l2</a><a id="1165" class="Symbol">)</a>
  <a id="1169" href="structured-types.function-wild-monoids.html#1126" class="Function">type-function-Wild-Monoid</a> <a id="1195" class="Symbol">=</a> <a id="1197" href="structured-types.wild-monoids.html#3781" class="Function">type-Wild-Monoid</a> <a id="1214" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>

  <a id="1238" href="structured-types.function-wild-monoids.html#1238" class="Function">unit-function-Wild-Monoid</a> <a id="1264" class="Symbol">:</a> <a id="1266" href="structured-types.function-wild-monoids.html#1126" class="Function">type-function-Wild-Monoid</a>
  <a id="1294" href="structured-types.function-wild-monoids.html#1238" class="Function">unit-function-Wild-Monoid</a> <a id="1320" class="Symbol">=</a> <a id="1322" href="structured-types.wild-monoids.html#3862" class="Function">unit-Wild-Monoid</a> <a id="1339" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>

  <a id="1363" href="structured-types.function-wild-monoids.html#1363" class="Function">mul-function-Wild-Monoid</a> <a id="1388" class="Symbol">:</a>
    <a id="1394" href="structured-types.function-wild-monoids.html#1126" class="Function">type-function-Wild-Monoid</a> <a id="1420" class="Symbol">→</a>
    <a id="1426" href="structured-types.function-wild-monoids.html#1126" class="Function">type-function-Wild-Monoid</a> <a id="1452" class="Symbol">→</a>
    <a id="1458" href="structured-types.function-wild-monoids.html#1126" class="Function">type-function-Wild-Monoid</a>
  <a id="1486" href="structured-types.function-wild-monoids.html#1363" class="Function">mul-function-Wild-Monoid</a> <a id="1511" class="Symbol">=</a> <a id="1513" href="structured-types.wild-monoids.html#4261" class="Function">mul-Wild-Monoid</a> <a id="1529" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>

  <a id="1553" href="structured-types.function-wild-monoids.html#1553" class="Function">left-unit-law-mul-function-Wild-Monoid</a> <a id="1592" class="Symbol">:</a>
    <a id="1598" class="Symbol">(</a> <a id="1600" href="structured-types.function-wild-monoids.html#1600" class="Bound">f</a> <a id="1602" class="Symbol">:</a> <a id="1604" href="structured-types.function-wild-monoids.html#1126" class="Function">type-function-Wild-Monoid</a><a id="1629" class="Symbol">)</a> <a id="1631" class="Symbol">→</a>
    <a id="1637" class="Symbol">(</a> <a id="1639" href="structured-types.function-wild-monoids.html#1363" class="Function">mul-function-Wild-Monoid</a> <a id="1664" class="Symbol">(</a><a id="1665" href="structured-types.function-wild-monoids.html#1238" class="Function">unit-function-Wild-Monoid</a><a id="1690" class="Symbol">)</a> <a id="1692" href="structured-types.function-wild-monoids.html#1600" class="Bound">f</a><a id="1693" class="Symbol">)</a> <a id="1695" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1697" href="structured-types.function-wild-monoids.html#1600" class="Bound">f</a>
  <a id="1701" href="structured-types.function-wild-monoids.html#1553" class="Function">left-unit-law-mul-function-Wild-Monoid</a> <a id="1740" class="Symbol">=</a>
    <a id="1746" href="structured-types.wild-monoids.html#4699" class="Function">left-unit-law-mul-Wild-Monoid</a> <a id="1776" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>

  <a id="1800" href="structured-types.function-wild-monoids.html#1800" class="Function">right-unit-law-mul-function-Wild-Monoid</a> <a id="1840" class="Symbol">:</a>
    <a id="1846" class="Symbol">(</a> <a id="1848" href="structured-types.function-wild-monoids.html#1848" class="Bound">f</a> <a id="1850" class="Symbol">:</a> <a id="1852" href="structured-types.function-wild-monoids.html#1126" class="Function">type-function-Wild-Monoid</a><a id="1877" class="Symbol">)</a> <a id="1879" class="Symbol">→</a>
    <a id="1885" class="Symbol">(</a> <a id="1887" href="structured-types.function-wild-monoids.html#1363" class="Function">mul-function-Wild-Monoid</a> <a id="1912" href="structured-types.function-wild-monoids.html#1848" class="Bound">f</a> <a id="1914" class="Symbol">(</a><a id="1915" href="structured-types.function-wild-monoids.html#1238" class="Function">unit-function-Wild-Monoid</a><a id="1940" class="Symbol">))</a> <a id="1943" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1945" href="structured-types.function-wild-monoids.html#1848" class="Bound">f</a>
  <a id="1949" href="structured-types.function-wild-monoids.html#1800" class="Function">right-unit-law-mul-function-Wild-Monoid</a> <a id="1989" class="Symbol">=</a>
    <a id="1995" href="structured-types.wild-monoids.html#4886" class="Function">right-unit-law-mul-Wild-Monoid</a> <a id="2026" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>

  <a id="2050" href="structured-types.function-wild-monoids.html#2050" class="Function">associator-function-Wild-Monoid</a> <a id="2082" class="Symbol">:</a>
    <a id="2088" href="structured-types.wild-monoids.html#2198" class="Function">associator-H-Space</a> <a id="2107" href="structured-types.function-wild-monoids.html#844" class="Function">h-space-function-Wild-Monoid</a>
  <a id="2138" href="structured-types.function-wild-monoids.html#2050" class="Function">associator-function-Wild-Monoid</a> <a id="2170" class="Symbol">=</a> <a id="2172" href="structured-types.wild-monoids.html#5423" class="Function">associator-Wild-Monoid</a> <a id="2195" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>

  <a id="2219" href="structured-types.function-wild-monoids.html#2219" class="Function">unital-associator-function-Wild-Monoid</a> <a id="2258" class="Symbol">:</a>
    <a id="2264" href="structured-types.wild-monoids.html#3447" class="Function">unital-associator</a> <a id="2282" class="Symbol">(</a><a id="2283" href="structured-types.wild-monoids.html#3716" class="Function">h-space-Wild-Monoid</a> <a id="2303" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a><a id="2323" class="Symbol">)</a>
  <a id="2327" href="structured-types.function-wild-monoids.html#2219" class="Function">unital-associator-function-Wild-Monoid</a> <a id="2366" class="Symbol">=</a>
    <a id="2372" href="structured-types.wild-monoids.html#5306" class="Function">unital-associator-Wild-Monoid</a> <a id="2402" href="structured-types.function-wild-monoids.html#745" class="Function">function-Wild-Monoid</a>
</pre>