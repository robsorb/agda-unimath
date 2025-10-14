# Terms

<pre class="Agda"><a id="18" class="Keyword">module</a> <a id="25" href="reflection.terms.html" class="Module">reflection.terms</a> <a id="42" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="98" class="Keyword">open</a> <a id="103" class="Keyword">import</a> <a id="110" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="lists.lists.html" class="Module">lists.lists</a>

<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="primitives.strings.html" class="Module">primitives.strings</a>

<a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="reflection.abstractions.html" class="Module">reflection.abstractions</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="reflection.arguments.html" class="Module">reflection.arguments</a>
<a id="365" class="Keyword">open</a> <a id="370" class="Keyword">import</a> <a id="377" href="reflection.literals.html" class="Module">reflection.literals</a>
<a id="397" class="Keyword">open</a> <a id="402" class="Keyword">import</a> <a id="409" href="reflection.metavariables.html" class="Module">reflection.metavariables</a>
<a id="434" class="Keyword">open</a> <a id="439" class="Keyword">import</a> <a id="446" href="reflection.names.html" class="Module">reflection.names</a>
</pre>
</details>

## Idea

In this module we represent the terms of agda by an inductive definition of the
type `Term-Agda`. See the comments for details on the constructors.

We can obtain a `Term-Agda` from an agda term through the keyword `quoteTerm`.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definition

<pre class="Agda"><a id="824" class="Keyword">data</a> <a id="Term-Agda"></a><a id="829" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="839" class="Symbol">:</a> <a id="841" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="844" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="850" class="Keyword">data</a> <a id="Sort-Agda"></a><a id="855" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a> <a id="865" class="Symbol">:</a> <a id="867" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="870" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="876" class="Keyword">data</a> <a id="Pattern-Agda"></a><a id="881" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a> <a id="894" class="Symbol">:</a> <a id="896" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="899" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="905" class="Keyword">data</a> <a id="Clause-Agda"></a><a id="910" href="reflection.terms.html#910" class="Datatype">Clause-Agda</a> <a id="922" class="Symbol">:</a> <a id="924" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="927" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="Telescope-Agda"></a><a id="933" href="reflection.terms.html#933" class="Function">Telescope-Agda</a> <a id="948" class="Symbol">=</a> <a id="950" href="lists.lists.html#1328" class="Datatype">list</a> <a id="955" class="Symbol">(</a><a id="956" href="primitives.strings.html#581" class="Postulate">String</a> <a id="963" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="965" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="979" href="reflection.terms.html#829" class="Datatype">Term-Agda</a><a id="988" class="Symbol">)</a>

<a id="991" class="Keyword">data</a> <a id="996" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="1006" class="Keyword">where</a>
  <a id="1014" class="Comment">-- Variables, where the natural number is a de Bruijn index</a>
  <a id="Term-Agda.variable-Term-Agda"></a><a id="1076" href="reflection.terms.html#1076" class="InductiveConstructor">variable-Term-Agda</a> <a id="1095" class="Symbol">:</a> <a id="1097" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1099" class="Symbol">→</a> <a id="1101" href="lists.lists.html#1328" class="Datatype">list</a> <a id="1106" class="Symbol">(</a><a id="1107" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="1121" href="reflection.terms.html#829" class="Datatype">Term-Agda</a><a id="1130" class="Symbol">)</a> <a id="1132" class="Symbol">→</a> <a id="1134" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="1146" class="Comment">-- An application of a constructor or definition</a>
  <a id="Term-Agda.constructor-Term-Agda"></a><a id="1197" href="reflection.terms.html#1197" class="InductiveConstructor">constructor-Term-Agda</a> <a id="1219" class="Symbol">:</a> <a id="1221" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="1231" class="Symbol">→</a> <a id="1233" href="lists.lists.html#1328" class="Datatype">list</a> <a id="1238" class="Symbol">(</a><a id="1239" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="1253" href="reflection.terms.html#829" class="Datatype">Term-Agda</a><a id="1262" class="Symbol">)</a> <a id="1264" class="Symbol">→</a> <a id="1266" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="Term-Agda.definition-Term-Agda"></a><a id="1278" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="1299" class="Symbol">:</a> <a id="1301" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="1311" class="Symbol">→</a> <a id="1313" href="lists.lists.html#1328" class="Datatype">list</a> <a id="1318" class="Symbol">(</a><a id="1319" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="1333" href="reflection.terms.html#829" class="Datatype">Term-Agda</a><a id="1342" class="Symbol">)</a> <a id="1344" class="Symbol">→</a> <a id="1346" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="1358" class="Comment">-- A lambda abstraction</a>
  <a id="Term-Agda.lambda-Term-Agda"></a><a id="1384" href="reflection.terms.html#1384" class="InductiveConstructor">lambda-Term-Agda</a> <a id="1401" class="Symbol">:</a>
    <a id="1407" href="reflection.arguments.html#863" class="Datatype">Visibility-Argument-Agda</a> <a id="1432" class="Symbol">→</a> <a id="1434" href="reflection.abstractions.html#299" class="Datatype">Abstraction-Agda</a> <a id="1451" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="1461" class="Symbol">→</a> <a id="1463" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="Term-Agda.pattern-lambda-Term-Agda"></a><a id="1475" href="reflection.terms.html#1475" class="InductiveConstructor">pattern-lambda-Term-Agda</a> <a id="1500" class="Symbol">:</a>
    <a id="1506" href="lists.lists.html#1328" class="Datatype">list</a> <a id="1511" href="reflection.terms.html#910" class="Datatype">Clause-Agda</a> <a id="1523" class="Symbol">→</a> <a id="1525" href="lists.lists.html#1328" class="Datatype">list</a> <a id="1530" class="Symbol">(</a><a id="1531" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="1545" href="reflection.terms.html#829" class="Datatype">Term-Agda</a><a id="1554" class="Symbol">)</a> <a id="1556" class="Symbol">→</a> <a id="1558" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="1570" class="Comment">-- A Pi term</a>
  <a id="Term-Agda.dependent-product-Term-Agda"></a><a id="1585" href="reflection.terms.html#1585" class="InductiveConstructor">dependent-product-Term-Agda</a> <a id="1613" class="Symbol">:</a>
    <a id="1619" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="1633" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="1643" class="Symbol">→</a> <a id="1645" href="reflection.abstractions.html#299" class="Datatype">Abstraction-Agda</a> <a id="1662" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="1672" class="Symbol">→</a> <a id="1674" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="1686" class="Comment">-- A sort, also called a universe</a>
  <a id="Term-Agda.sort-Term-Agda"></a><a id="1722" href="reflection.terms.html#1722" class="InductiveConstructor">sort-Term-Agda</a> <a id="1737" class="Symbol">:</a> <a id="1739" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a> <a id="1749" class="Symbol">→</a> <a id="1751" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="1763" class="Comment">-- A literal, e.g. `3`</a>
  <a id="Term-Agda.literal-Term-Agda"></a><a id="1788" href="reflection.terms.html#1788" class="InductiveConstructor">literal-Term-Agda</a> <a id="1806" class="Symbol">:</a> <a id="1808" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a> <a id="1821" class="Symbol">→</a> <a id="1823" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="1835" class="Comment">-- A metavariable</a>
  <a id="Term-Agda.metavariable-Term-Agda"></a><a id="1855" href="reflection.terms.html#1855" class="InductiveConstructor">metavariable-Term-Agda</a> <a id="1878" class="Symbol">:</a>
    <a id="1884" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="1902" class="Symbol">→</a> <a id="1904" href="lists.lists.html#1328" class="Datatype">list</a> <a id="1909" class="Symbol">(</a><a id="1910" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="1924" href="reflection.terms.html#829" class="Datatype">Term-Agda</a><a id="1933" class="Symbol">)</a> <a id="1935" class="Symbol">→</a> <a id="1937" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>
  <a id="1949" class="Comment">-- A hole</a>
  <a id="Term-Agda.unknown-Term-Agda"></a><a id="1961" href="reflection.terms.html#1961" class="InductiveConstructor">unknown-Term-Agda</a> <a id="1979" class="Symbol">:</a> <a id="1981" href="reflection.terms.html#829" class="Datatype">Term-Agda</a>

<a id="1992" class="Keyword">data</a> <a id="1997" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a> <a id="2007" class="Keyword">where</a>
  <a id="2015" class="Comment">-- A universe of a given (possibly neutral) level</a>
  <a id="Sort-Agda.universe-Sort-Agda"></a><a id="2067" href="reflection.terms.html#2067" class="InductiveConstructor">universe-Sort-Agda</a> <a id="2086" class="Symbol">:</a> <a id="2088" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="2098" class="Symbol">→</a> <a id="2100" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a>
  <a id="2112" class="Comment">-- A universe of a given concrete level</a>
  <a id="Sort-Agda.fixed-universe-Sort-Agda"></a><a id="2154" href="reflection.terms.html#2154" class="InductiveConstructor">fixed-universe-Sort-Agda</a> <a id="2179" class="Symbol">:</a> <a id="2181" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2183" class="Symbol">→</a> <a id="2185" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a>
  <a id="2197" class="Comment">-- A Prop of a given (possibly neutral) level</a>
  <a id="Sort-Agda.prop-Sort-Agda"></a><a id="2245" href="reflection.terms.html#2245" class="InductiveConstructor">prop-Sort-Agda</a> <a id="2260" class="Symbol">:</a> <a id="2262" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="2272" class="Symbol">→</a> <a id="2274" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a>
  <a id="2286" class="Comment">-- A Prop of a given concrete level</a>
  <a id="Sort-Agda.fixed-prop-Sort-Agda"></a><a id="2324" href="reflection.terms.html#2324" class="InductiveConstructor">fixed-prop-Sort-Agda</a> <a id="2345" class="Symbol">:</a> <a id="2347" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2349" class="Symbol">→</a> <a id="2351" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a>
  <a id="2363" class="Comment">-- UUωi of a given concrete level i.</a>
  <a id="Sort-Agda.fixed-large-universe-Sort-Agda"></a><a id="2402" href="reflection.terms.html#2402" class="InductiveConstructor">fixed-large-universe-Sort-Agda</a> <a id="2433" class="Symbol">:</a> <a id="2435" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2437" class="Symbol">→</a> <a id="2439" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a>
  <a id="2451" class="Comment">-- A hole</a>
  <a id="Sort-Agda.unknown-Sort-Agda"></a><a id="2463" href="reflection.terms.html#2463" class="InductiveConstructor">unknown-Sort-Agda</a> <a id="2481" class="Symbol">:</a> <a id="2483" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a>

<a id="2494" class="Keyword">data</a> <a id="2499" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a> <a id="2512" class="Keyword">where</a>
  <a id="Pattern-Agda.constructor-Term-Agda"></a><a id="2520" href="reflection.terms.html#2520" class="InductiveConstructor">constructor-Term-Agda</a> <a id="2542" class="Symbol">:</a>
    <a id="2548" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="2558" class="Symbol">→</a> <a id="2560" href="lists.lists.html#1328" class="Datatype">list</a> <a id="2565" class="Symbol">(</a><a id="2566" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="2580" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a><a id="2592" class="Symbol">)</a> <a id="2594" class="Symbol">→</a> <a id="2596" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a>
  <a id="Pattern-Agda.dot-Pattern-Agda"></a><a id="2611" href="reflection.terms.html#2611" class="InductiveConstructor">dot-Pattern-Agda</a> <a id="2628" class="Symbol">:</a> <a id="2630" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="2640" class="Symbol">→</a> <a id="2642" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a>
  <a id="Pattern-Agda.variable-Term-Agda"></a><a id="2657" href="reflection.terms.html#2657" class="InductiveConstructor">variable-Term-Agda</a> <a id="2676" class="Symbol">:</a> <a id="2678" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2680" class="Symbol">→</a> <a id="2682" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a>
  <a id="Pattern-Agda.literal-Term-Agda"></a><a id="2697" href="reflection.terms.html#2697" class="InductiveConstructor">literal-Term-Agda</a> <a id="2715" class="Symbol">:</a> <a id="2717" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a> <a id="2730" class="Symbol">→</a> <a id="2732" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a>
  <a id="Pattern-Agda.projection-Pattern-Agda"></a><a id="2747" href="reflection.terms.html#2747" class="InductiveConstructor">projection-Pattern-Agda</a> <a id="2771" class="Symbol">:</a> <a id="2773" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="2783" class="Symbol">→</a> <a id="2785" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a>
  <a id="2800" class="Comment">-- Absurd pattern with a de Bruijn index</a>
  <a id="Pattern-Agda.absurd-Pattern-Agda"></a><a id="2843" href="reflection.terms.html#2843" class="InductiveConstructor">absurd-Pattern-Agda</a> <a id="2863" class="Symbol">:</a> <a id="2865" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2867" class="Symbol">→</a> <a id="2869" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a>

<a id="2883" class="Comment">-- A clause-Clause-Agda on a pattern matching lambda</a>
<a id="2936" class="Keyword">data</a> <a id="2941" href="reflection.terms.html#910" class="Datatype">Clause-Agda</a> <a id="2953" class="Keyword">where</a>
  <a id="Clause-Agda.clause-Clause-Agda"></a><a id="2961" href="reflection.terms.html#2961" class="InductiveConstructor">clause-Clause-Agda</a> <a id="2980" class="Symbol">:</a>
    <a id="2986" href="reflection.terms.html#933" class="Function">Telescope-Agda</a> <a id="3001" class="Symbol">→</a> <a id="3003" href="lists.lists.html#1328" class="Datatype">list</a> <a id="3008" class="Symbol">(</a><a id="3009" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="3023" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a><a id="3035" class="Symbol">)</a> <a id="3037" class="Symbol">→</a> <a id="3039" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="3049" class="Symbol">→</a> <a id="3051" href="reflection.terms.html#910" class="Datatype">Clause-Agda</a>
  <a id="Clause-Agda.absurd-Clause-Agda"></a><a id="3065" href="reflection.terms.html#3065" class="InductiveConstructor">absurd-Clause-Agda</a> <a id="3084" class="Symbol">:</a>
    <a id="3090" href="reflection.terms.html#933" class="Function">Telescope-Agda</a> <a id="3105" class="Symbol">→</a> <a id="3107" href="lists.lists.html#1328" class="Datatype">list</a> <a id="3112" class="Symbol">(</a><a id="3113" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="3127" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a><a id="3139" class="Symbol">)</a> <a id="3141" class="Symbol">→</a> <a id="3143" href="reflection.terms.html#910" class="Datatype">Clause-Agda</a>
</pre>
## Bindings

<pre class="Agda"><a id="3181" class="Symbol">{-#</a> <a id="3185" class="Keyword">BUILTIN</a> <a id="3193" class="Keyword">AGDATERM</a> <a id="3202" href="reflection.terms.html#829" class="Datatype">Term-Agda</a> <a id="3212" class="Symbol">#-}</a>
<a id="3216" class="Symbol">{-#</a> <a id="3220" class="Keyword">BUILTIN</a> <a id="3228" class="Keyword">AGDASORT</a> <a id="3237" href="reflection.terms.html#855" class="Datatype">Sort-Agda</a> <a id="3247" class="Symbol">#-}</a>
<a id="3251" class="Symbol">{-#</a> <a id="3255" class="Keyword">BUILTIN</a> <a id="3263" class="Keyword">AGDAPATTERN</a> <a id="3275" href="reflection.terms.html#881" class="Datatype">Pattern-Agda</a> <a id="3288" class="Symbol">#-}</a>
<a id="3292" class="Symbol">{-#</a> <a id="3296" class="Keyword">BUILTIN</a> <a id="3304" class="Keyword">AGDACLAUSE</a> <a id="3315" href="reflection.terms.html#910" class="Datatype">Clause-Agda</a> <a id="3327" class="Symbol">#-}</a>

<a id="3332" class="Symbol">{-#</a> <a id="3336" class="Keyword">BUILTIN</a> <a id="3344" class="Keyword">AGDATERMVAR</a> <a id="3356" href="reflection.terms.html#1076" class="InductiveConstructor">variable-Term-Agda</a> <a id="3375" class="Symbol">#-}</a>
<a id="3379" class="Symbol">{-#</a> <a id="3383" class="Keyword">BUILTIN</a> <a id="3391" class="Keyword">AGDATERMCON</a> <a id="3403" href="reflection.terms.html#1197" class="InductiveConstructor">constructor-Term-Agda</a> <a id="3425" class="Symbol">#-}</a>
<a id="3429" class="Symbol">{-#</a> <a id="3433" class="Keyword">BUILTIN</a> <a id="3441" class="Keyword">AGDATERMDEF</a> <a id="3453" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="3474" class="Symbol">#-}</a>
<a id="3478" class="Symbol">{-#</a> <a id="3482" class="Keyword">BUILTIN</a> <a id="3490" class="Keyword">AGDATERMMETA</a> <a id="3503" href="reflection.terms.html#1855" class="InductiveConstructor">metavariable-Term-Agda</a> <a id="3526" class="Symbol">#-}</a>
<a id="3530" class="Symbol">{-#</a> <a id="3534" class="Keyword">BUILTIN</a> <a id="3542" class="Keyword">AGDATERMLAM</a> <a id="3554" href="reflection.terms.html#1384" class="InductiveConstructor">lambda-Term-Agda</a> <a id="3571" class="Symbol">#-}</a>
<a id="3575" class="Symbol">{-#</a> <a id="3579" class="Keyword">BUILTIN</a> <a id="3587" class="Keyword">AGDATERMEXTLAM</a> <a id="3602" href="reflection.terms.html#1475" class="InductiveConstructor">pattern-lambda-Term-Agda</a> <a id="3627" class="Symbol">#-}</a>
<a id="3631" class="Symbol">{-#</a> <a id="3635" class="Keyword">BUILTIN</a> <a id="3643" class="Keyword">AGDATERMPI</a> <a id="3654" href="reflection.terms.html#1585" class="InductiveConstructor">dependent-product-Term-Agda</a> <a id="3682" class="Symbol">#-}</a>
<a id="3686" class="Symbol">{-#</a> <a id="3690" class="Keyword">BUILTIN</a> <a id="3698" class="Keyword">AGDATERMSORT</a> <a id="3711" href="reflection.terms.html#1722" class="InductiveConstructor">sort-Term-Agda</a> <a id="3726" class="Symbol">#-}</a>
<a id="3730" class="Symbol">{-#</a> <a id="3734" class="Keyword">BUILTIN</a> <a id="3742" class="Keyword">AGDATERMLIT</a> <a id="3754" href="reflection.terms.html#1788" class="InductiveConstructor">literal-Term-Agda</a> <a id="3772" class="Symbol">#-}</a>
<a id="3776" class="Symbol">{-#</a> <a id="3780" class="Keyword">BUILTIN</a> <a id="3788" class="Keyword">AGDATERMUNSUPPORTED</a> <a id="3808" href="reflection.terms.html#1961" class="InductiveConstructor">unknown-Term-Agda</a> <a id="3826" class="Symbol">#-}</a>

<a id="3831" class="Symbol">{-#</a> <a id="3835" class="Keyword">BUILTIN</a> <a id="3843" class="Keyword">AGDASORTSET</a> <a id="3855" href="reflection.terms.html#2067" class="InductiveConstructor">universe-Sort-Agda</a> <a id="3874" class="Symbol">#-}</a>
<a id="3878" class="Symbol">{-#</a> <a id="3882" class="Keyword">BUILTIN</a> <a id="3890" class="Keyword">AGDASORTLIT</a> <a id="3902" href="reflection.terms.html#2154" class="InductiveConstructor">fixed-universe-Sort-Agda</a> <a id="3927" class="Symbol">#-}</a>
<a id="3931" class="Symbol">{-#</a> <a id="3935" class="Keyword">BUILTIN</a> <a id="3943" class="Keyword">AGDASORTPROP</a> <a id="3956" href="reflection.terms.html#2245" class="InductiveConstructor">prop-Sort-Agda</a> <a id="3971" class="Symbol">#-}</a>
<a id="3975" class="Symbol">{-#</a> <a id="3979" class="Keyword">BUILTIN</a> <a id="3987" class="Keyword">AGDASORTPROPLIT</a> <a id="4003" href="reflection.terms.html#2324" class="InductiveConstructor">fixed-prop-Sort-Agda</a> <a id="4024" class="Symbol">#-}</a>
<a id="4028" class="Symbol">{-#</a> <a id="4032" class="Keyword">BUILTIN</a> <a id="4040" class="Keyword">AGDASORTINF</a> <a id="4052" href="reflection.terms.html#2402" class="InductiveConstructor">fixed-large-universe-Sort-Agda</a> <a id="4083" class="Symbol">#-}</a>
<a id="4087" class="Symbol">{-#</a> <a id="4091" class="Keyword">BUILTIN</a> <a id="4099" class="Keyword">AGDASORTUNSUPPORTED</a> <a id="4119" href="reflection.terms.html#2463" class="InductiveConstructor">unknown-Sort-Agda</a> <a id="4137" class="Symbol">#-}</a>

<a id="4142" class="Symbol">{-#</a> <a id="4146" class="Keyword">BUILTIN</a> <a id="4154" class="Keyword">AGDAPATCON</a> <a id="4165" href="reflection.terms.html#2520" class="InductiveConstructor">constructor-Term-Agda</a> <a id="4187" class="Symbol">#-}</a>
<a id="4191" class="Symbol">{-#</a> <a id="4195" class="Keyword">BUILTIN</a> <a id="4203" class="Keyword">AGDAPATDOT</a> <a id="4214" href="reflection.terms.html#2611" class="InductiveConstructor">dot-Pattern-Agda</a> <a id="4231" class="Symbol">#-}</a>
<a id="4235" class="Symbol">{-#</a> <a id="4239" class="Keyword">BUILTIN</a> <a id="4247" class="Keyword">AGDAPATVAR</a> <a id="4258" href="reflection.terms.html#2657" class="InductiveConstructor">variable-Term-Agda</a> <a id="4277" class="Symbol">#-}</a>
<a id="4281" class="Symbol">{-#</a> <a id="4285" class="Keyword">BUILTIN</a> <a id="4293" class="Keyword">AGDAPATLIT</a> <a id="4304" href="reflection.terms.html#2697" class="InductiveConstructor">literal-Term-Agda</a> <a id="4322" class="Symbol">#-}</a>
<a id="4326" class="Symbol">{-#</a> <a id="4330" class="Keyword">BUILTIN</a> <a id="4338" class="Keyword">AGDAPATPROJ</a> <a id="4350" href="reflection.terms.html#2747" class="InductiveConstructor">projection-Pattern-Agda</a> <a id="4374" class="Symbol">#-}</a>
<a id="4378" class="Symbol">{-#</a> <a id="4382" class="Keyword">BUILTIN</a> <a id="4390" class="Keyword">AGDAPATABSURD</a> <a id="4404" href="reflection.terms.html#2843" class="InductiveConstructor">absurd-Pattern-Agda</a> <a id="4424" class="Symbol">#-}</a>

<a id="4429" class="Symbol">{-#</a> <a id="4433" class="Keyword">BUILTIN</a> <a id="4441" class="Keyword">AGDACLAUSECLAUSE</a> <a id="4458" href="reflection.terms.html#2961" class="InductiveConstructor">clause-Clause-Agda</a> <a id="4477" class="Symbol">#-}</a>
<a id="4481" class="Symbol">{-#</a> <a id="4485" class="Keyword">BUILTIN</a> <a id="4493" class="Keyword">AGDACLAUSEABSURD</a> <a id="4510" href="reflection.terms.html#3065" class="InductiveConstructor">absurd-Clause-Agda</a> <a id="4529" class="Symbol">#-}</a>
</pre>
## Helpers

<pre class="Agda"><a id="replicate-hidden-Argument-Agda"></a><a id="4558" href="reflection.terms.html#4558" class="Function">replicate-hidden-Argument-Agda</a> <a id="4589" class="Symbol">:</a> <a id="4591" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="4593" class="Symbol">→</a> <a id="4595" href="lists.lists.html#1328" class="Datatype">list</a> <a id="4600" class="Symbol">(</a><a id="4601" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="4615" href="reflection.terms.html#829" class="Datatype">Term-Agda</a><a id="4624" class="Symbol">)</a>
<a id="4626" href="reflection.terms.html#4558" class="Function">replicate-hidden-Argument-Agda</a> <a id="4657" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="4664" class="Symbol">=</a>
  <a id="4668" href="lists.lists.html#1371" class="InductiveConstructor">nil</a>
<a id="4672" href="reflection.terms.html#4558" class="Function">replicate-hidden-Argument-Agda</a> <a id="4703" class="Symbol">(</a><a id="4704" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="4711" href="reflection.terms.html#4711" class="Bound">n</a><a id="4712" class="Symbol">)</a> <a id="4714" class="Symbol">=</a>
  <a id="4718" href="lists.lists.html#1386" class="InductiveConstructor">cons</a>
    <a id="4727" class="Symbol">(</a> <a id="4729" href="reflection.arguments.html#3244" class="InductiveConstructor">hidden-Argument-Agda</a> <a id="4750" class="Symbol">(</a><a id="4751" href="reflection.terms.html#1961" class="InductiveConstructor">unknown-Term-Agda</a><a id="4768" class="Symbol">))</a>
    <a id="4775" class="Symbol">(</a> <a id="4777" href="reflection.terms.html#4558" class="Function">replicate-hidden-Argument-Agda</a> <a id="4808" href="reflection.terms.html#4711" class="Bound">n</a><a id="4809" class="Symbol">)</a>
</pre>