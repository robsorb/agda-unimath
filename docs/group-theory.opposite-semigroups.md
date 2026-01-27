# The opposite of a semigroup

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="group-theory.opposite-semigroups.html" class="Module">group-theory.opposite-semigroups</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="group-theory.semigroups.html" class="Module">group-theory.semigroups</a>
</pre>
</details>

## Idea

The **opposite of a [semigroup](group-theory.semigroups.md)** `G` with
multiplication `μ` is a semigroup with the same underlying
[set](foundation-core.sets.md) as `G` and multiplication given by `x y ↦ μ y x`.

## Definition

<pre class="Agda"><a id="583" class="Keyword">module</a> <a id="590" href="group-theory.opposite-semigroups.html#590" class="Module">_</a>
  <a id="594" class="Symbol">{</a><a id="595" href="group-theory.opposite-semigroups.html#595" class="Bound">l</a> <a id="597" class="Symbol">:</a> <a id="599" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="604" class="Symbol">}</a> <a id="606" class="Symbol">(</a><a id="607" href="group-theory.opposite-semigroups.html#607" class="Bound">G</a> <a id="609" class="Symbol">:</a> <a id="611" href="group-theory.semigroups.html#878" class="Function">Semigroup</a> <a id="621" href="group-theory.opposite-semigroups.html#595" class="Bound">l</a><a id="622" class="Symbol">)</a>
  <a id="626" class="Keyword">where</a>

  <a id="635" href="group-theory.opposite-semigroups.html#635" class="Function">set-op-Semigroup</a> <a id="652" class="Symbol">:</a> <a id="654" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="658" href="group-theory.opposite-semigroups.html#595" class="Bound">l</a>
  <a id="662" href="group-theory.opposite-semigroups.html#635" class="Function">set-op-Semigroup</a> <a id="679" class="Symbol">=</a> <a id="681" href="group-theory.semigroups.html#1019" class="Function">set-Semigroup</a> <a id="695" href="group-theory.opposite-semigroups.html#607" class="Bound">G</a>

  <a id="700" href="group-theory.opposite-semigroups.html#700" class="Function">type-op-Semigroup</a> <a id="718" class="Symbol">:</a> <a id="720" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="723" href="group-theory.opposite-semigroups.html#595" class="Bound">l</a>
  <a id="727" href="group-theory.opposite-semigroups.html#700" class="Function">type-op-Semigroup</a> <a id="745" class="Symbol">=</a> <a id="747" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="756" href="group-theory.opposite-semigroups.html#635" class="Function">set-op-Semigroup</a>

  <a id="776" href="group-theory.opposite-semigroups.html#776" class="Function">mul-op-Semigroup</a> <a id="793" class="Symbol">:</a> <a id="795" href="group-theory.opposite-semigroups.html#700" class="Function">type-op-Semigroup</a> <a id="813" class="Symbol">→</a> <a id="815" href="group-theory.opposite-semigroups.html#700" class="Function">type-op-Semigroup</a> <a id="833" class="Symbol">→</a> <a id="835" href="group-theory.opposite-semigroups.html#700" class="Function">type-op-Semigroup</a>
  <a id="855" href="group-theory.opposite-semigroups.html#776" class="Function">mul-op-Semigroup</a> <a id="872" href="group-theory.opposite-semigroups.html#872" class="Bound">x</a> <a id="874" href="group-theory.opposite-semigroups.html#874" class="Bound">y</a> <a id="876" class="Symbol">=</a> <a id="878" href="group-theory.semigroups.html#1350" class="Function">mul-Semigroup</a> <a id="892" href="group-theory.opposite-semigroups.html#607" class="Bound">G</a> <a id="894" href="group-theory.opposite-semigroups.html#874" class="Bound">y</a> <a id="896" href="group-theory.opposite-semigroups.html#872" class="Bound">x</a>

  <a id="901" href="group-theory.opposite-semigroups.html#901" class="Function">associative-mul-op-Semigroup</a> <a id="930" class="Symbol">:</a>
    <a id="936" class="Symbol">(</a><a id="937" href="group-theory.opposite-semigroups.html#937" class="Bound">x</a> <a id="939" href="group-theory.opposite-semigroups.html#939" class="Bound">y</a> <a id="941" href="group-theory.opposite-semigroups.html#941" class="Bound">z</a> <a id="943" class="Symbol">:</a> <a id="945" href="group-theory.opposite-semigroups.html#700" class="Function">type-op-Semigroup</a><a id="962" class="Symbol">)</a> <a id="964" class="Symbol">→</a>
    <a id="970" href="group-theory.semigroups.html#1350" class="Function">mul-Semigroup</a> <a id="984" href="group-theory.opposite-semigroups.html#607" class="Bound">G</a> <a id="986" href="group-theory.opposite-semigroups.html#941" class="Bound">z</a> <a id="988" class="Symbol">(</a><a id="989" href="group-theory.semigroups.html#1350" class="Function">mul-Semigroup</a> <a id="1003" href="group-theory.opposite-semigroups.html#607" class="Bound">G</a> <a id="1005" href="group-theory.opposite-semigroups.html#939" class="Bound">y</a> <a id="1007" href="group-theory.opposite-semigroups.html#937" class="Bound">x</a><a id="1008" class="Symbol">)</a> <a id="1010" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="1016" href="group-theory.semigroups.html#1350" class="Function">mul-Semigroup</a> <a id="1030" href="group-theory.opposite-semigroups.html#607" class="Bound">G</a> <a id="1032" class="Symbol">(</a><a id="1033" href="group-theory.semigroups.html#1350" class="Function">mul-Semigroup</a> <a id="1047" href="group-theory.opposite-semigroups.html#607" class="Bound">G</a> <a id="1049" href="group-theory.opposite-semigroups.html#941" class="Bound">z</a> <a id="1051" href="group-theory.opposite-semigroups.html#939" class="Bound">y</a><a id="1052" class="Symbol">)</a> <a id="1054" href="group-theory.opposite-semigroups.html#937" class="Bound">x</a>
  <a id="1058" href="group-theory.opposite-semigroups.html#901" class="Function">associative-mul-op-Semigroup</a> <a id="1087" href="group-theory.opposite-semigroups.html#1087" class="Bound">x</a> <a id="1089" href="group-theory.opposite-semigroups.html#1089" class="Bound">y</a> <a id="1091" href="group-theory.opposite-semigroups.html#1091" class="Bound">z</a> <a id="1093" class="Symbol">=</a> <a id="1095" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="1099" class="Symbol">(</a><a id="1100" href="group-theory.semigroups.html#1752" class="Function">associative-mul-Semigroup</a> <a id="1126" href="group-theory.opposite-semigroups.html#607" class="Bound">G</a> <a id="1128" href="group-theory.opposite-semigroups.html#1091" class="Bound">z</a> <a id="1130" href="group-theory.opposite-semigroups.html#1089" class="Bound">y</a> <a id="1132" href="group-theory.opposite-semigroups.html#1087" class="Bound">x</a><a id="1133" class="Symbol">)</a>

  <a id="1138" href="group-theory.opposite-semigroups.html#1138" class="Function">op-Semigroup</a> <a id="1151" class="Symbol">:</a> <a id="1153" href="group-theory.semigroups.html#878" class="Function">Semigroup</a> <a id="1163" href="group-theory.opposite-semigroups.html#595" class="Bound">l</a>
  <a id="1167" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1171" href="group-theory.opposite-semigroups.html#1138" class="Function">op-Semigroup</a> <a id="1184" class="Symbol">=</a> <a id="1186" href="group-theory.opposite-semigroups.html#635" class="Function">set-op-Semigroup</a>
  <a id="1205" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1209" class="Symbol">(</a><a id="1210" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1214" href="group-theory.opposite-semigroups.html#1138" class="Function">op-Semigroup</a><a id="1226" class="Symbol">)</a> <a id="1228" class="Symbol">=</a> <a id="1230" href="group-theory.opposite-semigroups.html#776" class="Function">mul-op-Semigroup</a>
  <a id="1249" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1253" class="Symbol">(</a><a id="1254" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1258" href="group-theory.opposite-semigroups.html#1138" class="Function">op-Semigroup</a><a id="1270" class="Symbol">)</a> <a id="1272" class="Symbol">=</a> <a id="1274" href="group-theory.opposite-semigroups.html#901" class="Function">associative-mul-op-Semigroup</a>
</pre>