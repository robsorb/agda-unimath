# Metavariables

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="reflection.metavariables.html" class="Module">reflection.metavariables</a> <a id="58" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="114" class="Keyword">open</a> <a id="119" class="Keyword">import</a> <a id="126" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="lists.lists.html" class="Module">lists.lists</a>

<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="primitives.strings.html" class="Module">primitives.strings</a>
</pre>
</details>

## Idea

The `Metavariable-Agda` type represents metavariables in Agda.

## Definition

<pre class="Agda"><a id="447" class="Keyword">postulate</a>
  <a id="Metavariable-Agda"></a><a id="459" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="477" class="Symbol">:</a> <a id="479" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="482" href="Agda.Primitive.html#915" class="Primitive">lzero</a>

<a id="489" class="Symbol">{-#</a> <a id="493" class="Keyword">BUILTIN</a> <a id="501" class="Keyword">AGDAMETA</a> <a id="510" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="528" class="Symbol">#-}</a>

<a id="533" class="Keyword">primitive</a>
  <a id="primMetaEquality"></a><a id="545" href="reflection.metavariables.html#545" class="Primitive">primMetaEquality</a> <a id="562" class="Symbol">:</a>
    <a id="568" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="586" class="Symbol">→</a> <a id="588" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="606" class="Symbol">→</a> <a id="608" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primMetaLess"></a><a id="615" href="reflection.metavariables.html#615" class="Primitive">primMetaLess</a> <a id="628" class="Symbol">:</a>
    <a id="634" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="652" class="Symbol">→</a> <a id="654" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="672" class="Symbol">→</a> <a id="674" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primShowMeta"></a><a id="681" href="reflection.metavariables.html#681" class="Primitive">primShowMeta</a> <a id="694" class="Symbol">:</a>
    <a id="700" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="718" class="Symbol">→</a> <a id="720" href="primitives.strings.html#581" class="Postulate">String</a>
  <a id="primMetaToNat"></a><a id="729" href="reflection.metavariables.html#729" class="Primitive">primMetaToNat</a> <a id="743" class="Symbol">:</a>
    <a id="749" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="767" class="Symbol">→</a> <a id="769" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
  <a id="primMetaToNatInjective"></a><a id="773" href="reflection.metavariables.html#773" class="Primitive">primMetaToNatInjective</a> <a id="796" class="Symbol">:</a>
    <a id="802" class="Symbol">(</a><a id="803" href="reflection.metavariables.html#803" class="Bound">a</a> <a id="805" href="reflection.metavariables.html#805" class="Bound">b</a> <a id="807" class="Symbol">:</a> <a id="809" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a><a id="826" class="Symbol">)</a> <a id="828" class="Symbol">→</a> <a id="830" href="reflection.metavariables.html#729" class="Primitive">primMetaToNat</a> <a id="844" href="reflection.metavariables.html#803" class="Bound">a</a> <a id="846" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="848" href="reflection.metavariables.html#729" class="Primitive">primMetaToNat</a> <a id="862" href="reflection.metavariables.html#805" class="Bound">b</a> <a id="864" class="Symbol">→</a> <a id="866" href="reflection.metavariables.html#803" class="Bound">a</a> <a id="868" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="870" href="reflection.metavariables.html#805" class="Bound">b</a>

<a id="873" class="Keyword">data</a> <a id="Blocker-Agda"></a><a id="878" href="reflection.metavariables.html#878" class="Datatype">Blocker-Agda</a> <a id="891" class="Symbol">:</a> <a id="893" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="896" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="902" class="Keyword">where</a>
  <a id="Blocker-Agda.any-Blocker-Agda"></a><a id="910" href="reflection.metavariables.html#910" class="InductiveConstructor">any-Blocker-Agda</a> <a id="927" class="Symbol">:</a> <a id="929" href="lists.lists.html#1328" class="Datatype">list</a> <a id="934" href="reflection.metavariables.html#878" class="Datatype">Blocker-Agda</a> <a id="947" class="Symbol">→</a> <a id="949" href="reflection.metavariables.html#878" class="Datatype">Blocker-Agda</a>
  <a id="Blocker-Agda.all-Blocker-Agda"></a><a id="964" href="reflection.metavariables.html#964" class="InductiveConstructor">all-Blocker-Agda</a> <a id="981" class="Symbol">:</a> <a id="983" href="lists.lists.html#1328" class="Datatype">list</a> <a id="988" href="reflection.metavariables.html#878" class="Datatype">Blocker-Agda</a> <a id="1001" class="Symbol">→</a> <a id="1003" href="reflection.metavariables.html#878" class="Datatype">Blocker-Agda</a>
  <a id="Blocker-Agda.metavariable-Blocker-Agda"></a><a id="1018" href="reflection.metavariables.html#1018" class="InductiveConstructor">metavariable-Blocker-Agda</a> <a id="1044" class="Symbol">:</a> <a id="1046" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="1064" class="Symbol">→</a> <a id="1066" href="reflection.metavariables.html#878" class="Datatype">Blocker-Agda</a>

<a id="1080" class="Symbol">{-#</a> <a id="1084" class="Keyword">BUILTIN</a> <a id="1092" class="Keyword">AGDABLOCKER</a> <a id="1104" href="reflection.metavariables.html#878" class="Datatype">Blocker-Agda</a> <a id="1117" class="Symbol">#-}</a>
<a id="1121" class="Symbol">{-#</a> <a id="1125" class="Keyword">BUILTIN</a> <a id="1133" class="Keyword">AGDABLOCKERANY</a> <a id="1148" href="reflection.metavariables.html#910" class="InductiveConstructor">any-Blocker-Agda</a> <a id="1165" class="Symbol">#-}</a>
<a id="1169" class="Symbol">{-#</a> <a id="1173" class="Keyword">BUILTIN</a> <a id="1181" class="Keyword">AGDABLOCKERALL</a> <a id="1196" href="reflection.metavariables.html#964" class="InductiveConstructor">all-Blocker-Agda</a> <a id="1213" class="Symbol">#-}</a>
<a id="1217" class="Symbol">{-#</a> <a id="1221" class="Keyword">BUILTIN</a> <a id="1229" class="Keyword">AGDABLOCKERMETA</a> <a id="1245" href="reflection.metavariables.html#1018" class="InductiveConstructor">metavariable-Blocker-Agda</a> <a id="1271" class="Symbol">#-}</a>
</pre>