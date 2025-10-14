# Literals

<pre class="Agda"><a id="21" class="Keyword">module</a> <a id="28" href="reflection.literals.html" class="Module">reflection.literals</a> <a id="48" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="104" class="Keyword">open</a> <a id="109" class="Keyword">import</a> <a id="116" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="primitives.characters.html" class="Module">primitives.characters</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="primitives.floats.html" class="Module">primitives.floats</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="primitives.machine-integers.html" class="Module">primitives.machine-integers</a>
<a id="302" class="Keyword">open</a> <a id="307" class="Keyword">import</a> <a id="314" href="primitives.strings.html" class="Module">primitives.strings</a>

<a id="334" class="Keyword">open</a> <a id="339" class="Keyword">import</a> <a id="346" href="reflection.metavariables.html" class="Module">reflection.metavariables</a>
<a id="371" class="Keyword">open</a> <a id="376" class="Keyword">import</a> <a id="383" href="reflection.names.html" class="Module">reflection.names</a>
</pre>
</details>

## Idea

The `Literal-Agda` type represents literals in Agda.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definition

<pre class="Agda"><a id="586" class="Keyword">data</a> <a id="Literal-Agda"></a><a id="591" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a> <a id="604" class="Symbol">:</a> <a id="606" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="609" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="615" class="Keyword">where</a>
  <a id="Literal-Agda.nat-Literal-Agda"></a><a id="623" href="reflection.literals.html#623" class="InductiveConstructor">nat-Literal-Agda</a> <a id="640" class="Symbol">:</a> <a id="642" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="644" class="Symbol">→</a> <a id="646" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a>
  <a id="Literal-Agda.word64-Literal-Agda"></a><a id="661" href="reflection.literals.html#661" class="InductiveConstructor">word64-Literal-Agda</a> <a id="681" class="Symbol">:</a> <a id="683" href="primitives.machine-integers.html#419" class="Postulate">Word64</a> <a id="690" class="Symbol">→</a> <a id="692" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a>
  <a id="Literal-Agda.float-Literal-Agda"></a><a id="707" href="reflection.literals.html#707" class="InductiveConstructor">float-Literal-Agda</a> <a id="726" class="Symbol">:</a> <a id="728" href="primitives.floats.html#558" class="Postulate">Float</a> <a id="734" class="Symbol">→</a> <a id="736" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a>
  <a id="Literal-Agda.char-Literal-Agda"></a><a id="751" href="reflection.literals.html#751" class="InductiveConstructor">char-Literal-Agda</a> <a id="769" class="Symbol">:</a> <a id="771" href="primitives.characters.html#448" class="Postulate">Char</a> <a id="776" class="Symbol">→</a> <a id="778" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a>
  <a id="Literal-Agda.string-Literal-Agda"></a><a id="793" href="reflection.literals.html#793" class="InductiveConstructor">string-Literal-Agda</a> <a id="813" class="Symbol">:</a> <a id="815" href="primitives.strings.html#581" class="Postulate">String</a> <a id="822" class="Symbol">→</a> <a id="824" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a>
  <a id="Literal-Agda.quoted-name-Literal-Agda"></a><a id="839" href="reflection.literals.html#839" class="InductiveConstructor">quoted-name-Literal-Agda</a> <a id="864" class="Symbol">:</a> <a id="866" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="876" class="Symbol">→</a> <a id="878" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a>
  <a id="Literal-Agda.metavariable-Literal-Agda"></a><a id="893" href="reflection.literals.html#893" class="InductiveConstructor">metavariable-Literal-Agda</a> <a id="919" class="Symbol">:</a> <a id="921" href="reflection.metavariables.html#459" class="Postulate">Metavariable-Agda</a> <a id="939" class="Symbol">→</a> <a id="941" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a>
</pre>
## Bindings

<pre class="Agda"><a id="980" class="Symbol">{-#</a> <a id="984" class="Keyword">BUILTIN</a> <a id="992" class="Keyword">AGDALITERAL</a> <a id="1004" href="reflection.literals.html#591" class="Datatype">Literal-Agda</a> <a id="1017" class="Symbol">#-}</a>
<a id="1021" class="Symbol">{-#</a> <a id="1025" class="Keyword">BUILTIN</a> <a id="1033" class="Keyword">AGDALITNAT</a> <a id="1044" href="reflection.literals.html#623" class="InductiveConstructor">nat-Literal-Agda</a> <a id="1061" class="Symbol">#-}</a>
<a id="1065" class="Symbol">{-#</a> <a id="1069" class="Keyword">BUILTIN</a> <a id="1077" class="Keyword">AGDALITWORD64</a> <a id="1091" href="reflection.literals.html#661" class="InductiveConstructor">word64-Literal-Agda</a> <a id="1111" class="Symbol">#-}</a>
<a id="1115" class="Symbol">{-#</a> <a id="1119" class="Keyword">BUILTIN</a> <a id="1127" class="Keyword">AGDALITFLOAT</a> <a id="1140" href="reflection.literals.html#707" class="InductiveConstructor">float-Literal-Agda</a> <a id="1159" class="Symbol">#-}</a>
<a id="1163" class="Symbol">{-#</a> <a id="1167" class="Keyword">BUILTIN</a> <a id="1175" class="Keyword">AGDALITCHAR</a> <a id="1187" href="reflection.literals.html#751" class="InductiveConstructor">char-Literal-Agda</a> <a id="1205" class="Symbol">#-}</a>
<a id="1209" class="Symbol">{-#</a> <a id="1213" class="Keyword">BUILTIN</a> <a id="1221" class="Keyword">AGDALITSTRING</a> <a id="1235" href="reflection.literals.html#793" class="InductiveConstructor">string-Literal-Agda</a> <a id="1255" class="Symbol">#-}</a>
<a id="1259" class="Symbol">{-#</a> <a id="1263" class="Keyword">BUILTIN</a> <a id="1271" class="Keyword">AGDALITQNAME</a> <a id="1284" href="reflection.literals.html#839" class="InductiveConstructor">quoted-name-Literal-Agda</a> <a id="1309" class="Symbol">#-}</a>
<a id="1313" class="Symbol">{-#</a> <a id="1317" class="Keyword">BUILTIN</a> <a id="1325" class="Keyword">AGDALITMETA</a> <a id="1337" href="reflection.literals.html#893" class="InductiveConstructor">metavariable-Literal-Agda</a> <a id="1363" class="Symbol">#-}</a>
</pre>