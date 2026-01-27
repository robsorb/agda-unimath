# Names

<pre class="Agda"><a id="18" class="Keyword">module</a> <a id="25" href="reflection.names.html" class="Module">reflection.names</a> <a id="42" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="98" class="Keyword">open</a> <a id="103" class="Keyword">import</a> <a id="110" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="130" class="Keyword">open</a> <a id="135" class="Keyword">import</a> <a id="142" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="primitives.machine-integers.html" class="Module">primitives.machine-integers</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="primitives.strings.html" class="Module">primitives.strings</a>
</pre>
</details>

## Idea

The `Name-Agda` type represents quoted names, i.e. they are an abstract
syntactic representation of terms. Agda provides primitive functions to
manipulate them, giving them an equality and ordering. A closed term can be
converted to a quoted name by means of the `quote` keyword, e.g. `quote bool`.

## Definition

<pre class="Agda"><a id="708" class="Keyword">postulate</a>
  <a id="Name-Agda"></a><a id="720" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="730" class="Symbol">:</a> <a id="732" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="735" href="Agda.Primitive.html#915" class="Primitive">lzero</a>

<a id="742" class="Symbol">{-#</a> <a id="746" class="Keyword">BUILTIN</a> <a id="754" class="Keyword">QNAME</a> <a id="760" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="770" class="Symbol">#-}</a>

<a id="775" class="Keyword">primitive</a>
  <a id="primQNameEquality"></a><a id="787" href="reflection.names.html#787" class="Primitive">primQNameEquality</a> <a id="805" class="Symbol">:</a> <a id="807" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="817" class="Symbol">→</a> <a id="819" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="829" class="Symbol">→</a> <a id="831" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primQNameLess"></a><a id="838" href="reflection.names.html#838" class="Primitive">primQNameLess</a> <a id="852" class="Symbol">:</a> <a id="854" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="864" class="Symbol">→</a> <a id="866" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="876" class="Symbol">→</a> <a id="878" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="primShowQName"></a><a id="885" href="reflection.names.html#885" class="Primitive">primShowQName</a> <a id="899" class="Symbol">:</a> <a id="901" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="911" class="Symbol">→</a> <a id="913" href="primitives.strings.html#581" class="Postulate">String</a>
  <a id="primQNameToWord64s"></a><a id="922" href="reflection.names.html#922" class="Primitive">primQNameToWord64s</a> <a id="941" class="Symbol">:</a> <a id="943" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="953" class="Symbol">→</a> <a id="955" href="primitives.machine-integers.html#419" class="Postulate">Word64</a> <a id="962" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="964" href="primitives.machine-integers.html#419" class="Postulate">Word64</a>
  <a id="primQNameToWord64sInjective"></a><a id="973" href="reflection.names.html#973" class="Primitive">primQNameToWord64sInjective</a> <a id="1001" class="Symbol">:</a>
    <a id="1007" class="Symbol">(</a><a id="1008" href="reflection.names.html#1008" class="Bound">a</a> <a id="1010" href="reflection.names.html#1010" class="Bound">b</a> <a id="1012" class="Symbol">:</a> <a id="1014" href="reflection.names.html#720" class="Postulate">Name-Agda</a><a id="1023" class="Symbol">)</a> <a id="1025" class="Symbol">→</a> <a id="1027" href="reflection.names.html#922" class="Primitive">primQNameToWord64s</a> <a id="1046" href="reflection.names.html#1008" class="Bound">a</a> <a id="1048" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1050" href="reflection.names.html#922" class="Primitive">primQNameToWord64s</a> <a id="1069" href="reflection.names.html#1010" class="Bound">b</a> <a id="1071" class="Symbol">→</a> <a id="1073" href="reflection.names.html#1008" class="Bound">a</a> <a id="1075" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1077" href="reflection.names.html#1010" class="Bound">b</a>
</pre>
## Examples

<pre class="Agda"><a id="1105" href="reflection.names.html#1105" class="Function">_</a> <a id="1107" class="Symbol">:</a> <a id="1109" href="reflection.names.html#838" class="Primitive">primQNameLess</a> <a id="1123" class="Symbol">(</a><a id="1124" class="Keyword">quote</a> <a id="1130" href="foundation.booleans.html#1556" class="Datatype">bool</a><a id="1134" class="Symbol">)</a> <a id="1136" class="Symbol">(</a><a id="1137" class="Keyword">quote</a> <a id="1143" href="foundation.unit-type.html#950" class="Record">unit</a><a id="1147" class="Symbol">)</a> <a id="1149" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1151" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a>
<a id="1156" class="Symbol">_</a> <a id="1158" class="Symbol">=</a> <a id="1160" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="1166" href="reflection.names.html#1166" class="Function">_</a> <a id="1168" class="Symbol">:</a> <a id="1170" href="reflection.names.html#885" class="Primitive">primShowQName</a> <a id="1184" class="Symbol">(</a><a id="1185" class="Keyword">quote</a> <a id="1191" href="foundation.booleans.html#1556" class="Datatype">bool</a><a id="1195" class="Symbol">)</a> <a id="1197" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1199" class="String">&quot;foundation.booleans.bool&quot;</a>
<a id="1226" class="Symbol">_</a> <a id="1228" class="Symbol">=</a> <a id="1230" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>