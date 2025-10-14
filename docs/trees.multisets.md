# Multisets

<pre class="Agda"><a id="22" class="Keyword">module</a> <a id="29" href="trees.multisets.html" class="Module">trees.multisets</a> <a id="45" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="101" class="Keyword">open</a> <a id="106" class="Keyword">import</a> <a id="113" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="trees.elementhood-relation-w-types.html" class="Module">trees.elementhood-relation-w-types</a>
<a id="305" class="Keyword">open</a> <a id="310" class="Keyword">import</a> <a id="317" href="trees.w-types.html" class="Module">trees.w-types</a>
</pre>
</details>

## Idea

The type of {{#concept "multisets" Agda=𝕍}} of
[universe level](foundation.universe-levels.md) `l` is the
[W-type](trees.w-types.md) of the universal family over the universe `UU l`.

## Definitions

### The type of small multisets

<pre class="Agda"><a id="𝕍"></a><a id="598" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="600" class="Symbol">:</a> <a id="602" class="Symbol">(</a><a id="603" href="trees.multisets.html#603" class="Bound">l</a> <a id="605" class="Symbol">:</a> <a id="607" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="612" class="Symbol">)</a> <a id="614" class="Symbol">→</a> <a id="616" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="619" class="Symbol">(</a><a id="620" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="625" href="trees.multisets.html#603" class="Bound">l</a><a id="626" class="Symbol">)</a>
<a id="628" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="630" href="trees.multisets.html#630" class="Bound">l</a> <a id="632" class="Symbol">=</a> <a id="634" href="trees.w-types.html#1681" class="Datatype">𝕎</a> <a id="636" class="Symbol">(</a><a id="637" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="640" href="trees.multisets.html#630" class="Bound">l</a><a id="641" class="Symbol">)</a> <a id="643" class="Symbol">(λ</a> <a id="646" href="trees.multisets.html#646" class="Bound">X</a> <a id="648" class="Symbol">→</a> <a id="650" href="trees.multisets.html#646" class="Bound">X</a><a id="651" class="Symbol">)</a>
</pre>
### The large type of all multisets

<pre class="Agda"><a id="703" class="Keyword">data</a>
  <a id="Large-𝕍"></a><a id="710" href="trees.multisets.html#710" class="Datatype">Large-𝕍</a> <a id="718" class="Symbol">:</a> <a id="720" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="726" class="Keyword">where</a>
  <a id="Large-𝕍.tree-Large-𝕍"></a><a id="734" href="trees.multisets.html#734" class="InductiveConstructor">tree-Large-𝕍</a> <a id="747" class="Symbol">:</a> <a id="749" class="Symbol">{</a><a id="750" href="trees.multisets.html#750" class="Bound">l</a> <a id="752" class="Symbol">:</a> <a id="754" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="759" class="Symbol">}</a> <a id="761" class="Symbol">(</a><a id="762" href="trees.multisets.html#762" class="Bound">X</a> <a id="764" class="Symbol">:</a> <a id="766" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="769" href="trees.multisets.html#750" class="Bound">l</a><a id="770" class="Symbol">)</a> <a id="772" class="Symbol">→</a> <a id="774" class="Symbol">(</a><a id="775" href="trees.multisets.html#762" class="Bound">X</a> <a id="777" class="Symbol">→</a> <a id="779" href="trees.multisets.html#710" class="Datatype">Large-𝕍</a><a id="786" class="Symbol">)</a> <a id="788" class="Symbol">→</a> <a id="790" href="trees.multisets.html#710" class="Datatype">Large-𝕍</a>
</pre>
### The elementhood relation on multisets

<pre class="Agda"><a id="854" class="Keyword">infix</a> <a id="860" class="Number">6</a> <a id="862" href="trees.multisets.html#875" class="Function Operator">_∈-𝕍_</a> <a id="868" href="trees.multisets.html#940" class="Function Operator">_∉-𝕍_</a>

<a id="_∈-𝕍_"></a><a id="875" href="trees.multisets.html#875" class="Function Operator">_∈-𝕍_</a> <a id="881" class="Symbol">:</a> <a id="883" class="Symbol">{</a><a id="884" href="trees.multisets.html#884" class="Bound">l</a> <a id="886" class="Symbol">:</a> <a id="888" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="893" class="Symbol">}</a> <a id="895" class="Symbol">→</a> <a id="897" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="899" href="trees.multisets.html#884" class="Bound">l</a> <a id="901" class="Symbol">→</a> <a id="903" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="905" href="trees.multisets.html#884" class="Bound">l</a> <a id="907" class="Symbol">→</a> <a id="909" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="912" class="Symbol">(</a><a id="913" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="918" href="trees.multisets.html#884" class="Bound">l</a><a id="919" class="Symbol">)</a>
<a id="921" href="trees.multisets.html#921" class="Bound">X</a> <a id="923" href="trees.multisets.html#875" class="Function Operator">∈-𝕍</a> <a id="927" href="trees.multisets.html#927" class="Bound">Y</a> <a id="929" class="Symbol">=</a> <a id="931" href="trees.multisets.html#921" class="Bound">X</a> <a id="933" href="trees.elementhood-relation-w-types.html#731" class="Function Operator">∈-𝕎</a> <a id="937" href="trees.multisets.html#927" class="Bound">Y</a>

<a id="_∉-𝕍_"></a><a id="940" href="trees.multisets.html#940" class="Function Operator">_∉-𝕍_</a> <a id="946" class="Symbol">:</a> <a id="948" class="Symbol">{</a><a id="949" href="trees.multisets.html#949" class="Bound">l</a> <a id="951" class="Symbol">:</a> <a id="953" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="958" class="Symbol">}</a> <a id="960" class="Symbol">→</a> <a id="962" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="964" href="trees.multisets.html#949" class="Bound">l</a> <a id="966" class="Symbol">→</a> <a id="968" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="970" href="trees.multisets.html#949" class="Bound">l</a> <a id="972" class="Symbol">→</a> <a id="974" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="977" class="Symbol">(</a><a id="978" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="983" href="trees.multisets.html#949" class="Bound">l</a><a id="984" class="Symbol">)</a>
<a id="986" href="trees.multisets.html#986" class="Bound">X</a> <a id="988" href="trees.multisets.html#940" class="Function Operator">∉-𝕍</a> <a id="992" href="trees.multisets.html#992" class="Bound">Y</a> <a id="994" class="Symbol">=</a> <a id="996" href="foundation-core.empty-types.html#972" class="Function">is-empty</a> <a id="1005" class="Symbol">(</a><a id="1006" href="trees.multisets.html#986" class="Bound">X</a> <a id="1008" href="trees.multisets.html#875" class="Function Operator">∈-𝕍</a> <a id="1012" href="trees.multisets.html#992" class="Bound">Y</a><a id="1013" class="Symbol">)</a>
</pre>
### Comprehension for multisets

<pre class="Agda"><a id="comprehension-𝕍"></a><a id="1061" href="trees.multisets.html#1061" class="Function">comprehension-𝕍</a> <a id="1077" class="Symbol">:</a>
  <a id="1081" class="Symbol">{</a><a id="1082" href="trees.multisets.html#1082" class="Bound">l</a> <a id="1084" class="Symbol">:</a> <a id="1086" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1091" class="Symbol">}</a> <a id="1093" class="Symbol">(</a><a id="1094" href="trees.multisets.html#1094" class="Bound">X</a> <a id="1096" class="Symbol">:</a> <a id="1098" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="1100" href="trees.multisets.html#1082" class="Bound">l</a><a id="1101" class="Symbol">)</a> <a id="1103" class="Symbol">(</a><a id="1104" href="trees.multisets.html#1104" class="Bound">P</a> <a id="1106" class="Symbol">:</a> <a id="1108" href="trees.w-types.html#1860" class="Function">shape-𝕎</a> <a id="1116" href="trees.multisets.html#1094" class="Bound">X</a> <a id="1118" class="Symbol">→</a> <a id="1120" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1123" href="trees.multisets.html#1082" class="Bound">l</a><a id="1124" class="Symbol">)</a> <a id="1126" class="Symbol">→</a> <a id="1128" href="trees.multisets.html#598" class="Function">𝕍</a> <a id="1130" href="trees.multisets.html#1082" class="Bound">l</a>
<a id="1132" href="trees.multisets.html#1061" class="Function">comprehension-𝕍</a> <a id="1148" href="trees.multisets.html#1148" class="Bound">X</a> <a id="1150" href="trees.multisets.html#1150" class="Bound">P</a> <a id="1152" class="Symbol">=</a>
  <a id="1156" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1163" class="Symbol">(</a><a id="1164" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1166" class="Symbol">(</a><a id="1167" href="trees.w-types.html#1860" class="Function">shape-𝕎</a> <a id="1175" href="trees.multisets.html#1148" class="Bound">X</a><a id="1176" class="Symbol">)</a> <a id="1178" href="trees.multisets.html#1150" class="Bound">P</a><a id="1179" class="Symbol">)</a> <a id="1181" class="Symbol">(</a><a id="1182" href="trees.w-types.html#1910" class="Function">component-𝕎</a> <a id="1194" href="trees.multisets.html#1148" class="Bound">X</a> <a id="1196" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1198" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a><a id="1201" class="Symbol">)</a>
</pre>