# Involutive types

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="structured-types.involutive-types.html" class="Module">structured-types.involutive-types</a> <a id="70" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="126" class="Keyword">open</a> <a id="131" class="Keyword">import</a> <a id="138" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
</pre>
</details>

## Idea

Involutive types are types equipped with a `ℤ/2`-action. In other words,
involutive types are type families over `2-Element-Type lzero`.

Similarly, an involutive structure on a type `X` consists of a type family `Y`
over `2-Element-Type lzero` equipped with an equivalence `X ≃ Y (Fin 2)`.

## Definitions

### Involutive types

<pre class="Agda"><a id="Involutive-Type"></a><a id="662" href="structured-types.involutive-types.html#662" class="Function">Involutive-Type</a> <a id="678" class="Symbol">:</a> <a id="680" class="Symbol">(</a><a id="681" href="structured-types.involutive-types.html#681" class="Bound">l</a> <a id="683" class="Symbol">:</a> <a id="685" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="690" class="Symbol">)</a> <a id="692" class="Symbol">→</a> <a id="694" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="697" class="Symbol">(</a><a id="698" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="703" href="structured-types.involutive-types.html#681" class="Bound">l</a><a id="704" class="Symbol">)</a>
<a id="706" href="structured-types.involutive-types.html#662" class="Function">Involutive-Type</a> <a id="722" href="structured-types.involutive-types.html#722" class="Bound">l</a> <a id="724" class="Symbol">=</a> <a id="726" href="univalent-combinatorics.2-element-types.html#2893" class="Function">2-Element-Type</a> <a id="741" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="747" class="Symbol">→</a> <a id="749" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="752" href="structured-types.involutive-types.html#722" class="Bound">l</a>

<a id="755" class="Keyword">module</a> <a id="762" href="structured-types.involutive-types.html#762" class="Module">_</a>
  <a id="766" class="Symbol">{</a><a id="767" href="structured-types.involutive-types.html#767" class="Bound">l</a> <a id="769" class="Symbol">:</a> <a id="771" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="776" class="Symbol">}</a> <a id="778" class="Symbol">(</a><a id="779" href="structured-types.involutive-types.html#779" class="Bound">X</a> <a id="781" class="Symbol">:</a> <a id="783" href="structured-types.involutive-types.html#662" class="Function">Involutive-Type</a> <a id="799" href="structured-types.involutive-types.html#767" class="Bound">l</a><a id="800" class="Symbol">)</a>
  <a id="804" class="Keyword">where</a>

  <a id="813" href="structured-types.involutive-types.html#813" class="Function">type-Involutive-Type</a> <a id="834" class="Symbol">:</a> <a id="836" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="839" href="structured-types.involutive-types.html#767" class="Bound">l</a>
  <a id="843" href="structured-types.involutive-types.html#813" class="Function">type-Involutive-Type</a> <a id="864" class="Symbol">=</a> <a id="866" href="structured-types.involutive-types.html#779" class="Bound">X</a> <a id="868" class="Symbol">(</a><a id="869" href="univalent-combinatorics.2-element-types.html#3652" class="Function">standard-2-Element-Type</a> <a id="893" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="898" class="Symbol">)</a>
</pre>
### Involutive structure on a type

<pre class="Agda"><a id="involutive-structure"></a><a id="949" href="structured-types.involutive-types.html#949" class="Function">involutive-structure</a> <a id="970" class="Symbol">:</a>
  <a id="974" class="Symbol">{</a><a id="975" href="structured-types.involutive-types.html#975" class="Bound">l1</a> <a id="978" class="Symbol">:</a> <a id="980" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="985" class="Symbol">}</a> <a id="987" class="Symbol">(</a><a id="988" href="structured-types.involutive-types.html#988" class="Bound">l2</a> <a id="991" class="Symbol">:</a> <a id="993" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="998" class="Symbol">)</a> <a id="1000" class="Symbol">(</a><a id="1001" href="structured-types.involutive-types.html#1001" class="Bound">X</a> <a id="1003" class="Symbol">:</a> <a id="1005" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1008" href="structured-types.involutive-types.html#975" class="Bound">l1</a><a id="1010" class="Symbol">)</a> <a id="1012" class="Symbol">→</a> <a id="1014" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1017" class="Symbol">(</a><a id="1018" href="structured-types.involutive-types.html#975" class="Bound">l1</a> <a id="1021" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1023" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1028" href="structured-types.involutive-types.html#988" class="Bound">l2</a><a id="1030" class="Symbol">)</a>
<a id="1032" href="structured-types.involutive-types.html#949" class="Function">involutive-structure</a> <a id="1053" href="structured-types.involutive-types.html#1053" class="Bound">l2</a> <a id="1056" href="structured-types.involutive-types.html#1056" class="Bound">X</a> <a id="1058" class="Symbol">=</a>
  <a id="1062" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1064" class="Symbol">(</a><a id="1065" href="structured-types.involutive-types.html#662" class="Function">Involutive-Type</a> <a id="1081" href="structured-types.involutive-types.html#1053" class="Bound">l2</a><a id="1083" class="Symbol">)</a> <a id="1085" class="Symbol">(λ</a> <a id="1088" href="structured-types.involutive-types.html#1088" class="Bound">Y</a> <a id="1090" class="Symbol">→</a> <a id="1092" href="structured-types.involutive-types.html#1056" class="Bound">X</a> <a id="1094" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1096" href="structured-types.involutive-types.html#813" class="Function">type-Involutive-Type</a> <a id="1117" href="structured-types.involutive-types.html#1088" class="Bound">Y</a><a id="1118" class="Symbol">)</a>
</pre>