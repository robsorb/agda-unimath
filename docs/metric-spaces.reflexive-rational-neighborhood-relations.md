# Reflexive rational neighborhood relations

<pre class="Agda"><a id="54" class="Keyword">module</a> <a id="61" href="metric-spaces.reflexive-rational-neighborhood-relations.html" class="Module">metric-spaces.reflexive-rational-neighborhood-relations</a> <a id="117" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="elementary-number-theory.positive-rational-numbers.html" class="Module">elementary-number-theory.positive-rational-numbers</a>

<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="391" class="Keyword">open</a> <a id="396" class="Keyword">import</a> <a id="403" href="metric-spaces.rational-neighborhood-relations.html" class="Module">metric-spaces.rational-neighborhood-relations</a>
</pre>
</details>

## Idea

A
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
is
{{#concept "reflexive" Disambiguation="rational neighborhood relation" Agda=is-reflexive-Rational-Neighborhood-Relation}}
if any element is in all neighborhoods of itself, i.e., if all `ε`-neighborhoods
are reflexive [binary relations](foundation.binary-relations.md).

## Definitions

### The property of being a reflexive rational neighborhood relation

<pre class="Agda"><a id="927" class="Keyword">module</a> <a id="934" href="metric-spaces.reflexive-rational-neighborhood-relations.html#934" class="Module">_</a>
  <a id="938" class="Symbol">{</a><a id="939" href="metric-spaces.reflexive-rational-neighborhood-relations.html#939" class="Bound">l1</a> <a id="942" href="metric-spaces.reflexive-rational-neighborhood-relations.html#942" class="Bound">l2</a> <a id="945" class="Symbol">:</a> <a id="947" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="952" class="Symbol">}</a> <a id="954" class="Symbol">{</a><a id="955" href="metric-spaces.reflexive-rational-neighborhood-relations.html#955" class="Bound">A</a> <a id="957" class="Symbol">:</a> <a id="959" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="962" href="metric-spaces.reflexive-rational-neighborhood-relations.html#939" class="Bound">l1</a><a id="964" class="Symbol">}</a> <a id="966" class="Symbol">(</a><a id="967" href="metric-spaces.reflexive-rational-neighborhood-relations.html#967" class="Bound">B</a> <a id="969" class="Symbol">:</a> <a id="971" href="metric-spaces.rational-neighborhood-relations.html#1912" class="Function">Rational-Neighborhood-Relation</a> <a id="1002" href="metric-spaces.reflexive-rational-neighborhood-relations.html#942" class="Bound">l2</a> <a id="1005" href="metric-spaces.reflexive-rational-neighborhood-relations.html#955" class="Bound">A</a><a id="1006" class="Symbol">)</a>
  <a id="1010" class="Keyword">where</a>

  <a id="1019" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1019" class="Function">is-reflexive-prop-Rational-Neighborhood-Relation</a> <a id="1068" class="Symbol">:</a> <a id="1070" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1075" class="Symbol">(</a><a id="1076" href="metric-spaces.reflexive-rational-neighborhood-relations.html#939" class="Bound">l1</a> <a id="1079" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1081" href="metric-spaces.reflexive-rational-neighborhood-relations.html#942" class="Bound">l2</a><a id="1083" class="Symbol">)</a>
  <a id="1087" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1019" class="Function">is-reflexive-prop-Rational-Neighborhood-Relation</a> <a id="1136" class="Symbol">=</a>
    <a id="1142" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1149" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="1152" class="Symbol">(</a><a id="1153" href="foundation.binary-relations.html#2991" class="Function">is-reflexive-prop-Relation-Prop</a> <a id="1185" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1187" href="metric-spaces.reflexive-rational-neighborhood-relations.html#967" class="Bound">B</a><a id="1188" class="Symbol">)</a>

  <a id="1193" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1193" class="Function">is-reflexive-Rational-Neighborhood-Relation</a> <a id="1237" class="Symbol">:</a> <a id="1239" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1242" class="Symbol">(</a><a id="1243" href="metric-spaces.reflexive-rational-neighborhood-relations.html#939" class="Bound">l1</a> <a id="1246" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1248" href="metric-spaces.reflexive-rational-neighborhood-relations.html#942" class="Bound">l2</a><a id="1250" class="Symbol">)</a>
  <a id="1254" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1193" class="Function">is-reflexive-Rational-Neighborhood-Relation</a> <a id="1298" class="Symbol">=</a>
    <a id="1304" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1314" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1019" class="Function">is-reflexive-prop-Rational-Neighborhood-Relation</a>

  <a id="1366" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1366" class="Function">is-prop-is-reflexive-Rational-Neighborhood-Relation</a> <a id="1418" class="Symbol">:</a>
    <a id="1424" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1432" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1193" class="Function">is-reflexive-Rational-Neighborhood-Relation</a>
  <a id="1478" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1366" class="Function">is-prop-is-reflexive-Rational-Neighborhood-Relation</a> <a id="1530" class="Symbol">=</a>
    <a id="1536" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1554" href="metric-spaces.reflexive-rational-neighborhood-relations.html#1019" class="Function">is-reflexive-prop-Rational-Neighborhood-Relation</a>
</pre>