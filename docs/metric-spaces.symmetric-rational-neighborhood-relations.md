# Symmetric rational neighborhood relations

<pre class="Agda"><a id="54" class="Keyword">module</a> <a id="61" href="metric-spaces.symmetric-rational-neighborhood-relations.html" class="Module">metric-spaces.symmetric-rational-neighborhood-relations</a> <a id="117" class="Keyword">where</a>
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
{{#concept "symmetric" Disambiguation="rational neighborhood relation" Agda=is-symmetric-Rational-Neighborhood-Relation}}
if all `ε`-neighborhoods are symmetric
[binary relations](foundation.binary-relations.md).

## Definitions

### The property of being a symmetric rational neighborhood relation

<pre class="Agda"><a id="871" class="Keyword">module</a> <a id="878" href="metric-spaces.symmetric-rational-neighborhood-relations.html#878" class="Module">_</a>
  <a id="882" class="Symbol">{</a><a id="883" href="metric-spaces.symmetric-rational-neighborhood-relations.html#883" class="Bound">l1</a> <a id="886" href="metric-spaces.symmetric-rational-neighborhood-relations.html#886" class="Bound">l2</a> <a id="889" class="Symbol">:</a> <a id="891" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="896" class="Symbol">}</a> <a id="898" class="Symbol">{</a><a id="899" href="metric-spaces.symmetric-rational-neighborhood-relations.html#899" class="Bound">A</a> <a id="901" class="Symbol">:</a> <a id="903" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="906" href="metric-spaces.symmetric-rational-neighborhood-relations.html#883" class="Bound">l1</a><a id="908" class="Symbol">}</a> <a id="910" class="Symbol">(</a><a id="911" href="metric-spaces.symmetric-rational-neighborhood-relations.html#911" class="Bound">B</a> <a id="913" class="Symbol">:</a> <a id="915" href="metric-spaces.rational-neighborhood-relations.html#1912" class="Function">Rational-Neighborhood-Relation</a> <a id="946" href="metric-spaces.symmetric-rational-neighborhood-relations.html#886" class="Bound">l2</a> <a id="949" href="metric-spaces.symmetric-rational-neighborhood-relations.html#899" class="Bound">A</a><a id="950" class="Symbol">)</a>
  <a id="954" class="Keyword">where</a>

  <a id="963" href="metric-spaces.symmetric-rational-neighborhood-relations.html#963" class="Function">is-symmetric-prop-Rational-Neighborhood-Relation</a> <a id="1012" class="Symbol">:</a> <a id="1014" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1019" class="Symbol">(</a><a id="1020" href="metric-spaces.symmetric-rational-neighborhood-relations.html#883" class="Bound">l1</a> <a id="1023" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1025" href="metric-spaces.symmetric-rational-neighborhood-relations.html#886" class="Bound">l2</a><a id="1027" class="Symbol">)</a>
  <a id="1031" href="metric-spaces.symmetric-rational-neighborhood-relations.html#963" class="Function">is-symmetric-prop-Rational-Neighborhood-Relation</a> <a id="1080" class="Symbol">=</a>
    <a id="1086" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1093" href="elementary-number-theory.positive-rational-numbers.html#4770" class="Function">ℚ⁺</a> <a id="1096" class="Symbol">(</a><a id="1097" href="foundation.binary-relations.html#4058" class="Function">is-symmetric-prop-Relation-Prop</a> <a id="1129" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1131" href="metric-spaces.symmetric-rational-neighborhood-relations.html#911" class="Bound">B</a><a id="1132" class="Symbol">)</a>

  <a id="1137" href="metric-spaces.symmetric-rational-neighborhood-relations.html#1137" class="Function">is-symmetric-Rational-Neighborhood-Relation</a> <a id="1181" class="Symbol">:</a> <a id="1183" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1186" class="Symbol">(</a><a id="1187" href="metric-spaces.symmetric-rational-neighborhood-relations.html#883" class="Bound">l1</a> <a id="1190" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1192" href="metric-spaces.symmetric-rational-neighborhood-relations.html#886" class="Bound">l2</a><a id="1194" class="Symbol">)</a>
  <a id="1198" href="metric-spaces.symmetric-rational-neighborhood-relations.html#1137" class="Function">is-symmetric-Rational-Neighborhood-Relation</a> <a id="1242" class="Symbol">=</a>
    <a id="1248" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1258" href="metric-spaces.symmetric-rational-neighborhood-relations.html#963" class="Function">is-symmetric-prop-Rational-Neighborhood-Relation</a>

  <a id="1310" href="metric-spaces.symmetric-rational-neighborhood-relations.html#1310" class="Function">is-prop-is-symmetric-Rational-Neighborhood-Relation</a> <a id="1362" class="Symbol">:</a>
    <a id="1368" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1376" href="metric-spaces.symmetric-rational-neighborhood-relations.html#1137" class="Function">is-symmetric-Rational-Neighborhood-Relation</a>
  <a id="1422" href="metric-spaces.symmetric-rational-neighborhood-relations.html#1310" class="Function">is-prop-is-symmetric-Rational-Neighborhood-Relation</a> <a id="1474" class="Symbol">=</a>
    <a id="1480" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1498" href="metric-spaces.symmetric-rational-neighborhood-relations.html#963" class="Function">is-symmetric-prop-Rational-Neighborhood-Relation</a>
</pre>