# Lifts of types

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="foundation.lifts-types.html" class="Module">foundation.lifts-types</a> <a id="57" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="113" class="Keyword">open</a> <a id="118" class="Keyword">import</a> <a id="125" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Consider a type `X`. A {{#concept "lift" Disambiguation="type" Agda=lift-type}}
of `X` is an object in the [slice](foundation.slice.md) over `X`, i.e., it
consists of a type `Y` and a map `f : Y → X`.

In the above definition of lifts of types our aim is to capture the most general
concept of what it means to be an lift of a type. Similarly, in any
[category](category-theory.categories.md) we would say that an lift of an object
`X` consists of an object `Y` equipped with a morphism `f : Y → X`.

## Definitions

<pre class="Agda"><a id="lift-type"></a><a id="747" href="foundation.lifts-types.html#747" class="Function">lift-type</a> <a id="757" class="Symbol">:</a> <a id="759" class="Symbol">{</a><a id="760" href="foundation.lifts-types.html#760" class="Bound">l1</a> <a id="763" class="Symbol">:</a> <a id="765" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="770" class="Symbol">}</a> <a id="772" class="Symbol">(</a><a id="773" href="foundation.lifts-types.html#773" class="Bound">l2</a> <a id="776" class="Symbol">:</a> <a id="778" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="783" class="Symbol">)</a> <a id="785" class="Symbol">(</a><a id="786" href="foundation.lifts-types.html#786" class="Bound">X</a> <a id="788" class="Symbol">:</a> <a id="790" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="793" href="foundation.lifts-types.html#760" class="Bound">l1</a><a id="795" class="Symbol">)</a> <a id="797" class="Symbol">→</a> <a id="799" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="802" class="Symbol">(</a><a id="803" href="foundation.lifts-types.html#760" class="Bound">l1</a> <a id="806" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="808" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="813" href="foundation.lifts-types.html#773" class="Bound">l2</a><a id="815" class="Symbol">)</a>
<a id="817" href="foundation.lifts-types.html#747" class="Function">lift-type</a> <a id="827" href="foundation.lifts-types.html#827" class="Bound">l2</a> <a id="830" href="foundation.lifts-types.html#830" class="Bound">X</a> <a id="832" class="Symbol">=</a> <a id="834" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="836" class="Symbol">(</a><a id="837" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="840" href="foundation.lifts-types.html#827" class="Bound">l2</a><a id="842" class="Symbol">)</a> <a id="844" class="Symbol">(λ</a> <a id="847" href="foundation.lifts-types.html#847" class="Bound">Y</a> <a id="849" class="Symbol">→</a> <a id="851" href="foundation.lifts-types.html#847" class="Bound">Y</a> <a id="853" class="Symbol">→</a> <a id="855" href="foundation.lifts-types.html#830" class="Bound">X</a><a id="856" class="Symbol">)</a>

<a id="859" class="Keyword">module</a> <a id="866" href="foundation.lifts-types.html#866" class="Module">_</a>
  <a id="870" class="Symbol">{</a><a id="871" href="foundation.lifts-types.html#871" class="Bound">l1</a> <a id="874" href="foundation.lifts-types.html#874" class="Bound">l2</a> <a id="877" class="Symbol">:</a> <a id="879" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="884" class="Symbol">}</a> <a id="886" class="Symbol">{</a><a id="887" href="foundation.lifts-types.html#887" class="Bound">X</a> <a id="889" class="Symbol">:</a> <a id="891" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="894" href="foundation.lifts-types.html#871" class="Bound">l1</a><a id="896" class="Symbol">}</a> <a id="898" class="Symbol">(</a><a id="899" href="foundation.lifts-types.html#899" class="Bound">Y</a> <a id="901" class="Symbol">:</a> <a id="903" href="foundation.lifts-types.html#747" class="Function">lift-type</a> <a id="913" href="foundation.lifts-types.html#874" class="Bound">l2</a> <a id="916" href="foundation.lifts-types.html#887" class="Bound">X</a><a id="917" class="Symbol">)</a>
  <a id="921" class="Keyword">where</a>

  <a id="930" href="foundation.lifts-types.html#930" class="Function">type-lift-type</a> <a id="945" class="Symbol">:</a> <a id="947" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="950" href="foundation.lifts-types.html#874" class="Bound">l2</a>
  <a id="955" href="foundation.lifts-types.html#930" class="Function">type-lift-type</a> <a id="970" class="Symbol">=</a> <a id="972" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="976" href="foundation.lifts-types.html#899" class="Bound">Y</a>

  <a id="981" href="foundation.lifts-types.html#981" class="Function">projection-lift-type</a> <a id="1002" class="Symbol">:</a> <a id="1004" href="foundation.lifts-types.html#930" class="Function">type-lift-type</a> <a id="1019" class="Symbol">→</a> <a id="1021" href="foundation.lifts-types.html#887" class="Bound">X</a>
  <a id="1025" href="foundation.lifts-types.html#981" class="Function">projection-lift-type</a> <a id="1046" class="Symbol">=</a> <a id="1048" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1052" href="foundation.lifts-types.html#899" class="Bound">Y</a>
</pre>