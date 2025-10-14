# Sequences in metric spaces

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="metric-spaces.sequences-metric-spaces.html" class="Module">metric-spaces.sequences-metric-spaces</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="234" class="Keyword">open</a> <a id="239" class="Keyword">import</a> <a id="246" href="metric-spaces.dependent-products-metric-spaces.html" class="Module">metric-spaces.dependent-products-metric-spaces</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="metric-spaces.metric-spaces.html" class="Module">metric-spaces.metric-spaces</a>
</pre>
</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a metric space" Agda=sequence-type-Metric-Space}}
in a [metric space](metric-spaces.metric-spaces.md) is a
[sequence](lists.sequences.md) in its underlying type.

## Definitions

### The metric space of sequences in a metric space

<pre class="Agda"><a id="642" class="Keyword">module</a> <a id="649" href="metric-spaces.sequences-metric-spaces.html#649" class="Module">_</a>
  <a id="653" class="Symbol">{</a><a id="654" href="metric-spaces.sequences-metric-spaces.html#654" class="Bound">l1</a> <a id="657" href="metric-spaces.sequences-metric-spaces.html#657" class="Bound">l2</a> <a id="660" class="Symbol">:</a> <a id="662" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="667" class="Symbol">}</a> <a id="669" class="Symbol">(</a><a id="670" href="metric-spaces.sequences-metric-spaces.html#670" class="Bound">M</a> <a id="672" class="Symbol">:</a> <a id="674" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="687" href="metric-spaces.sequences-metric-spaces.html#654" class="Bound">l1</a> <a id="690" href="metric-spaces.sequences-metric-spaces.html#657" class="Bound">l2</a><a id="692" class="Symbol">)</a>
  <a id="696" class="Keyword">where</a>

  <a id="705" href="metric-spaces.sequences-metric-spaces.html#705" class="Function">sequence-Metric-Space</a> <a id="727" class="Symbol">:</a> <a id="729" href="metric-spaces.metric-spaces.html#4139" class="Function">Metric-Space</a> <a id="742" href="metric-spaces.sequences-metric-spaces.html#654" class="Bound">l1</a> <a id="745" href="metric-spaces.sequences-metric-spaces.html#657" class="Bound">l2</a>
  <a id="750" href="metric-spaces.sequences-metric-spaces.html#705" class="Function">sequence-Metric-Space</a> <a id="772" class="Symbol">=</a> <a id="774" href="metric-spaces.dependent-products-metric-spaces.html#4462" class="Function">Π-Metric-Space</a> <a id="789" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="791" class="Symbol">(λ</a> <a id="794" href="metric-spaces.sequences-metric-spaces.html#794" class="Bound">_</a> <a id="796" class="Symbol">→</a> <a id="798" href="metric-spaces.sequences-metric-spaces.html#670" class="Bound">M</a><a id="799" class="Symbol">)</a>

  <a id="804" href="metric-spaces.sequences-metric-spaces.html#804" class="Function">sequence-type-Metric-Space</a> <a id="831" class="Symbol">:</a> <a id="833" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="836" href="metric-spaces.sequences-metric-spaces.html#654" class="Bound">l1</a>
  <a id="841" href="metric-spaces.sequences-metric-spaces.html#804" class="Function">sequence-type-Metric-Space</a> <a id="868" class="Symbol">=</a>
    <a id="874" href="metric-spaces.metric-spaces.html#5090" class="Function">type-Metric-Space</a> <a id="892" href="metric-spaces.sequences-metric-spaces.html#705" class="Function">sequence-Metric-Space</a>
</pre>