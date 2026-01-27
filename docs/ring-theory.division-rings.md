# Division rings

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="ring-theory.division-rings.html" class="Module">ring-theory.division-rings</a> <a id="61" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="117" class="Keyword">open</a> <a id="122" class="Keyword">import</a> <a id="129" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="164" class="Keyword">open</a> <a id="169" class="Keyword">import</a> <a id="176" href="foundation.negated-equality.html" class="Module">foundation.negated-equality</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="ring-theory.invertible-elements-rings.html" class="Module">ring-theory.invertible-elements-rings</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="ring-theory.trivial-rings.html" class="Module">ring-theory.trivial-rings</a>
</pre>
</details>

## Idea

Division rings are nontrivial rings in which all nonzero elements are
invertible.

## Definition

<pre class="Agda"><a id="is-division-Ring"></a><a id="494" href="ring-theory.division-rings.html#494" class="Function">is-division-Ring</a> <a id="511" class="Symbol">:</a>
  <a id="515" class="Symbol">{</a> <a id="517" href="ring-theory.division-rings.html#517" class="Bound">l</a> <a id="519" class="Symbol">:</a> <a id="521" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="526" class="Symbol">}</a> <a id="528" class="Symbol">→</a> <a id="530" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="535" href="ring-theory.division-rings.html#517" class="Bound">l</a> <a id="537" class="Symbol">→</a> <a id="539" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="542" href="ring-theory.division-rings.html#517" class="Bound">l</a>
<a id="544" href="ring-theory.division-rings.html#494" class="Function">is-division-Ring</a> <a id="561" href="ring-theory.division-rings.html#561" class="Bound">R</a> <a id="563" class="Symbol">=</a>
  <a id="567" class="Symbol">(</a><a id="568" href="ring-theory.trivial-rings.html#1219" class="Function">is-nontrivial-Ring</a> <a id="587" href="ring-theory.division-rings.html#561" class="Bound">R</a><a id="588" class="Symbol">)</a> <a id="590" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a>
  <a id="594" class="Symbol">((</a><a id="596" href="ring-theory.division-rings.html#596" class="Bound">x</a> <a id="598" class="Symbol">:</a> <a id="600" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="610" href="ring-theory.division-rings.html#561" class="Bound">R</a><a id="611" class="Symbol">)</a> <a id="613" class="Symbol">→</a> <a id="615" href="ring-theory.rings.html#7541" class="Function">zero-Ring</a> <a id="625" href="ring-theory.division-rings.html#561" class="Bound">R</a> <a id="627" href="foundation.negated-equality.html#733" class="Function Operator">≠</a> <a id="629" href="ring-theory.division-rings.html#596" class="Bound">x</a> <a id="631" class="Symbol">→</a> <a id="633" href="ring-theory.invertible-elements-rings.html#3693" class="Function">is-invertible-element-Ring</a> <a id="660" href="ring-theory.division-rings.html#561" class="Bound">R</a> <a id="662" href="ring-theory.division-rings.html#596" class="Bound">x</a><a id="663" class="Symbol">)</a>
</pre>