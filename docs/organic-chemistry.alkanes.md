# Alkanes

<pre class="Agda"><a id="20" class="Keyword">module</a> <a id="27" href="organic-chemistry.alkanes.html" class="Module">organic-chemistry.alkanes</a> <a id="53" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="109" class="Keyword">open</a> <a id="114" class="Keyword">import</a> <a id="121" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="149" class="Keyword">open</a> <a id="154" class="Keyword">import</a> <a id="161" href="organic-chemistry.hydrocarbons.html" class="Module">organic-chemistry.hydrocarbons</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="organic-chemistry.saturated-carbons.html" class="Module">organic-chemistry.saturated-carbons</a>
</pre>
</details>

## Idea

An **alkane** is a hydrocarbon that only has saturated carbons, i.e., it does
not have any double or triple carbon-carbon bonds.

## Definition

<pre class="Agda"><a id="is-alkane-hydrocarbon"></a><a id="419" href="organic-chemistry.alkanes.html#419" class="Function">is-alkane-hydrocarbon</a> <a id="441" class="Symbol">:</a> <a id="443" class="Symbol">{</a><a id="444" href="organic-chemistry.alkanes.html#444" class="Bound">l1</a> <a id="447" href="organic-chemistry.alkanes.html#447" class="Bound">l2</a> <a id="450" class="Symbol">:</a> <a id="452" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="457" class="Symbol">}</a> <a id="459" class="Symbol">→</a> <a id="461" href="organic-chemistry.hydrocarbons.html#1569" class="Function">hydrocarbon</a> <a id="473" href="organic-chemistry.alkanes.html#444" class="Bound">l1</a> <a id="476" href="organic-chemistry.alkanes.html#447" class="Bound">l2</a> <a id="479" class="Symbol">→</a> <a id="481" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="484" class="Symbol">(</a><a id="485" href="organic-chemistry.alkanes.html#444" class="Bound">l1</a> <a id="488" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="490" href="organic-chemistry.alkanes.html#447" class="Bound">l2</a><a id="492" class="Symbol">)</a>
<a id="494" href="organic-chemistry.alkanes.html#419" class="Function">is-alkane-hydrocarbon</a> <a id="516" href="organic-chemistry.alkanes.html#516" class="Bound">H</a> <a id="518" class="Symbol">=</a>
  <a id="522" class="Symbol">(</a><a id="523" href="organic-chemistry.alkanes.html#523" class="Bound">c</a> <a id="525" class="Symbol">:</a> <a id="527" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="546" href="organic-chemistry.alkanes.html#516" class="Bound">H</a><a id="547" class="Symbol">)</a> <a id="549" class="Symbol">→</a> <a id="551" href="organic-chemistry.saturated-carbons.html#854" class="Function">is-saturated-carbon-hydrocarbon</a> <a id="583" href="organic-chemistry.alkanes.html#516" class="Bound">H</a> <a id="585" href="organic-chemistry.alkanes.html#523" class="Bound">c</a>
</pre>