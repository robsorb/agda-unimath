# Undirected graph structures on standard finite sets

<pre class="Agda"><a id="64" class="Keyword">module</a> <a id="71" href="graph-theory.undirected-graph-structures-on-standard-finite-sets.html" class="Module">graph-theory.undirected-graph-structures-on-standard-finite-sets</a> <a id="136" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="329" class="Keyword">open</a> <a id="334" class="Keyword">import</a> <a id="341" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>

<a id="369" class="Keyword">open</a> <a id="374" class="Keyword">import</a> <a id="381" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Definition

<pre class="Agda"><a id="Undirected-Graph-Fin"></a><a id="467" href="graph-theory.undirected-graph-structures-on-standard-finite-sets.html#467" class="Function">Undirected-Graph-Fin</a> <a id="488" class="Symbol">:</a> <a id="490" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="493" class="Symbol">(</a><a id="494" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="499" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="504" class="Symbol">)</a>
<a id="506" href="graph-theory.undirected-graph-structures-on-standard-finite-sets.html#467" class="Function">Undirected-Graph-Fin</a> <a id="527" class="Symbol">=</a> <a id="529" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="531" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="533" class="Symbol">(λ</a> <a id="536" href="graph-theory.undirected-graph-structures-on-standard-finite-sets.html#536" class="Bound">V</a> <a id="538" class="Symbol">→</a> <a id="540" href="foundation.unordered-pairs.html#2222" class="Function">unordered-pair</a> <a id="555" class="Symbol">(</a><a id="556" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="560" href="graph-theory.undirected-graph-structures-on-standard-finite-sets.html#536" class="Bound">V</a><a id="561" class="Symbol">)</a> <a id="563" class="Symbol">→</a> <a id="565" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="566" class="Symbol">)</a>
</pre>
## External links

- [Graph](https://ncatlab.org/nlab/show/graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Graph (discrete mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>)
  at Wikipedia
- [Graph](https://mathworld.wolfram.com/Graph.html) at Wolfram MathWorld
