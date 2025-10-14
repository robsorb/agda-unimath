# Directed graph structures on standard finite sets

<pre class="Agda"><a id="62" class="Keyword">module</a> <a id="69" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html" class="Module">graph-theory.directed-graph-structures-on-standard-finite-sets</a> <a id="132" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

A
{{#concept "directed graph structure" WD="directed graph" WDID=Q1137726 Agda=structure-directed-graph-Fin}}
on a [standard finite set](univalent-combinatorics.standard-finite-types.md)
`Fin n` is a [binary type valued relation](foundation.binary-relations.md)

```text
  Fin n → Fin n → 𝒰.
```

## Definitions

### Directed graph structures on standard finite sets

<pre class="Agda"><a id="structure-directed-graph-Fin"></a><a id="786" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#786" class="Function">structure-directed-graph-Fin</a> <a id="815" class="Symbol">:</a> <a id="817" class="Symbol">(</a><a id="818" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#818" class="Bound">l</a> <a id="820" class="Symbol">:</a> <a id="822" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="827" class="Symbol">)</a> <a id="829" class="Symbol">(</a><a id="830" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#830" class="Bound">n</a> <a id="832" class="Symbol">:</a> <a id="834" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="835" class="Symbol">)</a> <a id="837" class="Symbol">→</a> <a id="839" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="842" class="Symbol">(</a><a id="843" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="848" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#818" class="Bound">l</a><a id="849" class="Symbol">)</a>
<a id="851" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#786" class="Function">structure-directed-graph-Fin</a> <a id="880" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#880" class="Bound">l</a> <a id="882" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#882" class="Bound">n</a> <a id="884" class="Symbol">=</a> <a id="886" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="890" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#882" class="Bound">n</a> <a id="892" class="Symbol">→</a> <a id="894" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="898" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#882" class="Bound">n</a> <a id="900" class="Symbol">→</a> <a id="902" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="905" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#880" class="Bound">l</a>
</pre>
### Directed graphs on standard finite sets

<pre class="Agda"><a id="Directed-Graph-Fin"></a><a id="965" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#965" class="Function">Directed-Graph-Fin</a> <a id="984" class="Symbol">:</a> <a id="986" class="Symbol">(</a><a id="987" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#987" class="Bound">l</a> <a id="989" class="Symbol">:</a> <a id="991" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="996" class="Symbol">)</a> <a id="998" class="Symbol">→</a> <a id="1000" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1003" class="Symbol">(</a><a id="1004" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1009" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#987" class="Bound">l</a><a id="1010" class="Symbol">)</a>
<a id="1012" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#965" class="Function">Directed-Graph-Fin</a> <a id="1031" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#1031" class="Bound">l</a> <a id="1033" class="Symbol">=</a> <a id="1035" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1037" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1039" class="Symbol">(</a><a id="1040" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#786" class="Function">structure-directed-graph-Fin</a> <a id="1069" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#1031" class="Bound">l</a><a id="1070" class="Symbol">)</a>
</pre>
### Labeled finite directed graphs on standard finite sets

A
{{#concept "labeled finite directed graph" Agda=Labeled-Finite-Directed-Graph}}
consists of a [natural number](elementary-number-theory.natural-numbers.md) `n`
and a map `Fin n → Fin n → ℕ`.

<pre class="Agda"><a id="Labeled-Finite-Directed-Graph"></a><a id="1339" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#1339" class="Function">Labeled-Finite-Directed-Graph</a> <a id="1369" class="Symbol">:</a> <a id="1371" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1374" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1380" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#1339" class="Function">Labeled-Finite-Directed-Graph</a> <a id="1410" class="Symbol">=</a> <a id="1412" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1414" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1416" class="Symbol">(λ</a> <a id="1419" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#1419" class="Bound">n</a> <a id="1421" class="Symbol">→</a> <a id="1423" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="1427" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#1419" class="Bound">n</a> <a id="1429" class="Symbol">→</a> <a id="1431" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="1435" href="graph-theory.directed-graph-structures-on-standard-finite-sets.html#1419" class="Bound">n</a> <a id="1437" class="Symbol">→</a> <a id="1439" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1440" class="Symbol">)</a>
</pre>
## External links

- [Digraph](https://ncatlab.org/nlab/show/digraph) at $n$Lab
- [Directed graph](https://ncatlab.org/nlab/show/directed+graph) at $n$Lab
- [Directed graph](https://www.wikidata.org/entity/Q1137726) on Wikidata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Directed graph](https://mathworld.wolfram.com/DirectedGraph.html) at Wolfram
  MathWorld
