# Hypergraphs

<pre class="Agda"><a id="24" class="Keyword">module</a> <a id="31" href="graph-theory.hypergraphs.html" class="Module">graph-theory.hypergraphs</a> <a id="56" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="112" class="Keyword">open</a> <a id="117" class="Keyword">import</a> <a id="124" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.unordered-tuples.html" class="Module">foundation.unordered-tuples</a>
</pre>
</details>

## Idea

A **`k`-hypergraph** consists of a type `V` of vertices and a family `E` of
types indexed by the [unordered `k`-tuples](foundation.unordered-tuples.md) of
vertices.

## Definition

<pre class="Agda"><a id="Hypergraph"></a><a id="504" href="graph-theory.hypergraphs.html#504" class="Function">Hypergraph</a> <a id="515" class="Symbol">:</a> <a id="517" class="Symbol">(</a><a id="518" href="graph-theory.hypergraphs.html#518" class="Bound">l1</a> <a id="521" href="graph-theory.hypergraphs.html#521" class="Bound">l2</a> <a id="524" class="Symbol">:</a> <a id="526" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="531" class="Symbol">)</a> <a id="533" class="Symbol">(</a><a id="534" href="graph-theory.hypergraphs.html#534" class="Bound">k</a> <a id="536" class="Symbol">:</a> <a id="538" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="539" class="Symbol">)</a> <a id="541" class="Symbol">→</a> <a id="543" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="546" class="Symbol">(</a><a id="547" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="552" href="graph-theory.hypergraphs.html#518" class="Bound">l1</a> <a id="555" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="557" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="562" href="graph-theory.hypergraphs.html#521" class="Bound">l2</a><a id="564" class="Symbol">)</a>
<a id="566" href="graph-theory.hypergraphs.html#504" class="Function">Hypergraph</a> <a id="577" href="graph-theory.hypergraphs.html#577" class="Bound">l1</a> <a id="580" href="graph-theory.hypergraphs.html#580" class="Bound">l2</a> <a id="583" href="graph-theory.hypergraphs.html#583" class="Bound">k</a> <a id="585" class="Symbol">=</a> <a id="587" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="589" class="Symbol">(</a><a id="590" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="593" href="graph-theory.hypergraphs.html#577" class="Bound">l1</a><a id="595" class="Symbol">)</a> <a id="597" class="Symbol">(λ</a> <a id="600" href="graph-theory.hypergraphs.html#600" class="Bound">V</a> <a id="602" class="Symbol">→</a> <a id="604" href="foundation.unordered-tuples.html#1551" class="Function">unordered-tuple</a> <a id="620" href="graph-theory.hypergraphs.html#583" class="Bound">k</a> <a id="622" href="graph-theory.hypergraphs.html#600" class="Bound">V</a> <a id="624" class="Symbol">→</a> <a id="626" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="629" href="graph-theory.hypergraphs.html#580" class="Bound">l2</a><a id="631" class="Symbol">)</a>

<a id="634" class="Keyword">module</a> <a id="641" href="graph-theory.hypergraphs.html#641" class="Module">_</a>
  <a id="645" class="Symbol">{</a><a id="646" href="graph-theory.hypergraphs.html#646" class="Bound">l1</a> <a id="649" href="graph-theory.hypergraphs.html#649" class="Bound">l2</a> <a id="652" class="Symbol">:</a> <a id="654" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="659" class="Symbol">}</a> <a id="661" class="Symbol">{</a><a id="662" href="graph-theory.hypergraphs.html#662" class="Bound">k</a> <a id="664" class="Symbol">:</a> <a id="666" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="667" class="Symbol">}</a> <a id="669" class="Symbol">(</a><a id="670" href="graph-theory.hypergraphs.html#670" class="Bound">G</a> <a id="672" class="Symbol">:</a> <a id="674" href="graph-theory.hypergraphs.html#504" class="Function">Hypergraph</a> <a id="685" href="graph-theory.hypergraphs.html#646" class="Bound">l1</a> <a id="688" href="graph-theory.hypergraphs.html#649" class="Bound">l2</a> <a id="691" href="graph-theory.hypergraphs.html#662" class="Bound">k</a><a id="692" class="Symbol">)</a>
  <a id="696" class="Keyword">where</a>

  <a id="705" href="graph-theory.hypergraphs.html#705" class="Function">vertex-Hypergraph</a> <a id="723" class="Symbol">:</a> <a id="725" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="728" href="graph-theory.hypergraphs.html#646" class="Bound">l1</a>
  <a id="733" href="graph-theory.hypergraphs.html#705" class="Function">vertex-Hypergraph</a> <a id="751" class="Symbol">=</a> <a id="753" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="757" href="graph-theory.hypergraphs.html#670" class="Bound">G</a>

  <a id="762" href="graph-theory.hypergraphs.html#762" class="Function">unordered-tuple-vertices-Hypergraph</a> <a id="798" class="Symbol">:</a> <a id="800" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="803" class="Symbol">(</a><a id="804" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="809" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="815" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="817" href="graph-theory.hypergraphs.html#646" class="Bound">l1</a><a id="819" class="Symbol">)</a>
  <a id="823" href="graph-theory.hypergraphs.html#762" class="Function">unordered-tuple-vertices-Hypergraph</a> <a id="859" class="Symbol">=</a> <a id="861" href="foundation.unordered-tuples.html#1551" class="Function">unordered-tuple</a> <a id="877" href="graph-theory.hypergraphs.html#662" class="Bound">k</a> <a id="879" href="graph-theory.hypergraphs.html#705" class="Function">vertex-Hypergraph</a>

  <a id="900" href="graph-theory.hypergraphs.html#900" class="Function">simplex-Hypergraph</a> <a id="919" class="Symbol">:</a> <a id="921" href="graph-theory.hypergraphs.html#762" class="Function">unordered-tuple-vertices-Hypergraph</a> <a id="957" class="Symbol">→</a> <a id="959" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="962" href="graph-theory.hypergraphs.html#649" class="Bound">l2</a>
  <a id="967" href="graph-theory.hypergraphs.html#900" class="Function">simplex-Hypergraph</a> <a id="986" class="Symbol">=</a> <a id="988" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="992" href="graph-theory.hypergraphs.html#670" class="Bound">G</a>
</pre>
## External links

- [Hypergraph](https://ncatlab.org/nlab/show/hypergraph) at $n$Lab
- [Hypergraph](https://www.wikidata.org/entity/Q840247) on Wikidata
- [Hypergraph](https://en.wikipedia.org/wiki/Hypergraph) at Wikipedia
- [Hypergraph](https://mathworld.wolfram.com/Hypergraph.html) at Wolfram
  MathWorld
