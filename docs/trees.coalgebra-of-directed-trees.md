# The coalgebra of directed trees

<pre class="Agda"><a id="44" class="Keyword">module</a> <a id="51" href="trees.coalgebra-of-directed-trees.html" class="Module">trees.coalgebra-of-directed-trees</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="trees.bases-directed-trees.html" class="Module">trees.bases-directed-trees</a>
<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="trees.coalgebras-polynomial-endofunctors.html" class="Module">trees.coalgebras-polynomial-endofunctors</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="trees.directed-trees.html" class="Module">trees.directed-trees</a>
<a id="350" class="Keyword">open</a> <a id="355" class="Keyword">import</a> <a id="362" href="trees.fibers-directed-trees.html" class="Module">trees.fibers-directed-trees</a>
</pre>
</details>

## Idea

Using the fibers of base elements, the type of directed trees, of which the type
of nodes and the types of edges are of the same universe level, has the
structure of a coalgebra for the polynomial endofunctor

```text
  A ↦ Σ (X : UU), X → A
```

## Definition

<pre class="Agda"><a id="coalgebra-Directed-Tree"></a><a id="686" href="trees.coalgebra-of-directed-trees.html#686" class="Function">coalgebra-Directed-Tree</a> <a id="710" class="Symbol">:</a>
  <a id="714" class="Symbol">(</a><a id="715" href="trees.coalgebra-of-directed-trees.html#715" class="Bound">l</a> <a id="717" class="Symbol">:</a> <a id="719" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="724" class="Symbol">)</a> <a id="726" class="Symbol">→</a> <a id="728" href="trees.coalgebras-polynomial-endofunctors.html#529" class="Function">coalgebra-polynomial-endofunctor</a> <a id="761" class="Symbol">(</a><a id="762" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="767" href="trees.coalgebra-of-directed-trees.html#715" class="Bound">l</a><a id="768" class="Symbol">)</a> <a id="770" class="Symbol">(</a><a id="771" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="774" href="trees.coalgebra-of-directed-trees.html#715" class="Bound">l</a><a id="775" class="Symbol">)</a> <a id="777" class="Symbol">(λ</a> <a id="780" href="trees.coalgebra-of-directed-trees.html#780" class="Bound">X</a> <a id="782" class="Symbol">→</a> <a id="784" href="trees.coalgebra-of-directed-trees.html#780" class="Bound">X</a><a id="785" class="Symbol">)</a>
<a id="787" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="791" class="Symbol">(</a><a id="792" href="trees.coalgebra-of-directed-trees.html#686" class="Function">coalgebra-Directed-Tree</a> <a id="816" href="trees.coalgebra-of-directed-trees.html#816" class="Bound">l</a><a id="817" class="Symbol">)</a> <a id="819" class="Symbol">=</a> <a id="821" href="trees.directed-trees.html#2349" class="Function">Directed-Tree</a> <a id="835" href="trees.coalgebra-of-directed-trees.html#816" class="Bound">l</a> <a id="837" href="trees.coalgebra-of-directed-trees.html#816" class="Bound">l</a>
<a id="839" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="843" class="Symbol">(</a><a id="844" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="848" class="Symbol">(</a><a id="849" href="trees.coalgebra-of-directed-trees.html#686" class="Function">coalgebra-Directed-Tree</a> <a id="873" href="trees.coalgebra-of-directed-trees.html#873" class="Bound">l</a><a id="874" class="Symbol">)</a> <a id="876" href="trees.coalgebra-of-directed-trees.html#876" class="Bound">T</a><a id="877" class="Symbol">)</a> <a id="879" class="Symbol">=</a> <a id="881" href="trees.bases-directed-trees.html#1223" class="Function">base-Directed-Tree</a> <a id="900" href="trees.coalgebra-of-directed-trees.html#876" class="Bound">T</a>
<a id="902" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="906" class="Symbol">(</a><a id="907" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="911" class="Symbol">(</a><a id="912" href="trees.coalgebra-of-directed-trees.html#686" class="Function">coalgebra-Directed-Tree</a> <a id="936" href="trees.coalgebra-of-directed-trees.html#936" class="Bound">l</a><a id="937" class="Symbol">)</a> <a id="939" href="trees.coalgebra-of-directed-trees.html#939" class="Bound">T</a><a id="940" class="Symbol">)</a> <a id="942" class="Symbol">=</a> <a id="944" href="trees.fibers-directed-trees.html#8130" class="Function">fiber-base-Directed-Tree</a> <a id="969" href="trees.coalgebra-of-directed-trees.html#939" class="Bound">T</a>
</pre>