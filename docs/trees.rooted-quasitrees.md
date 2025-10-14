# Rooted quasitrees

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="trees.rooted-quasitrees.html" class="Module">trees.rooted-quasitrees</a> <a id="61" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="117" class="Keyword">open</a> <a id="122" class="Keyword">import</a> <a id="129" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="159" class="Keyword">open</a> <a id="164" class="Keyword">import</a> <a id="171" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="graph-theory.trails-undirected-graphs.html" class="Module">graph-theory.trails-undirected-graphs</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
</details>

## Idea

A **rooted quasitree** is an undirected graph `G` equipped with a marked
vertex`r`, to be called the root, such that for every vertex `x` there is a
unique trail from `r` to `x`.

## Definition

<pre class="Agda"><a id="is-rooted-quasitree-Undirected-Graph"></a><a id="565" href="trees.rooted-quasitrees.html#565" class="Function">is-rooted-quasitree-Undirected-Graph</a> <a id="602" class="Symbol">:</a>
  <a id="606" class="Symbol">{</a><a id="607" href="trees.rooted-quasitrees.html#607" class="Bound">l1</a> <a id="610" href="trees.rooted-quasitrees.html#610" class="Bound">l2</a> <a id="613" class="Symbol">:</a> <a id="615" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="620" class="Symbol">}</a> <a id="622" class="Symbol">(</a><a id="623" href="trees.rooted-quasitrees.html#623" class="Bound">G</a> <a id="625" class="Symbol">:</a> <a id="627" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="644" href="trees.rooted-quasitrees.html#607" class="Bound">l1</a> <a id="647" href="trees.rooted-quasitrees.html#610" class="Bound">l2</a><a id="649" class="Symbol">)</a> <a id="651" class="Symbol">→</a>
  <a id="655" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="679" href="trees.rooted-quasitrees.html#623" class="Bound">G</a> <a id="681" class="Symbol">→</a> <a id="683" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="686" class="Symbol">(</a><a id="687" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="692" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="698" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="700" href="trees.rooted-quasitrees.html#607" class="Bound">l1</a> <a id="703" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="705" href="trees.rooted-quasitrees.html#610" class="Bound">l2</a><a id="707" class="Symbol">)</a>
<a id="709" href="trees.rooted-quasitrees.html#565" class="Function">is-rooted-quasitree-Undirected-Graph</a> <a id="746" href="trees.rooted-quasitrees.html#746" class="Bound">G</a> <a id="748" href="trees.rooted-quasitrees.html#748" class="Bound">r</a> <a id="750" class="Symbol">=</a>
  <a id="754" class="Symbol">(</a><a id="755" href="trees.rooted-quasitrees.html#755" class="Bound">x</a> <a id="757" class="Symbol">:</a> <a id="759" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="783" href="trees.rooted-quasitrees.html#746" class="Bound">G</a><a id="784" class="Symbol">)</a> <a id="786" class="Symbol">→</a> <a id="788" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="797" class="Symbol">(</a><a id="798" href="graph-theory.trails-undirected-graphs.html#1001" class="Function">trail-Undirected-Graph</a> <a id="821" href="trees.rooted-quasitrees.html#746" class="Bound">G</a> <a id="823" href="trees.rooted-quasitrees.html#748" class="Bound">r</a> <a id="825" href="trees.rooted-quasitrees.html#755" class="Bound">x</a><a id="826" class="Symbol">)</a>

<a id="Rooted-Quasitree"></a><a id="829" href="trees.rooted-quasitrees.html#829" class="Function">Rooted-Quasitree</a> <a id="846" class="Symbol">:</a> <a id="848" class="Symbol">(</a><a id="849" href="trees.rooted-quasitrees.html#849" class="Bound">l1</a> <a id="852" href="trees.rooted-quasitrees.html#852" class="Bound">l2</a> <a id="855" class="Symbol">:</a> <a id="857" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="862" class="Symbol">)</a> <a id="864" class="Symbol">→</a> <a id="866" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="869" class="Symbol">(</a><a id="870" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="875" href="trees.rooted-quasitrees.html#849" class="Bound">l1</a> <a id="878" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="880" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="885" href="trees.rooted-quasitrees.html#852" class="Bound">l2</a><a id="887" class="Symbol">)</a>
<a id="889" href="trees.rooted-quasitrees.html#829" class="Function">Rooted-Quasitree</a> <a id="906" href="trees.rooted-quasitrees.html#906" class="Bound">l1</a> <a id="909" href="trees.rooted-quasitrees.html#909" class="Bound">l2</a> <a id="912" class="Symbol">=</a>
  <a id="916" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="918" class="Symbol">(</a> <a id="920" href="graph-theory.undirected-graphs.html#627" class="Function">Undirected-Graph</a> <a id="937" href="trees.rooted-quasitrees.html#906" class="Bound">l1</a> <a id="940" href="trees.rooted-quasitrees.html#909" class="Bound">l2</a><a id="942" class="Symbol">)</a>
    <a id="948" class="Symbol">(</a> <a id="950" class="Symbol">λ</a> <a id="952" href="trees.rooted-quasitrees.html#952" class="Bound">G</a> <a id="954" class="Symbol">→</a>
      <a id="962" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="964" class="Symbol">(</a> <a id="966" href="graph-theory.undirected-graphs.html#823" class="Function">vertex-Undirected-Graph</a> <a id="990" href="trees.rooted-quasitrees.html#952" class="Bound">G</a><a id="991" class="Symbol">)</a>
        <a id="1001" class="Symbol">(</a> <a id="1003" href="trees.rooted-quasitrees.html#565" class="Function">is-rooted-quasitree-Undirected-Graph</a> <a id="1040" href="trees.rooted-quasitrees.html#952" class="Bound">G</a><a id="1041" class="Symbol">))</a>
</pre>