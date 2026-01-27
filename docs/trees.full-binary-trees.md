# Full binary trees

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="trees.full-binary-trees.html" class="Module">trees.full-binary-trees</a> <a id="61" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="117" class="Keyword">open</a> <a id="122" class="Keyword">import</a> <a id="129" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

A
{{#concept "full binary tree" Agda=full-binary-tree WD="full binary tree" WDID=Q29791667}}
is a finite [directed tree](trees.directed-trees.md) in which every non-leaf
node has a specified left branch and a specified right branch. More precisely, a
full binary tree consists of a root, a left full binary subtree and a right full
binary subtree.

## Definitions

### Full binary trees

<pre class="Agda"><a id="726" class="Keyword">data</a> <a id="full-binary-tree"></a><a id="731" href="trees.full-binary-trees.html#731" class="Datatype">full-binary-tree</a> <a id="748" class="Symbol">:</a> <a id="750" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="753" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="759" class="Keyword">where</a>
  <a id="full-binary-tree.leaf-full-binary-tree"></a><a id="767" href="trees.full-binary-trees.html#767" class="InductiveConstructor">leaf-full-binary-tree</a> <a id="789" class="Symbol">:</a> <a id="791" href="trees.full-binary-trees.html#731" class="Datatype">full-binary-tree</a>
  <a id="full-binary-tree.join-full-binary-tree"></a><a id="810" href="trees.full-binary-trees.html#810" class="InductiveConstructor">join-full-binary-tree</a> <a id="832" class="Symbol">:</a> <a id="834" class="Symbol">(</a><a id="835" href="trees.full-binary-trees.html#835" class="Bound">s</a> <a id="837" href="trees.full-binary-trees.html#837" class="Bound">t</a> <a id="839" class="Symbol">:</a> <a id="841" href="trees.full-binary-trees.html#731" class="Datatype">full-binary-tree</a><a id="857" class="Symbol">)</a> <a id="859" class="Symbol">→</a> <a id="861" href="trees.full-binary-trees.html#731" class="Datatype">full-binary-tree</a>
</pre>