# The universal tree

<pre class="Agda"><a id="31" class="Symbol">{-#</a> <a id="35" class="Keyword">OPTIONS</a> <a id="43" class="Pragma">--guardedness</a> <a id="57" class="Symbol">#-}</a>

<a id="62" class="Keyword">module</a> <a id="69" href="trees.universal-tree.html" class="Module">trees.universal-tree</a> <a id="90" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="146" class="Keyword">open</a> <a id="151" class="Keyword">import</a> <a id="158" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The universal tree is the coinductive type associated to the
[polynomial endofunctor](trees.polynomial-endofunctors.md)

```text
  X ↦ Σ 𝒰 (λ T → Xᵀ).
```

Note that this is the same polynomial endofunctor that we used to define the
type of [multisets](trees.multisets.md), which is the universal _well-founded_
tree.

## Definitions

### The universal tree of small trees

<pre class="Agda"><a id="593" class="Keyword">module</a> <a id="600" href="trees.universal-tree.html#600" class="Module">_</a>
  <a id="604" class="Symbol">(</a><a id="605" href="trees.universal-tree.html#605" class="Bound">l</a> <a id="607" class="Symbol">:</a> <a id="609" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="614" class="Symbol">)</a>
  <a id="618" class="Keyword">where</a>

  <a id="627" class="Keyword">record</a> <a id="634" href="trees.universal-tree.html#634" class="Record">Universal-Tree</a> <a id="649" class="Symbol">:</a> <a id="651" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="654" class="Symbol">(</a><a id="655" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="660" href="trees.universal-tree.html#605" class="Bound">l</a><a id="661" class="Symbol">)</a>
    <a id="667" class="Keyword">where</a>
    <a id="677" class="Keyword">coinductive</a>
    <a id="693" class="Keyword">field</a>
      <a id="705" href="trees.universal-tree.html#705" class="Field">type-Universal-Tree</a> <a id="725" class="Symbol">:</a>
        <a id="735" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="738" href="trees.universal-tree.html#605" class="Bound">l</a>
      <a id="746" href="trees.universal-tree.html#746" class="Field">branch-Universal-Tree</a> <a id="768" class="Symbol">:</a>
        <a id="778" class="Symbol">(</a><a id="779" href="trees.universal-tree.html#779" class="Bound">x</a> <a id="781" class="Symbol">:</a> <a id="783" href="trees.universal-tree.html#705" class="Field">type-Universal-Tree</a><a id="802" class="Symbol">)</a> <a id="804" class="Symbol">→</a> <a id="806" href="trees.universal-tree.html#634" class="Record">Universal-Tree</a>

  <a id="824" class="Keyword">open</a> <a id="829" href="trees.universal-tree.html#634" class="Module">Universal-Tree</a> <a id="844" class="Keyword">public</a>
</pre>