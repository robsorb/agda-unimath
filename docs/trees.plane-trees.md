# Plane trees

<pre class="Agda"><a id="24" class="Keyword">module</a> <a id="31" href="trees.plane-trees.html" class="Module">trees.plane-trees</a> <a id="49" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="105" class="Keyword">open</a> <a id="110" class="Keyword">import</a> <a id="117" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="159" class="Keyword">open</a> <a id="164" class="Keyword">import</a> <a id="171" href="foundation.action-on-identifications-binary-functions.html" class="Module">foundation.action-on-identifications-binary-functions</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="402" class="Keyword">open</a> <a id="407" class="Keyword">import</a> <a id="414" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="440" class="Keyword">open</a> <a id="445" class="Keyword">import</a> <a id="452" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="469" class="Keyword">open</a> <a id="474" class="Keyword">import</a> <a id="481" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="504" class="Keyword">open</a> <a id="509" class="Keyword">import</a> <a id="516" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="536" class="Keyword">open</a> <a id="541" class="Keyword">import</a> <a id="548" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="576" class="Keyword">open</a> <a id="581" class="Keyword">import</a> <a id="588" href="lists.lists.html" class="Module">lists.lists</a>

<a id="601" class="Keyword">open</a> <a id="606" class="Keyword">import</a> <a id="613" href="trees.full-binary-trees.html" class="Module">trees.full-binary-trees</a>
<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="trees.w-types.html" class="Module">trees.w-types</a>

<a id="664" class="Keyword">open</a> <a id="669" class="Keyword">import</a> <a id="676" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

A {{#concept "plane tree" Agda=plane-tree WD="ordered tree" WDID=Q10396021}} is
a finite [directed tree](trees.directed-trees.md) that can be drawn on a plane
with the root at the bottom, and all branches directed upwards. More precisely,
a plane tree consists of a root and a family of plane trees indexed by a
[standard finite type](univalent-combinatorics.standard-finite-types.md). Plane
trees are also known as _ordered trees_.

The type of plane trees can be defined in several equivalent ways:

- The type of plane trees is the inductive type with constructor

  ```text
    (n : ℕ) → (Fin n → plane-tree) → plane-tree.
  ```

- The type of plane trees is the [W-type](trees.w-types.md)

  ```text
    𝕎 ℕ Fin.
  ```

- The type of plane trees is the inductive type with constructor

  ```text
    list plane-tree → plane-tree.
  ```

The type of plane trees is therefore the least fixed point of the
[list](lists.lists.md) functor `X ↦ list X`. In particular, `plane-tree` is the
least fixed point of the functor

```text
  X ↦ 1 + plane-tree × X.
```

The least fixed point for this functor coincides with the least fixed point of
the functor

```text
  X ↦ 1 + X².
```

Thus we obtain an equivalence

```text
  plane-tree ≃ full-binary-tree
```

from the type of plane trees to the type of
[full binary trees](trees.full-binary-trees.md).

## Definitions

### Plane trees

<pre class="Agda"><a id="2139" class="Keyword">data</a> <a id="plane-tree"></a><a id="2144" href="trees.plane-trees.html#2144" class="Datatype">plane-tree</a> <a id="2155" class="Symbol">:</a> <a id="2157" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2160" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2166" class="Keyword">where</a>
  <a id="plane-tree.make-plane-tree"></a><a id="2174" href="trees.plane-trees.html#2174" class="InductiveConstructor">make-plane-tree</a> <a id="2190" class="Symbol">:</a> <a id="2192" class="Symbol">{</a><a id="2193" href="trees.plane-trees.html#2193" class="Bound">n</a> <a id="2195" class="Symbol">:</a> <a id="2197" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2198" class="Symbol">}</a> <a id="2200" class="Symbol">→</a> <a id="2202" class="Symbol">(</a><a id="2203" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="2207" href="trees.plane-trees.html#2193" class="Bound">n</a> <a id="2209" class="Symbol">→</a> <a id="2211" href="trees.plane-trees.html#2144" class="Datatype">plane-tree</a><a id="2221" class="Symbol">)</a> <a id="2223" class="Symbol">→</a> <a id="2225" href="trees.plane-trees.html#2144" class="Datatype">plane-tree</a>
</pre>
### Plane trees as W-types

<pre class="Agda"><a id="plane-tree-𝕎"></a><a id="2277" href="trees.plane-trees.html#2277" class="Function">plane-tree-𝕎</a> <a id="2290" class="Symbol">:</a> <a id="2292" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2295" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2301" href="trees.plane-trees.html#2277" class="Function">plane-tree-𝕎</a> <a id="2314" class="Symbol">=</a> <a id="2316" href="trees.w-types.html#1681" class="Datatype">𝕎</a> <a id="2318" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2320" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a>
</pre>
### Plane trees defined using lists

<pre class="Agda"><a id="2374" class="Keyword">data</a> <a id="listed-plane-tree"></a><a id="2379" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a> <a id="2397" class="Symbol">:</a> <a id="2399" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2402" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2408" class="Keyword">where</a>
  <a id="listed-plane-tree.make-listed-plane-tree"></a><a id="2416" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="2439" class="Symbol">:</a> <a id="2441" href="lists.lists.html#1328" class="Datatype">list</a> <a id="2446" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a> <a id="2464" class="Symbol">→</a> <a id="2466" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a>
</pre>
## Operations on plane trees

### The type of nodes, including leaves, of a plane tree

<pre class="Agda"><a id="node-plane-tree"></a><a id="2585" href="trees.plane-trees.html#2585" class="Function">node-plane-tree</a> <a id="2601" class="Symbol">:</a> <a id="2603" href="trees.plane-trees.html#2144" class="Datatype">plane-tree</a> <a id="2614" class="Symbol">→</a> <a id="2616" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2619" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="2625" href="trees.plane-trees.html#2585" class="Function">node-plane-tree</a> <a id="2641" class="Symbol">(</a><a id="2642" href="trees.plane-trees.html#2174" class="InductiveConstructor">make-plane-tree</a> <a id="2658" class="Symbol">{</a><a id="2659" href="trees.plane-trees.html#2659" class="Bound">n</a><a id="2660" class="Symbol">}</a> <a id="2662" href="trees.plane-trees.html#2662" class="Bound">T</a><a id="2663" class="Symbol">)</a> <a id="2665" class="Symbol">=</a>
  <a id="2669" href="foundation.maybe.html#1591" class="Function">Maybe</a> <a id="2675" class="Symbol">(</a><a id="2676" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2678" class="Symbol">(</a><a id="2679" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="2683" href="trees.plane-trees.html#2659" class="Bound">n</a><a id="2684" class="Symbol">)</a> <a id="2686" class="Symbol">(λ</a> <a id="2689" href="trees.plane-trees.html#2689" class="Bound">i</a> <a id="2691" class="Symbol">→</a> <a id="2693" href="trees.plane-trees.html#2585" class="Function">node-plane-tree</a> <a id="2709" class="Symbol">(</a><a id="2710" href="trees.plane-trees.html#2662" class="Bound">T</a> <a id="2712" href="trees.plane-trees.html#2689" class="Bound">i</a><a id="2713" class="Symbol">)))</a>
</pre>
### The root of a plane tree

<pre class="Agda"><a id="root-plane-tree"></a><a id="2760" href="trees.plane-trees.html#2760" class="Function">root-plane-tree</a> <a id="2776" class="Symbol">:</a> <a id="2778" class="Symbol">(</a><a id="2779" href="trees.plane-trees.html#2779" class="Bound">T</a> <a id="2781" class="Symbol">:</a> <a id="2783" href="trees.plane-trees.html#2144" class="Datatype">plane-tree</a><a id="2793" class="Symbol">)</a> <a id="2795" class="Symbol">→</a> <a id="2797" href="trees.plane-trees.html#2585" class="Function">node-plane-tree</a> <a id="2813" href="trees.plane-trees.html#2779" class="Bound">T</a>
<a id="2815" href="trees.plane-trees.html#2760" class="Function">root-plane-tree</a> <a id="2831" class="Symbol">(</a><a id="2832" href="trees.plane-trees.html#2174" class="InductiveConstructor">make-plane-tree</a> <a id="2848" href="trees.plane-trees.html#2848" class="Bound">T</a><a id="2849" class="Symbol">)</a> <a id="2851" class="Symbol">=</a> <a id="2853" href="foundation.maybe.html#1713" class="Function">exception-Maybe</a>
</pre>
## Properties

### The type of listed plane trees is equivalent to the type of lists of listed plane trees

<pre class="Agda"><a id="unpack-listed-plane-tree"></a><a id="2990" href="trees.plane-trees.html#2990" class="Function">unpack-listed-plane-tree</a> <a id="3015" class="Symbol">:</a> <a id="3017" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a> <a id="3035" class="Symbol">→</a> <a id="3037" href="lists.lists.html#1328" class="Datatype">list</a> <a id="3042" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a>
<a id="3060" href="trees.plane-trees.html#2990" class="Function">unpack-listed-plane-tree</a> <a id="3085" class="Symbol">(</a><a id="3086" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="3109" href="trees.plane-trees.html#3109" class="Bound">t</a><a id="3110" class="Symbol">)</a> <a id="3112" class="Symbol">=</a> <a id="3114" href="trees.plane-trees.html#3109" class="Bound">t</a>

<a id="is-section-unpack-listed-plane-tree"></a><a id="3117" href="trees.plane-trees.html#3117" class="Function">is-section-unpack-listed-plane-tree</a> <a id="3153" class="Symbol">:</a>
  <a id="3157" href="foundation-core.sections.html#1194" class="Function">is-section</a> <a id="3168" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="3191" href="trees.plane-trees.html#2990" class="Function">unpack-listed-plane-tree</a>
<a id="3216" href="trees.plane-trees.html#3117" class="Function">is-section-unpack-listed-plane-tree</a> <a id="3252" class="Symbol">(</a><a id="3253" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="3276" href="trees.plane-trees.html#3276" class="Bound">t</a><a id="3277" class="Symbol">)</a> <a id="3279" class="Symbol">=</a> <a id="3281" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="is-retraction-unpack-listed-plane-tree"></a><a id="3287" href="trees.plane-trees.html#3287" class="Function">is-retraction-unpack-listed-plane-tree</a> <a id="3326" class="Symbol">:</a>
  <a id="3330" href="foundation-core.retractions.html#790" class="Function">is-retraction</a> <a id="3344" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="3367" href="trees.plane-trees.html#2990" class="Function">unpack-listed-plane-tree</a>
<a id="3392" href="trees.plane-trees.html#3287" class="Function">is-retraction-unpack-listed-plane-tree</a> <a id="3431" href="trees.plane-trees.html#3431" class="Bound">l</a> <a id="3433" class="Symbol">=</a> <a id="3435" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="is-equiv-make-listed-plane-tree"></a><a id="3441" href="trees.plane-trees.html#3441" class="Function">is-equiv-make-listed-plane-tree</a> <a id="3473" class="Symbol">:</a>
  <a id="3477" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="3486" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a>
<a id="3509" href="trees.plane-trees.html#3441" class="Function">is-equiv-make-listed-plane-tree</a> <a id="3541" class="Symbol">=</a>
  <a id="3545" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
    <a id="3572" class="Symbol">(</a> <a id="3574" href="trees.plane-trees.html#2990" class="Function">unpack-listed-plane-tree</a><a id="3598" class="Symbol">)</a>
    <a id="3604" class="Symbol">(</a> <a id="3606" href="trees.plane-trees.html#3117" class="Function">is-section-unpack-listed-plane-tree</a><a id="3641" class="Symbol">)</a>
    <a id="3647" class="Symbol">(</a> <a id="3649" href="trees.plane-trees.html#3287" class="Function">is-retraction-unpack-listed-plane-tree</a><a id="3687" class="Symbol">)</a>

<a id="equiv-make-listed-plane-tree"></a><a id="3690" href="trees.plane-trees.html#3690" class="Function">equiv-make-listed-plane-tree</a> <a id="3719" class="Symbol">:</a> <a id="3721" href="lists.lists.html#1328" class="Datatype">list</a> <a id="3726" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a> <a id="3744" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="3746" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a>
<a id="3764" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3768" href="trees.plane-trees.html#3690" class="Function">equiv-make-listed-plane-tree</a> <a id="3797" class="Symbol">=</a> <a id="3799" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a>
<a id="3822" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3826" href="trees.plane-trees.html#3690" class="Function">equiv-make-listed-plane-tree</a> <a id="3855" class="Symbol">=</a> <a id="3857" href="trees.plane-trees.html#3441" class="Function">is-equiv-make-listed-plane-tree</a>
</pre>
### The type of listed plane trees is equivalent to the type of full binary trees

Since `plane-tree` is inductively generated by a constructor
`list plane-tree → plane-tree`, we have an
[equivalence](foundation-core.equivalences.md)

```text
  list plane-tree ≃ plane-tree.
```

This description allows us to obtain an equivalence
`plane-tree ≃ full-binary-tree` from the type of plane trees to the type of
[full binary trees](trees.full-binary-trees.md). Indeed, by the above
equivalence we can compute

```text
  plane-tree ≃ list plane-tree
             ≃ 1 + plane-tree × list plane-tree
             ≃ 1 + plane-tree²
```

On the other hand, the type `full-binary-tree` is a fixed point for the
[polynomial endofunctor](trees.polynomial-endofunctors.md)
`X ↦ 1 + full-binary-tree × X`, since we have equivalences.

```text
  full-binary-tree ≃ 1 + full-binary-tree²
                   ≃ 1 + full-binary-tree × full-binary-tree
```

Since `full-binary-tree` is the least fixed point of the polynomial endofunctor
`X ↦ 1 + X²`, we obtain a `(1 + X²)`-structure preserving map

```text
  full-binary-tree → plane-tree.
```

Likewise, since `plane-tree` is the least fixed point of the endofunctor `list`,
we obtain a `list`-structure preserving map

```text
  plane-tree → full-binary-tree.
```

Initiality of both `full-binary-tree` and `plane-tree` can then be used to show
that these two maps are inverse to each other, i.e., that we obtain an
equivalence

```text
  plane-tree ≃ full-binary-tree.
```

<pre class="Agda"><a id="full-binary-tree-listed-plane-tree"></a><a id="5411" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a> <a id="5446" class="Symbol">:</a> <a id="5448" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a> <a id="5466" class="Symbol">→</a> <a id="5468" href="trees.full-binary-trees.html#731" class="Datatype">full-binary-tree</a>
<a id="5485" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a> <a id="5520" class="Symbol">(</a><a id="5521" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="5544" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="5547" class="Symbol">)</a> <a id="5549" class="Symbol">=</a>
  <a id="5553" href="trees.full-binary-trees.html#767" class="InductiveConstructor">leaf-full-binary-tree</a>
<a id="5575" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a> <a id="5610" class="Symbol">(</a><a id="5611" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="5634" class="Symbol">(</a><a id="5635" href="lists.lists.html#1386" class="InductiveConstructor">cons</a> <a id="5640" href="trees.plane-trees.html#5640" class="Bound">T</a> <a id="5642" href="trees.plane-trees.html#5642" class="Bound">l</a><a id="5643" class="Symbol">))</a> <a id="5646" class="Symbol">=</a>
  <a id="5650" href="trees.full-binary-trees.html#810" class="InductiveConstructor">join-full-binary-tree</a>
    <a id="5676" class="Symbol">(</a> <a id="5678" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a> <a id="5713" href="trees.plane-trees.html#5640" class="Bound">T</a><a id="5714" class="Symbol">)</a>
    <a id="5720" class="Symbol">(</a> <a id="5722" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a> <a id="5757" class="Symbol">(</a><a id="5758" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="5781" href="trees.plane-trees.html#5642" class="Bound">l</a><a id="5782" class="Symbol">))</a>

<a id="listed-plane-tree-full-binary-tree"></a><a id="5786" href="trees.plane-trees.html#5786" class="Function">listed-plane-tree-full-binary-tree</a> <a id="5821" class="Symbol">:</a> <a id="5823" href="trees.full-binary-trees.html#731" class="Datatype">full-binary-tree</a> <a id="5840" class="Symbol">→</a> <a id="5842" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a>
<a id="5860" href="trees.plane-trees.html#5786" class="Function">listed-plane-tree-full-binary-tree</a> <a id="5895" href="trees.full-binary-trees.html#767" class="InductiveConstructor">leaf-full-binary-tree</a> <a id="5917" class="Symbol">=</a>
  <a id="5921" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="5944" href="lists.lists.html#1371" class="InductiveConstructor">nil</a>
<a id="5948" href="trees.plane-trees.html#5786" class="Function">listed-plane-tree-full-binary-tree</a> <a id="5983" class="Symbol">(</a><a id="5984" href="trees.full-binary-trees.html#810" class="InductiveConstructor">join-full-binary-tree</a> <a id="6006" href="trees.plane-trees.html#6006" class="Bound">S</a> <a id="6008" href="trees.plane-trees.html#6008" class="Bound">T</a><a id="6009" class="Symbol">)</a> <a id="6011" class="Symbol">=</a>
  <a id="6015" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a>
    <a id="6042" class="Symbol">(</a> <a id="6044" href="lists.lists.html#1386" class="InductiveConstructor">cons</a>
      <a id="6055" class="Symbol">(</a> <a id="6057" href="trees.plane-trees.html#5786" class="Function">listed-plane-tree-full-binary-tree</a> <a id="6092" href="trees.plane-trees.html#6006" class="Bound">S</a><a id="6093" class="Symbol">)</a>
      <a id="6101" class="Symbol">(</a> <a id="6103" href="trees.plane-trees.html#2990" class="Function">unpack-listed-plane-tree</a> <a id="6128" class="Symbol">(</a><a id="6129" href="trees.plane-trees.html#5786" class="Function">listed-plane-tree-full-binary-tree</a> <a id="6164" href="trees.plane-trees.html#6008" class="Bound">T</a><a id="6165" class="Symbol">)))</a>

<a id="is-section-listed-plane-tree-full-binary-tree"></a><a id="6170" href="trees.plane-trees.html#6170" class="Function">is-section-listed-plane-tree-full-binary-tree</a> <a id="6216" class="Symbol">:</a>
  <a id="6220" href="foundation-core.sections.html#1194" class="Function">is-section</a>
    <a id="6235" class="Symbol">(</a> <a id="6237" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a><a id="6271" class="Symbol">)</a>
    <a id="6277" class="Symbol">(</a> <a id="6279" href="trees.plane-trees.html#5786" class="Function">listed-plane-tree-full-binary-tree</a><a id="6313" class="Symbol">)</a>
<a id="6315" href="trees.plane-trees.html#6170" class="Function">is-section-listed-plane-tree-full-binary-tree</a> <a id="6361" href="trees.full-binary-trees.html#767" class="InductiveConstructor">leaf-full-binary-tree</a> <a id="6383" class="Symbol">=</a>
  <a id="6387" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
<a id="6392" href="trees.plane-trees.html#6170" class="Function">is-section-listed-plane-tree-full-binary-tree</a>
  <a id="6440" class="Symbol">(</a> <a id="6442" href="trees.full-binary-trees.html#810" class="InductiveConstructor">join-full-binary-tree</a> <a id="6464" href="trees.plane-trees.html#6464" class="Bound">S</a> <a id="6466" href="trees.plane-trees.html#6466" class="Bound">T</a><a id="6467" class="Symbol">)</a> <a id="6469" class="Symbol">=</a>
  <a id="6473" href="foundation.action-on-identifications-binary-functions.html#1521" class="Function">ap-binary</a>
    <a id="6487" class="Symbol">(</a> <a id="6489" href="trees.full-binary-trees.html#810" class="InductiveConstructor">join-full-binary-tree</a><a id="6510" class="Symbol">)</a>
    <a id="6516" class="Symbol">(</a> <a id="6518" href="trees.plane-trees.html#6170" class="Function">is-section-listed-plane-tree-full-binary-tree</a> <a id="6564" href="trees.plane-trees.html#6464" class="Bound">S</a><a id="6565" class="Symbol">)</a>
    <a id="6571" class="Symbol">(</a> <a id="6573" class="Symbol">(</a> <a id="6575" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
        <a id="6586" class="Symbol">(</a> <a id="6588" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a><a id="6622" class="Symbol">)</a>
        <a id="6632" class="Symbol">(</a> <a id="6634" href="trees.plane-trees.html#3117" class="Function">is-section-unpack-listed-plane-tree</a> <a id="6670" class="Symbol">_))</a> <a id="6674" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
      <a id="6682" class="Symbol">(</a> <a id="6684" href="trees.plane-trees.html#6170" class="Function">is-section-listed-plane-tree-full-binary-tree</a> <a id="6730" href="trees.plane-trees.html#6466" class="Bound">T</a><a id="6731" class="Symbol">))</a>

<a id="is-retraction-listed-plane-tree-full-binary-tree"></a><a id="6735" href="trees.plane-trees.html#6735" class="Function">is-retraction-listed-plane-tree-full-binary-tree</a> <a id="6784" class="Symbol">:</a>
  <a id="6788" href="foundation-core.retractions.html#790" class="Function">is-retraction</a>
    <a id="6806" class="Symbol">(</a> <a id="6808" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a><a id="6842" class="Symbol">)</a>
    <a id="6848" class="Symbol">(</a> <a id="6850" href="trees.plane-trees.html#5786" class="Function">listed-plane-tree-full-binary-tree</a><a id="6884" class="Symbol">)</a>
<a id="6886" href="trees.plane-trees.html#6735" class="Function">is-retraction-listed-plane-tree-full-binary-tree</a> <a id="6935" class="Symbol">(</a><a id="6936" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="6959" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="6962" class="Symbol">)</a> <a id="6964" class="Symbol">=</a>
  <a id="6968" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
<a id="6973" href="trees.plane-trees.html#6735" class="Function">is-retraction-listed-plane-tree-full-binary-tree</a>
  <a id="7024" class="Symbol">(</a> <a id="7026" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="7049" class="Symbol">(</a><a id="7050" href="lists.lists.html#1386" class="InductiveConstructor">cons</a> <a id="7055" href="trees.plane-trees.html#7055" class="Bound">T</a> <a id="7057" href="trees.plane-trees.html#7057" class="Bound">l</a><a id="7058" class="Symbol">))</a> <a id="7061" class="Symbol">=</a>
  <a id="7065" class="Symbol">(</a> <a id="7067" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
    <a id="7074" class="Symbol">(</a> <a id="7076" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a><a id="7098" class="Symbol">)</a>
    <a id="7104" class="Symbol">(</a> <a id="7106" href="foundation.action-on-identifications-binary-functions.html#1521" class="Function">ap-binary</a>
      <a id="7122" class="Symbol">(</a> <a id="7124" href="lists.lists.html#1386" class="InductiveConstructor">cons</a><a id="7128" class="Symbol">)</a>
      <a id="7136" class="Symbol">(</a> <a id="7138" href="trees.plane-trees.html#6735" class="Function">is-retraction-listed-plane-tree-full-binary-tree</a> <a id="7187" href="trees.plane-trees.html#7055" class="Bound">T</a><a id="7188" class="Symbol">)</a>
      <a id="7196" class="Symbol">(</a> <a id="7198" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a>
        <a id="7209" class="Symbol">(</a> <a id="7211" href="trees.plane-trees.html#2990" class="Function">unpack-listed-plane-tree</a><a id="7235" class="Symbol">)</a>
        <a id="7245" class="Symbol">(</a> <a id="7247" href="trees.plane-trees.html#6735" class="Function">is-retraction-listed-plane-tree-full-binary-tree</a>
          <a id="7306" class="Symbol">(</a> <a id="7308" href="trees.plane-trees.html#2416" class="InductiveConstructor">make-listed-plane-tree</a> <a id="7331" href="trees.plane-trees.html#7057" class="Bound">l</a><a id="7332" class="Symbol">)))))</a>

<a id="is-equiv-full-binary-tree-listed-plane-tree"></a><a id="7339" href="trees.plane-trees.html#7339" class="Function">is-equiv-full-binary-tree-listed-plane-tree</a> <a id="7383" class="Symbol">:</a>
  <a id="7387" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="7396" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a>
<a id="7431" href="trees.plane-trees.html#7339" class="Function">is-equiv-full-binary-tree-listed-plane-tree</a> <a id="7475" class="Symbol">=</a>
  <a id="7479" href="foundation-core.equivalences.html#4851" class="Function">is-equiv-is-invertible</a>
    <a id="7506" class="Symbol">(</a> <a id="7508" href="trees.plane-trees.html#5786" class="Function">listed-plane-tree-full-binary-tree</a><a id="7542" class="Symbol">)</a>
    <a id="7548" class="Symbol">(</a> <a id="7550" href="trees.plane-trees.html#6170" class="Function">is-section-listed-plane-tree-full-binary-tree</a><a id="7595" class="Symbol">)</a>
    <a id="7601" class="Symbol">(</a> <a id="7603" href="trees.plane-trees.html#6735" class="Function">is-retraction-listed-plane-tree-full-binary-tree</a><a id="7651" class="Symbol">)</a>

<a id="equiv-full-binary-tree-listed-plane-tree"></a><a id="7654" href="trees.plane-trees.html#7654" class="Function">equiv-full-binary-tree-listed-plane-tree</a> <a id="7695" class="Symbol">:</a>
  <a id="7699" href="trees.plane-trees.html#2379" class="Datatype">listed-plane-tree</a> <a id="7717" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="7719" href="trees.full-binary-trees.html#731" class="Datatype">full-binary-tree</a>
<a id="7736" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="7740" href="trees.plane-trees.html#7654" class="Function">equiv-full-binary-tree-listed-plane-tree</a> <a id="7781" class="Symbol">=</a>
  <a id="7785" href="trees.plane-trees.html#5411" class="Function">full-binary-tree-listed-plane-tree</a>
<a id="7820" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="7824" href="trees.plane-trees.html#7654" class="Function">equiv-full-binary-tree-listed-plane-tree</a> <a id="7865" class="Symbol">=</a>
  <a id="7869" href="trees.plane-trees.html#7339" class="Function">is-equiv-full-binary-tree-listed-plane-tree</a>
</pre>