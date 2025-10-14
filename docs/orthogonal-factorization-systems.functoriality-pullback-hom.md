# Functoriality of the pullback-hom

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="orthogonal-factorization-systems.functoriality-pullback-hom.html" class="Module">orthogonal-factorization-systems.functoriality-pullback-hom</a> <a id="113" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.action-on-identifications-binary-functions.html" class="Module">foundation.action-on-identifications-binary-functions</a>
<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="foundation.bicomposition-functions.html" class="Module">foundation.bicomposition-functions</a>
<a id="341" class="Keyword">open</a> <a id="346" class="Keyword">import</a> <a id="353" href="foundation.composition-algebra.html" class="Module">foundation.composition-algebra</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="481" class="Keyword">open</a> <a id="486" class="Keyword">import</a> <a id="493" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="528" class="Keyword">open</a> <a id="533" class="Keyword">import</a> <a id="540" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="566" class="Keyword">open</a> <a id="571" class="Keyword">import</a> <a id="578" href="foundation.functoriality-morphisms-arrows.html" class="Module">foundation.functoriality-morphisms-arrows</a>
<a id="620" class="Keyword">open</a> <a id="625" class="Keyword">import</a> <a id="632" href="foundation.functoriality-pullbacks.html" class="Module">foundation.functoriality-pullbacks</a>
<a id="667" class="Keyword">open</a> <a id="672" class="Keyword">import</a> <a id="679" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="701" class="Keyword">open</a> <a id="706" class="Keyword">import</a> <a id="713" href="foundation.homotopies-morphisms-arrows.html" class="Module">foundation.homotopies-morphisms-arrows</a>
<a id="752" class="Keyword">open</a> <a id="757" class="Keyword">import</a> <a id="764" href="foundation.homotopies-morphisms-cospan-diagrams.html" class="Module">foundation.homotopies-morphisms-cospan-diagrams</a>
<a id="812" class="Keyword">open</a> <a id="817" class="Keyword">import</a> <a id="824" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="850" class="Keyword">open</a> <a id="855" class="Keyword">import</a> <a id="862" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="890" class="Keyword">open</a> <a id="895" class="Keyword">import</a> <a id="902" href="foundation.morphisms-cospan-diagrams.html" class="Module">foundation.morphisms-cospan-diagrams</a>
<a id="939" class="Keyword">open</a> <a id="944" class="Keyword">import</a> <a id="951" href="foundation.postcomposition-functions.html" class="Module">foundation.postcomposition-functions</a>
<a id="988" class="Keyword">open</a> <a id="993" class="Keyword">import</a> <a id="1000" href="foundation.precomposition-functions.html" class="Module">foundation.precomposition-functions</a>
<a id="1036" class="Keyword">open</a> <a id="1041" class="Keyword">import</a> <a id="1048" href="foundation.retracts-of-maps.html" class="Module">foundation.retracts-of-maps</a>
<a id="1076" class="Keyword">open</a> <a id="1081" class="Keyword">import</a> <a id="1088" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="1115" class="Keyword">open</a> <a id="1120" class="Keyword">import</a> <a id="1127" href="foundation.whiskering-higher-homotopies-composition.html" class="Module">foundation.whiskering-higher-homotopies-composition</a>
<a id="1179" class="Keyword">open</a> <a id="1184" class="Keyword">import</a> <a id="1191" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="1237" class="Keyword">open</a> <a id="1242" class="Keyword">import</a> <a id="1249" href="orthogonal-factorization-systems.pullback-hom.html" class="Module">orthogonal-factorization-systems.pullback-hom</a>
</pre>
</details>

## Idea

The construction of the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is functorial.
I.e., we have a functorial action on pairs of
[morphisms of arrows](foundation.morphisms-arrows.md)

```text
  (α : f' ⇒ f, β : g ⇒ g') ↦ α ⋔ β : (f ⋔ g) ⇒ (f' ⋔ g')
```

We construct this action as the restriction of a more general action on
morphisms of _exponentiated cospan diagrams_ of the form:

```text
            - ∘ f           g ∘ -
   (B → Y) ------> (A → Y) <------ (A → X)
      |               |               |
      |               |               |
      ∨     - ∘ f'    ∨    g' ∘ -     ∨
  (B' → Y') ----> (A' → Y') <---- (A' → X').
```

In general, such morphisms need not necessarily come from pairs of morphisms of
the underlying arrows.

This gives us a commuting triangle of functors

```text
  [pairs of arrows of types] ---> [exponentiated cospan diagrams]
                     \                 /
                      \               /
                       ∨             ∨
                      [arrows of types]
```

where the functorial action of the pullback-hom on arrows is the left vertical
arrow.

### Functoriality of pullback-homs on exponentiated cospan diagrams

By [functoriality of pullbacks](foundation.functoriality-pullbacks.md), there is
a functor that maps cospan diagrams of the form

```text
           - ∘ f           g ∘ -
  (B → Y) ------> (A → Y) <------ (A → X)
```

to the type of [morphisms of arrows](foundation.morphisms-arrows.md) from `f` to
`g`

```text
  f ⇒ g -------> A → X
    | ⌟            |
    |              | g ∘ -
    ∨              ∨
  B → Y -------> A → Y.
          - ∘ f
```

For every morphism of cospan diagrams of this form

```text
            - ∘ f           g ∘ -
   (B → Y) ------> (A → Y) <------ (A → X)
      |               |               |
      |               |               |
      ∨     - ∘ f'    ∨    g' ∘ -     ∨
  (B' → Y') ----> (A' → Y') <---- (A' → X')
```

we thus have a commuting cube given by the functorial action of pullbacks

```text
                 f ⇒ g -----------> A → X
                /  | ⌟             /  |
              /    |             /    |
            ∨      |           ∨      |
      f' ⇒ g' ---------> A' → X'      |
         | ⌟       ∨        |         ∨
         |       B → Y ---- | ----> A → Y
         |      /           |      /
         |    /             |    /
         ∨  ∨               ∨  ∨
      B' → Y' ---------> A' → Y'.
```

This is the
{{#concept "functorial action of pullback-homs on exponentiated cospan diagrams"}}.

### Functoriality of pullback-homs on pairs of morphisms of arrows

There is a bifunctor mapping pairs of arrows to cospan diagrams of the form
described above. This bifunctor is contravariant in the left argument and
covariant in the right. I.e., a pair of morphisms of arrows `f' ⇒ f` and
`g ⇒ g'` gives a morphism of cospan diagrams

```text
            - ∘ f           g ∘ -
   (B → Y) ------> (A → Y) <------ (A → X)
      |               |               |
      |               |               |
      ∨     - ∘ f'    ∨    g' ∘ -     ∨
  (B' → Y') ----> (A' → Y') <---- (A' → X')
```

that is given componentwise by
[bicomposition of functions](foundation.bicomposition-functions.md).

Restricting along this bifunctor, the functorial action of pullbacks extends to
a bifunctorial action that we call the
{{#concept "bifunctoriality of the pullback-hom" Disambiguation="on types"}}.

Given a pair of maps `f` and `g`, the pullback-hom produces a new map
`f ⋔ g : (B → X) → (f ⇒ g)`, and given morphisms of arrows `f' ⇒ f` and
`g ⇒ g'`, we obtain a morphism of pullback-hom arrows

```text
     (B → X) -----> (B' → X')
        |               |
  f ⋔ g |               | f' ⋔ g'
        ∨               ∨
     (f ⇒ g) -----> (f' ⇒ g').
```

## Definitions

### Functorial action on maps of the pullback-hom

<pre class="Agda"><a id="5214" class="Keyword">module</a> <a id="5221" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5221" class="Module">_</a>
  <a id="5225" class="Symbol">{</a><a id="5226" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5226" class="Bound">l11</a> <a id="5230" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5230" class="Bound">l12</a> <a id="5234" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5234" class="Bound">l13</a> <a id="5238" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5238" class="Bound">l14</a> <a id="5242" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5242" class="Bound">l21</a> <a id="5246" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5246" class="Bound">l22</a> <a id="5250" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5250" class="Bound">l23</a> <a id="5254" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5254" class="Bound">l24</a> <a id="5258" class="Symbol">:</a> <a id="5260" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5265" class="Symbol">}</a>
  <a id="5269" class="Symbol">{</a><a id="5270" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5270" class="Bound">A1</a> <a id="5273" class="Symbol">:</a> <a id="5275" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5278" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5226" class="Bound">l11</a><a id="5281" class="Symbol">}</a> <a id="5283" class="Symbol">{</a><a id="5284" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5284" class="Bound">B1</a> <a id="5287" class="Symbol">:</a> <a id="5289" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5292" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5230" class="Bound">l12</a><a id="5295" class="Symbol">}</a> <a id="5297" class="Symbol">{</a><a id="5298" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5298" class="Bound">X1</a> <a id="5301" class="Symbol">:</a> <a id="5303" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5306" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5234" class="Bound">l13</a><a id="5309" class="Symbol">}</a> <a id="5311" class="Symbol">{</a><a id="5312" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5312" class="Bound">Y1</a> <a id="5315" class="Symbol">:</a> <a id="5317" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5320" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5238" class="Bound">l14</a><a id="5323" class="Symbol">}</a>
  <a id="5327" class="Symbol">{</a><a id="5328" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5328" class="Bound">A2</a> <a id="5331" class="Symbol">:</a> <a id="5333" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5336" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5242" class="Bound">l21</a><a id="5339" class="Symbol">}</a> <a id="5341" class="Symbol">{</a><a id="5342" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5342" class="Bound">B2</a> <a id="5345" class="Symbol">:</a> <a id="5347" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5350" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5246" class="Bound">l22</a><a id="5353" class="Symbol">}</a> <a id="5355" class="Symbol">{</a><a id="5356" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5356" class="Bound">X2</a> <a id="5359" class="Symbol">:</a> <a id="5361" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5364" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5250" class="Bound">l23</a><a id="5367" class="Symbol">}</a> <a id="5369" class="Symbol">{</a><a id="5370" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5370" class="Bound">Y2</a> <a id="5373" class="Symbol">:</a> <a id="5375" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5378" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5254" class="Bound">l24</a><a id="5381" class="Symbol">}</a>
  <a id="5385" class="Symbol">(</a><a id="5386" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5386" class="Bound">f1</a> <a id="5389" class="Symbol">:</a> <a id="5391" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5270" class="Bound">A1</a> <a id="5394" class="Symbol">→</a> <a id="5396" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5284" class="Bound">B1</a><a id="5398" class="Symbol">)</a> <a id="5400" class="Symbol">(</a><a id="5401" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5401" class="Bound">g1</a> <a id="5404" class="Symbol">:</a> <a id="5406" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5298" class="Bound">X1</a> <a id="5409" class="Symbol">→</a> <a id="5411" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5312" class="Bound">Y1</a><a id="5413" class="Symbol">)</a>
  <a id="5417" class="Symbol">(</a><a id="5418" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5418" class="Bound">f2</a> <a id="5421" class="Symbol">:</a> <a id="5423" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5328" class="Bound">A2</a> <a id="5426" class="Symbol">→</a> <a id="5428" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5342" class="Bound">B2</a><a id="5430" class="Symbol">)</a> <a id="5432" class="Symbol">(</a><a id="5433" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5433" class="Bound">g2</a> <a id="5436" class="Symbol">:</a> <a id="5438" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5356" class="Bound">X2</a> <a id="5441" class="Symbol">→</a> <a id="5443" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5370" class="Bound">Y2</a><a id="5445" class="Symbol">)</a>
  <a id="5449" class="Keyword">where</a>

  <a id="5458" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5458" class="Function">map-pullback-hom</a> <a id="5475" class="Symbol">:</a>
    <a id="5481" href="foundation.morphisms-cospan-diagrams.html#795" class="Function">hom-cospan-diagram</a>
      <a id="5506" class="Symbol">(</a> <a id="5508" href="foundation.functoriality-morphisms-arrows.html#3187" class="Function">cospan-diagram-hom-arrow</a> <a id="5533" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5418" class="Bound">f2</a> <a id="5536" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5433" class="Bound">g2</a><a id="5538" class="Symbol">)</a>
      <a id="5546" class="Symbol">(</a> <a id="5548" href="foundation.functoriality-morphisms-arrows.html#3187" class="Function">cospan-diagram-hom-arrow</a> <a id="5573" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5386" class="Bound">f1</a> <a id="5576" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5401" class="Bound">g1</a><a id="5578" class="Symbol">)</a> <a id="5580" class="Symbol">→</a>
    <a id="5586" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="5596" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5418" class="Bound">f2</a> <a id="5599" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5433" class="Bound">g2</a> <a id="5602" class="Symbol">→</a>
    <a id="5608" href="foundation.morphisms-arrows.html#1639" class="Function">hom-arrow</a> <a id="5618" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5386" class="Bound">f1</a> <a id="5621" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5401" class="Bound">g1</a>
  <a id="5626" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5458" class="Function">map-pullback-hom</a> <a id="5643" class="Symbol">=</a>
    <a id="5649" href="foundation.functoriality-pullbacks.html#1505" class="Function">map-pullback-cone</a>
      <a id="5673" class="Symbol">(</a> <a id="5675" href="foundation.functoriality-morphisms-arrows.html#3187" class="Function">cospan-diagram-hom-arrow</a> <a id="5700" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5418" class="Bound">f2</a> <a id="5703" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5433" class="Bound">g2</a><a id="5705" class="Symbol">)</a>
      <a id="5713" class="Symbol">(</a> <a id="5715" href="foundation.functoriality-morphisms-arrows.html#3187" class="Function">cospan-diagram-hom-arrow</a> <a id="5740" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5386" class="Bound">f1</a> <a id="5743" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5401" class="Bound">g1</a><a id="5745" class="Symbol">)</a>
      <a id="5753" class="Symbol">(</a> <a id="5755" href="orthogonal-factorization-systems.pullback-hom.html#12385" class="Function">pullback-cone-hom-arrow-pullback-hom</a> <a id="5792" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5418" class="Bound">f2</a> <a id="5795" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5433" class="Bound">g2</a><a id="5797" class="Symbol">)</a>
      <a id="5805" class="Symbol">(</a> <a id="5807" href="orthogonal-factorization-systems.pullback-hom.html#12385" class="Function">pullback-cone-hom-arrow-pullback-hom</a> <a id="5844" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5386" class="Bound">f1</a> <a id="5847" href="orthogonal-factorization-systems.functoriality-pullback-hom.html#5401" class="Bound">g1</a><a id="5849" class="Symbol">)</a>
</pre>