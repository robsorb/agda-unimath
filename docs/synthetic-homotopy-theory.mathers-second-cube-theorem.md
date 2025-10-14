# Mather's second cube theorem

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="synthetic-homotopy-theory.mathers-second-cube-theorem.html" class="Module">synthetic-homotopy-theory.mathers-second-cube-theorem</a> <a id="102" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.commuting-cubes-of-maps.html" class="Module">foundation.commuting-cubes-of-maps</a>
<a id="264" class="Keyword">open</a> <a id="269" class="Keyword">import</a> <a id="276" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="foundation.commuting-triangles-of-maps.html" class="Module">foundation.commuting-triangles-of-maps</a>
<a id="364" class="Keyword">open</a> <a id="369" class="Keyword">import</a> <a id="376" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="408" class="Keyword">open</a> <a id="413" class="Keyword">import</a> <a id="420" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="461" class="Keyword">open</a> <a id="466" class="Keyword">import</a> <a id="473" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="497" class="Keyword">open</a> <a id="502" class="Keyword">import</a> <a id="509" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="582" class="Keyword">open</a> <a id="587" class="Keyword">import</a> <a id="594" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="620" class="Keyword">open</a> <a id="625" class="Keyword">import</a> <a id="632" href="foundation.functoriality-dependent-function-types.html" class="Module">foundation.functoriality-dependent-function-types</a>
<a id="682" class="Keyword">open</a> <a id="687" class="Keyword">import</a> <a id="694" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="740" class="Keyword">open</a> <a id="745" class="Keyword">import</a> <a id="752" href="foundation.functoriality-fibers-of-maps.html" class="Module">foundation.functoriality-fibers-of-maps</a>
<a id="792" class="Keyword">open</a> <a id="797" class="Keyword">import</a> <a id="804" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="826" class="Keyword">open</a> <a id="831" class="Keyword">import</a> <a id="838" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="864" class="Keyword">open</a> <a id="869" class="Keyword">import</a> <a id="876" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="904" class="Keyword">open</a> <a id="909" class="Keyword">import</a> <a id="916" href="foundation.pullbacks.html" class="Module">foundation.pullbacks</a>
<a id="937" class="Keyword">open</a> <a id="942" class="Keyword">import</a> <a id="949" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="974" class="Keyword">open</a> <a id="979" class="Keyword">import</a> <a id="986" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="1029" class="Keyword">open</a> <a id="1034" class="Keyword">import</a> <a id="1041" href="foundation.universal-property-dependent-pair-types.html" class="Module">foundation.universal-property-dependent-pair-types</a>
<a id="1092" class="Keyword">open</a> <a id="1097" class="Keyword">import</a> <a id="1104" href="foundation.universal-property-pullbacks.html" class="Module">foundation.universal-property-pullbacks</a>
<a id="1144" class="Keyword">open</a> <a id="1149" class="Keyword">import</a> <a id="1156" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="1184" class="Keyword">open</a> <a id="1189" class="Keyword">import</a> <a id="1196" href="synthetic-homotopy-theory.cocones-under-spans.html" class="Module">synthetic-homotopy-theory.cocones-under-spans</a>
<a id="1242" class="Keyword">open</a> <a id="1247" class="Keyword">import</a> <a id="1254" href="synthetic-homotopy-theory.dependent-cocones-under-spans.html" class="Module">synthetic-homotopy-theory.dependent-cocones-under-spans</a>
<a id="1310" class="Keyword">open</a> <a id="1315" class="Keyword">import</a> <a id="1322" href="synthetic-homotopy-theory.dependent-universal-property-pushouts.html" class="Module">synthetic-homotopy-theory.dependent-universal-property-pushouts</a>
<a id="1386" class="Keyword">open</a> <a id="1391" class="Keyword">import</a> <a id="1398" href="synthetic-homotopy-theory.descent-data-pushouts.html" class="Module">synthetic-homotopy-theory.descent-data-pushouts</a>
<a id="1446" class="Keyword">open</a> <a id="1451" class="Keyword">import</a> <a id="1458" href="synthetic-homotopy-theory.equivalences-descent-data-pushouts.html" class="Module">synthetic-homotopy-theory.equivalences-descent-data-pushouts</a>
<a id="1519" class="Keyword">open</a> <a id="1524" class="Keyword">import</a> <a id="1531" href="synthetic-homotopy-theory.flattening-lemma-pushouts.html" class="Module">synthetic-homotopy-theory.flattening-lemma-pushouts</a>
<a id="1583" class="Keyword">open</a> <a id="1588" class="Keyword">import</a> <a id="1595" href="synthetic-homotopy-theory.pushouts.html" class="Module">synthetic-homotopy-theory.pushouts</a>
<a id="1630" class="Keyword">open</a> <a id="1635" class="Keyword">import</a> <a id="1642" href="synthetic-homotopy-theory.universal-property-pushouts.html" class="Module">synthetic-homotopy-theory.universal-property-pushouts</a>
</pre>
</details>

## Idea

{{#concept "Mather's second cube theorem" Disambiguation="for types"}} states
that every base change of a [pushout](synthetic-homotopy-theory.pushouts.md)
square is a pushout. In other words, if we are given a
[commuting cube](foundation.commuting-cubes-of-maps.md) where the bottom face is
a pushout and the vertical faces are [pullbacks](foundation-core.pullbacks.md)

```text
  ∙ ----------------> ∙
  |⌟\ ⌟               |⌟\
  |  \                |  \
  |   ∨               |   ∨
  |     ∙ ----------------> ∙
  |     | ⌟           |     |
  ∨     |             ∨     |
  ∙ ----|-----------> ∙     |
    \   |               \   |
     \  |                \  |
      ∨ ∨               ⌜ ∨ ∨
        ∙ ----------------> ∙,
```

then the top face is also a pushout.

## Theorem

```text
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (left : f ∘ hA ~ hB ∘ f')
  (back : g ∘ hA ~ hC ∘ g')
  (front : h ∘ hB ~ hD ∘ h')
  (right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top left back front right bottom)
  where

  mathers-second-cube-theorem :
    universal-property-pushout f g (h , k , bottom) →
    universal-property-pullback h hD (hB , h' , front) →
    universal-property-pullback k hD (hC , k' , right) →
    universal-property-pullback f hB (hA , f' , left) →
    universal-property-pullback g hC (hA , g' , back) →
    universal-property-pushout f' g' (h' , k' , top)
  mathers-second-cube-theorem po-bottom pb-front pb-right pb-left pb-back =
    universal-property-pushout-top-universal-property-pushout-bottom-cube-equiv
      _ _ _ _
      f' g' h' k'
      ( equiv-tot e-left ∘e inv-equiv-total-fiber' hA)
      ( inv-equiv-total-fiber' hB)
      ( inv-equiv-total-fiber' hC)
      ( inv-equiv-total-fiber' hD)
      ( top)
      ( λ x →
        eq-pair-Σ (left x) (inv-compute-tr-self-fiber' hB (f' x , left x)))
      ( λ x →
        eq-pair-Σ (back x) {!   !})
      ( λ x →
        eq-pair-Σ (front x) (inv-compute-tr-self-fiber' hD (h' x , front x)))
      ( λ x →
        eq-pair-Σ (right x) (inv-compute-tr-self-fiber' hD (k' x , right x)))
      ( {!   !})
      ( {!   !})
      ( flattening-lemma-descent-data-pushout
        ( f)
        ( g)
        ( h , k , bottom)
        ( ( fiber' hB) ,
          ( fiber' hC) ,
          ( λ s →
            ( inv-equiv (e-right (g s))) ∘e
            ( equiv-tr (fiber' hD) (bottom s)) ∘e
            ( e-front (f s))))
        ( fiber' hD)
        ( ( e-front) ,
          ( e-right) ,
          {!   !})
        ( po-bottom))
    where
      e-left =
        fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
          f hB (hA , f' , left) pb-left
      e-front =
        fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
          h hD (hB , h' , front) pb-front
      e-right =
        fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
          k hD (hC , k' , right) pb-right
```

## See also

- Mather's second cube theorem is the
  [unstraightened](foundation.type-duality.md) version of the
  [flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md)
- The
  [descent property for pushouts](synthetic-homotopy-theory.descent-property-pushouts.md).

## External links

- [Mather's Second Cube Theorem](https://kerodon.net/tag/011H) on Kerodon
