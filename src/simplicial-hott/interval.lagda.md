```agda

module simplicial-hott.interval where

```

```agda

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.cartesian-product-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.functoriality-dependent-pair-types

open import foundation.binary-relations
open import foundation.disjunction

open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.intersections-subtypes
open import foundation.equivalences
open import foundation.fibers-of-maps

open import order-theory.posets
open import order-theory.distributive-lattices
open import order-theory.top-elements-posets
open import order-theory.bottom-elements-posets

open import synthetic-homotopy-theory.joins-of-types
```

## Postulates

We postulate an interval type, which is a bounded (_we may want to drop this
assumption to allow for a model in cubical spaces_) distributive.

```agda

postulate
  Δ¹-Distributive-Lattice : Distributive-Lattice lzero lzero

Δ¹ : UU lzero
Δ¹ = type-Distributive-Lattice Δ¹-Distributive-Lattice

Δ¹-Poset : Poset lzero lzero
Δ¹-Poset = poset-Distributive-Lattice Δ¹-Distributive-Lattice


postulate
  0-Δ¹ : Δ¹
  1-Δ¹ : Δ¹

  0-is-bottom-element-Δ¹ : is-bottom-element-Poset Δ¹-Poset 0-Δ¹
  1-is-top-element-Δ¹ : is-top-element-Poset Δ¹-Poset 1-Δ¹

```

## Definitions

The relation on the interval.

```agda
Δ¹-Set : Set lzero
Δ¹-Set = set-Poset Δ¹-Poset

is-set-Δ¹ : is-set Δ¹
is-set-Δ¹ = is-set-type-Set Δ¹-Set

leq-Δ¹-Prop : Δ¹ → Δ¹ → Prop lzero
leq-Δ¹-Prop = leq-Distributive-Lattice-Prop Δ¹-Distributive-Lattice

geq-Δ¹-Prop : Δ¹ → Δ¹ → Prop lzero
geq-Δ¹-Prop x y = leq-Δ¹-Prop y x

_≤Δ¹_ : Δ¹ → Δ¹ → UU lzero
_≤Δ¹_ = type-Relation-Prop leq-Δ¹-Prop

_≥Δ¹_ : Δ¹ → Δ¹ → UU lzero
_≥Δ¹_ = type-Relation-Prop geq-Δ¹-Prop

_∧Δ¹_ : Δ¹ → Δ¹ → Δ¹
_∧Δ¹_ = meet-Distributive-Lattice Δ¹-Distributive-Lattice

_∨Δ¹_ : Δ¹ → Δ¹ → Δ¹
_∨Δ¹_ = join-Distributive-Lattice Δ¹-Distributive-Lattice

```

```agda
module _
  {l : Level} {C : UU l}
  where

  dom : (Δ¹ → C) → C
  dom f = f 0-Δ¹

  cod : (Δ¹ → C) → C
  cod f = f 1-Δ¹

  hom : (x y : C) → UU l
  hom x y = Σ (Δ¹ → C) (λ f → (dom f ＝ x) × (cod f ＝ y))

  ev-hom : {x y : C} → hom x y → Δ¹ → C
  ev-hom = pr1

  hom-dom-eq : {x y : C} → (f : hom x y) → (dom (ev-hom f) ＝ x)
  hom-dom-eq f = pr1 (pr2 f)

  hom-cod-eq : {x y : C} → (f : hom x y) → (cod (ev-hom f) ＝ y)
  hom-cod-eq f = pr2 (pr2 f)

  id-hom : (x : C) → hom x x
  id-hom x = (λ _ → x) , refl , refl
```

### The 2-1-horn

```agda
bottom-edge-square-subtype : subtype lzero (Δ¹ × Δ¹)
bottom-edge-square-subtype (_ , y) = Id-Prop Δ¹-Set y 0-Δ¹

right-edge-square-subtype : subtype lzero (Δ¹ × Δ¹)
right-edge-square-subtype (x , _) = Id-Prop Δ¹-Set x 1-Δ¹

Λ²₁-subtype : subtype lzero (Δ¹ × Δ¹)
Λ²₁-subtype = union-subtype right-edge-square-subtype bottom-edge-square-subtype

Λ²₁ : UU lzero
Λ²₁ = type-subtype Λ²₁-subtype

Λ²₁-Relation-implies-Δ²-Relation : (x : Δ¹ × Δ¹)  → type-Prop (Λ²₁-subtype x) → pr1 x ≥Δ¹ pr2 x
Λ²₁-Relation-implies-Δ²-Relation (x , y) =
  elim-disjunction
    (geq-Δ¹-Prop x y)
    (λ where refl → 1-is-top-element-Δ¹ y)
    (λ where refl → 0-is-bottom-element-Δ¹ x)

bottom-Λ²₁ : Δ¹ → Λ²₁
bottom-Λ²₁ i =
  map-inr-union-subtype
    right-edge-square-subtype
    bottom-edge-square-subtype
    ((i , 0-Δ¹) , refl)

right-Λ²₁ : Δ¹ → Λ²₁
right-Λ²₁ i =
  map-inl-union-subtype
    right-edge-square-subtype
    bottom-edge-square-subtype
    ((1-Δ¹ , i) , refl)

fist-vertex-Λ²₁ : Λ²₁
fist-vertex-Λ²₁ = dom bottom-Λ²₁

last-vertex-Λ²₁ : Λ²₁
last-vertex-Λ²₁ = cod right-Λ²₁
```

### 2-Simplex

```agda
subtype-Δ² : subtype lzero (Δ¹ × Δ¹)
subtype-Δ² (i , j ) = geq-Δ¹-Prop i j

Δ² : UU lzero
Δ² = type-subtype subtype-Δ²

Λ²₁-to-Δ² : Λ²₁ → Δ²
Λ²₁-to-Δ² = tot Λ²₁-Relation-implies-Δ²-Relation

bottom-Δ² : Δ¹ → Δ²
bottom-Δ² = Λ²₁-to-Δ² ∘ bottom-Λ²₁

right-Δ² : Δ¹ → Δ²
right-Δ² = Λ²₁-to-Δ² ∘ right-Λ²₁

diagonal-Δ² : Δ¹ → Δ²
diagonal-Δ² i = (i , i) , refl-leq-Poset Δ¹-Poset i

module _
  {l : Level} {C : UU l}
  where

  bottom-edge : (Δ² → C) → Δ¹ → C
  bottom-edge α = α ∘ bottom-Δ²

  right-edge : (Δ² → C) → Δ¹ → C
  right-edge α = α ∘ right-Δ²

  diagonal-edge : (Δ² → C) → Δ¹ → C
  diagonal-edge α = α ∘ diagonal-Δ²

  dom-diagonal : (α : Δ² → C) → dom (diagonal-edge α) ＝ dom (bottom-edge α)
  dom-diagonal α = ap α (eq-type-subtype subtype-Δ² refl)

  cod-diagonal : (α : Δ² → C) → cod (diagonal-edge α) ＝ cod (right-edge α)
  cod-diagonal α = ap α (eq-type-subtype subtype-Δ² refl)

```

### Horn fillers

```agda
module _
  {l : Level} (C : UU l)
  where
  restriction-to-Λ²₁ : (Δ² → C) → (Λ²₁ → C)
  restriction-to-Λ²₁ α = α ∘ Λ²₁-to-Δ²

module _
  {l : Level} {C : UU l}
  (h : Λ²₁ → C)
  where
  horn-filler : UU l
  horn-filler = fiber (restriction-to-Λ²₁ C) h

  simplex-horn-filler : horn-filler → Δ² → C
  simplex-horn-filler = pr1

  horn-filler-restricts-bottom : (α : horn-filler) → bottom-edge (simplex-horn-filler α) ~ h ∘ bottom-Λ²₁
  horn-filler-restricts-bottom = {!   !}

  horn-filler-restricts-right : (α : horn-filler) → right-edge (simplex-horn-filler α) ~ h ∘ right-Λ²₁
  horn-filler-restricts-right = {!   !}
```

### Mapping composable pairs of morphisms to horns

```agda

module _
  {l : Level} {C : UU l}
  {x y z : C} (f : hom x y) (g : hom y z)
  where

  cocone-composable-pair-to-horn :
    union-cocone right-edge-square-subtype bottom-edge-square-subtype C
  pr1 cocone-composable-pair-to-horn ((_ , y) , _) = ev-hom g y
  pr1 (pr2 cocone-composable-pair-to-horn) ((x , _), _) = ev-hom f x
  pr2 (pr2 cocone-composable-pair-to-horn) ((x , y) , (refl , refl)) =
    hom-dom-eq g ∙ inv (hom-cod-eq f)

  composable-pair-to-horn : Λ²₁ → C
  composable-pair-to-horn =
    cogap-union
      right-edge-square-subtype bottom-edge-square-subtype
      cocone-composable-pair-to-horn

  compute-composable-pair-horn-bottom :
    composable-pair-to-horn ∘ bottom-Λ²₁ ~ ev-hom f
  compute-composable-pair-horn-bottom x =
    compute-inr-cogap-union
      right-edge-square-subtype
      bottom-edge-square-subtype
      cocone-composable-pair-to-horn
      ((x , 0-Δ¹) , refl)

  compute-composable-pair-horn-right :
    composable-pair-to-horn ∘ right-Λ²₁ ~ ev-hom g
  compute-composable-pair-horn-right x =
    compute-inl-cogap-union
      right-edge-square-subtype
      bottom-edge-square-subtype
      cocone-composable-pair-to-horn
      ((1-Δ¹ , x) , refl)

```

### Commuting triangles of morphisms

```agda

module _
  {l : Level} {C : UU l}
  {x y z : C} (f : hom x y) (g : hom y z) (h : hom x z)
  where

  is-triangle : UU l
  is-triangle =
    Σ (Δ² → C)
      (λ α →
        (bottom-edge α ~ ev-hom f) ×
        (right-edge α ~ ev-hom g) ×
        (diagonal-edge α ~ ev-hom h))

module _
  {l : Level} {C : UU l}
  {x y z : C} (f : hom x y) (g : hom y z)
  where

  triangles : UU l
  triangles = Σ (hom x z) (is-triangle f g)

module _
  {l : Level} {C : UU l}
  where
  horn-filler-to-triangle :
    {x y z : C} (f : hom x y) (g : hom y z) → horn-filler (composable-pair-to-horn f g) → triangles f g
  horn-filler-to-triangle {x = x} {z = z} f g α =
    ( (diagonal-edge (pr1 α) , -- Diagonal hom
      (equational-reasoning    -- Domain
        dom (diagonal-edge (pr1 α))
          ＝ dom (bottom-edge (pr1 α))
            by dom-diagonal (pr1 α)
          ＝ dom (ev-hom f)
            by α-bottom 0-Δ¹
          ＝ x
            by hom-dom-eq f) ,
      (equational-reasoning   -- Codomain
        cod (diagonal-edge (pr1 α))
          ＝ cod (right-edge (pr1 α))
            by cod-diagonal (pr1 α)
          ＝ cod (ev-hom g)
            by α-right 1-Δ¹
          ＝ z
            by hom-cod-eq g)) ,

      (pr1 α ,                -- Triangle
        α-bottom ,
        α-right ,
        refl-htpy))
    where
      α-bottom : bottom-edge (pr1 α) ~ ev-hom f
      α-bottom =
        horn-filler-restricts-bottom (composable-pair-to-horn f g) α ∙h
          compute-composable-pair-horn-bottom f g

      α-right : right-edge (pr1 α) ~ ev-hom g
      α-right =
        horn-filler-restricts-right (composable-pair-to-horn f g) α ∙h
          compute-composable-pair-horn-right f g


  -- triangle-to-horn-filler : triangle → horn-filler (composable-pair-to-horn f g)
  -- triangle-to-horn-filler = {!   !}
```
