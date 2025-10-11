```agda

module simplicial where

```

```agda

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.cartesian-product-types
open import foundation-core.propositions
open import foundation.binary-relations
open import foundation.disjunction
open import foundation-core.sets
open import foundation.dependent-pair-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation.universe-levels
open import elementary-number-theory.natural-numbers
open import univalent-combinatorics.standard-finite-types
open import foundation.unit-type
open import order-theory.posets
open import order-theory.distributive-lattices
open import order-theory.top-elements-posets
open import order-theory.bottom-elements-posets
open import foundation.equivalences
open import synthetic-homotopy-theory.joins-of-types
open import foundation.action-on-identifications-functions
```

```agda

postulate
  Δ¹-Distributive-Lattice : Distributive-Lattice lzero lzero

Δ¹ : UU lzero
Δ¹ = type-Distributive-Lattice Δ¹-Distributive-Lattice

Δ¹-Poset : Poset lzero lzero
Δ¹-Poset = poset-Distributive-Lattice Δ¹-Distributive-Lattice

postulate
  is-set-Δ¹ : is-set Δ¹

Δ¹-Set : Set lzero
pr1 Δ¹-Set = Δ¹
pr2 Δ¹-Set = is-set-Δ¹

leq-Δ¹-Prop : Δ¹ → Δ¹ → Prop lzero
leq-Δ¹-Prop = leq-Distributive-Lattice-Prop Δ¹-Distributive-Lattice

geq-Δ¹-Prop : Δ¹ → Δ¹ → Prop lzero
geq-Δ¹-Prop x y = leq-Δ¹-Prop y x

_≤Δ¹_ : Δ¹ → Δ¹ → UU lzero
_≤Δ¹_ = type-Relation-Prop leq-Δ¹-Prop

_≥Δ¹_ : Δ¹ → Δ¹ → UU lzero
_≥Δ¹_ = type-Relation-Prop geq-Δ¹-Prop

Δ² : UU lzero
Δ² = total-space-Relation-Prop geq-Δ¹-Prop

postulate
  0-Δ¹ : Δ¹
  1-Δ¹ : Δ¹

  0-is-bottom-element-Δ¹ : is-bottom-element-Poset Δ¹-Poset 0-Δ¹
  1-is-top-element-Δ¹ : is-top-element-Poset Δ¹-Poset 1-Δ¹


Λ²₁-Relation-Prop : Relation-Prop lzero Δ¹
Λ²₁-Relation-Prop x y = Id-Prop Δ¹-Set x 1-Δ¹ ∨ Id-Prop Δ¹-Set y 0-Δ¹

Λ²₁-Relation : Relation lzero Δ¹
Λ²₁-Relation = type-Relation-Prop Λ²₁-Relation-Prop

Λ²₁ : UU lzero
Λ²₁ = total-space-Relation-Prop Λ²₁-Relation-Prop

Λ²₁-Relation-implies-Δ²-Relation : ((x , y) : Δ¹ × Δ¹)  →  Λ²₁-Relation x y → x ≥Δ¹ y
Λ²₁-Relation-implies-Δ²-Relation (x , y) =
  elim-disjunction
    (geq-Δ¹-Prop x y)
    (λ where refl → 1-is-top-element-Δ¹ y)
    (λ where refl → 0-is-bottom-element-Δ¹ x)

Λ²₁-to-Δ² : Λ²₁ → Δ²
Λ²₁-to-Δ² = tot Λ²₁-Relation-implies-Δ²-Relation

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

  hom-dom-eq : {x y : C} → (f : hom x y) → (ev-hom f 0-Δ¹ ＝ x)
  hom-dom-eq f = pr1 (pr2 f)

  hom-cod-eq : {x y : C} → (f : hom x y) → (ev-hom f 1-Δ¹ ＝ y)
  hom-cod-eq f = pr2 (pr2 f)

  id-morphism : (x : C) → hom x x
  id-morphism x = (λ _ → x) , refl , refl

module _
  {l : Level} (C : UU l)
  where

  restriction-to-Λ²₁ : (Δ² → C) → (Λ²₁ → C)
  restriction-to-Λ²₁ α = α ∘ Λ²₁-to-Δ²

  is-segal-Prop : Prop l
  is-segal-Prop = is-equiv-Prop restriction-to-Λ²₁

  is-segal : UU l
  is-segal = type-Prop is-segal-Prop

  composable-pair-to-horn : (x y z : C) → (f : hom x y) → (g : hom y z) → Λ²₁ → C
  composable-pair-to-horn x y z f g ((i , j) , p) =
    cogap-join
      (C)
      ((λ _ → ev-hom f i) ,
        (λ _ → ev-hom g j) ,
        λ (p , q) →
          equational-reasoning
            ev-hom f i
              ＝ ev-hom f 1-Δ¹
                by ap (ev-hom f) p
              ＝ y
                by hom-cod-eq f
              ＝ ev-hom g 0-Δ¹
                by inv (hom-dom-eq g)
              ＝ ev-hom g j
                by inv (ap (ev-hom g) q))
      (map-join-disjunction-Prop
        (Id-Prop Δ¹-Set i 1-Δ¹) (Id-Prop Δ¹-Set j 0-Δ¹) p)

module _
  {l : Level} {C : UU l} {is-segal-C : is-segal C}
  where

  comp-segal : (x y z : C) → (g : hom y z) → (f : hom x y) → hom x z
  comp-segal x y z g f = {!   !}

```
