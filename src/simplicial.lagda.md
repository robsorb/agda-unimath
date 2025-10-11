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
open import foundation.injective-maps
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.subtypes
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

subtype-Δ² : subtype lzero (Δ¹ × Δ¹)
subtype-Δ² (i , j ) = geq-Δ¹-Prop i j

Δ² : UU lzero
Δ² = type-subtype subtype-Δ²

composite-edge-Δ² : Δ¹ → Δ²
composite-edge-Δ² i = (i , i) , refl-leq-Poset Δ¹-Poset i

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

  hom-dom-eq : {x y : C} → (f : hom x y) → (dom (ev-hom f) ＝ x)
  hom-dom-eq f = pr1 (pr2 f)

  hom-cod-eq : {x y : C} → (f : hom x y) → (cod (ev-hom f) ＝ y)
  hom-cod-eq f = pr2 (pr2 f)

  id-hom : (x : C) → hom x x
  id-hom x = (λ _ → x) , refl , refl



left-morphism-Λ²₁ : Δ¹ → Λ²₁
left-morphism-Λ²₁ i = (i , 0-Δ¹) , inr-disjunction refl

right-morphism-Λ²₁ : Δ¹ → Λ²₁
right-morphism-Λ²₁ i = (1-Δ¹ , i) , inl-disjunction refl

fist-vertex-Λ²₁ : Λ²₁
fist-vertex-Λ²₁ = dom left-morphism-Λ²₁

last-vertex-Λ²₁ : Λ²₁
last-vertex-Λ²₁ = cod right-morphism-Λ²₁



module _
  {l : Level} (C : UU l)
  where

  restriction-to-Λ²₁ : (Δ² → C) → (Λ²₁ → C)
  restriction-to-Λ²₁ α = α ∘ Λ²₁-to-Δ²

  is-segal-Prop : Prop l
  is-segal-Prop = is-equiv-Prop restriction-to-Λ²₁

  is-segal : UU l
  is-segal = type-Prop is-segal-Prop


module _
  {l : Level} {C : UU l}
  {x y z : C} (f : hom x y) (g : hom y z)
  where
  abstract
    composable-pair-to-horn : Λ²₁ → C
    composable-pair-to-horn ((i , j) , p) =
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

    compute-composable-pair-horn-left :
      composable-pair-to-horn ∘ left-morphism-Λ²₁ ~ ev-hom f
    compute-composable-pair-horn-left i =
      {! compute-inr-cogap-join  !}

    compute-composable-pair-horn-right :
      composable-pair-to-horn ∘ right-morphism-Λ²₁ ~ ev-hom g
    compute-composable-pair-horn-right i =
      {! compute-inr-cogap-join  !}



Segal : (l : Level) → UU (lsuc l)
Segal l = Σ (UU l) is-segal

module _
  {l : Level}
  where

  type-Segal : Segal l → UU l
  type-Segal C = pr1 C

  is-segal-Segal : (C : Segal l) → is-segal (type-Segal C)
  is-segal-Segal C = pr2 C

module _
  {l : Level} {C : Segal l}
  where

  horn-triangle-equiv-Segal : (Δ² → type-Segal C) ≃ (Λ²₁ → type-Segal C)
  pr1 horn-triangle-equiv-Segal = restriction-to-Λ²₁ (type-Segal C)
  pr2 horn-triangle-equiv-Segal = is-segal-Segal C

  fill-horn-Segal : (Λ²₁ → type-Segal C) → Δ² → type-Segal C
  fill-horn-Segal = map-inv-equiv horn-triangle-equiv-Segal

  compute-fill-horn :
    {h : Λ²₁ → type-Segal C} → (i : Λ²₁) → fill-horn-Segal h (Λ²₁-to-Δ² i) ＝ h i
  compute-fill-horn {h = h} =
    htpy-eq (is-section-map-inv-equiv horn-triangle-equiv-Segal h)

  comp-Segal : (x y z : type-Segal C) → (g : hom y z) → (f : hom x y) → hom x z
  pr1 (comp-Segal x y z g f) i =
    fill-horn-Segal (composable-pair-to-horn f g) (composite-edge-Δ² i)
  pr1 (pr2 (comp-Segal x y z g f)) =
    equational-reasoning
      fill-horn-Segal (composable-pair-to-horn f g) (composite-edge-Δ² 0-Δ¹)
        ＝ fill-horn-Segal (composable-pair-to-horn f g) (Λ²₁-to-Δ² fist-vertex-Λ²₁)
          by
            ap
              (fill-horn-Segal (composable-pair-to-horn f g))
              (eq-type-subtype subtype-Δ² refl)
        ＝ composable-pair-to-horn f g (fist-vertex-Λ²₁)
          by compute-fill-horn fist-vertex-Λ²₁
        ＝ ev-hom f 0-Δ¹
          by compute-composable-pair-horn-left f g 0-Δ¹
        ＝ x
          by hom-dom-eq f
  pr2 (pr2 (comp-Segal x y z g f)) =
    equational-reasoning
      (fill-horn-Segal (composable-pair-to-horn f g) (composite-edge-Δ² 1-Δ¹))
        ＝ (fill-horn-Segal (composable-pair-to-horn f g) (Λ²₁-to-Δ² last-vertex-Λ²₁))
          by
            ap
              (fill-horn-Segal (composable-pair-to-horn f g))
              (eq-type-subtype subtype-Δ² refl)
        ＝ composable-pair-to-horn f g (cod right-morphism-Λ²₁)
          by compute-fill-horn last-vertex-Λ²₁
        ＝ cod (ev-hom g)
          by compute-composable-pair-horn-right f g 1-Δ¹
        ＝ z
          by hom-cod-eq g

```
