```agda
{-# OPTIONS --rewriting #-}

module simplicial-hott.segal-types where

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions

open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.subtypes
open import foundation.equivalences

open import synthetic-homotopy-theory.joins-of-types

open import simplicial-hott.interval
```

### Segal types

```agda
module _
  {l : Level} (C : UU l)
  where

  is-segal-Prop : Prop l
  is-segal-Prop = is-equiv-Prop (restriction-to-Λ²₁ C)

  is-segal : UU l
  is-segal = type-Prop is-segal-Prop

Segal : (l : Level) → UU (lsuc l)
Segal l = Σ (UU l) is-segal

```

### The composition operation for Segal types

```agda

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
    {h : Λ²₁ → type-Segal C} → (i : Λ²₁) → fill-horn-Segal h (inclusion-Δ²-Λ²₁ i) ＝ h i
  compute-fill-horn {h = h} =
    htpy-eq (is-section-map-inv-equiv horn-triangle-equiv-Segal h)

  compose-edges-Segal :
    (g : Δ¹ → type-Segal C) (f : Δ¹ → type-Segal C) (compat : dom g ＝ cod f) →
      Δ¹ → type-Segal C
  compose-edges-Segal g f compat =
    diagonal-edge (fill-horn-Segal (composable-edges-to-horn g f compat))

  compose-hom-Segal : {x y z : type-Segal C} (g : hom y z) (f : hom x y) → hom x z
  compose-hom-Segal (g , prf , refl) (f , refl , refl) =
    compose-edges-Segal
      g
      f
      prf ,
      {! compute-fill-horn  !} ,
      {!   !}

  -- qqq :
  --   diagonal-edge ∘ fill-horn-Segal ∘ restriction-to-Λ²₁ (type-Segal C) ~ diagonal-edge
  -- qqq α = ap diagonal-edge (is-retraction-map-inv-equiv horn-triangle-equiv-Segal α)


```
