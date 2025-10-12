```agda
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
    {h : Λ²₁ → type-Segal C} → (i : Λ²₁) → fill-horn-Segal h (Λ²₁-to-Δ² i) ＝ h i
  compute-fill-horn {h = h} =
    htpy-eq (is-section-map-inv-equiv horn-triangle-equiv-Segal h)

  compose-Segal : {x y z : type-Segal C} → (g : hom y z) → (f : hom x y) → hom x z
  pr1 (compose-Segal g f) i =
    fill-horn-Segal (composable-pair-to-horn f g) (diagonal-Δ² i)
  pr1 (pr2 (compose-Segal {x = x} g f)) =
    equational-reasoning
      fill-horn-Segal (composable-pair-to-horn f g) (diagonal-Δ² 0-Δ¹)
        ＝ fill-horn-Segal (composable-pair-to-horn f g) (Λ²₁-to-Δ² fist-vertex-Λ²₁)
          by
            ap
              (fill-horn-Segal (composable-pair-to-horn f g))
              (eq-type-subtype subtype-Δ² refl)
        ＝ composable-pair-to-horn f g (fist-vertex-Λ²₁)
          by compute-fill-horn fist-vertex-Λ²₁
        ＝ ev-hom f 0-Δ¹
          by compute-composable-pair-horn-bottom f g 0-Δ¹
        ＝ x
          by hom-dom-eq f
  pr2 (pr2 (compose-Segal {z = z} g f)) =
    equational-reasoning
      (fill-horn-Segal (composable-pair-to-horn f g) (diagonal-Δ² 1-Δ¹))
        ＝ (fill-horn-Segal (composable-pair-to-horn f g) (Λ²₁-to-Δ² last-vertex-Λ²₁))
          by
            ap
              (fill-horn-Segal (composable-pair-to-horn f g))
              (eq-type-subtype subtype-Δ² refl)
        ＝ composable-pair-to-horn f g (cod right-Λ²₁)
          by compute-fill-horn last-vertex-Λ²₁
        ＝ cod (ev-hom g)
          by compute-composable-pair-horn-right f g 1-Δ¹
        ＝ z
          by hom-cod-eq g

  -- comp-triangle :
  --   {x y z : type-Segal C} →
  --   (g : hom y z) → (f : hom x y) →
  --   triangle f g (compose-Segal g f)
  -- pr1 (comp-triangle g f) = fill-horn-Segal (composable-pair-to-horn f g)
  -- pr1 (pr2 (comp-triangle g f)) = {!   !}
  -- pr1 (pr2 (pr2 (comp-triangle g f))) = {!   !}
  -- pr2 (pr2 (pr2 (comp-triangle g f))) i = refl

  -- eq-triangle :
  --   {x y z : type-Segal C} →
  --   (f : hom x y) → (g : hom y z) → (h : hom x z) →
  --   triangle f g h → compose-Segal g f ＝ h
  -- eq-triangle = {!   !}

  degen-Δ² : (Δ¹ → type-Segal C) → Δ² → type-Segal C
  degen-Δ² f ((x , y) , prf) = f (x ∨Δ¹ y)

  -- bottom (degen-Δ² f) = f
  -- right (degen-Δ² f) = id
  -- diagonal (degen-Δ² f) = f

  -- idcomp : {x y : type-Segal C} → (f : hom x y) → compose-Segal f (id-hom x) ＝ f
  -- idcomp = {!   !}
```
