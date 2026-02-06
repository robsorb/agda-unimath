# Covariant Families

```agda
{-# OPTIONS --rewriting #-}

module simplicial-hott.covariant-families where

```

```agda
open import foundation.universe-levels
open import foundation.propositions
open import foundation.identity-types
open import foundation.dependent-pair-types
open import foundation.contractible-types
open import foundation.function-extensionality
open import foundation-core.equality-dependent-pair-types
open import foundation.action-on-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.homotopies
open import foundation.function-types
open import foundation.equivalences
open import foundation.sets
open import foundation-core.transport-along-identifications
open import foundation.transport-along-identifications
open import foundation.whiskering-homotopies-composition

open import simplicial-hott.interval
open import simplicial-hott.discrete-types

open import foundation.fibers-of-maps


```

## Definition

```agda

module _
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  where

  section-over-edge : (f : Δ¹ → B) → UU l2
  section-over-edge f = (i : Δ¹) → E (f i)

  dom-section : (f : Δ¹ → B) → (s : section-over-edge f) → E (f 0-Δ¹)
  dom-section f s = s 0-Δ¹

  lifts-over-edge : (f : Δ¹ → B) (e : E (f 0-Δ¹)) → UU l2
  lifts-over-edge f = fiber (dom-section f)

  is-covariant : Prop (l1 ⊔ l2)
  is-covariant = Π-Prop (Δ¹ → B) (λ f → is-equiv-Prop (dom-section f))
```

## Discrete families with action on fibers are covariant

```agda
module _
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  (action : (f : Δ¹ → B) → E (f 0-Δ¹) → E (f 1-Δ¹))
  (action-id : (x : B) → action (id-edge x) ~ id)
  (f : Δ¹ → B)
  where

  clamp-action : (x y : Δ¹) → E (f (x ∧Δ¹ y)) → E (f x)
  clamp-action x y = action (clamp-edge f x y)

  lift-edge-action : E (f 0-Δ¹) → section-over-edge E f
  lift-edge-action e i = clamp-action i 0-Δ¹ e

  lift-square-action : (g : section-over-edge E f) → (x y : Δ¹) → E (f x)
  lift-square-action g x y = clamp-action x y (g (x ∧Δ¹ y))

  is-retraction-dom-action : dom-section E f ∘ lift-edge-action ~ id
  is-retraction-dom-action = action-id (f 0-Δ¹)

module _
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  (action : (f : Δ¹ → B) → E (f 0-Δ¹) → E (f 1-Δ¹))
  (action-id : (x : B) → action (id-edge x) ~ id)
  (discrete-fibers : (b : B) → type-Prop (is-discrete (E b)))
  where

  is-section-dom-discrete-action :
    (f : Δ¹ → B) → (g : section-over-edge E f) →
      lift-edge-action E action action-id f (dom-section E f g) ＝ g
  is-section-dom-discrete-action f g =
    eq-htpy (λ x →
      equational-reasoning
        lift-edge-action E action action-id f (g 0-Δ¹) x
          ＝ clamp-action E action action-id f x 1-Δ¹ (g x)
            by discrete-dom-cod-htpy
              (discrete-fibers (f x))
              (lift-square-action E action action-id f g x)
          ＝ g x
            by action-id (f x) (g x))

  is-covariant-discrete-action : type-Prop (is-covariant E)
  pr1 (is-covariant-discrete-action f) =
    lift-edge-action E action action-id f , is-retraction-dom-action E action action-id f
  pr2 (is-covariant-discrete-action f) =
    lift-edge-action E action action-id f , is-section-dom-discrete-action f

```
