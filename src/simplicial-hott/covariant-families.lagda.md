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

  sections-over-edge : (f : Δ¹ → B) → UU l2
  sections-over-edge f = (i : Δ¹) → E (f i)

  dom-section : (f : Δ¹ → B) → (s : sections-over-edge f) → E (f 0-Δ¹)
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
  (discrete-fibers : (b : B) → type-Prop (is-discrete (E b)))
  (f : Δ¹ → B)
  where

  f-clamped : Δ¹ → Δ¹ → Δ¹ → B
  f-clamped x y i = f (x ∧Δ¹ (y ∨Δ¹ i))

  action-clamped : (x y : Δ¹) → E (f (x ∧Δ¹ y)) → E (f x)
  action-clamped x y = action (f-clamped x y)

  lift : E (f 0-Δ¹) → sections-over-edge E f
  lift e i = action-clamped i 0-Δ¹ e

  lift2 : (g : sections-over-edge E f) → (x y : Δ¹) → E (f x)
  lift2 g x y = action-clamped x y (g (x ∧Δ¹ y))

  is-retraction-dom : dom-section E f ∘ lift ~ id
  is-retraction-dom = action-id (f 0-Δ¹)

  is-section-dom : (g : sections-over-edge E f) → lift (dom-section E f g) ＝ g
  is-section-dom g =
    eq-htpy (λ x →
      equational-reasoning
        lift (g 0-Δ¹) x
          ＝ action-clamped x 1-Δ¹ (g x)
            by discrete-dom-cod-htpy (discrete-fibers (f x)) (lift2 g x)
          ＝ g x
            by action-id (f x) (g x))

module _
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  (action : (f : Δ¹ → B) → E (f 0-Δ¹) → E (f 1-Δ¹))
  (action-id : (x : B) → action (id-edge x) ~ id)
  (discrete-fibers : (b : B) → type-Prop (is-discrete (E b)))
  where

  is-covariant-discrete-action : type-Prop (is-covariant E)
  pr1 (is-covariant-discrete-action f) = lift E action action-id discrete-fibers f , is-retraction-dom E action action-id discrete-fibers f
  pr2 (is-covariant-discrete-action f) = lift E action action-id discrete-fibers f , is-section-dom E action action-id discrete-fibers f

```
