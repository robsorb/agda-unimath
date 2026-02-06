# Covariant Families

```agda
{-# OPTIONS --rewriting #-}

module simplicial-hott.cocartesian-families where

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
open import foundation.precomposition-dependent-functions

open import orthogonal-factorization-systems.orthogonal-maps

open import simplicial-hott.interval
open import simplicial-hott.discrete-types
open import simplicial-hott.covariant-families

open import foundation.fibers-of-maps


```

TODOS

- [x] Inner families
- [ ] Cocartesian morphisms
- [ ] Composition of dependent morphisms in inner families
- [ ] Characterisation of cocartesian families in terms of composition
- [ ] Uniqueness of composites
- [ ] Lift triangle to show one side
- [ ] Pushforward of triangles
- [ ] Characterize equalities of lifts
- [ ] Prove other side

```agda

module _ {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  where

  is-inner : UU (l1 ⊔ l2)
  is-inner = (α : Δ² → B) → is-equiv (precomp-Π inclusion-Δ²-Λ²₁ (E ∘ α))

  composable-sections-over-square : (α : Δ¹ → Δ¹ → B) → UU l2
  composable-sections-over-square α =
    Σ (section-over-edge E (λ x → α x 0-Δ¹))
      (λ f → Σ (section-over-edge E (λ y → α 1-Δ¹ y))
        (λ g → cod-section E f ＝ dom-section E g))



module _ {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  (inner-E : is-inner E)
  where

  is-cocartesian-edge : (f : Δ¹ → B) (g : (i : Δ¹) → E (f i)) → UU {!   !}
  is-cocartesian-edge f g = {!   !}
```
