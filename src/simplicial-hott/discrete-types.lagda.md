```agda
{-# OPTIONS --rewriting #-}

module simplicial-hott.discrete-types where

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

open import foundation.fibers-of-maps


```

```agda

module _
  {l1 : Level} (X : UU l1)
  where

  is-discrete : Prop l1
  is-discrete = is-equiv-Prop {A = X} id-edge

module _
  {l : Level} {X : UU l}
  (X-discrete : type-Prop (is-discrete X))
  where

  discrete-arrow-equiv : X ≃ (Δ¹ → X)
  discrete-arrow-equiv = id-edge , X-discrete

  discrete-dom-cod-htpy' : dom {C = X} ~ cod {C = X}
  discrete-dom-cod-htpy' =
    inv-htpy (htpy-map-inv-equiv-retraction discrete-arrow-equiv dom-retraction-id)
      ∙h htpy-map-inv-equiv-retraction discrete-arrow-equiv cod-retraction-id

  discrete-dom-cod-htpy : dom {C = X} ~ cod {C = X}
  discrete-dom-cod-htpy f =
    discrete-dom-cod-htpy' f ∙ inv (discrete-dom-cod-htpy' (id-edge (f 1-Δ¹)))

  discrete-dom-cod-htpy-id : (x : X) → discrete-dom-cod-htpy (id-edge x) ＝ refl
  discrete-dom-cod-htpy-id x = right-inv (discrete-dom-cod-htpy' (id-edge x))

  discrete-hom-eq : {x y : X} → hom x y → x ＝ y
  discrete-hom-eq f = inv (hom-dom-eq f) ∙ discrete-dom-cod-htpy (ev-hom f) ∙ hom-cod-eq f
```
