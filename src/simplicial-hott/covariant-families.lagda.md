```agda

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

module _
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  (action : (f : Δ¹ → B) → E (f 0-Δ¹) → E (f 1-Δ¹))
  (action-id : (x : B) → action (id-edge x) ~ id)
  (discrete-fibers : (b : B) → type-Prop (is-discrete (E b)))
  (f : Δ¹ → B)
  where

  dom-proj : ((i : Δ¹) → E (f i)) → E (f 0-Δ¹)
  dom-proj g = g 0-Δ¹

  extensions : E (f 0-Δ¹) → UU l2
  extensions = fiber dom-proj

  clamped-f : (x y i : Δ¹) → B
  clamped-f x y i = f (x ∧Δ¹ (y ∨Δ¹ i))

  lem : (x y : Δ¹) → (x ∧Δ¹ (y ∨Δ¹ 1-Δ¹)) ＝ x
  lem x y = ap (x ∧Δ¹_) (join-top-right-Δ¹ y) ∙ meet-top-right-Δ¹ x

  lem' : (x : Δ¹) → (x ∧Δ¹ (0-Δ¹ ∨Δ¹ 0-Δ¹)) ＝ 0-Δ¹
  lem' x = ap (x ∧Δ¹_) (join-bottom-right-Δ¹ 0-Δ¹) ∙ meet-bottom-right-Δ¹ x

  lem'' : (y i  : Δ¹) → (0-Δ¹ ∧Δ¹ (y ∨Δ¹ i)) ＝ 0-Δ¹
  lem'' y i = meet-bottom-left-Δ¹ (y ∨Δ¹ i)

  eq-id-dom-cod-eq : (x : B) (g : Δ¹ → B) → g ＝ id-edge x → g 0-Δ¹ ＝ g 1-Δ¹
  eq-id-dom-cod-eq x g p = htpy-eq p 0-Δ¹ ∙ inv (htpy-eq p 1-Δ¹)

  eq-id-action : (x : B) (g : Δ¹ → B) → (p : g ＝ id-edge x) → action g ~ tr E (eq-id-dom-cod-eq x g p)
  eq-id-action x g refl = action-id x

  clamped-f-0-0-id : clamped-f 0-Δ¹ 0-Δ¹ ＝ id-edge (f 0-Δ¹)
  clamped-f-0-0-id = eq-htpy (λ i → ap f (lem'' 0-Δ¹ i))

  clamped-f-0-0-dom-cod-eq :
    eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ 0-Δ¹) clamped-f-0-0-id
      ＝ ap f (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹))
  clamped-f-0-0-dom-cod-eq =
    equational-reasoning
      eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ 0-Δ¹) clamped-f-0-0-id
        ＝ ap f (lem'' 0-Δ¹ 0-Δ¹) ∙ inv (ap f (lem'' 0-Δ¹ 1-Δ¹))
          by
            ap-binary
              _∙_
              (ap (λ h → h 0-Δ¹) (is-section-eq-htpy λ i → ap f (meet-bottom-left-Δ¹ (0-Δ¹ ∨Δ¹ i))))
              (ap inv (ap (λ h → h 1-Δ¹) (is-section-eq-htpy λ i → ap f (meet-bottom-left-Δ¹ (0-Δ¹ ∨Δ¹ i)))))
        ＝ ap f (lem'' 0-Δ¹ 0-Δ¹) ∙ ap f (inv (lem'' 0-Δ¹ 1-Δ¹))
          by ap-binary _∙_ refl (inv (ap-inv f (lem'' 0-Δ¹ 1-Δ¹)))
        ＝ ap f (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹))
          by inv (ap-concat f (lem'' 0-Δ¹ 0-Δ¹) (inv (lem'' 0-Δ¹ 1-Δ¹)))

  action-clamped-0-0 : action (clamped-f 0-Δ¹ 0-Δ¹) ~ tr (E ∘ f) (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹))
  action-clamped-0-0 =
    homotopy-reasoning
      action (clamped-f 0-Δ¹ 0-Δ¹)
        ~ tr E (eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ 0-Δ¹) clamped-f-0-0-id)
          by eq-id-action (f 0-Δ¹) (clamped-f 0-Δ¹ 0-Δ¹) clamped-f-0-0-id
        ~ tr E (ap f (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹)))
          by (λ e → ap (λ p → tr E p e) clamped-f-0-0-dom-cod-eq)
        ~ tr (E ∘ f) (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹))
          by λ e → substitution-law-tr E f (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹))

  lift1' : (x : Δ¹) → E (f 0-Δ¹) → E (f x)
  lift1' x = tr (E ∘ f) (lem x 0-Δ¹) ∘ action (clamped-f x 0-Δ¹) ∘ tr (E ∘ f) (inv (lem' x))

  lift1'-0 : lift1' 0-Δ¹ ~ id
  lift1'-0 =
    homotopy-reasoning
      lift1' 0-Δ¹
        ~ tr (E ∘ f) (lem 0-Δ¹ 0-Δ¹) ∘ action (clamped-f 0-Δ¹ 0-Δ¹) ∘ tr (E ∘ f) (inv (lem' 0-Δ¹))
          by refl-htpy
        ~ tr (E ∘ f) (lem 0-Δ¹ 0-Δ¹) ∘ tr (E ∘ f) (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹)) ∘ tr (E ∘ f) (inv (lem' 0-Δ¹))
          by tr (E ∘ f) (lem 0-Δ¹ 0-Δ¹) ·l (action-clamped-0-0 ·r tr (E ∘ f) (inv (lem' 0-Δ¹)))
        ~ tr (E ∘ f) (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹) ∙ lem 0-Δ¹ 0-Δ¹) ∘ tr (E ∘ f) (inv (lem' 0-Δ¹))
          by (λ e → inv (tr-concat (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹)) (lem 0-Δ¹ 0-Δ¹) e)) ·r tr (E ∘ f) (inv (lem' 0-Δ¹))
        ~ tr (E ∘ f) (inv (lem' 0-Δ¹) ∙ (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹) ∙ lem 0-Δ¹ 0-Δ¹))
          by (λ e → inv (tr-concat (inv (lem' 0-Δ¹)) ((lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹) ∙ lem 0-Δ¹ 0-Δ¹)) e))
        ~ tr (E ∘ f) refl
          by (λ e → ap (λ p → tr (E ∘ f) p e) (eq-type-Prop (Id-Prop Δ¹-Set 0-Δ¹ 0-Δ¹)))
        ~ id
          by refl-htpy

  lift1 : (e : E (f 0-Δ¹)) → extensions e
  pr1 (lift1 e) x = lift1' x e
  pr2 (lift1 e) = lift1'-0 e

```
