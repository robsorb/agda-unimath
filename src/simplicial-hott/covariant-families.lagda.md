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

  lem'' : {y i  : Δ¹} → (0-Δ¹ ∧Δ¹ (y ∨Δ¹ i)) ＝ 0-Δ¹
  lem'' {y = y} {i = i} = meet-bottom-left-Δ¹ (y ∨Δ¹ i)

  lem''' : (x y : Δ¹) → (x ∧Δ¹ (x ∨Δ¹ 0-Δ¹)) ＝ x
  lem''' = {!   !}

  action-clamped : (x y : Δ¹) → E (f (x ∧Δ¹ y)) → E (f x)
  action-clamped x y =
    tr (E ∘ f) (lem x y)
      ∘ action (clamped-f x y)
      ∘ tr (E ∘ f) (ap (x ∧Δ¹_) (inv (join-bottom-right-Δ¹ y)))

  eq-id-dom-cod-eq : (x : B) (g : Δ¹ → B) → g ＝ id-edge x → g 0-Δ¹ ＝ g 1-Δ¹
  eq-id-dom-cod-eq x g p = htpy-eq p 0-Δ¹ ∙ inv (htpy-eq p 1-Δ¹)

  eq-id-action : (x : B) (g : Δ¹ → B) → (p : g ＝ id-edge x) → action g ~ tr E (eq-id-dom-cod-eq x g p)
  eq-id-action x g refl = action-id x

  clamped-f-0-id : (y : Δ¹) → clamped-f 0-Δ¹ y ＝ id-edge (f 0-Δ¹)
  clamped-f-0-id y = eq-htpy λ x → ap f lem''

  clamped-f-0-dom-cod-eq :
    (y : Δ¹) →
      eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ y) (clamped-f-0-id y)
        ＝ ap f (lem'' ∙ inv lem'')
  clamped-f-0-dom-cod-eq y =
    equational-reasoning
      eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ y) (clamped-f-0-id y)
        ＝ ap f lem'' ∙ inv (ap f lem'')
          by
            ap-binary
              _∙_
              (ap (λ h → h 0-Δ¹) (is-section-eq-htpy λ i → ap f lem''))
              (ap inv (ap (λ h → h 1-Δ¹) (is-section-eq-htpy λ i → ap f lem'')))
        ＝ ap f lem'' ∙ ap f (inv lem'')
          by ap-binary _∙_ refl (inv (ap-inv f lem''))
        ＝ ap f (lem'' ∙ inv lem'')
          by inv (ap-concat f lem'' (inv lem''))

  action-clamped-0-0 : action (clamped-f 0-Δ¹ 0-Δ¹) ~ tr (E ∘ f) (lem'' ∙ inv lem'')
  action-clamped-0-0 =
    homotopy-reasoning
      action (clamped-f 0-Δ¹ 0-Δ¹)
        ~ tr E (eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ 0-Δ¹) (clamped-f-0-id 0-Δ¹))
          by eq-id-action (f 0-Δ¹) (clamped-f 0-Δ¹ 0-Δ¹) (clamped-f-0-id 0-Δ¹)
        ~ tr E (ap f (lem'' ∙ inv lem''))
          by (λ e → ap (λ p → tr E p e) (clamped-f-0-dom-cod-eq 0-Δ¹))
        ~ tr (E ∘ f) (lem'' ∙ inv lem'')
          by λ e → substitution-law-tr E f (lem'' ∙ inv lem'')

  action-clamped-0-0' : (y : Δ¹) → action-clamped 0-Δ¹ y ~ tr (E ∘ f) (meet-bottom-left-Δ¹ y)
  action-clamped-0-0' y = {!   !}

  lift1' : (x : Δ¹) → E (f 0-Δ¹) → E (f x)
  lift1' x = action-clamped x 0-Δ¹ ∘ tr (E ∘ f) (inv (meet-bottom-right-Δ¹ x))

  -- lift1'-0 : lift1' 0-Δ¹ ~ id
  -- lift1'-0 =
  --   homotopy-reasoning
  --     lift1' 0-Δ¹
  --       ~ tr (E ∘ f) (lem 0-Δ¹ 0-Δ¹) ∘ action (clamped-f 0-Δ¹ 0-Δ¹) ∘ tr (E ∘ f) (inv (lem' 0-Δ¹))
  --         by refl-htpy
  --       ~ tr (E ∘ f) (lem 0-Δ¹ 0-Δ¹) ∘ tr (E ∘ f) (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹)) ∘ tr (E ∘ f) (inv (lem' 0-Δ¹))
  --         by tr (E ∘ f) (lem 0-Δ¹ 0-Δ¹) ·l (action-clamped-0-0 ·r tr (E ∘ f) (inv (lem' 0-Δ¹)))
  --       ~ tr (E ∘ f) (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹) ∙ lem 0-Δ¹ 0-Δ¹) ∘ tr (E ∘ f) (inv (lem' 0-Δ¹))
  --         by (λ e → inv (tr-concat (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹)) (lem 0-Δ¹ 0-Δ¹) e)) ·r tr (E ∘ f) (inv (lem' 0-Δ¹))
  --       ~ tr (E ∘ f) (inv (lem' 0-Δ¹) ∙ (lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹) ∙ lem 0-Δ¹ 0-Δ¹))
  --         by (λ e → inv (tr-concat (inv (lem' 0-Δ¹)) ((lem'' 0-Δ¹ 0-Δ¹ ∙ inv (lem'' 0-Δ¹ 1-Δ¹) ∙ lem 0-Δ¹ 0-Δ¹)) e))
  --       ~ tr (E ∘ f) refl
  --         by (λ e → ap (λ p → tr (E ∘ f) p e) (eq-type-Prop (Id-Prop Δ¹-Set 0-Δ¹ 0-Δ¹)))
  --       ~ id
  --         by refl-htpy

  -- lift1 : E (f 0-Δ¹) → (x : Δ¹) → E (f x)
  -- lift1 e x = lift1' x e

  -- is-section-lift1 : dom-proj ∘ lift1 ~ id
  -- is-section-lift1 e = lift1'-0 e

  -- is-retraction-lift1 : (g : (x : Δ¹) → E (f x)) → g ~ lift1 (g 0-Δ¹)
  -- is-retraction-lift1 g x =
  --   equational-reasoning g x
  --     ＝ (tr (E ∘ f) (lem x x) ∘ action (clamped-f x x) ∘ tr (E ∘ f) (inv (lem''' x x))) (g x)
  --       by {!   !}
  --     ＝ (tr (E ∘ f) (lem x 0-Δ¹) ∘ action (clamped-f x 0-Δ¹) ∘ tr (E ∘ f) (inv (lem' x))) (g 0-Δ¹)
  --       by {!   !}
  --     ＝ lift1 (g 0-Δ¹) x
  --       by refl

```
