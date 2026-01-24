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
open import foundation.homotopies
open import foundation.function-types
open import foundation.equivalences

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

module _
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  (f : Δ¹ → B)
  (action : {x y : B} (g : hom x y) → E x → E y)
  (action-id : (x : B) → action (id-hom x) ~ id)
  (discrete-fibers : (b : B) → type-Prop (is-discrete (E b)))
  where

  map-id : (i : Δ¹) → action (clamp-edge f (diagonal-Δ² i)) ~ id
  map-id i e =
    equational-reasoning
      action (clamp-edge f (diagonal-Δ² i)) e
        ＝ action (id-hom (f i)) e
          by ap (λ x → action x e) (clamp-edge-diagonal f i)
        ＝ e
          by action-id (f i) e

  lift1 : (E (f 0-Δ¹)) → (x : Δ¹) → E (f x)
  lift1 e x = action (clamp-edge f (bottom-Δ² x)) e

  lift2 : (g : (i : Δ¹) → E (f i)) (((x , y) , _) : Δ²) → E (f x)
  lift2 g t = action (clamp-edge f t) (g (pr2 (pr1 t)))

  dom-proj : ((i : Δ¹) → E (f i)) → E (f 0-Δ¹)
  dom-proj l = l 0-Δ¹

  extensions : (E (f 0-Δ¹)) → UU l2
  extensions e = fiber dom-proj e

  -- is-cov : (e : E (f 0-Δ¹)) → is-contr (extensions e)
  -- pr1 (is-cov e) = lift1 e , map-id 0-Δ¹ e
  -- pr2 (is-cov e) (g , p) =
  --   eq-Eq-fiber
  --     dom-proj
  --     e
  --     (eq-htpy λ i → ap (λ e' → lift1 e' i) (inv p) ∙ (discr (f i) (lift2 g i) ∙ map-id i (g i)) )
  --     (equational-reasoning
  --       (ap (λ l → l 0-Δ¹) (eq-htpy (λ i → ap (λ e' → lift1 e' i) (inv p) ∙ (discr (f i) (lift2 g i) ∙ map-id i (g i)))) ∙ p)
  --         ＝ (htpy-eq (eq-htpy (λ i → ap (λ e' → lift1 e' i) (inv p) ∙ (discr (f i) (lift2 g i) ∙ map-id i (g i)))) 0-Δ¹ ∙ p)
  --           by refl
  --         ＝ ap (λ e' → lift1 e' 0-Δ¹) (inv p) ∙ (discr (f 0-Δ¹) (lift2 g 0-Δ¹) ∙ map-id 0-Δ¹ (g 0-Δ¹)) ∙ p
  --           by ap (λ q → (q 0-Δ¹) ∙ p) (is-section-eq-htpy (λ i → ap (λ e' → lift1 e' i) (inv p) ∙ (discr (f i) (lift2 g i) ∙ map-id i (g i))))
  --         ＝ ap (λ e' → lift1 e' 0-Δ¹) (inv p) ∙ (refl ∙ map-id 0-Δ¹ (g 0-Δ¹)) ∙ p
  --           by ap
  --             (λ d →
  --                ap (λ e' → lift1 e' 0-Δ¹) (inv p) ∙ (d ∙ map-id 0-Δ¹ (g 0-Δ¹)) ∙ p)
  --                (discr-id (f 0-Δ¹) (lift1 (g 0-Δ¹) 0-Δ¹))
  --         ＝ (ap (λ e' → lift1 e' 0-Δ¹) (inv p) ∙ map-id 0-Δ¹ (g 0-Δ¹)) ∙ p
  --           by refl
  --         ＝ (map-id 0-Δ¹ e ∙ ap (λ x → x) (inv p)) ∙  p
  --           by ap (λ q → q ∙ p) (inv-nat-htpy (map-id 0-Δ¹) (inv p))
  --         ＝ map-id 0-Δ¹ e ∙ inv p ∙  p
  --           by ap (λ q → map-id 0-Δ¹ e ∙ q ∙  p) (ap-id (inv p))
  --         ＝ map-id 0-Δ¹ e ∙ refl
  --           by left-inv p
  --         ＝ map-id 0-Δ¹ e
  --           by right-unit)
      -- equational-reasoning lift1 e i
      --   ＝ lift1 (g 0-Δ¹) i
      --     by ap (λ e' → lift1 e' i) (inv p)
      --   ＝ lift2 g i 0-Δ¹
      --     by refl
      --   ＝ lift2 g i i
      --     by discr (f i) (lift2 g i)
      --   ＝ g i
      --     by map-id i (g i)) {!   !}
    -- eq-pair-Σ (eq-htpy λ i → {!   !}) {!   !}

```
