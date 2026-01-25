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
open import foundation.sets

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

  lift1-eq : (e : E (f 0-Δ¹)) → lift1 e 0-Δ¹ ＝ e
  lift1-eq e =
    equational-reasoning
      action (clamp-edge f (bottom-Δ² 0-Δ¹)) e
        ＝ action (clamp-edge f (diagonal-Δ² 0-Δ¹)) e
          by
            ap
              (λ p → action (clamp-edge f ((0-Δ¹ , 0-Δ¹), p)) e)
              (eq-type-Prop (leq-Δ¹-Prop 0-Δ¹ 0-Δ¹))
        ＝ e
          by map-id 0-Δ¹ e

  lift2 : (g : (i : Δ¹) → E (f i)) (((x , y) , _) : Δ²) → E (f x)
  lift2 g t = action (clamp-edge f t) (g (pr2 (pr1 t)))

  dom-proj : ((i : Δ¹) → E (f i)) → E (f 0-Δ¹)
  dom-proj l = l 0-Δ¹

  extensions : (E (f 0-Δ¹)) → UU l2
  extensions e = fiber dom-proj e

  extensions-ext :
    {e : E (f 0-Δ¹)} (g g' : extensions e) (H : pr1 g ~ pr1 g') →
    (inv (pr2 g) ∙ H 0-Δ¹ ∙ pr2 g' ＝ refl) → g ＝ g'
  extensions-ext {e = e} g g' H p =
    eq-Eq-fiber
      dom-proj
      e
      (eq-htpy H)
      (equational-reasoning
        a ∙ b
          ＝ a' ∙ b
            by ap (λ G → (G 0-Δ¹) ∙ b) (is-section-eq-htpy H)
          ＝ c ∙ inv c ∙ (a' ∙ b)
            by ap (_∙ (a' ∙ b)) (inv (right-inv c))
          ＝ c ∙ (inv c ∙ (a' ∙ b))
            by assoc c (inv c) (a' ∙ b)
          ＝ c ∙ (inv c ∙ a' ∙ b)
            by ap (c ∙_) (inv (assoc (inv c) a' b ))
          ＝ c ∙ refl
            by ap (c ∙_) p
          ＝ c
            by right-unit)
      where
        a = ap (λ l → l 0-Δ¹) (eq-htpy H)
        a' = H 0-Δ¹
        b = pr2 g'
        c = pr2 g

  lift2-square-0 :
    (g : (i : Δ¹) → E (f i)) → (x : Δ¹) →
      lift2 g (square-Δ² x 0-Δ¹) ＝ lift1 (g 0-Δ¹) x
  lift2-square-0 g x =
    ap
      (λ ((y , p)) → action (clamp-edge f ((x , y) , p)) (g y))
      (eq-pair-Σ (meet-bottom-right-Δ¹ x) (eq-type-Prop (leq-Δ¹-Prop 0-Δ¹ x)))

  lift2-diagonal :
    (g : (i : Δ¹) → E (f i)) (x : Δ¹) →
      lift2 g (square-Δ² x 1-Δ¹) ＝ lift2 g (diagonal-Δ² x)
  lift2-diagonal g x =
    ap
      (λ (y , p) → action (clamp-edge f ((x , y), p)) (g y))
      (eq-pair-Σ (meet-top-right-Δ¹ x) (eq-type-Prop (leq-Δ¹-Prop x x)))

  is-cov : (e : E (f 0-Δ¹)) → is-contr (extensions e)
  pr1 (is-cov e) = lift1 e , lift1-eq e
  pr2 (is-cov e) (g , refl) =
    extensions-ext
      (lift1 e , lift1-eq e)
      (g , refl)
      (λ x →
        inv (lift2-square-0 g x)
          ∙ discrete-dom-cod-htpy (discrete-fibers (f x)) (λ y → lift2 g (square-Δ² x y))
          ∙ lift2-diagonal g x
          ∙ map-id x (g x))
        -- discrete-hom-eq
        --   (discrete-fibers (f x))
        --   ((λ y → lift2 g (square-Δ² x y)) ,
        --     (lift2-square-0 g x ∙ ap (action (clamp-edge f (bottom-Δ² x))) p) ,
        --     (lift2-diagonal g x ∙ map-id x (g x))))
      {!   !}


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
