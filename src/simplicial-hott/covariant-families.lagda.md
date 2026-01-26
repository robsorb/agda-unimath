# Covariant Families

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

  private
    lem0 : {x y : Δ¹} → (x ∧Δ¹ (y ∨Δ¹ 1-Δ¹)) ＝ x
    lem0 {x = x} {y = y} = ap (x ∧Δ¹_) (join-top-right-Δ¹ y) ∙ meet-top-right-Δ¹ x

    lem1 : {x y : Δ¹} → (x ∧Δ¹ y) ＝ (x ∧Δ¹ (y ∨Δ¹ 0-Δ¹))
    lem1 {x = x} {y = y} = ap (x ∧Δ¹_) (inv (join-bottom-right-Δ¹ y))

    lem2 : {y i  : Δ¹} → (0-Δ¹ ∧Δ¹ (y ∨Δ¹ i)) ＝ 0-Δ¹
    lem2 {y = y} {i = i} = meet-bottom-left-Δ¹ (y ∨Δ¹ i)

    lem3 : {x i : Δ¹} → (x ∧Δ¹ (1-Δ¹ ∨Δ¹ i)) ＝ x
    lem3 {x = x} {i = i} = ap (x ∧Δ¹_) (join-top-left-Δ¹ i) ∙ meet-top-right-Δ¹ x

  clamped-f : (x y i : Δ¹) → B
  clamped-f x y i = f (x ∧Δ¹ (y ∨Δ¹ i))

  action-clamped : (x y : Δ¹) → E (f (x ∧Δ¹ y)) → E (f x)
  action-clamped x y = tr (E ∘ f) lem0 ∘ action (clamped-f x y) ∘ tr (E ∘ f) lem1

  eq-id-dom-cod-eq : (x : B) (g : Δ¹ → B) → g ＝ id-edge x → g 0-Δ¹ ＝ g 1-Δ¹
  eq-id-dom-cod-eq x g p = htpy-eq p 0-Δ¹ ∙ inv (htpy-eq p 1-Δ¹)

  eq-id-action : (x : B) (g : Δ¹ → B) → (p : g ＝ id-edge x) → action g ~ tr E (eq-id-dom-cod-eq x g p)
  eq-id-action x g refl = action-id x

  clamped-f-0-id : (y : Δ¹) → clamped-f 0-Δ¹ y ＝ id-edge (f 0-Δ¹)
  clamped-f-0-id y = eq-htpy λ x → ap f lem2

  clamped-f-0-dom-cod-eq :
    (y : Δ¹) →
      eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ y) (clamped-f-0-id y)
        ＝ ap f (lem2 ∙ inv lem2)
  clamped-f-0-dom-cod-eq y =
    equational-reasoning
      eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ y) (clamped-f-0-id y)
        ＝ ap f lem2 ∙ inv (ap f lem2)
          by
            ap-binary
              _∙_
              (ap (λ h → h 0-Δ¹) (is-section-eq-htpy λ i → ap f lem2))
              (ap inv (ap (λ h → h 1-Δ¹) (is-section-eq-htpy λ i → ap f lem2)))
        ＝ ap f lem2 ∙ ap f (inv lem2)
          by ap-binary _∙_ refl (inv (ap-inv f lem2))
        ＝ ap f (lem2 ∙ inv lem2)
          by inv (ap-concat f lem2 (inv lem2))

  action-clamped-0' : (y : Δ¹) → action (clamped-f 0-Δ¹ y) ~ tr (E ∘ f) (lem2 ∙ inv lem2)
  action-clamped-0' y =
    homotopy-reasoning
      action (clamped-f 0-Δ¹ y)
        ~ tr E (eq-id-dom-cod-eq (f 0-Δ¹) (clamped-f 0-Δ¹ y) (clamped-f-0-id y))
          by eq-id-action (f 0-Δ¹) (clamped-f 0-Δ¹ y) (clamped-f-0-id y)
        ~ tr E (ap f (lem2 ∙ inv lem2))
          by (λ e → ap (λ p → tr E p e) (clamped-f-0-dom-cod-eq y))
        ~ tr (E ∘ f) (lem2 ∙ inv lem2)
          by λ e → substitution-law-tr E f (lem2 ∙ inv lem2)

  action-clamped-0 : (y : Δ¹) → action-clamped 0-Δ¹ y ~ tr (E ∘ f) (meet-bottom-left-Δ¹ y)
  action-clamped-0 y =
    homotopy-reasoning
      tr (E ∘ f) lem0 ∘ action (clamped-f 0-Δ¹ y) ∘ tr (E ∘ f) lem1
        ~ tr (E ∘ f) lem0 ∘ tr (E ∘ f) (lem2 ∙ inv lem2) ∘ tr (E ∘ f) lem1
          by tr (E ∘ f) lem0 ·l (action-clamped-0' y ·r tr (E ∘ f) lem1)
        ~ (tr (E ∘ f) ((lem2 ∙ inv lem2) ∙ lem0)) ∘ tr (E ∘ f) lem1
          by inv-htpy (λ e → tr-concat (lem2 ∙ inv lem2) lem0 e) ·r tr (E ∘ f) lem1
        ~ tr (E ∘ f) (lem1 ∙ ((lem2 ∙ inv lem2) ∙ lem0))
          by inv-htpy (λ e → tr-concat lem1 ((lem2 ∙ inv lem2) ∙ lem0) e)
        ~ tr (E ∘ f) (meet-bottom-left-Δ¹ y)
        by λ e → ap (λ p → tr (E ∘ f) p e) (eq-type-Prop (Id-Prop Δ¹-Set (0-Δ¹ ∧Δ¹ y) 0-Δ¹))

  lift1' : (x : Δ¹) → E (f 0-Δ¹) → E (f x)
  lift1' x = action-clamped x 0-Δ¹ ∘ tr (E ∘ f) (inv (meet-bottom-right-Δ¹ x))

  lift1'-0 : lift1' 0-Δ¹ ~ id
  lift1'-0 =
    homotopy-reasoning
      lift1' 0-Δ¹
        ~ tr (E ∘ f) (meet-bottom-left-Δ¹ 0-Δ¹) ∘ tr (E ∘ f) (inv (meet-bottom-right-Δ¹ 0-Δ¹))
          by action-clamped-0 0-Δ¹ ·r tr (E ∘ f) (inv (meet-bottom-right-Δ¹ 0-Δ¹))
        ~ tr (E ∘ f) (inv (meet-bottom-right-Δ¹ 0-Δ¹) ∙ meet-bottom-left-Δ¹ 0-Δ¹)
          by inv-htpy (λ e → tr-concat (inv (meet-bottom-right-Δ¹ 0-Δ¹)) (meet-bottom-left-Δ¹ 0-Δ¹) e)
        ~ id
          by λ e → ap (λ p → tr (E ∘ f) p e) (eq-type-Prop (Id-Prop Δ¹-Set 0-Δ¹ 0-Δ¹))

  lift1 : E (f 0-Δ¹) → (x : Δ¹) → E (f x)
  lift1 e x = lift1' x e

  is-section-lift1 : dom-section E f ∘ lift1 ~ id
  is-section-lift1 e = lift1'-0 e

  clamped-f-1-id : (x : Δ¹) → clamped-f x 1-Δ¹ ＝ id-edge (f x)
  clamped-f-1-id x = eq-htpy λ i → ap f lem3

  clamped-f-1-dom-cod-eq :
    (x : Δ¹) →
      eq-id-dom-cod-eq (f x) (clamped-f x 1-Δ¹) (clamped-f-1-id x)
        ＝ ap f (lem3 ∙ inv lem3)
  clamped-f-1-dom-cod-eq x =
    equational-reasoning
      eq-id-dom-cod-eq (f x) (clamped-f x 1-Δ¹) (clamped-f-1-id x)
        ＝ ap f lem3 ∙ inv (ap f lem3)
          by
            ap-binary
              _∙_
              (ap (λ h → h 0-Δ¹) (is-section-eq-htpy λ i → ap f lem3))
              (ap inv (ap (λ h → h 1-Δ¹) (is-section-eq-htpy λ i → ap f lem3)))
        ＝ ap f lem3 ∙ ap f (inv lem3)
          by ap-binary _∙_ refl (inv (ap-inv f lem3))
        ＝ ap f (lem3 ∙ inv lem3)
          by inv (ap-concat f lem3 (inv lem3))

  action-clamped-1' : (x : Δ¹) → action (clamped-f x 1-Δ¹) ~ tr (E ∘ f) (lem3 ∙ inv lem3)
  action-clamped-1' x =
    homotopy-reasoning
      action (clamped-f x 1-Δ¹)
        ~ tr E (eq-id-dom-cod-eq (f x) (clamped-f x 1-Δ¹) (clamped-f-1-id x))
          by eq-id-action (f x) (clamped-f x 1-Δ¹) (clamped-f-1-id x)
        ~ tr E (ap f (lem3 ∙ inv lem3))
          by (λ e → ap (λ p → tr E p e) (clamped-f-1-dom-cod-eq x))
        ~ tr (E ∘ f) (lem3 ∙ inv lem3)
          by λ e → substitution-law-tr E f (lem3 ∙ inv lem3)

  lift2 : (g : (x : Δ¹) → E (f x)) → (y x : Δ¹) → E (f x)
  lift2 g y x =
    tr (E ∘ f) lem0
      (action (clamped-f x y)
        (tr (E ∘ f) lem1
          (g (x ∧Δ¹ y))))

  lift2-top : (g : (x : Δ¹) → E (f x)) → lift2 g 1-Δ¹ ~ g
  lift2-top g x =
    equational-reasoning
      lift2 g 1-Δ¹ x
        ＝ tr (E ∘ f) lem0 (tr (E ∘ f) (lem3 ∙ inv lem3) (tr (E ∘ f) lem1 (g (x ∧Δ¹ 1-Δ¹))))
          by ap (tr (E ∘ f) lem0) (action-clamped-1' x (tr (E ∘ f) lem1 (g (x ∧Δ¹ 1-Δ¹))))
        ＝ tr (E ∘ f) (lem3 ∙ inv lem3 ∙ lem0) (tr (E ∘ f) lem1 (g (x ∧Δ¹ 1-Δ¹)))
          by inv (tr-concat (lem3 ∙ inv lem3) lem0 (tr (E ∘ f) lem1 (g (x ∧Δ¹ 1-Δ¹))))
        ＝ tr (E ∘ f) (lem1 ∙ (lem3 ∙ inv lem3 ∙ lem0)) (g (x ∧Δ¹ 1-Δ¹))
          by inv (tr-concat lem1 (lem3 ∙ inv lem3 ∙ lem0) (g (x ∧Δ¹ 1-Δ¹)))
        ＝ g x
          by l g (lem1 ∙ (lem3 ∙ inv lem3 ∙ lem0))
    where
      l :
        {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
        (g : (a : A) → B a) {a a' : A} (p : a ＝ a') →
          tr B p (g a) ＝ g a'
      l g refl = refl

  lift2-bottom : (g : (x : Δ¹) → E (f x)) → lift2 g 0-Δ¹ ~ lift1 (g 0-Δ¹)
  lift2-bottom g x = ap (action-clamped x 0-Δ¹) (inv (l g (inv (meet-bottom-right-Δ¹ x))))
    where
      l :
        {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
        (g : (a : A) → B a) {a a' : A} (p : a ＝ a') →
          tr B p (g a) ＝ g a'
      l g refl = refl

  square-eq : (square : Δ¹ → (x : Δ¹) → E (f x)) → square 0-Δ¹ ~ square 1-Δ¹
  square-eq square x = discrete-dom-cod-htpy (discrete-fibers (f x)) (λ y → square y x)

  lifts-eq : (g : (x : Δ¹) → E (f x)) → g ~ lift1 (g 0-Δ¹)
  lifts-eq g =
    homotopy-reasoning
      g
        ~ lift2 g 1-Δ¹
          by inv-htpy (lift2-top g)
        ~ lift2 g 0-Δ¹
          by inv-htpy (square-eq (lift2 g))
        ~ lift1 (g 0-Δ¹)
          by lift2-bottom g

  is-retraction-lift1 : (g : (x : Δ¹) → E (f x)) → lift1 (dom-section E f g) ＝ g
  is-retraction-lift1 g = eq-htpy (inv-htpy (lifts-eq g))

  is-covariant' : is-equiv (dom-section E f)
  pr1 is-covariant' = lift1 , is-section-lift1
  pr2 is-covariant' = lift1 , is-retraction-lift1

module _
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2)
  (action : (f : Δ¹ → B) → E (f 0-Δ¹) → E (f 1-Δ¹))
  (action-id : (x : B) → action (id-edge x) ~ id)
  (discrete-fibers : (b : B) → type-Prop (is-discrete (E b)))
  where

  is-covariant-discrete-action : type-Prop (is-covariant E)
  is-covariant-discrete-action f = is-covariant' E action action-id discrete-fibers f

```
