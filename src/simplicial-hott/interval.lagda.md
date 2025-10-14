```agda

module simplicial-hott.interval where

```

```agda

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.cartesian-product-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.functoriality-dependent-pair-types

open import foundation.binary-relations
open import foundation.disjunction

open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.whiskering-homotopies-composition
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.intersections-subtypes
open import foundation.equivalences
open import foundation.fibers-of-maps

open import order-theory.posets
open import order-theory.lattices
open import order-theory.meet-semilattices
open import order-theory.join-semilattices
open import order-theory.distributive-lattices
open import order-theory.top-elements-posets
open import order-theory.bottom-elements-posets

open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.universal-property-pushouts
```

## Postulates

We postulate an interval type, which is a bounded (_we may want to drop this
assumption to allow for a model in cubical spaces_) distributive.

```agda

postulate
  Δ¹-Distributive-Lattice : Distributive-Lattice lzero lzero

Δ¹ : UU lzero
Δ¹ = type-Distributive-Lattice Δ¹-Distributive-Lattice

Δ¹-Lattice : Lattice lzero lzero
Δ¹-Lattice = lattice-Distributive-Lattice Δ¹-Distributive-Lattice

Δ¹-Meet-Semilattice : Meet-Semilattice lzero
Δ¹-Meet-Semilattice = meet-semilattice-Distributive-Lattice Δ¹-Distributive-Lattice


Δ¹-Join-Semilattice : Join-Semilattice lzero
Δ¹-Join-Semilattice = join-semilattice-Distributive-Lattice Δ¹-Distributive-Lattice

Δ¹-Poset : Poset lzero lzero
Δ¹-Poset = poset-Distributive-Lattice Δ¹-Distributive-Lattice


postulate
  0-Δ¹ : Δ¹
  1-Δ¹ : Δ¹

  0-is-bottom-element-Δ¹ : is-bottom-element-Poset Δ¹-Poset 0-Δ¹
  1-is-top-element-Δ¹ : is-top-element-Poset Δ¹-Poset 1-Δ¹

```

## Definitions

The relation on the interval.

```agda
Δ¹-Set : Set lzero
Δ¹-Set = set-Poset Δ¹-Poset

is-set-Δ¹ : is-set Δ¹
is-set-Δ¹ = is-set-type-Set Δ¹-Set

leq-Δ¹-Prop : Δ¹ → Δ¹ → Prop lzero
leq-Δ¹-Prop = leq-Distributive-Lattice-Prop Δ¹-Distributive-Lattice

geq-Δ¹-Prop : Δ¹ → Δ¹ → Prop lzero
geq-Δ¹-Prop x y = leq-Δ¹-Prop y x

_≤Δ¹_ : Δ¹ → Δ¹ → UU lzero
_≤Δ¹_ = type-Relation-Prop leq-Δ¹-Prop

_≥Δ¹_ : Δ¹ → Δ¹ → UU lzero
_≥Δ¹_ = type-Relation-Prop geq-Δ¹-Prop

_∧Δ¹_ : Δ¹ → Δ¹ → Δ¹
_∧Δ¹_ = meet-Distributive-Lattice Δ¹-Distributive-Lattice

_∨Δ¹_ : Δ¹ → Δ¹ → Δ¹
_∨Δ¹_ = join-Distributive-Lattice Δ¹-Distributive-Lattice

commutative-meet-Δ¹ : (i j : Δ¹) → i ∧Δ¹ j ＝ j ∧Δ¹ i
commutative-meet-Δ¹ = commutative-meet-Meet-Semilattice Δ¹-Meet-Semilattice

commutative-join-Δ¹ : (i j : Δ¹) → i ∨Δ¹ j ＝ j ∨Δ¹ i
commutative-join-Δ¹ = commutative-join-Join-Semilattice Δ¹-Join-Semilattice

meet-bottom-left-Δ¹ : (i : Δ¹) → 0-Δ¹ ∧Δ¹ i ＝ 0-Δ¹
meet-bottom-left-Δ¹ i =
  left-leq-right-meet-Lattice Δ¹-Lattice 0-Δ¹ i (0-is-bottom-element-Δ¹ i)

meet-bottom-right-Δ¹ : (i : Δ¹) → i ∧Δ¹ 0-Δ¹ ＝ 0-Δ¹
meet-bottom-right-Δ¹ i = commutative-meet-Δ¹ i 0-Δ¹ ∙ meet-bottom-left-Δ¹ i

meet-top-right-Δ¹ : (i : Δ¹) → i ∧Δ¹ 1-Δ¹ ＝ i
meet-top-right-Δ¹ i =
  left-leq-right-meet-Lattice Δ¹-Lattice i 1-Δ¹ (1-is-top-element-Δ¹ i)

meet-top-left-Δ¹ : (i : Δ¹) → 1-Δ¹ ∧Δ¹ i ＝ i
meet-top-left-Δ¹ i = commutative-meet-Δ¹ 1-Δ¹ i ∙ meet-top-right-Δ¹ i

join-bottom-left-Δ¹ : (i : Δ¹) → 0-Δ¹ ∨Δ¹ i ＝ i
join-bottom-left-Δ¹ i =
  left-leq-right-join-Lattice Δ¹-Lattice 0-Δ¹ i (0-is-bottom-element-Δ¹ i)

join-bottom-right-Δ¹ : (i : Δ¹) → i ∨Δ¹ 0-Δ¹ ＝ i
join-bottom-right-Δ¹ i = commutative-join-Δ¹ i 0-Δ¹ ∙ join-bottom-left-Δ¹ i

join-top-left-Δ¹ : (i : Δ¹) → 1-Δ¹ ∨Δ¹ i ＝ 1-Δ¹
join-top-left-Δ¹ i =
  right-leq-left-join-Lattice Δ¹-Lattice 1-Δ¹ i (1-is-top-element-Δ¹ i)

join-top-right-Δ¹ : (i : Δ¹) → i ∨Δ¹ 1-Δ¹ ＝ 1-Δ¹
join-top-right-Δ¹ i = commutative-join-Δ¹ i 1-Δ¹ ∙ join-top-left-Δ¹ i

idempotent-meet-Δ¹ : (i : Δ¹) → i ∧Δ¹ i ＝ i
idempotent-meet-Δ¹ i = idempotent-meet-Meet-Semilattice Δ¹-Meet-Semilattice i

idempotent-join-Δ¹ : (i : Δ¹) → i ∨Δ¹ i ＝ i
idempotent-join-Δ¹ i = idempotent-join-Join-Semilattice Δ¹-Join-Semilattice i

```

```agda
module _
  {l : Level} {C : UU l}
  where

  dom : (Δ¹ → C) → C
  dom f = f 0-Δ¹

  cod : (Δ¹ → C) → C
  cod f = f 1-Δ¹

  hom : (x y : C) → UU l
  hom x y = Σ (Δ¹ → C) (λ f → (dom f ＝ x) × (cod f ＝ y))

  ev-hom : {x y : C} → hom x y → Δ¹ → C
  ev-hom = pr1

  hom-ext : {x y : C} (f : hom x y) (g : hom x y) →
    ev-hom f ~ ev-hom g → f ＝ g
  hom-ext f g H =
    eq-pair-Σ
      (eq-htpy H)
      (eq-pair-Σ
        {!   !}
        {!   !})

  hom-dom-eq : {x y : C} → (f : hom x y) → (dom (ev-hom f) ＝ x)
  hom-dom-eq f = pr1 (pr2 f)

  hom-cod-eq : {x y : C} → (f : hom x y) → (cod (ev-hom f) ＝ y)
  hom-cod-eq f = pr2 (pr2 f)

  id-edge : (x : C) → Δ¹ → C
  id-edge x _ = x

  id-hom : (x : C) → hom x x
  id-hom x = (λ _ → x) , refl , refl
```

### The 2-1-horn

```agda
bottom-edge-square-subtype : subtype lzero (Δ¹ × Δ¹)
bottom-edge-square-subtype (_ , y) = Id-Prop Δ¹-Set y 0-Δ¹

right-edge-square-subtype : subtype lzero (Δ¹ × Δ¹)
right-edge-square-subtype (x , _) = Id-Prop Δ¹-Set x 1-Δ¹

Λ²₁-subtype : subtype lzero (Δ¹ × Δ¹)
Λ²₁-subtype = union-subtype right-edge-square-subtype bottom-edge-square-subtype

Λ²₁ : UU lzero
Λ²₁ = type-subtype Λ²₁-subtype

Λ²₁-Relation-implies-Δ²-Relation : (x : Δ¹ × Δ¹)  → type-Prop (Λ²₁-subtype x) → pr1 x ≥Δ¹ pr2 x
Λ²₁-Relation-implies-Δ²-Relation (x , y) =
  elim-disjunction
    (geq-Δ¹-Prop x y)
    (λ where refl → 1-is-top-element-Δ¹ y)
    (λ where refl → 0-is-bottom-element-Δ¹ x)

bottom-Λ²₁ : Δ¹ → Λ²₁
bottom-Λ²₁ i =
  map-inr-union-subtype
    right-edge-square-subtype
    bottom-edge-square-subtype
    ((i , 0-Δ¹) , refl)

right-Λ²₁ : Δ¹ → Λ²₁
right-Λ²₁ i =
  map-inl-union-subtype
    right-edge-square-subtype
    bottom-edge-square-subtype
    ((1-Δ¹ , i) , refl)

fist-vertex-Λ²₁ : Λ²₁
fist-vertex-Λ²₁ = dom bottom-Λ²₁

last-vertex-Λ²₁ : Λ²₁
last-vertex-Λ²₁ = cod right-Λ²₁
```

### 2-Simplex

```agda
subtype-Δ² : subtype lzero (Δ¹ × Δ¹)
subtype-Δ² (i , j ) = geq-Δ¹-Prop i j

Δ² : UU lzero
Δ² = type-subtype subtype-Δ²

Λ²₁-to-Δ² : Λ²₁ → Δ²
Λ²₁-to-Δ² = tot Λ²₁-Relation-implies-Δ²-Relation

bottom-Δ² : Δ¹ → Δ²
bottom-Δ² = Λ²₁-to-Δ² ∘ bottom-Λ²₁

right-Δ² : Δ¹ → Δ²
right-Δ² = Λ²₁-to-Δ² ∘ right-Λ²₁

diagonal-Δ² : Δ¹ → Δ²
diagonal-Δ² i = (i , i) , refl-leq-Poset Δ¹-Poset i

module _
  {l : Level} {C : UU l}
  where

  bottom-edge : (Δ² → C) → Δ¹ → C
  bottom-edge α = α ∘ bottom-Δ²

  right-edge : (Δ² → C) → Δ¹ → C
  right-edge α = α ∘ right-Δ²

  diagonal-edge : (Δ² → C) → Δ¹ → C
  diagonal-edge α = α ∘ diagonal-Δ²

  dom-diagonal : (α : Δ² → C) → dom (diagonal-edge α) ＝ dom (bottom-edge α)
  dom-diagonal α = ap α (eq-type-subtype subtype-Δ² refl)

  cod-diagonal : (α : Δ² → C) → cod (diagonal-edge α) ＝ cod (right-edge α)
  cod-diagonal α = ap α (eq-type-subtype subtype-Δ² refl)

module _
  {l : Level} {C : UU l} (f : Δ¹ → C)
  where
  degen-Δ²-bottom : Δ² → C
  degen-Δ²-bottom ((x , y), prf) = f (x ∧Δ¹ y)

  degen-Δ²-right : Δ² → C
  degen-Δ²-right ((x , y), prf) = f (x ∨Δ¹ y)

  bottom-degen-bottom : bottom-edge (degen-Δ²-bottom) ~ id-edge (f 0-Δ¹)
  bottom-degen-bottom i = ap f (meet-bottom-right-Δ¹ i)

  right-degen-bottom : right-edge (degen-Δ²-bottom) ~ f
  right-degen-bottom i = ap f (meet-top-left-Δ¹ i)

  diagonal-degen-bottom : diagonal-edge degen-Δ²-bottom ~ f
  diagonal-degen-bottom i = ap f (idempotent-meet-Δ¹ i)

  bottom-degen-right : bottom-edge degen-Δ²-right ~ f
  bottom-degen-right i = ap f (join-bottom-right-Δ¹ i)

  right-degen-right : right-edge degen-Δ²-right ~ id-edge (f 1-Δ¹)
  right-degen-right i = ap f (join-top-left-Δ¹ i)

  diagonal-degen-right : diagonal-edge degen-Δ²-right ~ f
  diagonal-degen-right i = ap f (idempotent-join-Δ¹ i)
```

### Horn fillers

```agda
module _
  {l : Level} (C : UU l)
  where
  restriction-to-Λ²₁ : (Δ² → C) → (Λ²₁ → C)
  restriction-to-Λ²₁ α = α ∘ Λ²₁-to-Δ²

module _
  {l : Level} {C : UU l}
  (h : Λ²₁ → C)
  where
  horn-filler : UU l
  horn-filler = fiber (restriction-to-Λ²₁ C) h

  simplex-horn-filler : horn-filler → Δ² → C
  simplex-horn-filler = pr1

  horn-filler-restricts : (α : horn-filler) → restriction-to-Λ²₁ C (simplex-horn-filler α) ~ h
  horn-filler-restricts α = htpy-eq (pr2 α)

  horn-filler-restricts-bottom :
    (α : horn-filler) → bottom-edge (simplex-horn-filler α) ~ h ∘ bottom-Λ²₁
  horn-filler-restricts-bottom α = horn-filler-restricts α ·r bottom-Λ²₁

  horn-filler-restricts-right :
    (α : horn-filler) → right-edge (simplex-horn-filler α) ~ h ∘ right-Λ²₁
  horn-filler-restricts-right α = horn-filler-restricts α ·r right-Λ²₁
```

### Mapping composable pairs of morphisms to horns

```agda

module _
  {l : Level} {C : UU l}
  where

  composable-edges-to-cocone :
    (g : Δ¹ → C)  (f : Δ¹ → C) (compat : dom g ＝ cod f) →
      union-cocones
        right-edge-square-subtype
        bottom-edge-square-subtype
        C
  pr1 (composable-edges-to-cocone g f compat) ((x , y), prfR) = g y
  pr1 (pr2 (composable-edges-to-cocone g f compat)) ((x , y), prfL) = f x
  pr2 (pr2 (composable-edges-to-cocone g f compat)) ((x , y), refl , refl) = compat

  horn-cocone-right-edge :
    (union-cocones right-edge-square-subtype bottom-edge-square-subtype C) → Δ¹ → C
  horn-cocone-right-edge (r , _ , _) i = r ((1-Δ¹ , i) , refl)

  horn-cocone-bottom-edge :
    (union-cocones right-edge-square-subtype bottom-edge-square-subtype C) → Δ¹ → C
  horn-cocone-bottom-edge (_ , b , _) i = b ((i , 0-Δ¹) , refl)

  compat-horn-cocone-edges :
    (c : union-cocones right-edge-square-subtype bottom-edge-square-subtype C) →
      dom (horn-cocone-right-edge c) ＝ cod (horn-cocone-bottom-edge c)
  compat-horn-cocone-edges (_ , _ , c) = c ((1-Δ¹ , 0-Δ¹) , refl , refl)

  composable-edges-to-horn :
    (g : Δ¹ → C)  (f : Δ¹ → C) (compat : dom g ＝ cod f) → Λ²₁ → C
  composable-edges-to-horn g f compat =
    map-universal-property-pushout
      (map-intersection-pr1 right-edge-square-subtype bottom-edge-square-subtype)
      (map-intersection-pr2 right-edge-square-subtype bottom-edge-square-subtype)
      (union-cocone right-edge-square-subtype bottom-edge-square-subtype)
      (union-cocone-is-pushout right-edge-square-subtype bottom-edge-square-subtype)
      (composable-edges-to-cocone g f compat)
```
