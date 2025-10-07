# Wedges of pointed types

```agda
module synthetic-homotopy-theory.wedges-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.raising-universe-levels
open import foundation.propositional-extensionality
open import foundation.function-extensionality
open import foundation-core.injective-maps
open import foundation-core.function-types
open import foundation.sections
open import foundation.retractions
open import foundation.action-on-identifications-functions
open import foundation-core.dependent-identifications
open import foundation-core.propositions
open import foundation-core.sets
open import foundation.unit-type
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.cocones-under-spans
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.cofibers-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.pushouts-of-pointed-types
```

</details>

## Idea

The
{{#concept "wedge" Disambiguation="of pointed types" WD="wedge sum" WDID=Q1781358 Agda=wedge-Pointed-Type}}
or **wedge sum** of two [pointed types](structured-types.pointed-types.md)
`a : A` and `b : B` is defined by the following
[pointed pushout](synthetic-homotopy-theory.pushouts-of-pointed-types.md):

```text
    * -------> A
    |          |
    |          |
    ∨        ⌜ ∨
    B -----> A ∨∗ B,
```

and is thus canonically pointed at the identified image of `a` and `b`.

## Definition

```agda
wedge-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
wedge-Pointed-Type A B =
  pushout-Pointed-Type
    ( inclusion-point-Pointed-Type A)
    ( inclusion-point-Pointed-Type B)

infixr 10 _∨∗_
_∨∗_ = wedge-Pointed-Type

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  inl-wedge-Pointed-Type : A →∗ (A ∨∗ B)
  inl-wedge-Pointed-Type =
    inl-pushout-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)

  map-inl-wedge-Pointed-Type :
    type-Pointed-Type A → type-Pointed-Type (A ∨∗ B)
  map-inl-wedge-Pointed-Type =
    map-pointed-map inl-wedge-Pointed-Type

  inr-wedge-Pointed-Type : B →∗ A ∨∗ B
  inr-wedge-Pointed-Type =
    inr-pushout-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)

  map-inr-wedge-Pointed-Type :
    type-Pointed-Type B → type-Pointed-Type (A ∨∗ B)
  map-inr-wedge-Pointed-Type =
    map-pointed-map inr-wedge-Pointed-Type

indexed-wedge-Pointed-Type :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
pr1 (indexed-wedge-Pointed-Type I A) =
  cofiber (λ i → (i , point-Pointed-Type (A i)))
pr2 (indexed-wedge-Pointed-Type I A) =
  point-cofiber (λ i → (i , point-Pointed-Type (A i)))

⋁∗ = indexed-wedge-Pointed-Type
```

**Note**: the symbols used for the wedge sum `_∨∗_` are the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`) and
the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`),
not the [latin small letter v](https://codepoints.net/U+0076) `v` or the
[asterisk](https://codepoints.net/U+002A) `*`. The `⋁` symbol used for the
indexed wedge sum, `⋁∗`, is the
[N-ary logical or](https://codepoints.net/U+22C1) (agda-input: `\bigvee`).

## Properties

### The images of the base points `a : A` and `b : B` are identified in `A ∨∗ B`

```agda
glue-wedge-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  map-inl-wedge-Pointed-Type A B (point-Pointed-Type A) ＝
  map-inr-wedge-Pointed-Type A B (point-Pointed-Type B)
glue-wedge-Pointed-Type A B =
  glue-pushout
    ( map-pointed-map (inclusion-point-Pointed-Type A))
    ( map-pointed-map (inclusion-point-Pointed-Type B))
    ( point-Pointed-Type unit-Pointed-Type)
```

### The inclusion of the wedge sum `A ∨∗ B` into the pointed product `A ×∗ B`

There is a canonical inclusion of the wedge sum into the pointed product that is
defined by the cogap map induced by the canonical inclusions `A → A ×∗ B ← B`.

Elements of the form `(x, b)` and `(a, y)`, where `b` and `a` are basepoints,
lie in the image of the inclusion of the wedge sum into the pointed product.

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  cocone-product-wedge-Pointed-Type :
    cocone-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)
      ( A ×∗ B)
  pr1 cocone-product-wedge-Pointed-Type = inl-product-Pointed-Type A B
  pr1 (pr2 cocone-product-wedge-Pointed-Type) = inr-product-Pointed-Type A B
  pr1 (pr2 (pr2 cocone-product-wedge-Pointed-Type)) = refl-htpy
  pr2 (pr2 (pr2 cocone-product-wedge-Pointed-Type)) = refl

  pointed-map-product-wedge-Pointed-Type :
    (A ∨∗ B) →∗ (A ×∗ B)
  pointed-map-product-wedge-Pointed-Type =
    cogap-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)
      ( cocone-product-wedge-Pointed-Type)

  map-product-wedge-Pointed-Type :
    type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ×∗ B)
  map-product-wedge-Pointed-Type = pr1 pointed-map-product-wedge-Pointed-Type

  compute-inl-product-wedge-Pointed-Type :
    ( x : type-Pointed-Type A) →
    ( map-product-wedge-Pointed-Type (map-inl-wedge-Pointed-Type A B x)) ＝
    ( x , point-Pointed-Type B)
  compute-inl-product-wedge-Pointed-Type =
    compute-inl-cogap-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)
      ( cocone-product-wedge-Pointed-Type)

  compute-inr-product-wedge-Pointed-Type :
    ( y : type-Pointed-Type B) →
    ( map-product-wedge-Pointed-Type (map-inr-wedge-Pointed-Type A B y)) ＝
    ( point-Pointed-Type A , y)
  compute-inr-product-wedge-Pointed-Type =
    compute-inr-cogap-Pointed-Type
      ( inclusion-point-Pointed-Type A)
      ( inclusion-point-Pointed-Type B)
      ( cocone-product-wedge-Pointed-Type)
```

### Cogap map for wedges

```agda
module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : UU l3}
  (f : (a : type-Pointed-Type A) → C)
  (g : (b : type-Pointed-Type B) → C)
  (p : (f (point-Pointed-Type A) ＝ g (point-Pointed-Type B)))
  where

  cocone-wedge-Pointed-Type : cocone (point (point-Pointed-Type A)) (point (point-Pointed-Type B)) C
  pr1 cocone-wedge-Pointed-Type = f
  pr1 (pr2 cocone-wedge-Pointed-Type) = g
  pr2 (pr2 cocone-wedge-Pointed-Type) star = p

  cogap-wedge-Pointed-Type : type-Pointed-Type (A ∨∗ B) → C
  cogap-wedge-Pointed-Type =
    cogap
      (point (point-Pointed-Type A))
      (point (point-Pointed-Type B))
      cocone-wedge-Pointed-Type

module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : UU l3}
  {f : (a : type-Pointed-Type A) → C}
  {g : (b : type-Pointed-Type B) → C}
  {p : (f (point-Pointed-Type A) ＝ g (point-Pointed-Type B))}
  where

  compute-inl-cogap-wedge-Pointed-Type :
    (a : type-Pointed-Type A) → cogap-wedge-Pointed-Type f g p (map-inl-wedge-Pointed-Type A B a) ＝ f a
  compute-inl-cogap-wedge-Pointed-Type =
    compute-inl-cogap
      (point (point-Pointed-Type A))
      (point (point-Pointed-Type B))
      (cocone-wedge-Pointed-Type f g p)

  compute-inr-cogap-wedge-Pointed-Type :
    (b : type-Pointed-Type B) → cogap-wedge-Pointed-Type f g p (map-inr-wedge-Pointed-Type A B b) ＝ g b
  compute-inr-cogap-wedge-Pointed-Type =
    compute-inr-cogap
      (point (point-Pointed-Type A))
      (point (point-Pointed-Type B))
      (cocone-wedge-Pointed-Type f g p)

```





### Dependent cogap map for wedges

```agda
module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (P : type-Pointed-Type (A ∨∗ B) → UU l3)
  (f : (a : type-Pointed-Type A) → P (map-inl-wedge-Pointed-Type A B a))
  (g : (b : type-Pointed-Type B) → P (map-inr-wedge-Pointed-Type A B b))
  (p :
      dependent-identification P
        (glue-wedge-Pointed-Type A B)
        (f (point-Pointed-Type A))
        (g (point-Pointed-Type B)))
  where

  dependent-cocone-wedge-Pointed-Type :
    dependent-cocone
      (point (point-Pointed-Type A)) (point (point-Pointed-Type B))
      (cocone-pushout
        (point (point-Pointed-Type A))
        (point (point-Pointed-Type B)))
      P
  pr1 dependent-cocone-wedge-Pointed-Type = f
  pr1 (pr2 dependent-cocone-wedge-Pointed-Type) = g
  pr2 (pr2 dependent-cocone-wedge-Pointed-Type) star = p

  dependent-cogap-wedge-Pointed-Type : (x : type-Pointed-Type (A ∨∗ B)) → P x
  dependent-cogap-wedge-Pointed-Type =
    dependent-cogap
      (point (point-Pointed-Type A))
      (point (point-Pointed-Type B))
      (dependent-cocone-wedge-Pointed-Type)

```

### Double cogap map for wedges

```agda
module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : UU l3}
  (ll : type-Pointed-Type A → type-Pointed-Type A → C)
  (lr : type-Pointed-Type A → type-Pointed-Type B → C)
  (rl : type-Pointed-Type B → type-Pointed-Type A → C)
  (rr : type-Pointed-Type B → type-Pointed-Type B → C)
  (leq : (a : type-Pointed-Type A) → ll a (point-Pointed-Type A) ＝ lr a (point-Pointed-Type B))
  (req : (b : type-Pointed-Type B) → rl b (point-Pointed-Type A) ＝ rr b (point-Pointed-Type B))
  (eql : (a : type-Pointed-Type A) → ll (point-Pointed-Type A) a ＝ rl (point-Pointed-Type B) a)
  (eqr : (b : type-Pointed-Type B) → lr (point-Pointed-Type A) b ＝ rr (point-Pointed-Type B) b)
  where

  double-cogap-wedge-Pointed-Type : type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ∨∗ B) → C
  double-cogap-wedge-Pointed-Type =
    cogap-wedge-Pointed-Type
      l r
      (eq-htpy
        (dependent-cogap-wedge-Pointed-Type
          (λ x → l (point-Pointed-Type A) x ＝ r (point-Pointed-Type B) x)
          (λ a →
            equational-reasoning
              l (point-Pointed-Type A) (map-inl-wedge-Pointed-Type A B a)
                ＝ ll (point-Pointed-Type A) a
                  by
                  compute-inl-cogap-wedge-Pointed-Type a
                ＝ rl (point-Pointed-Type B) a
                  by
                  eql a
                ＝ r (point-Pointed-Type B) (map-inl-wedge-Pointed-Type A B a)
                  by
                  inv (compute-inl-cogap-wedge-Pointed-Type a))
          (λ b →
            equational-reasoning
              l (point-Pointed-Type A) (map-inr-wedge-Pointed-Type A B b)
                ＝ lr (point-Pointed-Type A) b
                  by
                  compute-inr-cogap-wedge-Pointed-Type b
                ＝ rr (point-Pointed-Type B) b
                  by
                  eqr b
                ＝ r (point-Pointed-Type B) (map-inr-wedge-Pointed-Type A B b)
                  by
                  inv (compute-inr-cogap-wedge-Pointed-Type b))
          {!   !}))
      where
        l : type-Pointed-Type A → type-Pointed-Type (A ∨∗ B) → C
        l a = cogap-wedge-Pointed-Type (ll a) (lr a) (leq a)

        r : type-Pointed-Type B → type-Pointed-Type (A ∨∗ B) → C
        r b = cogap-wedge-Pointed-Type (rl b) (rr b) (req b)
```



### Mapping wedges into props

```agda

module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (P : type-Pointed-Type (A ∨∗ B) → Prop l3)
  (f : (a : type-Pointed-Type A) → type-Prop (P (map-inl-wedge-Pointed-Type A B a)))
  (g : (b : type-Pointed-Type B) → type-Prop (P (map-inr-wedge-Pointed-Type A B b)))
  where

  wedge-into-Prop-Pointed-Type : (z : type-Pointed-Type (A ∨∗ B)) → type-Prop (P z)
  wedge-into-Prop-Pointed-Type =
    dependent-cogap-wedge-Pointed-Type
      (type-Prop ∘ P) f g
      (eq-is-prop
        (is-prop-type-Prop
          (P (map-inr-wedge-Pointed-Type A B (point-Pointed-Type B)))))

module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (P : type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ∨∗ B) → Prop l3)
  (ll :
      (a : type-Pointed-Type A) → (a' : type-Pointed-Type A)
      → type-Prop (P (map-inl-wedge-Pointed-Type A B a) (map-inl-wedge-Pointed-Type A B a')))

  (lr :
      (a : type-Pointed-Type A) → (b : type-Pointed-Type B)
      → type-Prop (P (map-inl-wedge-Pointed-Type A B a) (map-inr-wedge-Pointed-Type A B b)))

  (rl :
      (b : type-Pointed-Type B) → (a : type-Pointed-Type A)
      → type-Prop (P (map-inr-wedge-Pointed-Type A B b) (map-inl-wedge-Pointed-Type A B a)))

  (rr :
      (b : type-Pointed-Type B) → (b' : type-Pointed-Type B)
      → type-Prop (P (map-inr-wedge-Pointed-Type A B b) (map-inr-wedge-Pointed-Type A B b')))
  where

  double-wedge-into-Prop-Pointed-Type : (z : type-Pointed-Type (A ∨∗ B)) → (z' : type-Pointed-Type (A ∨∗ B)) → type-Prop (P z z')
  double-wedge-into-Prop-Pointed-Type =
    wedge-into-Prop-Pointed-Type
      (λ z → Π-Prop (type-Pointed-Type (A ∨∗ B)) (P z))
      (λ a →
        wedge-into-Prop-Pointed-Type
          (P (map-inl-wedge-Pointed-Type A B a))
          (ll a)
          (lr a))
      (λ b →
        wedge-into-Prop-Pointed-Type
          (P (map-inr-wedge-Pointed-Type A B b))
          (rl b)
          (rr b))
```


```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  prl-wedge-Pointed-Type : type-Pointed-Type (A ∨∗ B) → type-Pointed-Type A
  prl-wedge-Pointed-Type = pr1 ∘ map-product-wedge-Pointed-Type A B

  prr-wedge-Pointed-Type : type-Pointed-Type (A ∨∗ B) → type-Pointed-Type B
  prr-wedge-Pointed-Type = pr2 ∘ map-product-wedge-Pointed-Type A B

  is-retract-inl-wedge-Pointed-Type : is-retraction (map-inl-wedge-Pointed-Type A B) (prl-wedge-Pointed-Type)
  is-retract-inl-wedge-Pointed-Type = ap pr1 ∘ compute-inl-product-wedge-Pointed-Type A B

  is-injective-inl : is-injective (map-inl-wedge-Pointed-Type A B)
  is-injective-inl =
    is-injective-retraction
      (map-inl-wedge-Pointed-Type A B)
      (prl-wedge-Pointed-Type , is-retract-inl-wedge-Pointed-Type)

  is-retract-inr-wedge-Pointed-Type : is-retraction (map-inr-wedge-Pointed-Type A B) (prr-wedge-Pointed-Type)
  is-retract-inr-wedge-Pointed-Type = ap pr2 ∘ compute-inr-product-wedge-Pointed-Type A B

  is-injective-inr : is-injective (map-inr-wedge-Pointed-Type A B)
  is-injective-inr =
    is-injective-retraction
      (map-inr-wedge-Pointed-Type A B)
      (prr-wedge-Pointed-Type , is-retract-inr-wedge-Pointed-Type)

```

```agda



module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (is-set-A : is-set (type-Pointed-Type A)) (is-set-B : is-set (type-Pointed-Type B))
  (a : type-Pointed-Type A)
  where

  set-A : Set l1
  set-A = (type-Pointed-Type A , is-set-A)

  set-B : Set l2
  set-B = (type-Pointed-Type B , is-set-B)

  code : type-Pointed-Type (A ∨∗ B) → type-Pointed-Type (A ∨∗ B) → Prop (l1 ⊔ l2)
  code =
    cogap-wedge-Pointed-Type
      (λ a → cogap-wedge-Pointed-Type (code-ll a) (code-lr a) (code-l-Id a))
      (λ b → cogap-wedge-Pointed-Type (code-rl b) (code-rr b) (code-r-Id b))
      ({!   !})
    where
      code-ll : type-Pointed-Type A → type-Pointed-Type A → Prop (l1 ⊔ l2)
      code-ll a a' = Id-Prop (raise-Set l2 set-A) (map-raise a) (map-raise a')

      code-lr : type-Pointed-Type A → type-Pointed-Type B → Prop (l1 ⊔ l2)
      code-lr a b =
        product-Prop
          (Id-Prop (raise-Set l2 set-A) (map-raise a) (map-raise (point-Pointed-Type A)))
          (Id-Prop (raise-Set l1 set-B) (map-raise b) (map-raise (point-Pointed-Type B)))


      code-l-Id : (a : type-Pointed-Type A) → code-ll a (point-Pointed-Type A) ＝ code-lr a (point-Pointed-Type B)
      code-l-Id a =
        eq-iff
          (λ p → p , refl)
          (λ (p , q) → p)

      code-rl : type-Pointed-Type B → type-Pointed-Type A → Prop (l1 ⊔ l2)
      code-rl b a = code-lr a b

      code-rr : type-Pointed-Type B → type-Pointed-Type B → Prop (l1 ⊔ l2)
      code-rr b b' = Id-Prop (raise-Set l1 set-B) (map-raise b) (map-raise b')

      code-r-Id : (b : type-Pointed-Type B) → code-rl b (point-Pointed-Type A) ＝ code-rr b (point-Pointed-Type B)
      code-r-Id b =
        eq-iff
          (λ (p , q) → q)
          (λ p → refl , p)


  is-set-wedge-Pointed-Set : is-set (type-Pointed-Type (A ∨∗ B))
  is-set-wedge-Pointed-Set = {!   !}
    where
      ll :
        (a : type-Pointed-Type A) → (a' : type-Pointed-Type A)
        → is-prop (
          map-inl-wedge-Pointed-Type A B a
            ＝ map-inl-wedge-Pointed-Type A B a')
      ll = {!   !}


module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (is-set-A : is-set (type-Pointed-Type A)) (is-set-B : is-set (type-Pointed-Type B))
  (a : type-Pointed-Type A)
  where

  ll' :
    (a' : type-Pointed-Type A) →
    (a , point-Pointed-Type B) ＝ (a' , point-Pointed-Type B)
    → map-inl-wedge-Pointed-Type A B a ＝ map-inl-wedge-Pointed-Type A B a'
  ll' a' x = ap (map-inl-wedge-Pointed-Type A B) (ap pr1 x)

  ll :
    (a' : type-Pointed-Type A) →
    (map-product-wedge-Pointed-Type A B (map-inl-wedge-Pointed-Type A B a)
      ＝ map-product-wedge-Pointed-Type A B (map-inl-wedge-Pointed-Type A B a')
    ) → map-inl-wedge-Pointed-Type A B a ＝ map-inl-wedge-Pointed-Type A B a'
  ll a' p =
    ll' a'
      (equational-reasoning
        (a , point-Pointed-Type B)
        ＝ map-product-wedge-Pointed-Type A B (map-inl-wedge-Pointed-Type A B a)
          by
          inv (compute-inl-product-wedge-Pointed-Type A B a)
        ＝ map-product-wedge-Pointed-Type A B (map-inl-wedge-Pointed-Type A B a')
          by
          p
        ＝ (a' , point-Pointed-Type B)
          by
          compute-inl-product-wedge-Pointed-Type A B a'
      )

  lr' :
    (b : type-Pointed-Type B) →
    (a , point-Pointed-Type B) ＝ (point-Pointed-Type A , b)
    → map-inl-wedge-Pointed-Type A B a ＝ map-inr-wedge-Pointed-Type A B b
  lr' b p =
    equational-reasoning
      map-inl-wedge-Pointed-Type A B a
        ＝ map-inl-wedge-Pointed-Type A B (point-Pointed-Type A)
          by ap (map-inl-wedge-Pointed-Type A B) (ap pr1 p)
        ＝ map-inr-wedge-Pointed-Type A B (point-Pointed-Type B)
          by glue-wedge-Pointed-Type A B
        ＝ map-inr-wedge-Pointed-Type A B b
          by (ap (map-inr-wedge-Pointed-Type A B) (ap pr2 p))

  lr :
    (b : type-Pointed-Type B) →
    (map-product-wedge-Pointed-Type A B (map-inl-wedge-Pointed-Type A B a)
      ＝ map-product-wedge-Pointed-Type A B (map-inr-wedge-Pointed-Type A B b)
    ) → map-inl-wedge-Pointed-Type A B a ＝ map-inr-wedge-Pointed-Type A B b
  lr b p =
    lr' b
      (equational-reasoning
        (a , point-Pointed-Type B)
        ＝ map-product-wedge-Pointed-Type A B (map-inl-wedge-Pointed-Type A B a)
          by
          inv (compute-inl-product-wedge-Pointed-Type A B a)
        ＝ map-product-wedge-Pointed-Type A B (map-inr-wedge-Pointed-Type A B b)
          by
          p
        ＝ (point-Pointed-Type A , b)
          by
          compute-inr-product-wedge-Pointed-Type A B b
      )

  qqq : (z : type-Pointed-Type (A ∨∗ B)) → Prop (l1 ⊔ l2)
  qqq z =
    Π-Prop
      ((map-product-wedge-Pointed-Type A B (map-inl-wedge-Pointed-Type A B a)
        ＝ map-product-wedge-Pointed-Type A B z))
      λ _ → Id-Prop {!   !} {!   !} {!   !}

  l : (z : type-Pointed-Type (A ∨∗ B)) →
    (map-product-wedge-Pointed-Type A B (map-inl-wedge-Pointed-Type A B a)
      ＝ map-product-wedge-Pointed-Type A B z)
    → map-inl-wedge-Pointed-Type A B a ＝ z
  l = wedge-into-Prop-Pointed-Type {!   !} {!   !} {!   !}
```



## See also

- [Smash products of pointed types](synthetic-homotopy-theory.smash-products-of-pointed-types.md)
  for a related construction.
