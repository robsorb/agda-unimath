```agda

{-# OPTIONS --no-exact-split #-}

module reflection.test where
```

```agda
open import foundation.universe-levels
open import foundation.unit-type
open import lists.lists
open import reflection.terms
open import reflection.type-checking-monad
open import primitives.strings

open import reflection.arguments
open import reflection.abstractions
open import reflection.metavariables
open import reflection.names

open import foundation.function-types
open import foundation.coproduct-types
open import foundation.booleans
open import foundation.maybe
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import lists.functoriality-lists

open import elementary-number-theory.natural-numbers

```

```agda

print : String → type-Type-Checker unit
print s = debug-print "reflection.test" 2 (cons (string-Error-Part s) nil)

printT : String → Term-Agda → type-Type-Checker unit
printT s t = debug-print "reflection.test" 2 (cons (string-Error-Part s) (cons (term-Error-Part t) nil))

try-block-meta : Term-Agda → type-Type-Checker unit
try-block-meta (metavariable-Term-Agda m _) = block-Type-Checker (metavariable-Blocker-Agda m)
try-block-meta _ = print "not-meta"

unpack-fun-type : {A : UU lzero} → Term-Agda → (Term-Agda → Term-Agda → type-Type-Checker A) → type-Type-Checker A
unpack-fun-type (dependent-product-Term-Agda (visible-Argument-Agda A) (cons-Abstraction-Agda s B)) h = h A B
unpack-fun-type _ h = type-error nil

mk-fun-type : Term-Agda → Term-Agda → Term-Agda
mk-fun-type A B =
  dependent-product-Term-Agda
    (visible-Argument-Agda A)
    (cons-Abstraction-Agda "_" B)

coe-non-dep-fun : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → A → B
coe-non-dep-fun x = x

coe-non-dep-fun' : (A : UU lzero) (B : UU lzero) → (A → B) → A → B
coe-non-dep-fun' A B x = x


maybe-replace-term : (Term-Agda → Maybe Term-Agda) → Term-Agda → Term-Agda
maybe-replace-term h t = rec-coproduct id (λ _ → t) (h t)


map-argument : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Argument-Agda A → Argument-Agda B
map-argument f (cons-Argument-Agda info a) = cons-Argument-Agda info (f a)

map-abstraction : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Abstraction-Agda A → Abstraction-Agda B
map-abstraction f (cons-Abstraction-Agda str a) = cons-Abstraction-Agda str (f a)

map-sort : (Term-Agda → Term-Agda) → Sort-Agda → Sort-Agda
map-sort f (universe-Sort-Agda t) = universe-Sort-Agda (f t)
map-sort f (fixed-universe-Sort-Agda n) = fixed-universe-Sort-Agda n
map-sort f (prop-Sort-Agda t) = prop-Sort-Agda (f t)
map-sort f (fixed-prop-Sort-Agda n) = fixed-prop-Sort-Agda n
map-sort f (fixed-large-universe-Sort-Agda n) = fixed-large-universe-Sort-Agda n
map-sort f unknown-Sort-Agda = unknown-Sort-Agda

mutual
  map-term : (Term-Agda → Maybe Term-Agda) → Term-Agda → Term-Agda
  map-term h t = rec-coproduct id (λ _ → map-term' h t) (h t)

  {-# TERMINATING #-}
  map-term' : (Term-Agda → Maybe Term-Agda) → Term-Agda → Term-Agda
  map-term' h (variable-Term-Agda n args) = variable-Term-Agda n (map-list (map-argument (map-term h)) args)
  map-term' h (constructor-Term-Agda name args) = constructor-Term-Agda name (map-list (map-argument (map-term h)) args)
  map-term' h (definition-Term-Agda name args) = definition-Term-Agda name (map-list (map-argument (map-term h)) args)
  map-term' h (lambda-Term-Agda vis abs) = lambda-Term-Agda vis (map-abstraction (map-term h) abs)
  map-term' h (pattern-lambda-Term-Agda clauses args) = {!   !}
  map-term' h (dependent-product-Term-Agda arg abs) =
    dependent-product-Term-Agda (map-argument (map-term h) arg) (map-abstraction (map-term h) abs)
  map-term' h (sort-Term-Agda sort) = sort-Term-Agda (map-sort (map-term h) sort)
  map-term' h (literal-Term-Agda lit) = literal-Term-Agda lit
  map-term' h (metavariable-Term-Agda meta args) = metavariable-Term-Agda meta (map-list (map-argument (map-term h)) args)
  map-term' h unknown-Term-Agda = unknown-Term-Agda



init-tactic : Term-Agda → type-Type-Checker (Term-Agda × Term-Agda)
init-tactic hole = do
  -- We start by creating a new non-dependent function type
  dom ← check-type unknown-Term-Agda unknown-Term-Agda
  cod ← check-type unknown-Term-Agda unknown-Term-Agda
  let fun = mk-fun-type dom cod

  -- We unify the type of the goal with this new function type and stick to it
  check-type hole fun
  commit-Type-Checker

  hole-type ← infer-type hole

  -- We wait until the codomain (the final goal) can be infered
  unpack-fun-type hole-type (λ new-goal-type goal-type → do
    try-block-meta goal-type
    return-Type-Checker (goal-type , new-goal-type))

no-nothing-tactic : Term-Agda → Term-Agda → Term-Agda → type-Type-Checker unit
no-nothing-tactic new-goal-type goal-type hole = do
  unify new-goal-type goal-type
  unify
    hole
    (lambda-Term-Agda visible-Visibility-Argument-Agda
      (cons-Abstraction-Agda "_" (variable-Term-Agda 0 nil)))

macro
  exact : Term-Agda → type-Type-Checker unit
  exact hole = do
    (goal-type , new-goal-type) ← init-tactic hole

    no-nothing-tactic new-goal-type goal-type hole

  unfold : Name-Agda → Term-Agda → type-Type-Checker unit
  unfold name hole = do
    (goal-type , new-goal-type) ← (
      with-normalization true (
        with-reduce-definitions (true , cons name nil) (init-tactic hole)))

    no-nothing-tactic new-goal-type goal-type hole

T = bool
T' = unit


ex1 : T × T'
ex1 = unfold T {!   !}

ex2 : T × T'
ex2 = unfold T (true , star)

```
