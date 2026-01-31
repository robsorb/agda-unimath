```agda

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

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types

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


macro
  exact : Term-Agda → type-Type-Checker unit
  exact hole = do
    (goal-type , new-goal-type) ← init-tactic hole

    unify new-goal-type goal-type
    unify hole (quoteTerm (λ x → x))

  unfold : Name-Agda → Term-Agda → type-Type-Checker unit
  unfold name hole = do
    (goal-type , new-goal-type) ← (
      with-normalization true (
        with-reduce-definitions (true , cons name nil) (init-tactic hole)))

    unify new-goal-type goal-type

T = bool
T' = unit


x : T × T'
x = unfold T' {!   !}

```
