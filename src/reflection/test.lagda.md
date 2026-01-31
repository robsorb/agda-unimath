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

unpack-fun-type : (Term-Agda → Term-Agda → type-Type-Checker unit) → Term-Agda → type-Type-Checker unit
unpack-fun-type h (dependent-product-Term-Agda (visible-Argument-Agda A) (cons-Abstraction-Agda s B)) = h A B
unpack-fun-type h _ = print "not function type"

mk-fun-type : Term-Agda → Term-Agda → Term-Agda
mk-fun-type A B =
  dependent-product-Term-Agda
    (visible-Argument-Agda A)
    (cons-Abstraction-Agda "_" B)

coe-non-dep-fun : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → A → B
coe-non-dep-fun x = x

coe-non-dep-fun' : (A : UU lzero) (B : UU lzero) → (A → B) → A → B
coe-non-dep-fun' A B x = x


T = bool
T' = unit


macro
  test-macro' : Term-Agda → type-Type-Checker unit
  test-macro' goal = do
    print "1"
    goal-type ← infer-type goal
    printT "" goal-type
    unpack-fun-type (λ dom cod → try-block-meta cod) goal-type
    unpack-fun-type (λ dom cod → unify dom (quoteTerm unit)) goal-type
    unpack-fun-type (λ dom cod → printT "goal: " cod) goal-type
    print "done"

  test-macro : Term-Agda → type-Type-Checker unit
  test-macro goal = do
    print "2"

    dom ← check-type unknown-Term-Agda unknown-Term-Agda
    cod ← check-type unknown-Term-Agda unknown-Term-Agda

    goal' ← check-type unknown-Term-Agda unknown-Term-Agda

    unify goal (definition-Term-Agda (quote coe-non-dep-fun') (cons (visible-Argument-Agda dom) (cons (visible-Argument-Agda cod) (cons (visible-Argument-Agda goal') nil))))
    commit-Type-Checker
    goal-type ← infer-type goal

    printT "goaltype: " goal-type

    unpack-fun-type (λ dom cod → try-block-meta cod) goal-type

    printT "done: " goal'
    -- unify goal (quoteTerm coe-non-dep-fun')

  test-macro'' : Term-Agda → type-Type-Checker unit
  test-macro'' goal = do
    dom ← check-type unknown-Term-Agda unknown-Term-Agda
    cod ← check-type unknown-Term-Agda unknown-Term-Agda
    let fun = mk-fun-type dom cod

    check-type goal fun
    commit-Type-Checker

    goal-type ← infer-type goal

    unpack-fun-type (λ dom cod → try-block-meta cod) goal-type

    with-normalization true (with-reduce-definitions (true , cons (quote T) nil) (do
      brbrb ← quote-Type-Checker (T × T')
      unify dom brbrb))

    goal-type ← infer-type goal

    printT "dom " dom
    printT "cod " cod
    printT "done " goal-type
    print "bing"

    -- goal-type ← infer-type goal

    -- printT "dom " dom
    -- printT "cod " cod
    -- printT "done " goal-type



f : ℕ → ℕ
f = {!   !}



x : ℕ
x = test-macro'' {!   !}

```
