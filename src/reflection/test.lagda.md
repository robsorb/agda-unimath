```agda
module reflection.test where
```

```agda
open import foundation.function-types
open import lists.lists
open import foundation.identity-types

open import reflection.names
open import reflection.terms
open import reflection.definitions
open import reflection.abstractions
open import reflection.arguments
```

```agda

y : (p : nil ＝ nil) → nil ＝ nil
y p = (refl ＝ nil by p)

x = {! y  !}

```
