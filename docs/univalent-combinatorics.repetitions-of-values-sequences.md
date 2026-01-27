# Repetitions of values in sequences

<pre class="Agda"><a id="47" class="Keyword">module</a> <a id="54" href="univalent-combinatorics.repetitions-of-values-sequences.html" class="Module">univalent-combinatorics.repetitions-of-values-sequences</a> <a id="110" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda">
</pre>
</details>

## Properties

```text
is-decidable-is-ordered-repetition-of-values-ℕ-Fin :
  (k : ℕ) (f : ℕ → Fin k) (x : ℕ) →
  is-decidable (is-ordered-repetition-of-values-ℕ f x)
is-decidable-is-ordered-repetition-of-values-ℕ-Fin k f x = {!!}

{-
  is-decidable-strictly-bounded-Σ-ℕ' x
    ( λ y → Id (f y) (f x))
    ( λ y → has-decidable-equality-Fin k (f y) (f x))
-}

is-decidable-is-ordered-repetition-of-values-ℕ-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) (x : ℕ) →
  is-decidable (is-ordered-repetition-of-values-ℕ f x)
is-decidable-is-ordered-repetition-of-values-ℕ-count e f x = {!!}

{-
  is-decidable-strictly-bounded-Σ-ℕ' x
    ( λ y → Id (f y) (f x))
    ( λ y → has-decidable-equality-count e (f y) (f x))
  -}
```
