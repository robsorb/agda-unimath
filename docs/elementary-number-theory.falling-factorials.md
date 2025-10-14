# Falling factorials

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="elementary-number-theory.falling-factorials.html" class="Module">elementary-number-theory.falling-factorials</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
</pre>
</details>

## Idea

The
{{#concept "falling factorial" WD="falling and rising factorial" WDID=Q2339261 Agda=falling-factorial-ℕ}}
`(n)ₘ` is the number `n(n-1)⋯(n-m+1)`.

## Definition

<pre class="Agda"><a id="falling-factorial-ℕ"></a><a id="458" href="elementary-number-theory.falling-factorials.html#458" class="Function">falling-factorial-ℕ</a> <a id="478" class="Symbol">:</a> <a id="480" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="482" class="Symbol">→</a> <a id="484" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="486" class="Symbol">→</a> <a id="488" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="490" href="elementary-number-theory.falling-factorials.html#458" class="Function">falling-factorial-ℕ</a> <a id="510" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="517" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="524" class="Symbol">=</a> <a id="526" class="Number">1</a>
<a id="528" href="elementary-number-theory.falling-factorials.html#458" class="Function">falling-factorial-ℕ</a> <a id="548" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="555" class="Symbol">(</a><a id="556" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="563" href="elementary-number-theory.falling-factorials.html#563" class="Bound">m</a><a id="564" class="Symbol">)</a> <a id="566" class="Symbol">=</a> <a id="568" class="Number">0</a>
<a id="570" href="elementary-number-theory.falling-factorials.html#458" class="Function">falling-factorial-ℕ</a> <a id="590" class="Symbol">(</a><a id="591" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="598" href="elementary-number-theory.falling-factorials.html#598" class="Bound">n</a><a id="599" class="Symbol">)</a> <a id="601" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="608" class="Symbol">=</a> <a id="610" class="Number">1</a>
<a id="612" href="elementary-number-theory.falling-factorials.html#458" class="Function">falling-factorial-ℕ</a> <a id="632" class="Symbol">(</a><a id="633" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="640" href="elementary-number-theory.falling-factorials.html#640" class="Bound">n</a><a id="641" class="Symbol">)</a> <a id="643" class="Symbol">(</a><a id="644" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="651" href="elementary-number-theory.falling-factorials.html#651" class="Bound">m</a><a id="652" class="Symbol">)</a> <a id="654" class="Symbol">=</a>
  <a id="658" class="Symbol">(</a><a id="659" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="666" href="elementary-number-theory.falling-factorials.html#640" class="Bound">n</a><a id="667" class="Symbol">)</a> <a id="669" href="elementary-number-theory.multiplication-natural-numbers.html#1398" class="Primitive Operator">*ℕ</a> <a id="672" class="Symbol">(</a><a id="673" href="elementary-number-theory.falling-factorials.html#458" class="Function">falling-factorial-ℕ</a> <a id="693" href="elementary-number-theory.falling-factorials.html#640" class="Bound">n</a> <a id="695" href="elementary-number-theory.falling-factorials.html#651" class="Bound">m</a><a id="696" class="Symbol">)</a>

<a id="699" class="Comment">{-
Fin-falling-factorial-ℕ :
  (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ n m = {!!}
-}</a>

<a id="829" class="Comment">{-
Fin-falling-factorial-ℕ :
  (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ zero-ℕ zero-ℕ =
  equiv-is-contr
    ( is-contr-Fin-1)
    ( is-contr-equiv
      ( is-emb id)
      ( left-unit-law-Σ-is-contr
        ( universal-property-empty&#39; empty)
        ( id))
      ( dependent-universal-property-empty&#39;
        ( λ x → (y : empty) → is-equiv (ap id))))
Fin-falling-factorial-ℕ zero-ℕ (succ-ℕ m) =
  equiv-is-empty id (λ f → map-emb f (inr star))
Fin-falling-factorial-ℕ (succ-ℕ n) zero-ℕ =
  equiv-is-contr
    ( is-contr-Fin-1)
    ( is-contr-equiv
      ( is-emb ex-falso)
      ( left-unit-law-Σ-is-contr
        ( universal-property-empty&#39; (Fin (succ-ℕ n)))
        ( ex-falso))
      ( dependent-universal-property-empty&#39;
        ( λ x → (y : empty) → is-equiv (ap ex-falso))))
Fin-falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) =
  ( ( ( right-unit-law-Σ-is-contr
        { B = λ f → is-decidable (fiber (map-emb f) (inr star))}
        ( λ f →
          is-proof-irrelevant-is-prop
            ( is-prop-is-decidable
              ( is-prop-map-is-emb (is-emb-map-emb f) (inr star)))
            ( is-decidable-Σ-Fin
              ( λ x →
                has-decidable-equality-Fin (map-emb f x) (inr star))))) ∘e
      ( ( inv-equiv
          ( left-distributive-Σ-coproduct
            ( Fin (succ-ℕ m) ↪ Fin (succ-ℕ n))
            ( λ f → fiber (map-emb f) (inr star))
            ( λ f → ¬ (fiber (map-emb f) (inr star))))) ∘e
        {!!})) ∘e
    ( equiv-coproduct
      ( Fin-falling-factorial-ℕ n m)
      ( Fin-falling-factorial-ℕ n (succ-ℕ m)))) ∘e
  ( inv-compute-coproduct-Fin (falling-factorial-ℕ n m) (falling-factorial-ℕ n (succ-ℕ m)))
-}</a>
</pre>