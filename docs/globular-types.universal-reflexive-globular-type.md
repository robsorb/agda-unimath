# The universal reflexive globular type

<pre class="Agda"><a id="50" class="Symbol">{-#</a> <a id="54" class="Keyword">OPTIONS</a> <a id="62" class="Pragma">--guardedness</a> <a id="76" class="Symbol">#-}</a>

<a id="81" class="Keyword">module</a> <a id="88" href="globular-types.universal-reflexive-globular-type.html" class="Module">globular-types.universal-reflexive-globular-type</a> <a id="137" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="277" class="Keyword">open</a> <a id="282" class="Keyword">import</a> <a id="289" href="globular-types.reflexive-globular-types.html" class="Module">globular-types.reflexive-globular-types</a>
</pre>
</details>

## Idea

The {{#concept "universal reflexive globular type"}} `𝒢 l` at
[universe level](foundation.universe-levels.md) is a translation from category
theory into type theory of the Hofmann–Streicher universe {{#cite Awodey22}} of
presheaves on the reflexive globular category `Γʳ`

```text
      s₀       s₁       s₂
    ----->   ----->   ----->
  0 <-r₀-- 1 <-r₁-- 2 <-r₂-- ⋯,
    ----->   ----->   ----->
      t₀       t₁       t₂
```

in which the _reflexive globular identities_

```text
  rs = id
  rt = id
  ss = ts
  tt = st
```

hold.

The Hofmann–Streicher universe of presheaves on a category `𝒞` is the presheaf
obtained by applying the functoriality of the right adjoint `ν : Cat → Psh 𝒞` of
the _category of elements functor_ `∫_𝒞 : Psh 𝒞 → Cat` to the universal discrete
fibration `π : Pointed-Type → Type`. More specifically, the Hofmann–Streicher
universe `(𝒰_𝒞 , El_𝒞)` is given by

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A *,
```

where `*` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute a few instances of the slice category `Γʳ/I`:

- The category Γʳ/0 is the category

  ```text
        s₀        s₁          s₂
      ----->    ----->      ----->
    1 <-r₀-- r₀ <-r₁-- r₀r₁ <-r₂-- ⋯.
      ----->    ----->      ----->
        t₀        t₁          t₂
  ```

  In other words, we have an isomorphism of categories `Γʳ/0 ≅ Γʳ`.

- The category Γʳ/1 is the category

  ```text
                                        ⋮
                                       r₁r₂
                                       ∧|∧
                                       |||
                                       |∨|
                                        r₁
                                       ∧|∧
             s₁          s₀            |||            s₀          s₁
           <-----      <-----      s₀  |∨|  t₀      ----->      ----->
  ⋯ s₀r₀r₁ --r₁-> s₀r₀ --r₀-> s₀ -----> 1 <----- t₀ <-r₀-- t₀r₀ <-r₁-- t₀r₀r₁ ⋯.
           <-----      <-----                       ----->      ----->
             t₁          t₀                           t₀          t₁
  ```

## Definitions

<pre class="Agda"><a id="2481" class="Keyword">module</a> <a id="2488" href="globular-types.universal-reflexive-globular-type.html#2488" class="Module">_</a>
  <a id="2492" class="Symbol">(</a><a id="2493" href="globular-types.universal-reflexive-globular-type.html#2493" class="Bound">l1</a> <a id="2496" href="globular-types.universal-reflexive-globular-type.html#2496" class="Bound">l2</a> <a id="2499" class="Symbol">:</a> <a id="2501" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2506" class="Symbol">)</a>
  <a id="2510" class="Keyword">where</a>

  <a id="2519" href="globular-types.universal-reflexive-globular-type.html#2519" class="Function">0-cell-universal-Reflexive-Globular-Type</a> <a id="2560" class="Symbol">:</a> <a id="2562" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2565" class="Symbol">(</a><a id="2566" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2571" href="globular-types.universal-reflexive-globular-type.html#2493" class="Bound">l1</a> <a id="2574" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2576" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2581" href="globular-types.universal-reflexive-globular-type.html#2496" class="Bound">l2</a><a id="2583" class="Symbol">)</a>
  <a id="2587" href="globular-types.universal-reflexive-globular-type.html#2519" class="Function">0-cell-universal-Reflexive-Globular-Type</a> <a id="2628" class="Symbol">=</a>
    <a id="2634" href="globular-types.reflexive-globular-types.html#3909" class="Record">Reflexive-Globular-Type</a> <a id="2658" href="globular-types.universal-reflexive-globular-type.html#2493" class="Bound">l1</a> <a id="2661" href="globular-types.universal-reflexive-globular-type.html#2496" class="Bound">l2</a>
</pre>
## See also

- [The universal directed graph](graph-theory.universal-directed-graph.md)
- [The universal globular type](globular-types.universal-globular-type.md)
- [The universal reflexive graph](graph-theory.universal-reflexive-graph.md)

## External links

- [Globular sets](https://ncatlab.org/nlab/show/globular+set) at the $n$Lab.

## References

{{#bibliography}}
