# Uniqueness of the truncations

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="foundation.uniqueness-truncation.html" class="Module">foundation.uniqueness-truncation</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

## Idea

The universal property of `n`-truncations implies that `n`-truncations are
determined uniquely up to a unique equivalence.

<pre class="Agda"><a id="508" class="Keyword">module</a> <a id="515" href="foundation.uniqueness-truncation.html#515" class="Module">_</a>
  <a id="519" class="Symbol">{</a><a id="520" href="foundation.uniqueness-truncation.html#520" class="Bound">l1</a> <a id="523" href="foundation.uniqueness-truncation.html#523" class="Bound">l2</a> <a id="526" href="foundation.uniqueness-truncation.html#526" class="Bound">l3</a> <a id="529" class="Symbol">:</a> <a id="531" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="536" class="Symbol">}</a> <a id="538" class="Symbol">(</a><a id="539" href="foundation.uniqueness-truncation.html#539" class="Bound">k</a> <a id="541" class="Symbol">:</a> <a id="543" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="544" class="Symbol">)</a> <a id="546" class="Symbol">{</a><a id="547" href="foundation.uniqueness-truncation.html#547" class="Bound">A</a> <a id="549" class="Symbol">:</a> <a id="551" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="554" href="foundation.uniqueness-truncation.html#520" class="Bound">l1</a><a id="556" class="Symbol">}</a>
  <a id="560" class="Symbol">(</a><a id="561" href="foundation.uniqueness-truncation.html#561" class="Bound">B</a> <a id="563" class="Symbol">:</a> <a id="565" href="foundation-core.truncated-types.html#1603" class="Function">Truncated-Type</a> <a id="580" href="foundation.uniqueness-truncation.html#523" class="Bound">l2</a> <a id="583" href="foundation.uniqueness-truncation.html#539" class="Bound">k</a><a id="584" class="Symbol">)</a> <a id="586" class="Symbol">(</a><a id="587" href="foundation.uniqueness-truncation.html#587" class="Bound">f</a> <a id="589" class="Symbol">:</a> <a id="591" href="foundation.uniqueness-truncation.html#547" class="Bound">A</a> <a id="593" class="Symbol">→</a> <a id="595" href="foundation-core.truncated-types.html#1736" class="Function">type-Truncated-Type</a> <a id="615" href="foundation.uniqueness-truncation.html#561" class="Bound">B</a><a id="616" class="Symbol">)</a>
  <a id="620" class="Symbol">(</a><a id="621" href="foundation.uniqueness-truncation.html#621" class="Bound">C</a> <a id="623" class="Symbol">:</a> <a id="625" href="foundation-core.truncated-types.html#1603" class="Function">Truncated-Type</a> <a id="640" href="foundation.uniqueness-truncation.html#526" class="Bound">l3</a> <a id="643" href="foundation.uniqueness-truncation.html#539" class="Bound">k</a><a id="644" class="Symbol">)</a> <a id="646" class="Symbol">(</a><a id="647" href="foundation.uniqueness-truncation.html#647" class="Bound">g</a> <a id="649" class="Symbol">:</a> <a id="651" href="foundation.uniqueness-truncation.html#547" class="Bound">A</a> <a id="653" class="Symbol">→</a> <a id="655" href="foundation-core.truncated-types.html#1736" class="Function">type-Truncated-Type</a> <a id="675" href="foundation.uniqueness-truncation.html#621" class="Bound">C</a><a id="676" class="Symbol">)</a>
  <a id="680" class="Symbol">{</a><a id="681" href="foundation.uniqueness-truncation.html#681" class="Bound">h</a> <a id="683" class="Symbol">:</a> <a id="685" href="foundation-core.truncated-types.html#11832" class="Function">type-hom-Truncated-Type</a> <a id="709" href="foundation.uniqueness-truncation.html#539" class="Bound">k</a> <a id="711" href="foundation.uniqueness-truncation.html#561" class="Bound">B</a> <a id="713" href="foundation.uniqueness-truncation.html#621" class="Bound">C</a><a id="714" class="Symbol">}</a> <a id="716" class="Symbol">(</a><a id="717" href="foundation.uniqueness-truncation.html#717" class="Bound">H</a> <a id="719" class="Symbol">:</a> <a id="721" class="Symbol">(</a><a id="722" href="foundation.uniqueness-truncation.html#681" class="Bound">h</a> <a id="724" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="726" href="foundation.uniqueness-truncation.html#587" class="Bound">f</a><a id="727" class="Symbol">)</a> <a id="729" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="731" href="foundation.uniqueness-truncation.html#647" class="Bound">g</a><a id="732" class="Symbol">)</a>
  <a id="736" class="Keyword">where</a>

<a id="743" class="Comment">{-

  abstract
    is-equiv-is-truncation-is-truncation :
      is-truncation B f → is-truncation C g → is-equiv h
    is-equiv-is-truncation-is-truncation K L =
      is-equiv-is-invertible
        ( map-inv-is-equiv (L B) f)
        ( {!!})
        {!!}

      is-equiv-is-invertible
        ( pr1 (center K))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Ug C)
            { h ∘ k}
            { id}
            ( ( precomp-comp-Set-Quotient R C g B k C h) ∙
              ( ( ap (λ t → precomp-Set-Quotient R B t C h) α) ∙
                ( ( eq-htpy-reflecting-map-equivalence-relation R C
                    ( precomp-Set-Quotient R B f C h) g H) ∙
                  ( inv (precomp-id-Set-Quotient R C g)))))))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Uf B)
            { k ∘ h}
            { id}
            ( ( precomp-comp-Set-Quotient R B f C h B k) ∙
              ( ( ap
                  ( λ t → precomp-Set-Quotient R C t B k)
                  ( eq-htpy-reflecting-map-equivalence-relation R C
                    ( precomp-Set-Quotient R B f C h) g H)) ∙
                ( ( α) ∙
                  ( inv (precomp-id-Set-Quotient R B f)))))))
      where
      K : is-contr
            ( Σ ( type-hom-Set C B)
                ( λ h →
                  ( h ∘ map-reflecting-map-equivalence-relation R g) ~
                  ( map-reflecting-map-equivalence-relation R f)))
      K = universal-property-set-quotient-is-set-quotient R C g Ug B f
      k : type-Set C → type-Set B
      k = pr1 (center K)
      α : Id (precomp-Set-Quotient R C g B k) f
      α = eq-htpy-reflecting-map-equivalence-relation R B
            ( precomp-Set-Quotient R C g B k)
            ( f)
            ( pr2 (center K))
            -}</a>
</pre>
### Uniqueness of set truncations

<pre class="Agda"><a id="2568" class="Comment">{-
module _
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (C : Set l3) (g : A → type-Set C) {h : type-hom-Set B C}
  (H : (h ∘ f) ~ g)
  where

  abstract
    is-equiv-is-set-truncation-is-set-truncation :
      ({l : Level} → is-set-truncation l B f) →
      ({l : Level} → is-set-truncation l C g) →
      is-equiv h
    is-equiv-is-set-truncation-is-set-truncation Sf Sg =
      is-equiv-is-set-quotient-is-set-quotient
        ( mere-eq-equivalence-relation A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( C)
        ( reflecting-map-mere-eq C g)
        ( H)
        ( λ {l} → is-set-quotient-is-set-truncation B f Sf)
        ( λ {l} → is-set-quotient-is-set-truncation C g Sg)

  abstract
    is-set-truncation-is-equiv-is-set-truncation :
      ({l : Level} → is-set-truncation l C g) → is-equiv h →
      {l : Level} → is-set-truncation l B f
    is-set-truncation-is-equiv-is-set-truncation Sg Eh =
      is-set-truncation-is-set-quotient B f
        ( is-set-quotient-is-equiv-is-set-quotient
          ( mere-eq-equivalence-relation A)
          ( B)
          ( reflecting-map-mere-eq B f)
          ( C)
          ( reflecting-map-mere-eq C g)
          ( H)
          ( is-set-quotient-is-set-truncation C g Sg)
          ( Eh))

  abstract
    is-set-truncation-is-set-truncation-is-equiv :
      is-equiv h → ({l : Level} → is-set-truncation l B f) →
      {l : Level} → is-set-truncation l C g
    is-set-truncation-is-set-truncation-is-equiv Eh Sf =
      is-set-truncation-is-set-quotient C g
        ( is-set-quotient-is-set-quotient-is-equiv
          ( mere-eq-equivalence-relation A)
          ( B)
          ( reflecting-map-mere-eq B f)
          ( C)
          ( reflecting-map-mere-eq C g)
          ( H)
          ( Eh)
          ( is-set-quotient-is-set-truncation B f Sf))

module _
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  (C : Set l3) (g : A → type-Set C)
  (Sf : {l : Level} → is-set-truncation l B f)
  (Sg : {l : Level} → is-set-truncation l C g)
  where

  abstract
    uniqueness-set-truncation :
      is-contr (Σ (type-Set B ≃ type-Set C) (λ e → (map-equiv e ∘ f) ~ g))
    uniqueness-set-truncation =
      uniqueness-set-quotient
        ( mere-eq-equivalence-relation A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( is-set-quotient-is-set-truncation B f Sf)
        ( C)
        ( reflecting-map-mere-eq C g)
        ( is-set-quotient-is-set-truncation C g Sg)

  equiv-uniqueness-set-truncation : type-Set B ≃ type-Set C
  equiv-uniqueness-set-truncation =
    pr1 (center uniqueness-set-truncation)

  map-equiv-uniqueness-set-truncation : type-Set B → type-Set C
  map-equiv-uniqueness-set-truncation =
    map-equiv equiv-uniqueness-set-truncation

  triangle-uniqueness-set-truncation :
    (map-equiv-uniqueness-set-truncation ∘ f) ~ g
  triangle-uniqueness-set-truncation =
    pr2 (center uniqueness-set-truncation)
-}</a>
</pre>