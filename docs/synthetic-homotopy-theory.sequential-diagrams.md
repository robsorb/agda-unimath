# Sequential diagrams

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="synthetic-homotopy-theory.sequential-diagrams.html" class="Module">synthetic-homotopy-theory.sequential-diagrams</a> <a id="85" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="195" class="Keyword">open</a> <a id="200" class="Keyword">import</a> <a id="207" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A **sequential diagram** `(A, a)` is a [sequence](lists.sequences.md) of types
`A : ℕ → 𝒰` over the natural numbers, equipped with a family of maps
`aₙ : Aₙ → Aₙ₊₁` for all `n`.

They can be represented by diagrams

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯
```

extending infinitely to the right.

Sequential diagrams are dual to
[inverse sequential diagrams](foundation.inverse-sequential-diagrams.md), and
are also sometimes called **cotowers**.

## Definition

<pre class="Agda"><a id="sequential-diagram"></a><a id="872" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="891" class="Symbol">:</a> <a id="893" class="Symbol">(</a><a id="894" href="synthetic-homotopy-theory.sequential-diagrams.html#894" class="Bound">l</a> <a id="896" class="Symbol">:</a> <a id="898" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="903" class="Symbol">)</a> <a id="905" class="Symbol">→</a> <a id="907" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="910" class="Symbol">(</a><a id="911" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="916" href="synthetic-homotopy-theory.sequential-diagrams.html#894" class="Bound">l</a><a id="917" class="Symbol">)</a>
<a id="919" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="938" href="synthetic-homotopy-theory.sequential-diagrams.html#938" class="Bound">l</a> <a id="940" class="Symbol">=</a> <a id="942" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="944" class="Symbol">(</a><a id="945" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="947" class="Symbol">→</a> <a id="949" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="952" href="synthetic-homotopy-theory.sequential-diagrams.html#938" class="Bound">l</a><a id="953" class="Symbol">)</a> <a id="955" class="Symbol">(λ</a> <a id="958" href="synthetic-homotopy-theory.sequential-diagrams.html#958" class="Bound">A</a> <a id="960" class="Symbol">→</a> <a id="962" class="Symbol">(</a><a id="963" href="synthetic-homotopy-theory.sequential-diagrams.html#963" class="Bound">n</a> <a id="965" class="Symbol">:</a> <a id="967" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="968" class="Symbol">)</a> <a id="970" class="Symbol">→</a> <a id="972" href="synthetic-homotopy-theory.sequential-diagrams.html#958" class="Bound">A</a> <a id="974" href="synthetic-homotopy-theory.sequential-diagrams.html#963" class="Bound">n</a> <a id="976" class="Symbol">→</a> <a id="978" href="synthetic-homotopy-theory.sequential-diagrams.html#958" class="Bound">A</a> <a id="980" class="Symbol">(</a><a id="981" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="988" href="synthetic-homotopy-theory.sequential-diagrams.html#963" class="Bound">n</a><a id="989" class="Symbol">))</a>

<a id="993" class="Keyword">module</a> <a id="1000" href="synthetic-homotopy-theory.sequential-diagrams.html#1000" class="Module">_</a>
  <a id="1004" class="Symbol">{</a> <a id="1006" href="synthetic-homotopy-theory.sequential-diagrams.html#1006" class="Bound">l</a> <a id="1008" class="Symbol">:</a> <a id="1010" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1015" class="Symbol">}</a> <a id="1017" class="Symbol">(</a><a id="1018" href="synthetic-homotopy-theory.sequential-diagrams.html#1018" class="Bound">A</a> <a id="1020" class="Symbol">:</a> <a id="1022" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="1041" href="synthetic-homotopy-theory.sequential-diagrams.html#1006" class="Bound">l</a><a id="1042" class="Symbol">)</a>
  <a id="1046" class="Keyword">where</a>

  <a id="1055" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="1081" class="Symbol">:</a> <a id="1083" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1085" class="Symbol">→</a> <a id="1087" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1090" href="synthetic-homotopy-theory.sequential-diagrams.html#1006" class="Bound">l</a>
  <a id="1094" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="1120" class="Symbol">=</a> <a id="1122" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1126" href="synthetic-homotopy-theory.sequential-diagrams.html#1018" class="Bound">A</a>

  <a id="1131" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="1154" class="Symbol">:</a>
    <a id="1160" class="Symbol">(</a><a id="1161" href="synthetic-homotopy-theory.sequential-diagrams.html#1161" class="Bound">n</a> <a id="1163" class="Symbol">:</a> <a id="1165" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1166" class="Symbol">)</a> <a id="1168" class="Symbol">→</a> <a id="1170" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="1196" href="synthetic-homotopy-theory.sequential-diagrams.html#1161" class="Bound">n</a> <a id="1198" class="Symbol">→</a> <a id="1200" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="1226" class="Symbol">(</a><a id="1227" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1234" href="synthetic-homotopy-theory.sequential-diagrams.html#1161" class="Bound">n</a><a id="1235" class="Symbol">)</a>
  <a id="1239" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="1262" class="Symbol">=</a> <a id="1264" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1268" href="synthetic-homotopy-theory.sequential-diagrams.html#1018" class="Bound">A</a>
</pre>
<pre class="Agda"><a id="1283" class="Keyword">module</a> <a id="1290" href="synthetic-homotopy-theory.sequential-diagrams.html#1290" class="Module">_</a>
  <a id="1294" class="Symbol">{</a> <a id="1296" href="synthetic-homotopy-theory.sequential-diagrams.html#1296" class="Bound">l</a> <a id="1298" class="Symbol">:</a> <a id="1300" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1305" class="Symbol">}</a> <a id="1307" class="Symbol">(</a><a id="1308" href="synthetic-homotopy-theory.sequential-diagrams.html#1308" class="Bound">X</a> <a id="1310" class="Symbol">:</a> <a id="1312" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1315" href="synthetic-homotopy-theory.sequential-diagrams.html#1296" class="Bound">l</a><a id="1316" class="Symbol">)</a>
  <a id="1320" class="Keyword">where</a>

  <a id="1329" href="synthetic-homotopy-theory.sequential-diagrams.html#1329" class="Function">constant-sequential-diagram</a> <a id="1357" class="Symbol">:</a> <a id="1359" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="1378" href="synthetic-homotopy-theory.sequential-diagrams.html#1296" class="Bound">l</a>
  <a id="1382" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1386" href="synthetic-homotopy-theory.sequential-diagrams.html#1329" class="Function">constant-sequential-diagram</a> <a id="1414" class="Symbol">_</a> <a id="1416" class="Symbol">=</a> <a id="1418" href="synthetic-homotopy-theory.sequential-diagrams.html#1308" class="Bound">X</a>
  <a id="1422" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1426" href="synthetic-homotopy-theory.sequential-diagrams.html#1329" class="Function">constant-sequential-diagram</a> <a id="1454" class="Symbol">_</a> <a id="1456" href="synthetic-homotopy-theory.sequential-diagrams.html#1456" class="Bound">x</a> <a id="1458" class="Symbol">=</a> <a id="1460" href="synthetic-homotopy-theory.sequential-diagrams.html#1456" class="Bound">x</a>
</pre>
## Properties

The [identity type](foundation.identity-types.md) of sequential diagrams is
characterized in the file about
[equivalences of sequential diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md).

### Postcomposition sequential diagrams

Given a sequential diagram `A` and a type `X` there is a sequential diagram
`X → A` defined by levelwise postcomposition.

```text
           (f₀ ∘ -)          (f₁ ∘ -)          (f₂ ∘ -)
  (X → A₀) -------> (X → A₁) -------> (X → A₂) -------> (X → A₃) -------> ⋯
```

<pre class="Agda"><a id="2010" class="Keyword">module</a> <a id="2017" href="synthetic-homotopy-theory.sequential-diagrams.html#2017" class="Module">_</a>
  <a id="2021" class="Symbol">{</a><a id="2022" href="synthetic-homotopy-theory.sequential-diagrams.html#2022" class="Bound">l1</a> <a id="2025" href="synthetic-homotopy-theory.sequential-diagrams.html#2025" class="Bound">l2</a> <a id="2028" class="Symbol">:</a> <a id="2030" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2035" class="Symbol">}</a> <a id="2037" class="Symbol">(</a><a id="2038" href="synthetic-homotopy-theory.sequential-diagrams.html#2038" class="Bound">X</a> <a id="2040" class="Symbol">:</a> <a id="2042" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2045" href="synthetic-homotopy-theory.sequential-diagrams.html#2022" class="Bound">l1</a><a id="2047" class="Symbol">)</a> <a id="2049" class="Symbol">(</a><a id="2050" href="synthetic-homotopy-theory.sequential-diagrams.html#2050" class="Bound">A</a> <a id="2052" class="Symbol">:</a> <a id="2054" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="2073" href="synthetic-homotopy-theory.sequential-diagrams.html#2025" class="Bound">l2</a><a id="2075" class="Symbol">)</a>
  <a id="2079" class="Keyword">where</a>

  <a id="2088" href="synthetic-homotopy-theory.sequential-diagrams.html#2088" class="Function">postcomp-sequential-diagram</a> <a id="2116" class="Symbol">:</a> <a id="2118" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="2137" class="Symbol">(</a><a id="2138" href="synthetic-homotopy-theory.sequential-diagrams.html#2022" class="Bound">l1</a> <a id="2141" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2143" href="synthetic-homotopy-theory.sequential-diagrams.html#2025" class="Bound">l2</a><a id="2145" class="Symbol">)</a>
  <a id="2149" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2153" href="synthetic-homotopy-theory.sequential-diagrams.html#2088" class="Function">postcomp-sequential-diagram</a> <a id="2181" href="synthetic-homotopy-theory.sequential-diagrams.html#2181" class="Bound">n</a> <a id="2183" class="Symbol">=</a> <a id="2185" href="synthetic-homotopy-theory.sequential-diagrams.html#2038" class="Bound">X</a> <a id="2187" class="Symbol">→</a> <a id="2189" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="2215" href="synthetic-homotopy-theory.sequential-diagrams.html#2050" class="Bound">A</a> <a id="2217" href="synthetic-homotopy-theory.sequential-diagrams.html#2181" class="Bound">n</a>
  <a id="2221" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2225" href="synthetic-homotopy-theory.sequential-diagrams.html#2088" class="Function">postcomp-sequential-diagram</a> <a id="2253" href="synthetic-homotopy-theory.sequential-diagrams.html#2253" class="Bound">n</a> <a id="2255" href="synthetic-homotopy-theory.sequential-diagrams.html#2255" class="Bound">g</a> <a id="2257" href="synthetic-homotopy-theory.sequential-diagrams.html#2257" class="Bound">x</a> <a id="2259" class="Symbol">=</a> <a id="2261" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="2284" href="synthetic-homotopy-theory.sequential-diagrams.html#2050" class="Bound">A</a> <a id="2286" href="synthetic-homotopy-theory.sequential-diagrams.html#2253" class="Bound">n</a> <a id="2288" class="Symbol">(</a><a id="2289" href="synthetic-homotopy-theory.sequential-diagrams.html#2255" class="Bound">g</a> <a id="2291" href="synthetic-homotopy-theory.sequential-diagrams.html#2257" class="Bound">x</a><a id="2292" class="Symbol">)</a>
</pre>
### A sequential diagram of contractible types consists of equivalences

This is an easy corollary of the fact that every map between
[contractible types](foundation-core.contractible-types.md) is an
[equivalence](foundation-core.equivalences.md).

<pre class="Agda"><a id="2556" class="Keyword">module</a> <a id="2563" href="synthetic-homotopy-theory.sequential-diagrams.html#2563" class="Module">_</a>
  <a id="2567" class="Symbol">{</a><a id="2568" href="synthetic-homotopy-theory.sequential-diagrams.html#2568" class="Bound">l1</a> <a id="2571" class="Symbol">:</a> <a id="2573" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2578" class="Symbol">}</a> <a id="2580" class="Symbol">{</a><a id="2581" href="synthetic-homotopy-theory.sequential-diagrams.html#2581" class="Bound">A</a> <a id="2583" class="Symbol">:</a> <a id="2585" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="2604" href="synthetic-homotopy-theory.sequential-diagrams.html#2568" class="Bound">l1</a><a id="2606" class="Symbol">}</a>
  <a id="2610" class="Keyword">where</a>

  <a id="2619" href="synthetic-homotopy-theory.sequential-diagrams.html#2619" class="Function">is-equiv-sequential-diagram-is-contr</a> <a id="2656" class="Symbol">:</a>
    <a id="2662" class="Symbol">((</a><a id="2664" href="synthetic-homotopy-theory.sequential-diagrams.html#2664" class="Bound">n</a> <a id="2666" class="Symbol">:</a> <a id="2668" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2669" class="Symbol">)</a> <a id="2671" class="Symbol">→</a> <a id="2673" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2682" class="Symbol">(</a><a id="2683" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="2709" href="synthetic-homotopy-theory.sequential-diagrams.html#2581" class="Bound">A</a> <a id="2711" href="synthetic-homotopy-theory.sequential-diagrams.html#2664" class="Bound">n</a><a id="2712" class="Symbol">))</a> <a id="2715" class="Symbol">→</a>
    <a id="2721" class="Symbol">(</a><a id="2722" href="synthetic-homotopy-theory.sequential-diagrams.html#2722" class="Bound">n</a> <a id="2724" class="Symbol">:</a> <a id="2726" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2727" class="Symbol">)</a> <a id="2729" class="Symbol">→</a> <a id="2731" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="2740" class="Symbol">(</a><a id="2741" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="2764" href="synthetic-homotopy-theory.sequential-diagrams.html#2581" class="Bound">A</a> <a id="2766" href="synthetic-homotopy-theory.sequential-diagrams.html#2722" class="Bound">n</a><a id="2767" class="Symbol">)</a>
  <a id="2771" href="synthetic-homotopy-theory.sequential-diagrams.html#2619" class="Function">is-equiv-sequential-diagram-is-contr</a> <a id="2808" href="synthetic-homotopy-theory.sequential-diagrams.html#2808" class="Bound">contrs</a> <a id="2815" href="synthetic-homotopy-theory.sequential-diagrams.html#2815" class="Bound">n</a> <a id="2817" class="Symbol">=</a>
    <a id="2823" href="foundation-core.contractible-types.html#3139" class="Function">is-equiv-is-contr</a>
      <a id="2847" class="Symbol">(</a> <a id="2849" href="synthetic-homotopy-theory.sequential-diagrams.html#1131" class="Function">map-sequential-diagram</a> <a id="2872" href="synthetic-homotopy-theory.sequential-diagrams.html#2581" class="Bound">A</a> <a id="2874" href="synthetic-homotopy-theory.sequential-diagrams.html#2815" class="Bound">n</a><a id="2875" class="Symbol">)</a>
      <a id="2883" class="Symbol">(</a> <a id="2885" href="synthetic-homotopy-theory.sequential-diagrams.html#2808" class="Bound">contrs</a> <a id="2892" href="synthetic-homotopy-theory.sequential-diagrams.html#2815" class="Bound">n</a><a id="2893" class="Symbol">)</a>
      <a id="2901" class="Symbol">(</a> <a id="2903" href="synthetic-homotopy-theory.sequential-diagrams.html#2808" class="Bound">contrs</a> <a id="2910" class="Symbol">(</a><a id="2911" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2918" href="synthetic-homotopy-theory.sequential-diagrams.html#2815" class="Bound">n</a><a id="2919" class="Symbol">))</a>
</pre>
## References

{{#bibliography}} {{#reference SvDR20}}
