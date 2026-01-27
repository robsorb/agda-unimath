# The flattening lemma for sequential colimits

<pre class="Agda"><a id="57" class="Keyword">module</a> <a id="64" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html" class="Module">synthetic-homotopy-theory.flattening-lemma-sequential-colimits</a> <a id="127" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="foundation.equivalences-double-arrows.html" class="Module">foundation.equivalences-double-arrows</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="405" class="Keyword">open</a> <a id="410" class="Keyword">import</a> <a id="417" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="439" class="Keyword">open</a> <a id="444" class="Keyword">import</a> <a id="451" href="foundation.type-arithmetic-dependent-pair-types.html" class="Module">foundation.type-arithmetic-dependent-pair-types</a>
<a id="499" class="Keyword">open</a> <a id="504" class="Keyword">import</a> <a id="511" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="538" class="Keyword">open</a> <a id="543" class="Keyword">import</a> <a id="550" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="596" class="Keyword">open</a> <a id="601" class="Keyword">import</a> <a id="608" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.cocones-under-sequential-diagrams</a>
<a id="668" class="Keyword">open</a> <a id="673" class="Keyword">import</a> <a id="680" href="synthetic-homotopy-theory.coforks.html" class="Module">synthetic-homotopy-theory.coforks</a>
<a id="714" class="Keyword">open</a> <a id="719" class="Keyword">import</a> <a id="726" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams</a>
<a id="794" class="Keyword">open</a> <a id="799" class="Keyword">import</a> <a id="806" href="synthetic-homotopy-theory.dependent-universal-property-sequential-colimits.html" class="Module">synthetic-homotopy-theory.dependent-universal-property-sequential-colimits</a>
<a id="881" class="Keyword">open</a> <a id="886" class="Keyword">import</a> <a id="893" href="synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows.html" class="Module">synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows</a>
<a id="973" class="Keyword">open</a> <a id="978" class="Keyword">import</a> <a id="985" href="synthetic-homotopy-theory.families-descent-data-sequential-colimits.html" class="Module">synthetic-homotopy-theory.families-descent-data-sequential-colimits</a>
<a id="1053" class="Keyword">open</a> <a id="1058" class="Keyword">import</a> <a id="1065" href="synthetic-homotopy-theory.flattening-lemma-coequalizers.html" class="Module">synthetic-homotopy-theory.flattening-lemma-coequalizers</a>
<a id="1121" class="Keyword">open</a> <a id="1126" class="Keyword">import</a> <a id="1133" href="synthetic-homotopy-theory.sequential-diagrams.html" class="Module">synthetic-homotopy-theory.sequential-diagrams</a>
<a id="1179" class="Keyword">open</a> <a id="1184" class="Keyword">import</a> <a id="1191" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.total-cocones-families-sequential-diagrams</a>
<a id="1260" class="Keyword">open</a> <a id="1265" class="Keyword">import</a> <a id="1272" href="synthetic-homotopy-theory.total-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.total-sequential-diagrams</a>
<a id="1324" class="Keyword">open</a> <a id="1329" class="Keyword">import</a> <a id="1336" href="synthetic-homotopy-theory.universal-property-coequalizers.html" class="Module">synthetic-homotopy-theory.universal-property-coequalizers</a>
<a id="1394" class="Keyword">open</a> <a id="1399" class="Keyword">import</a> <a id="1406" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html" class="Module">synthetic-homotopy-theory.universal-property-sequential-colimits</a>
</pre>
</details>

## Idea

The
{{#concept "flattening lemma" Disambiguation="sequential colimits" Agda=flattening-lemma-sequential-colimit}}
for
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
states that sequential colimits commute with
[dependent pair types](foundation.dependent-pair-types.md). Specifically, given
a [cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)

```text
  A₀ ---> A₁ ---> A₂ ---> ⋯ ---> X
```

with the universal property of sequential colimits, and a family `P : X → 𝒰`,
the induced cocone under the
[total sequential diagram](synthetic-homotopy-theory.total-sequential-diagrams.md)

```text
  Σ (a : A₀) P(i₀ a) ---> Σ (a : A₁) P(i₁ a) ---> ⋯ ---> Σ (x : X) P(x)
```

is again a sequential colimit.

The result may be read as
`colimₙ (Σ (a : Aₙ) P(iₙ a)) ≃ Σ (a : colimₙ Aₙ) P(a)`.

More generally, given a type family `P : X → 𝒰` and
[descent data](synthetic-homotopy-theory.descent-data-sequential-colimits.md)
`B`
[associated to it](synthetic-homotopy-theory.families-descent-data-sequential-colimits.md),
we have that the induced cocone

```text
  Σ A₀ B₀ ---> Σ A₁ B₁ ---> ⋯ ---> Σ X P
```

is a sequential colimit.

## Theorems

### Flattening lemma for sequential colimits

Similarly to the proof of the
[flattening lemma for coequalizers](synthetic-homotopy-theory.flattening-lemma-coequalizers.md),
this proof uses the fact that sequential colimits correspond to certain
coequalizers, which is recorded in
[`synthetic-homotopy-theory.dependent-universal-property-sequential-colimits`](synthetic-homotopy-theory.dependent-universal-property-sequential-colimits.md),
so it suffices to invoke the flattening lemma for coequalizers.

**Proof:** The diagram we construct is

```text
                               ------->
  Σ (n : ℕ) Σ (a : Aₙ) P(iₙ a) -------> Σ (n : ℕ) Σ (a : Aₙ) P(iₙ a) ----> Σ (x : X) P(x)
             |                                     |                            |
 inv-assoc-Σ | ≃                       inv-assoc-Σ | ≃                       id | ≃
             |                                     |                            |
             ∨                --------->           ∨                            ∨
   Σ ((n, a) : Σ ℕ A) P(iₙ a) ---------> Σ ((n, a) : Σ ℕ A) P(iₙ a) -----> Σ (x : X) P(x) ,
```

where the top is the cofork corresponding to the cocone for the flattening
lemma, and the bottom is the cofork obtained by flattening the cofork
corresponding to the given base cocone.

By assumption, the original cocone is a sequential colimit, which implies that
its corresponding cofork is a coequalizer. The flattening lemma for coequalizers
implies that the bottom cofork is a coequalizer, which in turn implies that the
top cofork is a coequalizer, hence the flattening of the original cocone is a
sequential colimit.

<pre class="Agda"><a id="4340" class="Keyword">module</a> <a id="4347" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4347" class="Module">_</a>
  <a id="4351" class="Symbol">{</a> <a id="4353" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4353" class="Bound">l1</a> <a id="4356" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4356" class="Bound">l2</a> <a id="4359" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4359" class="Bound">l3</a> <a id="4362" class="Symbol">:</a> <a id="4364" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4369" class="Symbol">}</a> <a id="4371" class="Symbol">{</a><a id="4372" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4372" class="Bound">A</a> <a id="4374" class="Symbol">:</a> <a id="4376" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="4395" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4353" class="Bound">l1</a><a id="4397" class="Symbol">}</a> <a id="4399" class="Symbol">{</a><a id="4400" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4400" class="Bound">X</a> <a id="4402" class="Symbol">:</a> <a id="4404" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4407" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4356" class="Bound">l2</a><a id="4409" class="Symbol">}</a>
  <a id="4413" class="Symbol">(</a> <a id="4415" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a> <a id="4417" class="Symbol">:</a> <a id="4419" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="4445" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4372" class="Bound">A</a> <a id="4447" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4400" class="Bound">X</a><a id="4448" class="Symbol">)</a>
  <a id="4452" class="Symbol">(</a> <a id="4454" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a> <a id="4456" class="Symbol">:</a> <a id="4458" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4400" class="Bound">X</a> <a id="4460" class="Symbol">→</a> <a id="4462" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4465" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4359" class="Bound">l3</a><a id="4467" class="Symbol">)</a>
  <a id="4471" class="Keyword">where</a>

  <a id="4480" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4480" class="Function">equiv-double-arrow-flattening-lemma-sequential-colimit</a> <a id="4535" class="Symbol">:</a>
    <a id="4541" href="foundation.equivalences-double-arrows.html#2241" class="Function">equiv-double-arrow</a>
      <a id="4566" class="Symbol">(</a> <a id="4568" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#4912" class="Function">double-arrow-sequential-diagram</a>
        <a id="4608" class="Symbol">(</a> <a id="4610" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#4239" class="Function">total-sequential-diagram-family-cocone-sequential-diagram</a> <a id="4668" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a> <a id="4670" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="4671" class="Symbol">))</a>
      <a id="4680" class="Symbol">(</a> <a id="4682" href="synthetic-homotopy-theory.flattening-lemma-coequalizers.html#2505" class="Function">double-arrow-flattening-lemma-coequalizer</a>
        <a id="4732" class="Symbol">(</a> <a id="4734" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#4912" class="Function">double-arrow-sequential-diagram</a> <a id="4766" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4372" class="Bound">A</a><a id="4767" class="Symbol">)</a>
        <a id="4777" class="Symbol">(</a> <a id="4779" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="4780" class="Symbol">)</a>
        <a id="4790" class="Symbol">(</a> <a id="4792" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#7245" class="Function">cofork-cocone-sequential-diagram</a> <a id="4825" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a><a id="4826" class="Symbol">))</a>
  <a id="4831" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4835" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4480" class="Function">equiv-double-arrow-flattening-lemma-sequential-colimit</a> <a id="4890" class="Symbol">=</a>
    <a id="4896" href="foundation.type-arithmetic-dependent-pair-types.html#6981" class="Function">inv-associative-Σ</a>
      <a id="4920" class="Symbol">(</a> <a id="4922" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="4923" class="Symbol">)</a>
      <a id="4931" class="Symbol">(</a> <a id="4933" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="4959" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4372" class="Bound">A</a><a id="4960" class="Symbol">)</a>
      <a id="4968" class="Symbol">(</a> <a id="4970" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a> <a id="4972" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="4974" href="foundation.dependent-pair-types.html#873" class="Function">ind-Σ</a> <a id="4980" class="Symbol">(</a><a id="4981" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2233" class="Function">map-cocone-sequential-diagram</a> <a id="5011" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a><a id="5012" class="Symbol">))</a>
  <a id="5017" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5021" class="Symbol">(</a><a id="5022" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5026" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4480" class="Function">equiv-double-arrow-flattening-lemma-sequential-colimit</a><a id="5080" class="Symbol">)</a> <a id="5082" class="Symbol">=</a>
    <a id="5088" href="foundation.type-arithmetic-dependent-pair-types.html#6981" class="Function">inv-associative-Σ</a>
      <a id="5112" class="Symbol">(</a> <a id="5114" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="5115" class="Symbol">)</a>
      <a id="5123" class="Symbol">(</a> <a id="5125" href="synthetic-homotopy-theory.sequential-diagrams.html#1055" class="Function">family-sequential-diagram</a> <a id="5151" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4372" class="Bound">A</a><a id="5152" class="Symbol">)</a>
      <a id="5160" class="Symbol">(</a> <a id="5162" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a> <a id="5164" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="5166" href="foundation.dependent-pair-types.html#873" class="Function">ind-Σ</a> <a id="5172" class="Symbol">(</a><a id="5173" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#2233" class="Function">map-cocone-sequential-diagram</a> <a id="5203" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a><a id="5204" class="Symbol">))</a>
  <a id="5209" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5213" class="Symbol">(</a><a id="5214" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5218" class="Symbol">(</a><a id="5219" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5223" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4480" class="Function">equiv-double-arrow-flattening-lemma-sequential-colimit</a><a id="5277" class="Symbol">))</a> <a id="5280" class="Symbol">=</a>
    <a id="5286" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="5298" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5302" class="Symbol">(</a><a id="5303" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5307" class="Symbol">(</a><a id="5308" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5312" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4480" class="Function">equiv-double-arrow-flattening-lemma-sequential-colimit</a><a id="5366" class="Symbol">))</a> <a id="5369" class="Symbol">=</a>
    <a id="5375" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>

  <a id="5388" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#5388" class="Function">equiv-cofork-flattening-lemma-sequential-colimit</a> <a id="5437" class="Symbol">:</a>
    <a id="5443" href="synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows.html#5518" class="Function">equiv-cofork-equiv-double-arrow</a>
      <a id="5481" class="Symbol">(</a> <a id="5483" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#7245" class="Function">cofork-cocone-sequential-diagram</a>
        <a id="5524" class="Symbol">(</a> <a id="5526" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#4541" class="Function">total-cocone-family-cocone-sequential-diagram</a> <a id="5572" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a> <a id="5574" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="5575" class="Symbol">))</a>
      <a id="5584" class="Symbol">(</a> <a id="5586" href="synthetic-homotopy-theory.flattening-lemma-coequalizers.html#2774" class="Function">cofork-flattening-lemma-coequalizer</a>
        <a id="5630" class="Symbol">(</a> <a id="5632" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#4912" class="Function">double-arrow-sequential-diagram</a> <a id="5664" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4372" class="Bound">A</a><a id="5665" class="Symbol">)</a>
        <a id="5675" class="Symbol">(</a> <a id="5677" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="5678" class="Symbol">)</a>
        <a id="5688" class="Symbol">(</a> <a id="5690" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#7245" class="Function">cofork-cocone-sequential-diagram</a> <a id="5723" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a><a id="5724" class="Symbol">))</a>
      <a id="5733" class="Symbol">(</a> <a id="5735" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4480" class="Function">equiv-double-arrow-flattening-lemma-sequential-colimit</a><a id="5789" class="Symbol">)</a>
  <a id="5793" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5797" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#5388" class="Function">equiv-cofork-flattening-lemma-sequential-colimit</a> <a id="5846" class="Symbol">=</a> <a id="5848" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
  <a id="5859" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="5863" class="Symbol">(</a><a id="5864" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5868" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#5388" class="Function">equiv-cofork-flattening-lemma-sequential-colimit</a><a id="5916" class="Symbol">)</a> <a id="5918" class="Symbol">=</a>
    <a id="5924" href="foundation-core.homotopies.html#2724" class="Function">refl-htpy</a>
  <a id="5936" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5940" class="Symbol">(</a><a id="5941" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="5945" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#5388" class="Function">equiv-cofork-flattening-lemma-sequential-colimit</a><a id="5993" class="Symbol">)</a> <a id="5995" class="Symbol">=</a>
    <a id="6001" href="foundation-core.homotopies.html#2897" class="Function">inv-htpy</a>
      <a id="6016" class="Symbol">(</a> <a id="6018" class="Symbol">(</a> <a id="6020" href="foundation-core.homotopies.html#5171" class="Function">right-unit-htpy</a><a id="6035" class="Symbol">)</a> <a id="6037" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a>
        <a id="6048" class="Symbol">(</a> <a id="6050" href="foundation-core.homotopies.html#5171" class="Function">right-unit-htpy</a><a id="6065" class="Symbol">)</a> <a id="6067" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a>
        <a id="6078" class="Symbol">(</a> <a id="6080" href="foundation.whiskering-homotopies-composition.html#4058" class="Function">left-unit-law-left-whisker-comp</a>
          <a id="6122" class="Symbol">(</a> <a id="6124" href="synthetic-homotopy-theory.coforks.html#2425" class="Function">coh-cofork</a> <a id="6135" class="Symbol">_</a>
            <a id="6149" class="Symbol">(</a> <a id="6151" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#7245" class="Function">cofork-cocone-sequential-diagram</a>
              <a id="6198" class="Symbol">(</a> <a id="6200" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#4541" class="Function">total-cocone-family-cocone-sequential-diagram</a> <a id="6246" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a> <a id="6248" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="6249" class="Symbol">)))))</a>

  <a id="6258" class="Keyword">abstract</a>
    <a id="6271" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#6271" class="Function">flattening-lemma-sequential-colimit</a> <a id="6307" class="Symbol">:</a>
      <a id="6315" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="6353" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a> <a id="6355" class="Symbol">→</a>
      <a id="6363" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a>
        <a id="6409" class="Symbol">(</a> <a id="6411" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#4541" class="Function">total-cocone-family-cocone-sequential-diagram</a> <a id="6457" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a> <a id="6459" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="6460" class="Symbol">)</a>
    <a id="6466" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#6271" class="Function">flattening-lemma-sequential-colimit</a> <a id="6502" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#6502" class="Bound">up-c</a> <a id="6507" class="Symbol">=</a>
      <a id="6515" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#7055" class="Function">universal-property-sequential-colimit-universal-property-coequalizer</a>
        <a id="6592" class="Symbol">(</a> <a id="6594" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#4541" class="Function">total-cocone-family-cocone-sequential-diagram</a> <a id="6640" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a> <a id="6642" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="6643" class="Symbol">)</a>
        <a id="6653" class="Symbol">(</a> <a id="6655" href="synthetic-homotopy-theory.universal-property-coequalizers.html#6086" class="Function">universal-property-coequalizer-equiv-cofork-equiv-double-arrow</a>
          <a id="6728" class="Symbol">(</a> <a id="6730" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#7245" class="Function">cofork-cocone-sequential-diagram</a>
            <a id="6775" class="Symbol">(</a> <a id="6777" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#4541" class="Function">total-cocone-family-cocone-sequential-diagram</a> <a id="6823" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a> <a id="6825" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="6826" class="Symbol">))</a>
          <a id="6839" class="Symbol">(</a> <a id="6841" href="synthetic-homotopy-theory.flattening-lemma-coequalizers.html#2774" class="Function">cofork-flattening-lemma-coequalizer</a> <a id="6877" class="Symbol">_</a>
            <a id="6891" class="Symbol">(</a> <a id="6893" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="6894" class="Symbol">)</a>
            <a id="6908" class="Symbol">(</a> <a id="6910" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#7245" class="Function">cofork-cocone-sequential-diagram</a> <a id="6943" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a><a id="6944" class="Symbol">))</a>
          <a id="6957" class="Symbol">(</a> <a id="6959" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4480" class="Function">equiv-double-arrow-flattening-lemma-sequential-colimit</a><a id="7013" class="Symbol">)</a>
          <a id="7025" class="Symbol">(</a> <a id="7027" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#5388" class="Function">equiv-cofork-flattening-lemma-sequential-colimit</a><a id="7075" class="Symbol">)</a>
          <a id="7087" class="Symbol">(</a> <a id="7089" href="synthetic-homotopy-theory.flattening-lemma-coequalizers.html#4400" class="Function">flattening-lemma-coequalizer</a> <a id="7118" class="Symbol">_</a>
            <a id="7132" class="Symbol">(</a> <a id="7134" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4454" class="Bound">P</a><a id="7135" class="Symbol">)</a>
            <a id="7149" class="Symbol">(</a> <a id="7151" href="synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams.html#7245" class="Function">cofork-cocone-sequential-diagram</a> <a id="7184" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a><a id="7185" class="Symbol">)</a>
            <a id="7199" class="Symbol">(</a> <a id="7201" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#7746" class="Function">universal-property-coequalizer-universal-property-sequential-colimit</a>
              <a id="7284" class="Symbol">(</a> <a id="7286" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#4415" class="Bound">c</a><a id="7287" class="Symbol">)</a>
              <a id="7303" class="Symbol">(</a> <a id="7305" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#6502" class="Bound">up-c</a><a id="7309" class="Symbol">))))</a>
</pre>
### Flattening lemma for sequential colimits with descent data

**Proof:** We have shown in
[`total-cocones-families-sequential-diagrams`](synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.md)
that given a family `P : X → 𝒰` with its descent data `B`, there is an
[equivalence of cocones](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.md)

```text
     Σ A₀ B₀ ---------> Σ A₁ B₁ ------> ⋯ -----> Σ X P
        |                  |                       |
        | ≃                | ≃                     | ≃
        ∨                  ∨                       ∨
  Σ A₀ (P ∘ i₀) ---> Σ A₁ (P ∘ i₁) ---> ⋯ -----> Σ X P .
```

The bottom cocone is a sequential colimit by the flattening lemma, and the
universal property of sequential colimits is preserved by equivalences, as shown
in
[`universal-property-sequential-colimits`](synthetic-homotopy-theory.universal-property-sequential-colimits.md).

<pre class="Agda"><a id="8285" class="Keyword">module</a> <a id="8292" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8292" class="Module">_</a>
  <a id="8296" class="Symbol">{</a><a id="8297" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8297" class="Bound">l1</a> <a id="8300" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8300" class="Bound">l2</a> <a id="8303" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8303" class="Bound">l3</a> <a id="8306" class="Symbol">:</a> <a id="8308" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="8313" class="Symbol">}</a> <a id="8315" class="Symbol">{</a><a id="8316" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8316" class="Bound">A</a> <a id="8318" class="Symbol">:</a> <a id="8320" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="8339" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8297" class="Bound">l1</a><a id="8341" class="Symbol">}</a>
  <a id="8345" class="Symbol">{</a><a id="8346" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8346" class="Bound">X</a> <a id="8348" class="Symbol">:</a> <a id="8350" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="8353" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8300" class="Bound">l2</a><a id="8355" class="Symbol">}</a> <a id="8357" class="Symbol">(</a><a id="8358" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8358" class="Bound">c</a> <a id="8360" class="Symbol">:</a> <a id="8362" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="8388" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8316" class="Bound">A</a> <a id="8390" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8346" class="Bound">X</a><a id="8391" class="Symbol">)</a>
  <a id="8395" class="Symbol">(</a><a id="8396" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8396" class="Bound">P</a> <a id="8398" class="Symbol">:</a> <a id="8400" href="synthetic-homotopy-theory.families-descent-data-sequential-colimits.html#1949" class="Function">family-with-descent-data-sequential-colimit</a> <a id="8444" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8358" class="Bound">c</a> <a id="8446" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8303" class="Bound">l3</a><a id="8448" class="Symbol">)</a>
  <a id="8452" class="Keyword">where</a>

  <a id="8461" class="Keyword">abstract</a>
    <a id="8474" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8474" class="Function">flattening-lemma-descent-data-sequential-colimit</a> <a id="8523" class="Symbol">:</a>
      <a id="8531" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="8569" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8358" class="Bound">c</a> <a id="8571" class="Symbol">→</a>
      <a id="8579" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a>
        <a id="8625" class="Symbol">(</a> <a id="8627" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#3002" class="Function">total-cocone-family-with-descent-data-sequential-colimit</a> <a id="8684" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8396" class="Bound">P</a><a id="8685" class="Symbol">)</a>
    <a id="8691" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8474" class="Function">flattening-lemma-descent-data-sequential-colimit</a> <a id="8740" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8740" class="Bound">up-c</a> <a id="8745" class="Symbol">=</a>
      <a id="8753" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#8884" class="Function">universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram</a>
        <a id="8837" class="Symbol">(</a> <a id="8839" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#5718" class="Function">equiv-total-sequential-diagram-family-with-descent-data-sequential-colimit</a>
          <a id="8924" class="Symbol">(</a> <a id="8926" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8396" class="Bound">P</a><a id="8927" class="Symbol">))</a>
        <a id="8938" class="Symbol">(</a> <a id="8940" href="synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.html#6397" class="Function">equiv-total-cocone-family-with-descent-data-sequential-colimit</a> <a id="9003" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8396" class="Bound">P</a><a id="9004" class="Symbol">)</a>
        <a id="9014" class="Symbol">(</a> <a id="9016" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#6271" class="Function">flattening-lemma-sequential-colimit</a> <a id="9052" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8358" class="Bound">c</a>
          <a id="9064" class="Symbol">(</a> <a id="9066" href="synthetic-homotopy-theory.families-descent-data-sequential-colimits.html#2600" class="Function">family-cocone-family-with-descent-data-sequential-colimit</a> <a id="9124" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8396" class="Bound">P</a><a id="9125" class="Symbol">)</a>
          <a id="9137" class="Symbol">(</a> <a id="9139" href="synthetic-homotopy-theory.flattening-lemma-sequential-colimits.html#8740" class="Bound">up-c</a><a id="9143" class="Symbol">))</a>
</pre>