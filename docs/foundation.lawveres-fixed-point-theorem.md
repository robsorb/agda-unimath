# Lawvere's fixed point theorem

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

{{#concept "Lawvere's fixed point theorem" Agda=fixed-point-theorem-Lawvere WD="Lawvere's fixed-point theorem" WDID=Q15809744}}
asserts that if there is a [surjective map](foundation.surjective-maps.md)
`A → (A → B)`, then any map `B → B` must have a
[fixed point](foundation.fixed-points-endofunctions.md).

## Theorem

<pre class="Agda"><a id="812" class="Keyword">module</a> <a id="819" href="foundation.lawveres-fixed-point-theorem.html#819" class="Module">_</a>
  <a id="823" class="Symbol">{</a><a id="824" href="foundation.lawveres-fixed-point-theorem.html#824" class="Bound">l1</a> <a id="827" href="foundation.lawveres-fixed-point-theorem.html#827" class="Bound">l2</a> <a id="830" class="Symbol">:</a> <a id="832" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="837" class="Symbol">}</a> <a id="839" class="Symbol">{</a><a id="840" href="foundation.lawveres-fixed-point-theorem.html#840" class="Bound">A</a> <a id="842" class="Symbol">:</a> <a id="844" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="847" href="foundation.lawveres-fixed-point-theorem.html#824" class="Bound">l1</a><a id="849" class="Symbol">}</a> <a id="851" class="Symbol">{</a><a id="852" href="foundation.lawveres-fixed-point-theorem.html#852" class="Bound">B</a> <a id="854" class="Symbol">:</a> <a id="856" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="859" href="foundation.lawveres-fixed-point-theorem.html#827" class="Bound">l2</a><a id="861" class="Symbol">}</a> <a id="863" class="Symbol">{</a><a id="864" href="foundation.lawveres-fixed-point-theorem.html#864" class="Bound">f</a> <a id="866" class="Symbol">:</a> <a id="868" href="foundation.lawveres-fixed-point-theorem.html#840" class="Bound">A</a> <a id="870" class="Symbol">→</a> <a id="872" href="foundation.lawveres-fixed-point-theorem.html#840" class="Bound">A</a> <a id="874" class="Symbol">→</a> <a id="876" href="foundation.lawveres-fixed-point-theorem.html#852" class="Bound">B</a><a id="877" class="Symbol">}</a>
  <a id="881" class="Keyword">where</a>

  <a id="890" class="Keyword">abstract</a>
    <a id="903" href="foundation.lawveres-fixed-point-theorem.html#903" class="Function">fixed-point-theorem-Lawvere</a> <a id="931" class="Symbol">:</a>
      <a id="939" href="foundation.surjective-maps.html#2524" class="Function">is-surjective</a> <a id="953" href="foundation.lawveres-fixed-point-theorem.html#864" class="Bound">f</a> <a id="955" class="Symbol">→</a> <a id="957" class="Symbol">(</a><a id="958" href="foundation.lawveres-fixed-point-theorem.html#958" class="Bound">h</a> <a id="960" class="Symbol">:</a> <a id="962" href="foundation.lawveres-fixed-point-theorem.html#852" class="Bound">B</a> <a id="964" class="Symbol">→</a> <a id="966" href="foundation.lawveres-fixed-point-theorem.html#852" class="Bound">B</a><a id="967" class="Symbol">)</a> <a id="969" class="Symbol">→</a> <a id="971" href="foundation.existential-quantification.html#3741" class="Function">exists-structure</a> <a id="988" href="foundation.lawveres-fixed-point-theorem.html#852" class="Bound">B</a> <a id="990" class="Symbol">(λ</a> <a id="993" href="foundation.lawveres-fixed-point-theorem.html#993" class="Bound">b</a> <a id="995" class="Symbol">→</a> <a id="997" href="foundation.lawveres-fixed-point-theorem.html#958" class="Bound">h</a> <a id="999" href="foundation.lawveres-fixed-point-theorem.html#993" class="Bound">b</a> <a id="1001" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1003" href="foundation.lawveres-fixed-point-theorem.html#993" class="Bound">b</a><a id="1004" class="Symbol">)</a>
    <a id="1010" href="foundation.lawveres-fixed-point-theorem.html#903" class="Function">fixed-point-theorem-Lawvere</a> <a id="1038" href="foundation.lawveres-fixed-point-theorem.html#1038" class="Bound">H</a> <a id="1040" href="foundation.lawveres-fixed-point-theorem.html#1040" class="Bound">h</a> <a id="1042" class="Symbol">=</a>
      <a id="1050" href="foundation.propositional-truncations.html#6198" class="Function">apply-universal-property-trunc-Prop</a>
        <a id="1094" class="Symbol">(</a> <a id="1096" href="foundation.lawveres-fixed-point-theorem.html#1038" class="Bound">H</a> <a id="1098" href="foundation.lawveres-fixed-point-theorem.html#1234" class="Function">g</a><a id="1099" class="Symbol">)</a>
        <a id="1109" class="Symbol">(</a> <a id="1111" href="foundation.existential-quantification.html#3654" class="Function">exists-structure-Prop</a> <a id="1133" href="foundation.lawveres-fixed-point-theorem.html#852" class="Bound">B</a> <a id="1135" class="Symbol">(λ</a> <a id="1138" href="foundation.lawveres-fixed-point-theorem.html#1138" class="Bound">b</a> <a id="1140" class="Symbol">→</a> <a id="1142" href="foundation.lawveres-fixed-point-theorem.html#1040" class="Bound">h</a> <a id="1144" href="foundation.lawveres-fixed-point-theorem.html#1138" class="Bound">b</a> <a id="1146" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1148" href="foundation.lawveres-fixed-point-theorem.html#1138" class="Bound">b</a><a id="1149" class="Symbol">))</a>
        <a id="1160" class="Symbol">(</a> <a id="1162" class="Symbol">λ</a> <a id="1164" class="Symbol">(</a><a id="1165" href="foundation.lawveres-fixed-point-theorem.html#1165" class="Bound">x</a> <a id="1167" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1169" href="foundation.lawveres-fixed-point-theorem.html#1169" class="Bound">p</a><a id="1170" class="Symbol">)</a> <a id="1172" class="Symbol">→</a> <a id="1174" href="foundation.existential-quantification.html#4482" class="Function">intro-exists</a> <a id="1187" class="Symbol">(</a><a id="1188" href="foundation.lawveres-fixed-point-theorem.html#864" class="Bound">f</a> <a id="1190" href="foundation.lawveres-fixed-point-theorem.html#1165" class="Bound">x</a> <a id="1192" href="foundation.lawveres-fixed-point-theorem.html#1165" class="Bound">x</a><a id="1193" class="Symbol">)</a> <a id="1195" class="Symbol">(</a><a id="1196" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="1200" class="Symbol">(</a><a id="1201" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a> <a id="1209" href="foundation.lawveres-fixed-point-theorem.html#1169" class="Bound">p</a> <a id="1211" href="foundation.lawveres-fixed-point-theorem.html#1165" class="Bound">x</a><a id="1212" class="Symbol">)))</a>
      <a id="1222" class="Keyword">where</a>
      <a id="1234" href="foundation.lawveres-fixed-point-theorem.html#1234" class="Function">g</a> <a id="1236" class="Symbol">:</a> <a id="1238" href="foundation.lawveres-fixed-point-theorem.html#840" class="Bound">A</a> <a id="1240" class="Symbol">→</a> <a id="1242" href="foundation.lawveres-fixed-point-theorem.html#852" class="Bound">B</a>
      <a id="1250" href="foundation.lawveres-fixed-point-theorem.html#1234" class="Function">g</a> <a id="1252" href="foundation.lawveres-fixed-point-theorem.html#1252" class="Bound">a</a> <a id="1254" class="Symbol">=</a> <a id="1256" href="foundation.lawveres-fixed-point-theorem.html#1040" class="Bound">h</a> <a id="1258" class="Symbol">(</a><a id="1259" href="foundation.lawveres-fixed-point-theorem.html#864" class="Bound">f</a> <a id="1261" href="foundation.lawveres-fixed-point-theorem.html#1252" class="Bound">a</a> <a id="1263" href="foundation.lawveres-fixed-point-theorem.html#1252" class="Bound">a</a><a id="1264" class="Symbol">)</a>
</pre>
## See also

- Lawvere's fixed point theorem generalizes
  [Cantor's theorem](foundation.cantors-theorem.md) in the following way: When
  `B` is the universe of
  [decidable propositions](foundation-core.decidable-propositions.md) or the
  universe of all [propositions](foundation-core.propositions.md), then we have
  an operator `B → B` with no fixed points, namely
  [negation](foundation-core.negation.md). Since `𝒫(A) = (A → Prop)`, It follows
  that there can be no surjection `A ↠ 𝒫(A)`.

## External links

- [Lawvere's fixed point theorem](https://ncatlab.org/nlab/show/Lawvere%27s+fixed+point+theorem)
  at $n$Lab
- [Lawvere's fixed-point theorem](https://en.wikipedia.org/wiki/Lawvere%27s_fixed-point_theorem)
  at Wikipedia
