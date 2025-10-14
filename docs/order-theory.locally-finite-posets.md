# Locally finite posets

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="order-theory.locally-finite-posets.html" class="Module">order-theory.locally-finite-posets</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="208" class="Keyword">open</a> <a id="213" class="Keyword">import</a> <a id="220" href="order-theory.finite-posets.html" class="Module">order-theory.finite-posets</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="order-theory.interval-subposets.html" class="Module">order-theory.interval-subposets</a>
<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="order-theory.posets.html" class="Module">order-theory.posets</a>
</pre>
</details>

## Idea

A poset `X` is said to be **locally finite** if for every `x, y ∈ X`, the
[interval subposet](order-theory.interval-subposets.md) `[x, y]` consisting of
`z : X` such that `x ≤ z ≤ y`, is finite.

## Definition

<pre class="Agda"><a id="568" class="Keyword">module</a> <a id="575" href="order-theory.locally-finite-posets.html#575" class="Module">_</a>
  <a id="579" class="Symbol">{</a><a id="580" href="order-theory.locally-finite-posets.html#580" class="Bound">l1</a> <a id="583" href="order-theory.locally-finite-posets.html#583" class="Bound">l2</a> <a id="586" class="Symbol">:</a> <a id="588" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="593" class="Symbol">}</a> <a id="595" class="Symbol">(</a><a id="596" href="order-theory.locally-finite-posets.html#596" class="Bound">X</a> <a id="598" class="Symbol">:</a> <a id="600" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="606" href="order-theory.locally-finite-posets.html#580" class="Bound">l1</a> <a id="609" href="order-theory.locally-finite-posets.html#583" class="Bound">l2</a><a id="611" class="Symbol">)</a>
  <a id="615" class="Keyword">where</a>

  <a id="624" href="order-theory.locally-finite-posets.html#624" class="Function">is-locally-finite-Poset-Prop</a> <a id="653" class="Symbol">:</a> <a id="655" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="660" class="Symbol">(</a><a id="661" href="order-theory.locally-finite-posets.html#580" class="Bound">l1</a> <a id="664" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="666" href="order-theory.locally-finite-posets.html#583" class="Bound">l2</a><a id="668" class="Symbol">)</a>
  <a id="672" href="order-theory.locally-finite-posets.html#624" class="Function">is-locally-finite-Poset-Prop</a> <a id="701" class="Symbol">=</a>
    <a id="707" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="720" class="Symbol">(</a> <a id="722" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="733" href="order-theory.locally-finite-posets.html#596" class="Bound">X</a><a id="734" class="Symbol">)</a>
      <a id="742" class="Symbol">(</a> <a id="744" class="Symbol">λ</a> <a id="746" href="order-theory.locally-finite-posets.html#746" class="Bound">x</a> <a id="748" class="Symbol">→</a>
        <a id="758" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
          <a id="775" class="Symbol">(</a> <a id="777" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="788" href="order-theory.locally-finite-posets.html#596" class="Bound">X</a><a id="789" class="Symbol">)</a>
          <a id="801" class="Symbol">(</a> <a id="803" class="Symbol">λ</a> <a id="805" href="order-theory.locally-finite-posets.html#805" class="Bound">y</a> <a id="807" class="Symbol">→</a>
            <a id="821" href="order-theory.finite-posets.html#795" class="Function">is-finite-Poset-Prop</a> <a id="842" class="Symbol">(</a><a id="843" href="order-theory.interval-subposets.html#910" class="Function">poset-interval-Subposet</a> <a id="867" href="order-theory.locally-finite-posets.html#596" class="Bound">X</a> <a id="869" href="order-theory.locally-finite-posets.html#746" class="Bound">x</a> <a id="871" href="order-theory.locally-finite-posets.html#805" class="Bound">y</a><a id="872" class="Symbol">)))</a>

  <a id="879" href="order-theory.locally-finite-posets.html#879" class="Function">is-locally-finite-Poset</a> <a id="903" class="Symbol">:</a> <a id="905" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="908" class="Symbol">(</a><a id="909" href="order-theory.locally-finite-posets.html#580" class="Bound">l1</a> <a id="912" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="914" href="order-theory.locally-finite-posets.html#583" class="Bound">l2</a><a id="916" class="Symbol">)</a>
  <a id="920" href="order-theory.locally-finite-posets.html#879" class="Function">is-locally-finite-Poset</a> <a id="944" class="Symbol">=</a> <a id="946" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="956" href="order-theory.locally-finite-posets.html#624" class="Function">is-locally-finite-Poset-Prop</a>

  <a id="988" href="order-theory.locally-finite-posets.html#988" class="Function">is-prop-is-locally-finite-Poset</a> <a id="1020" class="Symbol">:</a> <a id="1022" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1030" href="order-theory.locally-finite-posets.html#879" class="Function">is-locally-finite-Poset</a>
  <a id="1056" href="order-theory.locally-finite-posets.html#988" class="Function">is-prop-is-locally-finite-Poset</a> <a id="1088" class="Symbol">=</a>
    <a id="1094" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1112" href="order-theory.locally-finite-posets.html#624" class="Function">is-locally-finite-Poset-Prop</a>
</pre>