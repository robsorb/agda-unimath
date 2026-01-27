# Sorial type families

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="foundation.sorial-type-families.html" class="Module">foundation.sorial-type-families</a> <a id="72" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>

<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The notion of _sorial type family_ is a generalization of the notion of
[torsorial type family](foundation.torsorial-type-families.md). Recall that if a
type family `E` over a [pointed type](structured-types.pointed-types.md) `B` is
torsorial, then we obtain in a canonical way, for each `x : B` an action

```text
  E x → (E pt ≃ E x)
```

A **sorial type family** is a type family `E` over a pointed type `B` for which
we have such an action.

## Definitions

### Sorial type families

<pre class="Agda"><a id="775" class="Keyword">module</a> <a id="782" href="foundation.sorial-type-families.html#782" class="Module">_</a>
  <a id="786" class="Symbol">{</a><a id="787" href="foundation.sorial-type-families.html#787" class="Bound">l1</a> <a id="790" href="foundation.sorial-type-families.html#790" class="Bound">l2</a> <a id="793" class="Symbol">:</a> <a id="795" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="800" class="Symbol">}</a> <a id="802" class="Symbol">(</a><a id="803" href="foundation.sorial-type-families.html#803" class="Bound">B</a> <a id="805" class="Symbol">:</a> <a id="807" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="820" href="foundation.sorial-type-families.html#787" class="Bound">l1</a><a id="822" class="Symbol">)</a> <a id="824" class="Symbol">(</a><a id="825" href="foundation.sorial-type-families.html#825" class="Bound">E</a> <a id="827" class="Symbol">:</a> <a id="829" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="847" href="foundation.sorial-type-families.html#803" class="Bound">B</a> <a id="849" class="Symbol">→</a> <a id="851" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="854" href="foundation.sorial-type-families.html#790" class="Bound">l2</a><a id="856" class="Symbol">)</a>
  <a id="860" class="Keyword">where</a>

  <a id="869" href="foundation.sorial-type-families.html#869" class="Function">is-sorial-family-of-types</a> <a id="895" class="Symbol">:</a> <a id="897" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="900" class="Symbol">(</a><a id="901" href="foundation.sorial-type-families.html#787" class="Bound">l1</a> <a id="904" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="906" href="foundation.sorial-type-families.html#790" class="Bound">l2</a><a id="908" class="Symbol">)</a>
  <a id="912" href="foundation.sorial-type-families.html#869" class="Function">is-sorial-family-of-types</a> <a id="938" class="Symbol">=</a>
    <a id="944" class="Symbol">(</a><a id="945" href="foundation.sorial-type-families.html#945" class="Bound">x</a> <a id="947" class="Symbol">:</a> <a id="949" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="967" href="foundation.sorial-type-families.html#803" class="Bound">B</a><a id="968" class="Symbol">)</a> <a id="970" class="Symbol">→</a> <a id="972" href="foundation.sorial-type-families.html#825" class="Bound">E</a> <a id="974" href="foundation.sorial-type-families.html#945" class="Bound">x</a> <a id="976" class="Symbol">→</a> <a id="978" class="Symbol">(</a><a id="979" href="foundation.sorial-type-families.html#825" class="Bound">E</a> <a id="981" class="Symbol">(</a><a id="982" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1001" href="foundation.sorial-type-families.html#803" class="Bound">B</a><a id="1002" class="Symbol">)</a> <a id="1004" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1006" href="foundation.sorial-type-families.html#825" class="Bound">E</a> <a id="1008" href="foundation.sorial-type-families.html#945" class="Bound">x</a><a id="1009" class="Symbol">)</a>
</pre>