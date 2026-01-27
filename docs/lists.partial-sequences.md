# Partial sequences

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="lists.partial-sequences.html" class="Module">lists.partial-sequences</a> <a id="61" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="117" class="Keyword">open</a> <a id="122" class="Keyword">import</a> <a id="129" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.partial-functions.html" class="Module">foundation.partial-functions</a>
<a id="212" class="Keyword">open</a> <a id="217" class="Keyword">import</a> <a id="224" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A {{#concept "partial sequence" Agda=partial-sequence}} of elements of a type
`A` is a [partial function](foundation.partial-functions.md) from `ℕ` to `A`. In
other words, a partial sequence is a map

```text
  ℕ → Σ (P : Prop), (P → A)
```

from `ℕ` into the type of [partial elements](foundation.partial-elements.md) of
`A`.

## Definitions

### Partial sequences

<pre class="Agda"><a id="partial-sequence"></a><a id="694" href="lists.partial-sequences.html#694" class="Function">partial-sequence</a> <a id="711" class="Symbol">:</a> <a id="713" class="Symbol">{</a><a id="714" href="lists.partial-sequences.html#714" class="Bound">l1</a> <a id="717" class="Symbol">:</a> <a id="719" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="724" class="Symbol">}</a> <a id="726" class="Symbol">(</a><a id="727" href="lists.partial-sequences.html#727" class="Bound">l2</a> <a id="730" class="Symbol">:</a> <a id="732" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="737" class="Symbol">)</a> <a id="739" class="Symbol">→</a> <a id="741" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="744" href="lists.partial-sequences.html#714" class="Bound">l1</a> <a id="747" class="Symbol">→</a> <a id="749" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="752" class="Symbol">(</a><a id="753" href="lists.partial-sequences.html#714" class="Bound">l1</a> <a id="756" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="758" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="763" href="lists.partial-sequences.html#727" class="Bound">l2</a><a id="765" class="Symbol">)</a>
<a id="767" href="lists.partial-sequences.html#694" class="Function">partial-sequence</a> <a id="784" href="lists.partial-sequences.html#784" class="Bound">l2</a> <a id="787" href="lists.partial-sequences.html#787" class="Bound">A</a> <a id="789" class="Symbol">=</a> <a id="791" href="foundation.partial-functions.html#1432" class="Function">partial-function</a> <a id="808" href="lists.partial-sequences.html#784" class="Bound">l2</a> <a id="811" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="813" href="lists.partial-sequences.html#787" class="Bound">A</a>
</pre>
### Defined elements of partial sequences

<pre class="Agda"><a id="871" class="Keyword">module</a> <a id="878" href="lists.partial-sequences.html#878" class="Module">_</a>
  <a id="882" class="Symbol">{</a><a id="883" href="lists.partial-sequences.html#883" class="Bound">l1</a> <a id="886" href="lists.partial-sequences.html#886" class="Bound">l2</a> <a id="889" class="Symbol">:</a> <a id="891" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="896" class="Symbol">}</a> <a id="898" class="Symbol">{</a><a id="899" href="lists.partial-sequences.html#899" class="Bound">A</a> <a id="901" class="Symbol">:</a> <a id="903" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="906" href="lists.partial-sequences.html#883" class="Bound">l1</a><a id="908" class="Symbol">}</a> <a id="910" class="Symbol">(</a><a id="911" href="lists.partial-sequences.html#911" class="Bound">a</a> <a id="913" class="Symbol">:</a> <a id="915" href="lists.partial-sequences.html#694" class="Function">partial-sequence</a> <a id="932" href="lists.partial-sequences.html#886" class="Bound">l2</a> <a id="935" href="lists.partial-sequences.html#899" class="Bound">A</a><a id="936" class="Symbol">)</a>
  <a id="940" class="Keyword">where</a>

  <a id="949" href="lists.partial-sequences.html#949" class="Function">is-defined-prop-partial-sequence</a> <a id="982" class="Symbol">:</a> <a id="984" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="986" class="Symbol">→</a> <a id="988" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="993" href="lists.partial-sequences.html#886" class="Bound">l2</a>
  <a id="998" href="lists.partial-sequences.html#949" class="Function">is-defined-prop-partial-sequence</a> <a id="1031" class="Symbol">=</a> <a id="1033" href="foundation.partial-functions.html#2311" class="Function">is-defined-prop-partial-function</a> <a id="1066" href="lists.partial-sequences.html#911" class="Bound">a</a>

  <a id="1071" href="lists.partial-sequences.html#1071" class="Function">is-defined-partial-sequence</a> <a id="1099" class="Symbol">:</a> <a id="1101" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1103" class="Symbol">→</a> <a id="1105" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1108" href="lists.partial-sequences.html#886" class="Bound">l2</a>
  <a id="1113" href="lists.partial-sequences.html#1071" class="Function">is-defined-partial-sequence</a> <a id="1141" class="Symbol">=</a> <a id="1143" href="foundation.partial-functions.html#2445" class="Function">is-defined-partial-function</a> <a id="1171" href="lists.partial-sequences.html#911" class="Bound">a</a>
</pre>