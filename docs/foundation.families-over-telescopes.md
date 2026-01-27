# Families of types over telescopes

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="foundation.families-over-telescopes.html" class="Module">foundation.families-over-telescopes</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.telescopes.html" class="Module">foundation.telescopes</a>
<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A
{{#concept "type family" Disambiguation="over a telescope" Agda=family-over-telescope}}
over a [telescope](foundation.telescopes.md) is a family of types defined in the
context of the telescope.

For instance, given a length three telescope

```text
  Γ := ⟨x : A, y : B x, z : C x y z⟩
```

a type family over `Γ` is a ternary family of types

```text
  D : (x : A) (y : B x) (z : C x y z) → 𝒰.
```

## Definitions

### Type families over telescopes

<pre class="Agda"><a id="family-over-telescope"></a><a id="807" href="foundation.families-over-telescopes.html#807" class="Function">family-over-telescope</a> <a id="829" class="Symbol">:</a>
  <a id="833" class="Symbol">{</a><a id="834" href="foundation.families-over-telescopes.html#834" class="Bound">l1</a> <a id="837" class="Symbol">:</a> <a id="839" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="844" class="Symbol">}</a> <a id="846" class="Symbol">(</a><a id="847" href="foundation.families-over-telescopes.html#847" class="Bound">l2</a> <a id="850" class="Symbol">:</a> <a id="852" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="857" class="Symbol">)</a> <a id="859" class="Symbol">{</a><a id="860" href="foundation.families-over-telescopes.html#860" class="Bound">n</a> <a id="862" class="Symbol">:</a> <a id="864" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="865" class="Symbol">}</a> <a id="867" class="Symbol">→</a> <a id="869" href="foundation.telescopes.html#1281" class="Datatype">telescope</a> <a id="879" href="foundation.families-over-telescopes.html#834" class="Bound">l1</a> <a id="882" href="foundation.families-over-telescopes.html#860" class="Bound">n</a> <a id="884" class="Symbol">→</a> <a id="886" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="889" class="Symbol">(</a><a id="890" href="foundation.families-over-telescopes.html#834" class="Bound">l1</a> <a id="893" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="895" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="900" href="foundation.families-over-telescopes.html#847" class="Bound">l2</a><a id="902" class="Symbol">)</a>
<a id="904" href="foundation.families-over-telescopes.html#807" class="Function">family-over-telescope</a> <a id="926" class="Symbol">{</a><a id="927" href="foundation.families-over-telescopes.html#927" class="Bound">l1</a><a id="929" class="Symbol">}</a> <a id="931" href="foundation.families-over-telescopes.html#931" class="Bound">l2</a> <a id="934" class="Symbol">(</a><a id="935" href="foundation.telescopes.html#1325" class="InductiveConstructor">base-telescope</a> <a id="950" href="foundation.families-over-telescopes.html#950" class="Bound">X</a><a id="951" class="Symbol">)</a> <a id="953" class="Symbol">=</a>
  <a id="957" href="foundation.raising-universe-levels.html#1034" class="Datatype">raise</a> <a id="963" class="Symbol">(</a><a id="964" href="foundation.families-over-telescopes.html#927" class="Bound">l1</a> <a id="967" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="969" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="974" href="foundation.families-over-telescopes.html#931" class="Bound">l2</a><a id="976" class="Symbol">)</a> <a id="978" class="Symbol">(</a><a id="979" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="982" href="foundation.families-over-telescopes.html#931" class="Bound">l2</a><a id="984" class="Symbol">)</a>
<a id="986" href="foundation.families-over-telescopes.html#807" class="Function">family-over-telescope</a> <a id="1008" href="foundation.families-over-telescopes.html#1008" class="Bound">l2</a> <a id="1011" class="Symbol">(</a><a id="1012" href="foundation.telescopes.html#1386" class="InductiveConstructor">cons-telescope</a> <a id="1027" class="Symbol">{</a><a id="1028" class="Argument">X</a> <a id="1030" class="Symbol">=</a> <a id="1032" href="foundation.families-over-telescopes.html#1032" class="Bound">X</a><a id="1033" class="Symbol">}</a> <a id="1035" href="foundation.families-over-telescopes.html#1035" class="Bound">Γ</a><a id="1036" class="Symbol">)</a> <a id="1038" class="Symbol">=</a>
  <a id="1042" class="Symbol">(</a><a id="1043" href="foundation.families-over-telescopes.html#1043" class="Bound">x</a> <a id="1045" class="Symbol">:</a> <a id="1047" href="foundation.families-over-telescopes.html#1032" class="Bound">X</a><a id="1048" class="Symbol">)</a> <a id="1050" class="Symbol">→</a> <a id="1052" href="foundation.families-over-telescopes.html#807" class="Function">family-over-telescope</a> <a id="1074" href="foundation.families-over-telescopes.html#1008" class="Bound">l2</a> <a id="1077" class="Symbol">(</a><a id="1078" href="foundation.families-over-telescopes.html#1035" class="Bound">Γ</a> <a id="1080" href="foundation.families-over-telescopes.html#1043" class="Bound">x</a><a id="1081" class="Symbol">)</a>
</pre>