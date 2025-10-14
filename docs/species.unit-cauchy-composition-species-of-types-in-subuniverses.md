# The unit of Cauchy composition of species of types in subuniverses

<pre class="Agda"><a id="79" class="Keyword">module</a> <a id="86" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html" class="Module">species.unit-cauchy-composition-species-of-types-in-subuniverses</a> <a id="151" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation.global-subuniverses.html" class="Module">foundation.global-subuniverses</a>
<a id="336" class="Keyword">open</a> <a id="341" class="Keyword">import</a> <a id="348" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="412" class="Keyword">open</a> <a id="417" class="Keyword">import</a> <a id="424" href="species.species-of-types-in-subuniverses.html" class="Module">species.species-of-types-in-subuniverses</a>
</pre>
</details>

## Idea

Given a [global subuniverse](foundation.global-subuniverses.md) closed under
`is-contr`, we define the unit of the
[Cauchy composition](species.cauchy-composition-species-of-types-in-subuniverses.md)
of
[species of types in a subuniverse](species.species-of-types-in-subuniverses.md)
by

```text
  X ↦ is-contr X.
```

## Definition

<pre class="Agda"><a id="833" class="Keyword">module</a> <a id="840" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#840" class="Module">_</a>
  <a id="844" class="Symbol">{</a><a id="845" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#845" class="Bound">α</a> <a id="847" class="Symbol">:</a> <a id="849" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="855" class="Symbol">→</a> <a id="857" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="862" class="Symbol">}</a> <a id="864" class="Symbol">{</a><a id="865" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#865" class="Bound">l1</a> <a id="868" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#868" class="Bound">l2</a> <a id="871" class="Symbol">:</a> <a id="873" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="878" class="Symbol">}</a>
  <a id="882" class="Symbol">(</a><a id="883" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#883" class="Bound">P</a> <a id="885" class="Symbol">:</a> <a id="887" href="foundation.subuniverses.html#1114" class="Function">subuniverse</a> <a id="899" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#865" class="Bound">l1</a> <a id="902" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#868" class="Bound">l2</a><a id="904" class="Symbol">)</a> <a id="906" class="Symbol">(</a><a id="907" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#907" class="Bound">Q</a> <a id="909" class="Symbol">:</a> <a id="911" href="foundation.global-subuniverses.html#1810" class="Record">global-subuniverse</a> <a id="930" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#845" class="Bound">α</a><a id="931" class="Symbol">)</a>
  <a id="935" class="Symbol">(</a><a id="936" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#936" class="Bound">C4</a> <a id="939" class="Symbol">:</a>
    <a id="945" href="foundation.contractible-types.html#2967" class="Function">is-closed-under-is-contr-subuniverses</a> <a id="983" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#883" class="Bound">P</a>
      <a id="991" class="Symbol">(</a> <a id="993" href="foundation.global-subuniverses.html#1873" class="Field">subuniverse-global-subuniverse</a> <a id="1024" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#907" class="Bound">Q</a> <a id="1026" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#865" class="Bound">l1</a><a id="1028" class="Symbol">))</a>
  <a id="1033" class="Keyword">where</a>

  <a id="1042" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#1042" class="Function">cauchy-composition-unit-species-subuniverse</a> <a id="1086" class="Symbol">:</a>
    <a id="1092" href="species.species-of-types-in-subuniverses.html#828" class="Function">species-subuniverse</a> <a id="1112" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#883" class="Bound">P</a> <a id="1114" class="Symbol">(</a><a id="1115" href="foundation.global-subuniverses.html#1873" class="Field">subuniverse-global-subuniverse</a> <a id="1146" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#907" class="Bound">Q</a> <a id="1148" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#865" class="Bound">l1</a><a id="1150" class="Symbol">)</a>
  <a id="1154" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#1042" class="Function">cauchy-composition-unit-species-subuniverse</a> <a id="1198" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#1198" class="Bound">X</a> <a id="1200" class="Symbol">=</a>
    <a id="1206" class="Symbol">(</a><a id="1207" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="1216" class="Symbol">(</a><a id="1217" href="foundation.subuniverses.html#1720" class="Function">inclusion-subuniverse</a> <a id="1239" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#883" class="Bound">P</a> <a id="1241" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#1198" class="Bound">X</a><a id="1242" class="Symbol">)</a> <a id="1244" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1246" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#936" class="Bound">C4</a> <a id="1249" href="species.unit-cauchy-composition-species-of-types-in-subuniverses.html#1198" class="Bound">X</a><a id="1250" class="Symbol">)</a>
</pre>