# Reflexive relations

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="foundation.reflexive-relations.html" class="Module">foundation.reflexive-relations</a> <a id="70" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="126" class="Keyword">open</a> <a id="131" class="Keyword">import</a> <a id="138" href="foundation.binary-dependent-identifications.html" class="Module">foundation.binary-dependent-identifications</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="306" class="Keyword">open</a> <a id="311" class="Keyword">import</a> <a id="318" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

A {{#concept "reflexive relation" Agda=Reflexive-Relation}} on a type `A` is a
type valued [binary relation](foundation.binary-relations.md) `R : A → A → 𝒰`
[equipped](foundation.structure.md) with a proof `r : (x : A) → R x x`.

## Definitions

### Reflexive relations

<pre class="Agda"><a id="Reflexive-Relation"></a><a id="654" href="foundation.reflexive-relations.html#654" class="Function">Reflexive-Relation</a> <a id="673" class="Symbol">:</a>
  <a id="677" class="Symbol">{</a><a id="678" href="foundation.reflexive-relations.html#678" class="Bound">l1</a> <a id="681" class="Symbol">:</a> <a id="683" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="688" class="Symbol">}</a> <a id="690" class="Symbol">(</a><a id="691" href="foundation.reflexive-relations.html#691" class="Bound">l2</a> <a id="694" class="Symbol">:</a> <a id="696" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="701" class="Symbol">)</a> <a id="703" class="Symbol">→</a> <a id="705" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="708" href="foundation.reflexive-relations.html#678" class="Bound">l1</a> <a id="711" class="Symbol">→</a> <a id="713" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="716" class="Symbol">(</a><a id="717" href="foundation.reflexive-relations.html#678" class="Bound">l1</a> <a id="720" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="722" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="727" href="foundation.reflexive-relations.html#691" class="Bound">l2</a><a id="729" class="Symbol">)</a>
<a id="731" href="foundation.reflexive-relations.html#654" class="Function">Reflexive-Relation</a> <a id="750" href="foundation.reflexive-relations.html#750" class="Bound">l2</a> <a id="753" href="foundation.reflexive-relations.html#753" class="Bound">A</a> <a id="755" class="Symbol">=</a> <a id="757" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="759" class="Symbol">(</a><a id="760" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="769" href="foundation.reflexive-relations.html#750" class="Bound">l2</a> <a id="772" href="foundation.reflexive-relations.html#753" class="Bound">A</a><a id="773" class="Symbol">)</a> <a id="775" class="Symbol">(λ</a> <a id="778" href="foundation.reflexive-relations.html#778" class="Bound">R</a> <a id="780" class="Symbol">→</a> <a id="782" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="795" href="foundation.reflexive-relations.html#778" class="Bound">R</a><a id="796" class="Symbol">)</a>

<a id="799" class="Keyword">module</a> <a id="806" href="foundation.reflexive-relations.html#806" class="Module">_</a>
  <a id="810" class="Symbol">{</a><a id="811" href="foundation.reflexive-relations.html#811" class="Bound">l1</a> <a id="814" href="foundation.reflexive-relations.html#814" class="Bound">l2</a> <a id="817" class="Symbol">:</a> <a id="819" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="824" class="Symbol">}</a> <a id="826" class="Symbol">{</a><a id="827" href="foundation.reflexive-relations.html#827" class="Bound">A</a> <a id="829" class="Symbol">:</a> <a id="831" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="834" href="foundation.reflexive-relations.html#811" class="Bound">l1</a><a id="836" class="Symbol">}</a> <a id="838" class="Symbol">(</a><a id="839" href="foundation.reflexive-relations.html#839" class="Bound">R</a> <a id="841" class="Symbol">:</a> <a id="843" href="foundation.reflexive-relations.html#654" class="Function">Reflexive-Relation</a> <a id="862" href="foundation.reflexive-relations.html#814" class="Bound">l2</a> <a id="865" href="foundation.reflexive-relations.html#827" class="Bound">A</a><a id="866" class="Symbol">)</a>
  <a id="870" class="Keyword">where</a>

  <a id="879" href="foundation.reflexive-relations.html#879" class="Function">rel-Reflexive-Relation</a> <a id="902" class="Symbol">:</a> <a id="904" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="913" href="foundation.reflexive-relations.html#814" class="Bound">l2</a> <a id="916" href="foundation.reflexive-relations.html#827" class="Bound">A</a>
  <a id="920" href="foundation.reflexive-relations.html#879" class="Function">rel-Reflexive-Relation</a> <a id="943" class="Symbol">=</a> <a id="945" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="949" href="foundation.reflexive-relations.html#839" class="Bound">R</a>

  <a id="954" href="foundation.reflexive-relations.html#954" class="Function">refl-Reflexive-Relation</a> <a id="978" class="Symbol">:</a> <a id="980" href="foundation.binary-relations.html#2368" class="Function">is-reflexive</a> <a id="993" href="foundation.reflexive-relations.html#879" class="Function">rel-Reflexive-Relation</a>
  <a id="1018" href="foundation.reflexive-relations.html#954" class="Function">refl-Reflexive-Relation</a> <a id="1042" class="Symbol">=</a> <a id="1044" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1048" href="foundation.reflexive-relations.html#839" class="Bound">R</a>
</pre>
### The identity reflexive relation on a type

<pre class="Agda"><a id="Id-Reflexive-Relation"></a><a id="1110" href="foundation.reflexive-relations.html#1110" class="Function">Id-Reflexive-Relation</a> <a id="1132" class="Symbol">:</a> <a id="1134" class="Symbol">{</a><a id="1135" href="foundation.reflexive-relations.html#1135" class="Bound">l</a> <a id="1137" class="Symbol">:</a> <a id="1139" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1144" class="Symbol">}</a> <a id="1146" class="Symbol">(</a><a id="1147" href="foundation.reflexive-relations.html#1147" class="Bound">A</a> <a id="1149" class="Symbol">:</a> <a id="1151" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1154" href="foundation.reflexive-relations.html#1135" class="Bound">l</a><a id="1155" class="Symbol">)</a> <a id="1157" class="Symbol">→</a> <a id="1159" href="foundation.reflexive-relations.html#654" class="Function">Reflexive-Relation</a> <a id="1178" href="foundation.reflexive-relations.html#1135" class="Bound">l</a> <a id="1180" href="foundation.reflexive-relations.html#1147" class="Bound">A</a>
<a id="1182" href="foundation.reflexive-relations.html#1110" class="Function">Id-Reflexive-Relation</a> <a id="1204" href="foundation.reflexive-relations.html#1204" class="Bound">A</a> <a id="1206" class="Symbol">=</a> <a id="1208" class="Symbol">(</a><a id="1209" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a> <a id="1212" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="1214" class="Symbol">(λ</a> <a id="1217" href="foundation.reflexive-relations.html#1217" class="Bound">x</a> <a id="1219" class="Symbol">→</a> <a id="1221" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="1225" class="Symbol">))</a>
</pre>
## Properties

### A formulation of the dependent action on identifications of reflexivity

Consider a reflexive relation `R` on a type `A` with reflexivity
`r : (x : A) → R x x`, and consider an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A`. The
usual
[action on identifications](foundation.action-on-identifications-dependent-functions.md)
yields a [dependent identification](foundation.dependent-identifications.md)

```text
  tr (λ u → R u u) p (r x) ＝ (r y).
```

However, since `R` is a binary indexed family of types, there is also the
[binary dependent identity type](foundation.binary-dependent-identifications.md),
which can be used to express another version of the action on identifications of
the reflexivity element `r`:

```text
  binary-dependent-identification R p p (r x) (r y).
```

This action on identifications can be seen as an instance of a dependent
function over the diagonal map `Δ : A → A × A`, a situation which can be
generalized. At the time of writing, however, the library lacks infrastructure
for the general formulation of the action on identifications of dependent
functions over functions yielding binary dependent identifications.

<pre class="Agda"><a id="2436" class="Keyword">module</a> <a id="2443" href="foundation.reflexive-relations.html#2443" class="Module">_</a>
  <a id="2447" class="Symbol">{</a><a id="2448" href="foundation.reflexive-relations.html#2448" class="Bound">l1</a> <a id="2451" href="foundation.reflexive-relations.html#2451" class="Bound">l2</a> <a id="2454" class="Symbol">:</a> <a id="2456" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2461" class="Symbol">}</a> <a id="2463" class="Symbol">{</a><a id="2464" href="foundation.reflexive-relations.html#2464" class="Bound">A</a> <a id="2466" class="Symbol">:</a> <a id="2468" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2471" href="foundation.reflexive-relations.html#2448" class="Bound">l1</a><a id="2473" class="Symbol">}</a> <a id="2475" class="Symbol">(</a><a id="2476" href="foundation.reflexive-relations.html#2476" class="Bound">R</a> <a id="2478" class="Symbol">:</a> <a id="2480" href="foundation.reflexive-relations.html#654" class="Function">Reflexive-Relation</a> <a id="2499" href="foundation.reflexive-relations.html#2451" class="Bound">l2</a> <a id="2502" href="foundation.reflexive-relations.html#2464" class="Bound">A</a><a id="2503" class="Symbol">)</a>
  <a id="2507" class="Keyword">where</a>

  <a id="2516" href="foundation.reflexive-relations.html#2516" class="Function">binary-dependent-identification-refl-Reflexive-Relation</a> <a id="2572" class="Symbol">:</a>
    <a id="2578" class="Symbol">{</a><a id="2579" href="foundation.reflexive-relations.html#2579" class="Bound">x</a> <a id="2581" href="foundation.reflexive-relations.html#2581" class="Bound">y</a> <a id="2583" class="Symbol">:</a> <a id="2585" href="foundation.reflexive-relations.html#2464" class="Bound">A</a><a id="2586" class="Symbol">}</a> <a id="2588" class="Symbol">(</a><a id="2589" href="foundation.reflexive-relations.html#2589" class="Bound">p</a> <a id="2591" class="Symbol">:</a> <a id="2593" href="foundation.reflexive-relations.html#2579" class="Bound">x</a> <a id="2595" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2597" href="foundation.reflexive-relations.html#2581" class="Bound">y</a><a id="2598" class="Symbol">)</a> <a id="2600" class="Symbol">→</a>
    <a id="2606" href="foundation.binary-dependent-identifications.html#927" class="Function">binary-dependent-identification</a>
      <a id="2644" class="Symbol">(</a> <a id="2646" href="foundation.reflexive-relations.html#879" class="Function">rel-Reflexive-Relation</a> <a id="2669" href="foundation.reflexive-relations.html#2476" class="Bound">R</a><a id="2670" class="Symbol">)</a>
      <a id="2678" class="Symbol">(</a> <a id="2680" href="foundation.reflexive-relations.html#2589" class="Bound">p</a><a id="2681" class="Symbol">)</a>
      <a id="2689" class="Symbol">(</a> <a id="2691" href="foundation.reflexive-relations.html#2589" class="Bound">p</a><a id="2692" class="Symbol">)</a>
      <a id="2700" class="Symbol">(</a> <a id="2702" href="foundation.reflexive-relations.html#954" class="Function">refl-Reflexive-Relation</a> <a id="2726" href="foundation.reflexive-relations.html#2476" class="Bound">R</a> <a id="2728" href="foundation.reflexive-relations.html#2579" class="Bound">x</a><a id="2729" class="Symbol">)</a>
      <a id="2737" class="Symbol">(</a> <a id="2739" href="foundation.reflexive-relations.html#954" class="Function">refl-Reflexive-Relation</a> <a id="2763" href="foundation.reflexive-relations.html#2476" class="Bound">R</a> <a id="2765" href="foundation.reflexive-relations.html#2581" class="Bound">y</a><a id="2766" class="Symbol">)</a>
  <a id="2770" href="foundation.reflexive-relations.html#2516" class="Function">binary-dependent-identification-refl-Reflexive-Relation</a> <a id="2826" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="2831" class="Symbol">=</a> <a id="2833" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>