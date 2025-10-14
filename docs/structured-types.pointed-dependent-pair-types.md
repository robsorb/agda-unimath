# Pointed dependent pair types

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="structured-types.pointed-dependent-pair-types.html" class="Module">structured-types.pointed-dependent-pair-types</a> <a id="94" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="150" class="Keyword">open</a> <a id="155" class="Keyword">import</a> <a id="162" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="234" class="Keyword">open</a> <a id="239" class="Keyword">import</a> <a id="246" href="structured-types.pointed-families-of-types.html" class="Module">structured-types.pointed-families-of-types</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

Given a pointed type `(A , a)` and a pointed family over it `(B , b)`, then the
dependent pair type `Σ A B` is again canonically pointed at `(a , b)`.

## Definition

<pre class="Agda"><a id="533" class="Keyword">module</a> <a id="540" href="structured-types.pointed-dependent-pair-types.html#540" class="Module">_</a>
  <a id="544" class="Symbol">{</a><a id="545" href="structured-types.pointed-dependent-pair-types.html#545" class="Bound">l1</a> <a id="548" href="structured-types.pointed-dependent-pair-types.html#548" class="Bound">l2</a> <a id="551" class="Symbol">:</a> <a id="553" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="558" class="Symbol">}</a>
  <a id="562" class="Keyword">where</a>

  <a id="571" href="structured-types.pointed-dependent-pair-types.html#571" class="Function">Σ-Pointed-Type</a> <a id="586" class="Symbol">:</a>
    <a id="592" class="Symbol">(</a><a id="593" href="structured-types.pointed-dependent-pair-types.html#593" class="Bound">A</a> <a id="595" class="Symbol">:</a> <a id="597" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="610" href="structured-types.pointed-dependent-pair-types.html#545" class="Bound">l1</a><a id="612" class="Symbol">)</a> <a id="614" class="Symbol">(</a><a id="615" href="structured-types.pointed-dependent-pair-types.html#615" class="Bound">B</a> <a id="617" class="Symbol">:</a> <a id="619" href="structured-types.pointed-families-of-types.html#583" class="Function">Pointed-Fam</a> <a id="631" href="structured-types.pointed-dependent-pair-types.html#548" class="Bound">l2</a> <a id="634" href="structured-types.pointed-dependent-pair-types.html#593" class="Bound">A</a><a id="635" class="Symbol">)</a> <a id="637" class="Symbol">→</a> <a id="639" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="652" class="Symbol">(</a><a id="653" href="structured-types.pointed-dependent-pair-types.html#545" class="Bound">l1</a> <a id="656" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="658" href="structured-types.pointed-dependent-pair-types.html#548" class="Bound">l2</a><a id="660" class="Symbol">)</a>
  <a id="664" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="668" class="Symbol">(</a><a id="669" href="structured-types.pointed-dependent-pair-types.html#571" class="Function">Σ-Pointed-Type</a> <a id="684" class="Symbol">(</a><a id="685" href="structured-types.pointed-dependent-pair-types.html#685" class="Bound">A</a> <a id="687" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="689" href="structured-types.pointed-dependent-pair-types.html#689" class="Bound">a</a><a id="690" class="Symbol">)</a> <a id="692" class="Symbol">(</a><a id="693" href="structured-types.pointed-dependent-pair-types.html#693" class="Bound">B</a> <a id="695" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="697" href="structured-types.pointed-dependent-pair-types.html#697" class="Bound">b</a><a id="698" class="Symbol">))</a> <a id="701" class="Symbol">=</a> <a id="703" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="705" href="structured-types.pointed-dependent-pair-types.html#685" class="Bound">A</a> <a id="707" href="structured-types.pointed-dependent-pair-types.html#693" class="Bound">B</a>
  <a id="711" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="715" class="Symbol">(</a><a id="716" href="structured-types.pointed-dependent-pair-types.html#571" class="Function">Σ-Pointed-Type</a> <a id="731" class="Symbol">(</a><a id="732" href="structured-types.pointed-dependent-pair-types.html#732" class="Bound">A</a> <a id="734" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="736" href="structured-types.pointed-dependent-pair-types.html#736" class="Bound">a</a><a id="737" class="Symbol">)</a> <a id="739" class="Symbol">(</a><a id="740" href="structured-types.pointed-dependent-pair-types.html#740" class="Bound">B</a> <a id="742" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="744" href="structured-types.pointed-dependent-pair-types.html#744" class="Bound">b</a><a id="745" class="Symbol">))</a> <a id="748" class="Symbol">=</a> <a id="750" href="structured-types.pointed-dependent-pair-types.html#736" class="Bound">a</a> <a id="752" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="754" href="structured-types.pointed-dependent-pair-types.html#744" class="Bound">b</a>

  <a id="759" href="structured-types.pointed-dependent-pair-types.html#759" class="Function">Σ∗</a> <a id="762" class="Symbol">=</a> <a id="764" href="structured-types.pointed-dependent-pair-types.html#571" class="Function">Σ-Pointed-Type</a>
</pre>
**Note**: the subscript asterisk symbol used for the pointed dependent pair type
`Σ∗`, and pointed type constructions in general, is the
[asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`), not
the [asterisk](https://codepoints.net/U+002A) `*`.
