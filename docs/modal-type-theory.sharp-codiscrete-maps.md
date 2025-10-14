# Sharp codiscrete maps

<pre class="Agda"><a id="34" class="Symbol">{-#</a> <a id="38" class="Keyword">OPTIONS</a> <a id="46" class="Pragma">--cohesion</a> <a id="57" class="Pragma">--flat-split</a> <a id="70" class="Symbol">#-}</a>

<a id="75" class="Keyword">module</a> <a id="82" href="modal-type-theory.sharp-codiscrete-maps.html" class="Module">modal-type-theory.sharp-codiscrete-maps</a> <a id="122" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="modal-type-theory.sharp-codiscrete-types.html" class="Module">modal-type-theory.sharp-codiscrete-types</a>
</pre>
</details>

## Idea

A map is said to be
{{#concept "sharp codiscrete" Disambiguation="map" Agda=is-sharp-codiscrete-map}}
if its [fibers](foundation-core.fibers-of-maps.md) are
[sharp codiscrete](modal-type-theory.sharp-codiscrete-types.md).

## Definition

<pre class="Agda"><a id="617" class="Keyword">module</a> <a id="624" href="modal-type-theory.sharp-codiscrete-maps.html#624" class="Module">_</a>
  <a id="628" class="Symbol">{</a><a id="629" href="modal-type-theory.sharp-codiscrete-maps.html#629" class="Bound">l1</a> <a id="632" href="modal-type-theory.sharp-codiscrete-maps.html#632" class="Bound">l2</a> <a id="635" class="Symbol">:</a> <a id="637" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="642" class="Symbol">}</a> <a id="644" class="Symbol">{</a><a id="645" href="modal-type-theory.sharp-codiscrete-maps.html#645" class="Bound">A</a> <a id="647" class="Symbol">:</a> <a id="649" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="652" href="modal-type-theory.sharp-codiscrete-maps.html#629" class="Bound">l1</a><a id="654" class="Symbol">}</a> <a id="656" class="Symbol">{</a><a id="657" href="modal-type-theory.sharp-codiscrete-maps.html#657" class="Bound">B</a> <a id="659" class="Symbol">:</a> <a id="661" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="664" href="modal-type-theory.sharp-codiscrete-maps.html#632" class="Bound">l2</a><a id="666" class="Symbol">}</a> <a id="668" class="Symbol">(</a><a id="669" href="modal-type-theory.sharp-codiscrete-maps.html#669" class="Bound">f</a> <a id="671" class="Symbol">:</a> <a id="673" href="modal-type-theory.sharp-codiscrete-maps.html#645" class="Bound">A</a> <a id="675" class="Symbol">→</a> <a id="677" href="modal-type-theory.sharp-codiscrete-maps.html#657" class="Bound">B</a><a id="678" class="Symbol">)</a>
  <a id="682" class="Keyword">where</a>

  <a id="691" href="modal-type-theory.sharp-codiscrete-maps.html#691" class="Function">is-sharp-codiscrete-map</a> <a id="715" class="Symbol">:</a> <a id="717" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="720" class="Symbol">(</a><a id="721" href="modal-type-theory.sharp-codiscrete-maps.html#629" class="Bound">l1</a> <a id="724" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="726" href="modal-type-theory.sharp-codiscrete-maps.html#632" class="Bound">l2</a><a id="728" class="Symbol">)</a>
  <a id="732" href="modal-type-theory.sharp-codiscrete-maps.html#691" class="Function">is-sharp-codiscrete-map</a> <a id="756" class="Symbol">=</a> <a id="758" href="modal-type-theory.sharp-codiscrete-types.html#1967" class="Function">is-sharp-codiscrete-family</a> <a id="785" class="Symbol">(</a><a id="786" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="792" href="modal-type-theory.sharp-codiscrete-maps.html#669" class="Bound">f</a><a id="793" class="Symbol">)</a>

  <a id="798" href="modal-type-theory.sharp-codiscrete-maps.html#798" class="Function">is-sharp-codiscrete-map-Prop</a> <a id="827" class="Symbol">:</a> <a id="829" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="834" class="Symbol">(</a><a id="835" href="modal-type-theory.sharp-codiscrete-maps.html#629" class="Bound">l1</a> <a id="838" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="840" href="modal-type-theory.sharp-codiscrete-maps.html#632" class="Bound">l2</a><a id="842" class="Symbol">)</a>
  <a id="846" href="modal-type-theory.sharp-codiscrete-maps.html#798" class="Function">is-sharp-codiscrete-map-Prop</a> <a id="875" class="Symbol">=</a> <a id="877" href="modal-type-theory.sharp-codiscrete-types.html#2199" class="Function">is-sharp-codiscrete-family-Prop</a> <a id="909" class="Symbol">(</a><a id="910" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="916" href="modal-type-theory.sharp-codiscrete-maps.html#669" class="Bound">f</a><a id="917" class="Symbol">)</a>

  <a id="922" href="modal-type-theory.sharp-codiscrete-maps.html#922" class="Function">is-prop-is-sharp-codiscrete-map</a> <a id="954" class="Symbol">:</a> <a id="956" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="964" href="modal-type-theory.sharp-codiscrete-maps.html#691" class="Function">is-sharp-codiscrete-map</a>
  <a id="990" href="modal-type-theory.sharp-codiscrete-maps.html#922" class="Function">is-prop-is-sharp-codiscrete-map</a> <a id="1022" class="Symbol">=</a>
    <a id="1028" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1046" href="modal-type-theory.sharp-codiscrete-maps.html#798" class="Function">is-sharp-codiscrete-map-Prop</a>
</pre>