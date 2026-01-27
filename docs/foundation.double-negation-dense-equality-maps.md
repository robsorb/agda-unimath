# Maps with double negation dense equality

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="foundation.double-negation-dense-equality-maps.html" class="Module">foundation.double-negation-dense-equality-maps</a> <a id="107" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.double-negation-dense-equality.html" class="Module">foundation.double-negation-dense-equality</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="foundation.irrefutable-equality.html" class="Module">foundation.irrefutable-equality</a>
<a id="261" class="Keyword">open</a> <a id="266" class="Keyword">import</a> <a id="273" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
</pre>
</details>

## Idea

A map `f : A → B` is said to have
{{#concept "double negation dense equality" Disambiguation="map of types" Agda=has-double-negation-dense-equality-map}}
if its [fibers](foundation-core.fibers-of-maps.md) have
[double negation dense equality](foundation.irrefutable-equality.md). I.e., if
for every `y : B` and every pair `p q : fiber f y` it is
[irrefutable](foundation.irrefutable-propositions.md) that `p` equals `q`. In
other words, `¬¬ (p ＝ q)` holds.

## Definitions

<pre class="Agda"><a id="has-double-negation-dense-equality-map"></a><a id="852" href="foundation.double-negation-dense-equality-maps.html#852" class="Function">has-double-negation-dense-equality-map</a> <a id="891" class="Symbol">:</a>
  <a id="895" class="Symbol">{</a><a id="896" href="foundation.double-negation-dense-equality-maps.html#896" class="Bound">l1</a> <a id="899" href="foundation.double-negation-dense-equality-maps.html#899" class="Bound">l2</a> <a id="902" class="Symbol">:</a> <a id="904" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="909" class="Symbol">}</a> <a id="911" class="Symbol">{</a><a id="912" href="foundation.double-negation-dense-equality-maps.html#912" class="Bound">A</a> <a id="914" class="Symbol">:</a> <a id="916" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="919" href="foundation.double-negation-dense-equality-maps.html#896" class="Bound">l1</a><a id="921" class="Symbol">}</a> <a id="923" class="Symbol">{</a><a id="924" href="foundation.double-negation-dense-equality-maps.html#924" class="Bound">B</a> <a id="926" class="Symbol">:</a> <a id="928" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="931" href="foundation.double-negation-dense-equality-maps.html#899" class="Bound">l2</a><a id="933" class="Symbol">}</a> <a id="935" class="Symbol">→</a> <a id="937" class="Symbol">(</a><a id="938" href="foundation.double-negation-dense-equality-maps.html#912" class="Bound">A</a> <a id="940" class="Symbol">→</a> <a id="942" href="foundation.double-negation-dense-equality-maps.html#924" class="Bound">B</a><a id="943" class="Symbol">)</a> <a id="945" class="Symbol">→</a> <a id="947" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="950" class="Symbol">(</a><a id="951" href="foundation.double-negation-dense-equality-maps.html#896" class="Bound">l1</a> <a id="954" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="956" href="foundation.double-negation-dense-equality-maps.html#899" class="Bound">l2</a><a id="958" class="Symbol">)</a>
<a id="960" href="foundation.double-negation-dense-equality-maps.html#852" class="Function">has-double-negation-dense-equality-map</a> <a id="999" class="Symbol">{</a><a id="1000" class="Argument">B</a> <a id="1002" class="Symbol">=</a> <a id="1004" href="foundation.double-negation-dense-equality-maps.html#1004" class="Bound">B</a><a id="1005" class="Symbol">}</a> <a id="1007" href="foundation.double-negation-dense-equality-maps.html#1007" class="Bound">f</a> <a id="1009" class="Symbol">=</a>
  <a id="1013" class="Symbol">(</a><a id="1014" href="foundation.double-negation-dense-equality-maps.html#1014" class="Bound">y</a> <a id="1016" class="Symbol">:</a> <a id="1018" href="foundation.double-negation-dense-equality-maps.html#1004" class="Bound">B</a><a id="1019" class="Symbol">)</a> <a id="1021" class="Symbol">→</a> <a id="1023" href="foundation.double-negation-dense-equality.html#1686" class="Function">has-double-negation-dense-equality</a> <a id="1058" class="Symbol">(</a><a id="1059" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="1065" href="foundation.double-negation-dense-equality-maps.html#1007" class="Bound">f</a> <a id="1067" href="foundation.double-negation-dense-equality-maps.html#1014" class="Bound">y</a><a id="1068" class="Symbol">)</a>
</pre>