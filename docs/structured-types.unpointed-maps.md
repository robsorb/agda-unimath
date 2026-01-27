# Unpointed maps between pointed types

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="structured-types.unpointed-maps.html" class="Module">structured-types.unpointed-maps</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="228" class="Keyword">open</a> <a id="233" class="Keyword">import</a> <a id="240" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The type of unpointed maps between pointed types is a pointed type, pointed at
the constant function.

## Definition

<pre class="Agda"><a id="unpointed-map-Pointed-Type"></a><a id="423" href="structured-types.unpointed-maps.html#423" class="Function">unpointed-map-Pointed-Type</a> <a id="450" class="Symbol">:</a>
  <a id="454" class="Symbol">{</a><a id="455" href="structured-types.unpointed-maps.html#455" class="Bound">l1</a> <a id="458" href="structured-types.unpointed-maps.html#458" class="Bound">l2</a> <a id="461" class="Symbol">:</a> <a id="463" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="468" class="Symbol">}</a> <a id="470" class="Symbol">→</a> <a id="472" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="485" href="structured-types.unpointed-maps.html#455" class="Bound">l1</a> <a id="488" class="Symbol">→</a> <a id="490" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="503" href="structured-types.unpointed-maps.html#458" class="Bound">l2</a> <a id="506" class="Symbol">→</a> <a id="508" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="521" class="Symbol">(</a><a id="522" href="structured-types.unpointed-maps.html#455" class="Bound">l1</a> <a id="525" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="527" href="structured-types.unpointed-maps.html#458" class="Bound">l2</a><a id="529" class="Symbol">)</a>
<a id="531" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="535" class="Symbol">(</a><a id="536" href="structured-types.unpointed-maps.html#423" class="Function">unpointed-map-Pointed-Type</a> <a id="563" href="structured-types.unpointed-maps.html#563" class="Bound">A</a> <a id="565" href="structured-types.unpointed-maps.html#565" class="Bound">B</a><a id="566" class="Symbol">)</a> <a id="568" class="Symbol">=</a> <a id="570" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="588" href="structured-types.unpointed-maps.html#563" class="Bound">A</a> <a id="590" class="Symbol">→</a> <a id="592" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="610" href="structured-types.unpointed-maps.html#565" class="Bound">B</a>
<a id="612" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="616" class="Symbol">(</a><a id="617" href="structured-types.unpointed-maps.html#423" class="Function">unpointed-map-Pointed-Type</a> <a id="644" href="structured-types.unpointed-maps.html#644" class="Bound">A</a> <a id="646" href="structured-types.unpointed-maps.html#646" class="Bound">B</a><a id="647" class="Symbol">)</a> <a id="649" href="structured-types.unpointed-maps.html#649" class="Bound">x</a> <a id="651" class="Symbol">=</a> <a id="653" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="672" href="structured-types.unpointed-maps.html#646" class="Bound">B</a>
</pre>