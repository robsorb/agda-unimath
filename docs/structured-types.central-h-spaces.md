# Central H-spaces

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="structured-types.central-h-spaces.html" class="Module">structured-types.central-h-spaces</a> <a id="70" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="126" class="Keyword">open</a> <a id="131" class="Keyword">import</a> <a id="138" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

In [`structured-types.h-spaces`](structured-types.h-spaces.md) we saw that the
type of H-space structures on a
[pointed type](structured-types.pointed-types.md) `A` is equivalently described
as the type of [pointed sections](structured-types.pointed-types.md) of the
pointed evaluation map `(A → A) →∗ A`. If the type `A` is
[connected](foundation.connected-types.md), then the section maps to the
[connected component](foundation.connected-components.md) of `(A ≃ A)` at the
identity [equivalence](foundation-core.equivalences.md). An **evaluative
H-space** is a pointed type such that the map `ev_pt : (A ≃ A)_{(id)} → A` is an
equivalence.

## Definition

<pre class="Agda"><a id="is-central-h-space"></a><a id="938" href="structured-types.central-h-spaces.html#938" class="Function">is-central-h-space</a> <a id="957" class="Symbol">:</a>
  <a id="961" class="Symbol">{</a><a id="962" href="structured-types.central-h-spaces.html#962" class="Bound">l</a> <a id="964" class="Symbol">:</a> <a id="966" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="971" class="Symbol">}</a> <a id="973" class="Symbol">(</a><a id="974" href="structured-types.central-h-spaces.html#974" class="Bound">A</a> <a id="976" class="Symbol">:</a> <a id="978" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="991" href="structured-types.central-h-spaces.html#962" class="Bound">l</a><a id="992" class="Symbol">)</a> <a id="994" class="Symbol">→</a> <a id="996" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="999" href="structured-types.central-h-spaces.html#962" class="Bound">l</a>
<a id="1001" href="structured-types.central-h-spaces.html#938" class="Function">is-central-h-space</a> <a id="1020" href="structured-types.central-h-spaces.html#1020" class="Bound">A</a> <a id="1022" class="Symbol">=</a>
  <a id="1026" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a>
    <a id="1039" class="Symbol">{</a> <a id="1041" class="Argument">A</a> <a id="1043" class="Symbol">=</a> <a id="1045" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1063" href="structured-types.central-h-spaces.html#1020" class="Bound">A</a> <a id="1065" class="Symbol">→</a> <a id="1067" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1085" href="structured-types.central-h-spaces.html#1020" class="Bound">A</a><a id="1086" class="Symbol">}</a>
    <a id="1092" class="Symbol">(</a> <a id="1094" href="structured-types.pointed-types.html#659" class="Function">ev-point-Pointed-Type</a> <a id="1116" href="structured-types.central-h-spaces.html#1020" class="Bound">A</a><a id="1117" class="Symbol">)</a>
</pre>
## References

{{#bibliography}} {{#reference BCFR23}}
