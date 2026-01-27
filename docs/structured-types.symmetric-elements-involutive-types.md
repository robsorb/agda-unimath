# Symmetric elements of involutive types

<pre class="Agda"><a id="51" class="Keyword">module</a> <a id="58" href="structured-types.symmetric-elements-involutive-types.html" class="Module">structured-types.symmetric-elements-involutive-types</a> <a id="111" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="167" class="Keyword">open</a> <a id="172" class="Keyword">import</a> <a id="179" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="structured-types.involutive-types.html" class="Module">structured-types.involutive-types</a>

<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
</pre>
</details>

## Idea

Symmetric elements of involutive types are fixed points of the involution. In
other words, the type of symmetric elements of an involutive type `A` is defined
to be

```text
  (X : 2-Element-Type lzero) → A X
```

## Definition

<pre class="Agda"><a id="symmetric-element-Involutive-Type"></a><a id="569" href="structured-types.symmetric-elements-involutive-types.html#569" class="Function">symmetric-element-Involutive-Type</a> <a id="603" class="Symbol">:</a>
  <a id="607" class="Symbol">{</a><a id="608" href="structured-types.symmetric-elements-involutive-types.html#608" class="Bound">l</a> <a id="610" class="Symbol">:</a> <a id="612" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="617" class="Symbol">}</a> <a id="619" class="Symbol">(</a><a id="620" href="structured-types.symmetric-elements-involutive-types.html#620" class="Bound">A</a> <a id="622" class="Symbol">:</a> <a id="624" href="structured-types.involutive-types.html#662" class="Function">Involutive-Type</a> <a id="640" href="structured-types.symmetric-elements-involutive-types.html#608" class="Bound">l</a><a id="641" class="Symbol">)</a> <a id="643" class="Symbol">→</a> <a id="645" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="648" class="Symbol">(</a><a id="649" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="654" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="660" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="662" href="structured-types.symmetric-elements-involutive-types.html#608" class="Bound">l</a><a id="663" class="Symbol">)</a>
<a id="665" href="structured-types.symmetric-elements-involutive-types.html#569" class="Function">symmetric-element-Involutive-Type</a> <a id="699" href="structured-types.symmetric-elements-involutive-types.html#699" class="Bound">A</a> <a id="701" class="Symbol">=</a> <a id="703" class="Symbol">(</a><a id="704" href="structured-types.symmetric-elements-involutive-types.html#704" class="Bound">X</a> <a id="706" class="Symbol">:</a> <a id="708" href="univalent-combinatorics.2-element-types.html#2893" class="Function">2-Element-Type</a> <a id="723" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="728" class="Symbol">)</a> <a id="730" class="Symbol">→</a> <a id="732" href="structured-types.symmetric-elements-involutive-types.html#699" class="Bound">A</a> <a id="734" href="structured-types.symmetric-elements-involutive-types.html#704" class="Bound">X</a>
</pre>