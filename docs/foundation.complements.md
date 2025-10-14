# Complements of type families

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="foundation.complements.html" class="Module">foundation.complements</a> <a id="71" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="171" class="Keyword">open</a> <a id="176" class="Keyword">import</a> <a id="183" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

The **complement** of a type family `B` over `A` consists of the type of points
in `A` at which `B x` is [empty](foundation-core.empty-types.md).

<pre class="Agda"><a id="complement"></a><a id="475" href="foundation.complements.html#475" class="Function">complement</a> <a id="486" class="Symbol">:</a>
  <a id="490" class="Symbol">{</a><a id="491" href="foundation.complements.html#491" class="Bound">l1</a> <a id="494" href="foundation.complements.html#494" class="Bound">l2</a> <a id="497" class="Symbol">:</a> <a id="499" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="504" class="Symbol">}</a> <a id="506" class="Symbol">{</a><a id="507" href="foundation.complements.html#507" class="Bound">A</a> <a id="509" class="Symbol">:</a> <a id="511" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="514" href="foundation.complements.html#491" class="Bound">l1</a><a id="516" class="Symbol">}</a> <a id="518" class="Symbol">(</a><a id="519" href="foundation.complements.html#519" class="Bound">B</a> <a id="521" class="Symbol">:</a> <a id="523" href="foundation.complements.html#507" class="Bound">A</a> <a id="525" class="Symbol">→</a> <a id="527" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="530" href="foundation.complements.html#494" class="Bound">l2</a><a id="532" class="Symbol">)</a> <a id="534" class="Symbol">→</a> <a id="536" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="539" class="Symbol">(</a><a id="540" href="foundation.complements.html#491" class="Bound">l1</a> <a id="543" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="545" href="foundation.complements.html#494" class="Bound">l2</a><a id="547" class="Symbol">)</a>
<a id="549" href="foundation.complements.html#475" class="Function">complement</a> <a id="560" class="Symbol">{</a><a id="561" href="foundation.complements.html#561" class="Bound">l1</a><a id="563" class="Symbol">}</a> <a id="565" class="Symbol">{</a><a id="566" href="foundation.complements.html#566" class="Bound">l2</a><a id="568" class="Symbol">}</a> <a id="570" class="Symbol">{</a><a id="571" href="foundation.complements.html#571" class="Bound">A</a><a id="572" class="Symbol">}</a> <a id="574" href="foundation.complements.html#574" class="Bound">B</a> <a id="576" class="Symbol">=</a> <a id="578" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="580" href="foundation.complements.html#571" class="Bound">A</a> <a id="582" class="Symbol">(</a><a id="583" href="foundation-core.empty-types.html#972" class="Function">is-empty</a> <a id="592" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="594" href="foundation.complements.html#574" class="Bound">B</a><a id="595" class="Symbol">)</a>
</pre>