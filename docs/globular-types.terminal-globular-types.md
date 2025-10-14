# Terminal globular types

<pre class="Agda"><a id="36" class="Symbol">{-#</a> <a id="40" class="Keyword">OPTIONS</a> <a id="48" class="Pragma">--guardedness</a> <a id="62" class="Symbol">#-}</a>

<a id="67" class="Keyword">module</a> <a id="74" href="globular-types.terminal-globular-types.html" class="Module">globular-types.terminal-globular-types</a> <a id="113" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="211" class="Keyword">open</a> <a id="216" class="Keyword">import</a> <a id="223" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="251" class="Keyword">open</a> <a id="256" class="Keyword">import</a> <a id="263" href="globular-types.globular-maps.html" class="Module">globular-types.globular-maps</a>
<a id="292" class="Keyword">open</a> <a id="297" class="Keyword">import</a> <a id="304" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

A [globular type](globular-types.globular-types.md) `G` is said to be
{{#concept "terminal" Disambiguation="globular type" Agda=is-terminal-Globular-Type}}
if for any globular type `H` the type of
[globular maps](globular-types.globular-maps.md) `H → G` is
[contractible](foundation-core.contractible-types.md).

## Definitions

### The predicate of being a terminal globular type

<pre class="Agda"><a id="is-terminal-Globular-Type"></a><a id="750" href="globular-types.terminal-globular-types.html#750" class="Function">is-terminal-Globular-Type</a> <a id="776" class="Symbol">:</a>
  <a id="780" class="Symbol">{</a><a id="781" href="globular-types.terminal-globular-types.html#781" class="Bound">l1</a> <a id="784" href="globular-types.terminal-globular-types.html#784" class="Bound">l2</a> <a id="787" class="Symbol">:</a> <a id="789" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="794" class="Symbol">}</a> <a id="796" class="Symbol">→</a> <a id="798" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="812" href="globular-types.terminal-globular-types.html#781" class="Bound">l1</a> <a id="815" href="globular-types.terminal-globular-types.html#784" class="Bound">l2</a> <a id="818" class="Symbol">→</a> <a id="820" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
<a id="824" href="globular-types.terminal-globular-types.html#750" class="Function">is-terminal-Globular-Type</a> <a id="850" href="globular-types.terminal-globular-types.html#850" class="Bound">G</a> <a id="852" class="Symbol">=</a>
  <a id="856" class="Symbol">{</a><a id="857" href="globular-types.terminal-globular-types.html#857" class="Bound">l3</a> <a id="860" href="globular-types.terminal-globular-types.html#860" class="Bound">l4</a> <a id="863" class="Symbol">:</a> <a id="865" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="870" class="Symbol">}</a> <a id="872" class="Symbol">(</a><a id="873" href="globular-types.terminal-globular-types.html#873" class="Bound">H</a> <a id="875" class="Symbol">:</a> <a id="877" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="891" href="globular-types.terminal-globular-types.html#857" class="Bound">l3</a> <a id="894" href="globular-types.terminal-globular-types.html#860" class="Bound">l4</a><a id="896" class="Symbol">)</a> <a id="898" class="Symbol">→</a> <a id="900" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="909" class="Symbol">(</a><a id="910" href="globular-types.globular-maps.html#774" class="Record">globular-map</a> <a id="923" href="globular-types.terminal-globular-types.html#873" class="Bound">H</a> <a id="925" href="globular-types.terminal-globular-types.html#850" class="Bound">G</a><a id="926" class="Symbol">)</a>
</pre>