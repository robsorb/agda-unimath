# Large identity types

<pre class="Agda"><a id="33" class="Keyword">module</a> <a id="40" href="foundation.large-identity-types.html" class="Module">foundation.large-identity-types</a> <a id="72" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Definition

<pre class="Agda"><a id="207" class="Keyword">module</a> <a id="214" href="foundation.large-identity-types.html#214" class="Module">_</a>
  <a id="218" class="Symbol">{</a><a id="219" href="foundation.large-identity-types.html#219" class="Bound">A</a> <a id="221" class="Symbol">:</a> <a id="223" href="Agda.Primitive.html#512" class="Primitive">UUω</a><a id="226" class="Symbol">}</a>
  <a id="230" class="Keyword">where</a>

  <a id="239" class="Keyword">data</a> <a id="244" href="foundation.large-identity-types.html#244" class="Datatype">Idω</a> <a id="248" class="Symbol">(</a><a id="249" href="foundation.large-identity-types.html#249" class="Bound">x</a> <a id="251" class="Symbol">:</a> <a id="253" href="foundation.large-identity-types.html#219" class="Bound">A</a><a id="254" class="Symbol">)</a> <a id="256" class="Symbol">:</a> <a id="258" href="foundation.large-identity-types.html#219" class="Bound">A</a> <a id="260" class="Symbol">→</a> <a id="262" href="Agda.Primitive.html#512" class="Primitive">UUω</a> <a id="266" class="Keyword">where</a>
    <a id="276" href="foundation.large-identity-types.html#276" class="InductiveConstructor">reflω</a> <a id="282" class="Symbol">:</a> <a id="284" href="foundation.large-identity-types.html#244" class="Datatype">Idω</a> <a id="288" href="foundation.large-identity-types.html#249" class="Bound">x</a> <a id="290" href="foundation.large-identity-types.html#249" class="Bound">x</a>

  <a id="295" href="foundation.large-identity-types.html#295" class="Function Operator">_＝ω_</a> <a id="300" class="Symbol">:</a> <a id="302" href="foundation.large-identity-types.html#219" class="Bound">A</a> <a id="304" class="Symbol">→</a> <a id="306" href="foundation.large-identity-types.html#219" class="Bound">A</a> <a id="308" class="Symbol">→</a> <a id="310" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="316" class="Symbol">(</a><a id="317" href="foundation.large-identity-types.html#317" class="Bound">a</a> <a id="319" href="foundation.large-identity-types.html#295" class="Function Operator">＝ω</a> <a id="322" href="foundation.large-identity-types.html#322" class="Bound">b</a><a id="323" class="Symbol">)</a> <a id="325" class="Symbol">=</a> <a id="327" href="foundation.large-identity-types.html#244" class="Datatype">Idω</a> <a id="331" href="foundation.large-identity-types.html#317" class="Bound">a</a> <a id="333" href="foundation.large-identity-types.html#322" class="Bound">b</a>
</pre>