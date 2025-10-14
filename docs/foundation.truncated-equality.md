# Truncated equality

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="foundation.truncated-equality.html" class="Module">foundation.truncated-equality</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="159" class="Keyword">open</a> <a id="164" class="Keyword">import</a> <a id="171" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="242" class="Keyword">open</a> <a id="247" class="Keyword">import</a> <a id="254" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

## Definition

<pre class="Agda"><a id="trunc-eq"></a><a id="372" href="foundation.truncated-equality.html#372" class="Function">trunc-eq</a> <a id="381" class="Symbol">:</a> <a id="383" class="Symbol">{</a><a id="384" href="foundation.truncated-equality.html#384" class="Bound">l</a> <a id="386" class="Symbol">:</a> <a id="388" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="393" class="Symbol">}</a> <a id="395" class="Symbol">(</a><a id="396" href="foundation.truncated-equality.html#396" class="Bound">k</a> <a id="398" class="Symbol">:</a> <a id="400" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="401" class="Symbol">)</a> <a id="403" class="Symbol">{</a><a id="404" href="foundation.truncated-equality.html#404" class="Bound">A</a> <a id="406" class="Symbol">:</a> <a id="408" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="411" href="foundation.truncated-equality.html#384" class="Bound">l</a><a id="412" class="Symbol">}</a> <a id="414" class="Symbol">→</a> <a id="416" href="foundation.truncated-equality.html#404" class="Bound">A</a> <a id="418" class="Symbol">→</a> <a id="420" href="foundation.truncated-equality.html#404" class="Bound">A</a> <a id="422" class="Symbol">→</a> <a id="424" href="foundation-core.truncated-types.html#1603" class="Function">Truncated-Type</a> <a id="439" href="foundation.truncated-equality.html#384" class="Bound">l</a> <a id="441" href="foundation.truncated-equality.html#396" class="Bound">k</a>
<a id="443" href="foundation.truncated-equality.html#372" class="Function">trunc-eq</a> <a id="452" href="foundation.truncated-equality.html#452" class="Bound">k</a> <a id="454" href="foundation.truncated-equality.html#454" class="Bound">x</a> <a id="456" href="foundation.truncated-equality.html#456" class="Bound">y</a> <a id="458" class="Symbol">=</a> <a id="460" href="foundation.truncations.html#1445" class="Function">trunc</a> <a id="466" href="foundation.truncated-equality.html#452" class="Bound">k</a> <a id="468" class="Symbol">(</a><a id="469" href="foundation.truncated-equality.html#454" class="Bound">x</a> <a id="471" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="473" href="foundation.truncated-equality.html#456" class="Bound">y</a><a id="474" class="Symbol">)</a>
</pre>