# Identity types of truncated types

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="foundation.identity-truncated-types.html" class="Module">foundation.identity-truncated-types</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="347" class="Keyword">open</a> <a id="352" class="Keyword">import</a> <a id="359" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

### The type of identity of truncated types is truncated

<pre class="Agda"><a id="476" class="Keyword">module</a> <a id="483" href="foundation.identity-truncated-types.html#483" class="Module">_</a>
  <a id="487" class="Symbol">{</a><a id="488" href="foundation.identity-truncated-types.html#488" class="Bound">l</a> <a id="490" class="Symbol">:</a> <a id="492" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="497" class="Symbol">}</a> <a id="499" class="Symbol">{</a><a id="500" href="foundation.identity-truncated-types.html#500" class="Bound">A</a> <a id="502" href="foundation.identity-truncated-types.html#502" class="Bound">B</a> <a id="504" class="Symbol">:</a> <a id="506" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="509" href="foundation.identity-truncated-types.html#488" class="Bound">l</a><a id="510" class="Symbol">}</a>
  <a id="514" class="Keyword">where</a>

  <a id="523" href="foundation.identity-truncated-types.html#523" class="Function">is-trunc-id-is-trunc</a> <a id="544" class="Symbol">:</a>
    <a id="550" class="Symbol">(</a><a id="551" href="foundation.identity-truncated-types.html#551" class="Bound">k</a> <a id="553" class="Symbol">:</a> <a id="555" href="foundation-core.truncation-levels.html#521" class="Datatype">𝕋</a><a id="556" class="Symbol">)</a> <a id="558" class="Symbol">→</a> <a id="560" href="foundation-core.truncated-types.html#1305" class="Function">is-trunc</a> <a id="569" href="foundation.identity-truncated-types.html#551" class="Bound">k</a> <a id="571" href="foundation.identity-truncated-types.html#500" class="Bound">A</a> <a id="573" class="Symbol">→</a> <a id="575" href="foundation-core.truncated-types.html#1305" class="Function">is-trunc</a> <a id="584" href="foundation.identity-truncated-types.html#551" class="Bound">k</a> <a id="586" href="foundation.identity-truncated-types.html#502" class="Bound">B</a> <a id="588" class="Symbol">→</a> <a id="590" href="foundation-core.truncated-types.html#1305" class="Function">is-trunc</a> <a id="599" href="foundation.identity-truncated-types.html#551" class="Bound">k</a> <a id="601" class="Symbol">(</a><a id="602" href="foundation.identity-truncated-types.html#500" class="Bound">A</a> <a id="604" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="606" href="foundation.identity-truncated-types.html#502" class="Bound">B</a><a id="607" class="Symbol">)</a>
  <a id="611" href="foundation.identity-truncated-types.html#523" class="Function">is-trunc-id-is-trunc</a> <a id="632" href="foundation.identity-truncated-types.html#632" class="Bound">k</a> <a id="634" href="foundation.identity-truncated-types.html#634" class="Bound">is-trunc-A</a> <a id="645" href="foundation.identity-truncated-types.html#645" class="Bound">is-trunc-B</a> <a id="656" class="Symbol">=</a>
    <a id="662" href="foundation-core.truncated-types.html#4262" class="Function">is-trunc-equiv</a> <a id="677" href="foundation.identity-truncated-types.html#632" class="Bound">k</a>
      <a id="685" class="Symbol">(</a> <a id="687" href="foundation.identity-truncated-types.html#500" class="Bound">A</a> <a id="689" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="691" href="foundation.identity-truncated-types.html#502" class="Bound">B</a><a id="692" class="Symbol">)</a>
      <a id="700" class="Symbol">(</a> <a id="702" href="foundation.univalence.html#2311" class="Function">equiv-univalence</a><a id="718" class="Symbol">)</a>
      <a id="726" class="Symbol">(</a> <a id="728" href="foundation-core.truncated-types.html#13193" class="Function">is-trunc-equiv-is-trunc</a> <a id="752" href="foundation.identity-truncated-types.html#632" class="Bound">k</a> <a id="754" href="foundation.identity-truncated-types.html#634" class="Bound">is-trunc-A</a> <a id="765" href="foundation.identity-truncated-types.html#645" class="Bound">is-trunc-B</a><a id="775" class="Symbol">)</a>
</pre>