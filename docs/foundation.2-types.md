# `2`-Types

<pre class="Agda"><a id="22" class="Keyword">module</a> <a id="29" href="foundation.2-types.html" class="Module">foundation.2-types</a> <a id="48" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="104" class="Keyword">open</a> <a id="109" class="Keyword">import</a> <a id="116" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="148" class="Keyword">open</a> <a id="153" class="Keyword">import</a> <a id="160" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
</pre>
</details>

## Definition

A 2-type is a type that is 2-truncated

<pre class="Agda"><a id="is-2-type"></a><a id="358" href="foundation.2-types.html#358" class="Function">is-2-type</a> <a id="368" class="Symbol">:</a> <a id="370" class="Symbol">{</a><a id="371" href="foundation.2-types.html#371" class="Bound">l</a> <a id="373" class="Symbol">:</a> <a id="375" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="380" class="Symbol">}</a> <a id="382" class="Symbol">→</a> <a id="384" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="387" href="foundation.2-types.html#371" class="Bound">l</a> <a id="389" class="Symbol">→</a> <a id="391" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="394" href="foundation.2-types.html#371" class="Bound">l</a>
<a id="396" href="foundation.2-types.html#358" class="Function">is-2-type</a> <a id="406" class="Symbol">=</a> <a id="408" href="foundation-core.truncated-types.html#1305" class="Function">is-trunc</a> <a id="417" class="Symbol">(</a><a id="418" href="foundation-core.truncation-levels.html#743" class="Function">two-𝕋</a><a id="423" class="Symbol">)</a>

<a id="UU-2-Type"></a><a id="426" href="foundation.2-types.html#426" class="Function">UU-2-Type</a> <a id="436" class="Symbol">:</a> <a id="438" class="Symbol">(</a><a id="439" href="foundation.2-types.html#439" class="Bound">l</a> <a id="441" class="Symbol">:</a> <a id="443" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="448" class="Symbol">)</a> <a id="450" class="Symbol">→</a> <a id="452" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="455" class="Symbol">(</a><a id="456" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="461" href="foundation.2-types.html#439" class="Bound">l</a><a id="462" class="Symbol">)</a>
<a id="464" href="foundation.2-types.html#426" class="Function">UU-2-Type</a> <a id="474" href="foundation.2-types.html#474" class="Bound">l</a> <a id="476" class="Symbol">=</a> <a id="478" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="480" class="Symbol">(</a><a id="481" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="484" href="foundation.2-types.html#474" class="Bound">l</a><a id="485" class="Symbol">)</a> <a id="487" href="foundation.2-types.html#358" class="Function">is-2-type</a>

<a id="type-2-Type"></a><a id="498" href="foundation.2-types.html#498" class="Function">type-2-Type</a> <a id="510" class="Symbol">:</a>
  <a id="514" class="Symbol">{</a><a id="515" href="foundation.2-types.html#515" class="Bound">l</a> <a id="517" class="Symbol">:</a> <a id="519" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="524" class="Symbol">}</a> <a id="526" class="Symbol">→</a> <a id="528" href="foundation.2-types.html#426" class="Function">UU-2-Type</a> <a id="538" href="foundation.2-types.html#515" class="Bound">l</a> <a id="540" class="Symbol">→</a> <a id="542" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="545" href="foundation.2-types.html#515" class="Bound">l</a>
<a id="547" href="foundation.2-types.html#498" class="Function">type-2-Type</a> <a id="559" class="Symbol">=</a> <a id="561" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

<a id="566" class="Keyword">abstract</a>
  <a id="is-2-type-type-2-Type"></a><a id="577" href="foundation.2-types.html#577" class="Function">is-2-type-type-2-Type</a> <a id="599" class="Symbol">:</a>
    <a id="605" class="Symbol">{</a><a id="606" href="foundation.2-types.html#606" class="Bound">l</a> <a id="608" class="Symbol">:</a> <a id="610" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="615" class="Symbol">}</a> <a id="617" class="Symbol">(</a><a id="618" href="foundation.2-types.html#618" class="Bound">A</a> <a id="620" class="Symbol">:</a> <a id="622" href="foundation.2-types.html#426" class="Function">UU-2-Type</a> <a id="632" href="foundation.2-types.html#606" class="Bound">l</a><a id="633" class="Symbol">)</a> <a id="635" class="Symbol">→</a> <a id="637" href="foundation.2-types.html#358" class="Function">is-2-type</a> <a id="647" class="Symbol">(</a><a id="648" href="foundation.2-types.html#498" class="Function">type-2-Type</a> <a id="660" href="foundation.2-types.html#618" class="Bound">A</a><a id="661" class="Symbol">)</a>
  <a id="665" href="foundation.2-types.html#577" class="Function">is-2-type-type-2-Type</a> <a id="687" class="Symbol">=</a> <a id="689" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>