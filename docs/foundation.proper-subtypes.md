# Proper subsets

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="foundation.proper-subtypes.html" class="Module">foundation.proper-subtypes</a> <a id="61" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="117" class="Keyword">open</a> <a id="122" class="Keyword">import</a> <a id="129" href="foundation.complements-subtypes.html" class="Module">foundation.complements-subtypes</a>
<a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="foundation.inhabited-subtypes.html" class="Module">foundation.inhabited-subtypes</a>
<a id="203" class="Keyword">open</a> <a id="208" class="Keyword">import</a> <a id="215" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="foundation-core.subtypes.html" class="Module">foundation-core.subtypes</a>
</pre>
</details>

## Idea

A subtype of a type is said to be **proper** if its complement is inhabited.

<pre class="Agda"><a id="is-proper-subtype-Prop"></a><a id="433" href="foundation.proper-subtypes.html#433" class="Function">is-proper-subtype-Prop</a> <a id="456" class="Symbol">:</a>
  <a id="460" class="Symbol">{</a><a id="461" href="foundation.proper-subtypes.html#461" class="Bound">l1</a> <a id="464" href="foundation.proper-subtypes.html#464" class="Bound">l2</a> <a id="467" class="Symbol">:</a> <a id="469" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="474" class="Symbol">}</a> <a id="476" class="Symbol">{</a><a id="477" href="foundation.proper-subtypes.html#477" class="Bound">A</a> <a id="479" class="Symbol">:</a> <a id="481" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="484" href="foundation.proper-subtypes.html#461" class="Bound">l1</a><a id="486" class="Symbol">}</a> <a id="488" class="Symbol">→</a> <a id="490" href="foundation-core.subtypes.html#1435" class="Function">subtype</a> <a id="498" href="foundation.proper-subtypes.html#464" class="Bound">l2</a> <a id="501" href="foundation.proper-subtypes.html#477" class="Bound">A</a> <a id="503" class="Symbol">→</a> <a id="505" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="510" class="Symbol">(</a><a id="511" href="foundation.proper-subtypes.html#461" class="Bound">l1</a> <a id="514" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="516" href="foundation.proper-subtypes.html#464" class="Bound">l2</a><a id="518" class="Symbol">)</a>
<a id="520" href="foundation.proper-subtypes.html#433" class="Function">is-proper-subtype-Prop</a> <a id="543" href="foundation.proper-subtypes.html#543" class="Bound">P</a> <a id="545" class="Symbol">=</a>
  <a id="549" href="foundation.inhabited-subtypes.html#700" class="Function">is-inhabited-subtype-Prop</a> <a id="575" class="Symbol">(</a><a id="576" href="foundation.complements-subtypes.html#1332" class="Function">complement-subtype</a> <a id="595" href="foundation.proper-subtypes.html#543" class="Bound">P</a><a id="596" class="Symbol">)</a>
</pre>