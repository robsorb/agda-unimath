# Predicates on lists

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="lists.predicates-on-lists.html" class="Module">lists.predicates-on-lists</a> <a id="65" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="121" class="Keyword">open</a> <a id="126" class="Keyword">import</a> <a id="133" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="lists.lists.html" class="Module">lists.lists</a>
</pre>
</details>

## Definitions

### For all

<pre class="Agda"><a id="308" class="Keyword">module</a> <a id="315" href="lists.predicates-on-lists.html#315" class="Module">_</a>
  <a id="319" class="Symbol">{</a><a id="320" href="lists.predicates-on-lists.html#320" class="Bound">l1</a> <a id="323" href="lists.predicates-on-lists.html#323" class="Bound">l2</a> <a id="326" class="Symbol">:</a> <a id="328" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="333" class="Symbol">}</a> <a id="335" class="Symbol">(</a><a id="336" href="lists.predicates-on-lists.html#336" class="Bound">X</a> <a id="338" class="Symbol">:</a> <a id="340" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="343" href="lists.predicates-on-lists.html#320" class="Bound">l1</a><a id="345" class="Symbol">)</a> <a id="347" class="Symbol">(</a><a id="348" href="lists.predicates-on-lists.html#348" class="Bound">P</a> <a id="350" class="Symbol">:</a> <a id="352" href="lists.predicates-on-lists.html#336" class="Bound">X</a> <a id="354" class="Symbol">→</a> <a id="356" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="361" href="lists.predicates-on-lists.html#323" class="Bound">l2</a><a id="363" class="Symbol">)</a>
  <a id="367" class="Keyword">where</a>

  <a id="376" href="lists.predicates-on-lists.html#376" class="Function">for-all-list-Prop</a> <a id="394" class="Symbol">:</a>
    <a id="400" class="Symbol">(</a><a id="401" href="lists.predicates-on-lists.html#401" class="Bound">l</a> <a id="403" class="Symbol">:</a> <a id="405" href="lists.lists.html#1328" class="Datatype">list</a> <a id="410" href="lists.predicates-on-lists.html#336" class="Bound">X</a><a id="411" class="Symbol">)</a> <a id="413" class="Symbol">→</a> <a id="415" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="420" href="lists.predicates-on-lists.html#323" class="Bound">l2</a>
  <a id="425" href="lists.predicates-on-lists.html#376" class="Function">for-all-list-Prop</a> <a id="443" href="lists.lists.html#1371" class="InductiveConstructor">nil</a> <a id="447" class="Symbol">=</a> <a id="449" href="foundation.unit-type.html#4828" class="Function">raise-unit-Prop</a> <a id="465" href="lists.predicates-on-lists.html#323" class="Bound">l2</a>
  <a id="470" href="lists.predicates-on-lists.html#376" class="Function">for-all-list-Prop</a> <a id="488" class="Symbol">(</a><a id="489" href="lists.lists.html#1386" class="InductiveConstructor">cons</a> <a id="494" href="lists.predicates-on-lists.html#494" class="Bound">x</a> <a id="496" href="lists.predicates-on-lists.html#496" class="Bound">l</a><a id="497" class="Symbol">)</a> <a id="499" class="Symbol">=</a> <a id="501" href="foundation-core.propositions.html#6270" class="Function">product-Prop</a> <a id="514" class="Symbol">(</a><a id="515" href="lists.predicates-on-lists.html#348" class="Bound">P</a> <a id="517" href="lists.predicates-on-lists.html#494" class="Bound">x</a><a id="518" class="Symbol">)</a> <a id="520" class="Symbol">(</a><a id="521" href="lists.predicates-on-lists.html#376" class="Function">for-all-list-Prop</a> <a id="539" href="lists.predicates-on-lists.html#496" class="Bound">l</a><a id="540" class="Symbol">)</a>

  <a id="545" href="lists.predicates-on-lists.html#545" class="Function">for-all-list</a> <a id="558" class="Symbol">:</a>
    <a id="564" class="Symbol">(</a><a id="565" href="lists.predicates-on-lists.html#565" class="Bound">l</a> <a id="567" class="Symbol">:</a> <a id="569" href="lists.lists.html#1328" class="Datatype">list</a> <a id="574" href="lists.predicates-on-lists.html#336" class="Bound">X</a><a id="575" class="Symbol">)</a> <a id="577" class="Symbol">→</a> <a id="579" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="582" href="lists.predicates-on-lists.html#323" class="Bound">l2</a>
  <a id="587" href="lists.predicates-on-lists.html#545" class="Function">for-all-list</a> <a id="600" href="lists.predicates-on-lists.html#600" class="Bound">l</a> <a id="602" class="Symbol">=</a> <a id="604" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="614" class="Symbol">(</a><a id="615" href="lists.predicates-on-lists.html#376" class="Function">for-all-list-Prop</a> <a id="633" href="lists.predicates-on-lists.html#600" class="Bound">l</a><a id="634" class="Symbol">)</a>

  <a id="639" href="lists.predicates-on-lists.html#639" class="Function">is-prop-for-all-list</a> <a id="660" class="Symbol">:</a>
    <a id="666" class="Symbol">(</a><a id="667" href="lists.predicates-on-lists.html#667" class="Bound">l</a> <a id="669" class="Symbol">:</a> <a id="671" href="lists.lists.html#1328" class="Datatype">list</a> <a id="676" href="lists.predicates-on-lists.html#336" class="Bound">X</a><a id="677" class="Symbol">)</a> <a id="679" class="Symbol">→</a> <a id="681" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="689" class="Symbol">(</a><a id="690" href="lists.predicates-on-lists.html#545" class="Function">for-all-list</a> <a id="703" href="lists.predicates-on-lists.html#667" class="Bound">l</a><a id="704" class="Symbol">)</a>
  <a id="708" href="lists.predicates-on-lists.html#639" class="Function">is-prop-for-all-list</a> <a id="729" href="lists.predicates-on-lists.html#729" class="Bound">l</a> <a id="731" class="Symbol">=</a> <a id="733" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="751" class="Symbol">(</a><a id="752" href="lists.predicates-on-lists.html#376" class="Function">for-all-list-Prop</a> <a id="770" href="lists.predicates-on-lists.html#729" class="Bound">l</a><a id="771" class="Symbol">)</a>
</pre>