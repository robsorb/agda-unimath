# Perfect subgroups

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="group-theory.perfect-subgroups.html" class="Module">group-theory.perfect-subgroups</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="group-theory.perfect-groups.html" class="Module">group-theory.perfect-groups</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
</pre>
</details>

## Idea

A [subgroup](group-theory.subgroups.md) `H` of a [group](group-theory.groups.md)
`G` is a **perfect subgroup** if it is a
[perfect group](group-theory.perfect-groups.md) on its own.

## Definitions

### The predicate of being a perfect subgroup

<pre class="Agda"><a id="587" class="Keyword">module</a> <a id="594" href="group-theory.perfect-subgroups.html#594" class="Module">_</a>
  <a id="598" class="Symbol">{</a><a id="599" href="group-theory.perfect-subgroups.html#599" class="Bound">l1</a> <a id="602" href="group-theory.perfect-subgroups.html#602" class="Bound">l2</a> <a id="605" class="Symbol">:</a> <a id="607" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="612" class="Symbol">}</a> <a id="614" class="Symbol">(</a><a id="615" href="group-theory.perfect-subgroups.html#615" class="Bound">G</a> <a id="617" class="Symbol">:</a> <a id="619" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="625" href="group-theory.perfect-subgroups.html#599" class="Bound">l1</a><a id="627" class="Symbol">)</a> <a id="629" class="Symbol">(</a><a id="630" href="group-theory.perfect-subgroups.html#630" class="Bound">H</a> <a id="632" class="Symbol">:</a> <a id="634" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="643" href="group-theory.perfect-subgroups.html#602" class="Bound">l2</a> <a id="646" href="group-theory.perfect-subgroups.html#615" class="Bound">G</a><a id="647" class="Symbol">)</a>
  <a id="651" class="Keyword">where</a>

  <a id="660" href="group-theory.perfect-subgroups.html#660" class="Function">is-perfect-prop-Subgroup</a> <a id="685" class="Symbol">:</a> <a id="687" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="692" class="Symbol">(</a><a id="693" href="group-theory.perfect-subgroups.html#599" class="Bound">l1</a> <a id="696" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="698" href="group-theory.perfect-subgroups.html#602" class="Bound">l2</a><a id="700" class="Symbol">)</a>
  <a id="704" href="group-theory.perfect-subgroups.html#660" class="Function">is-perfect-prop-Subgroup</a> <a id="729" class="Symbol">=</a> <a id="731" href="group-theory.perfect-groups.html#671" class="Function">is-perfect-prop-Group</a> <a id="753" class="Symbol">(</a><a id="754" href="group-theory.subgroups.html#10896" class="Function">group-Subgroup</a> <a id="769" href="group-theory.perfect-subgroups.html#615" class="Bound">G</a> <a id="771" href="group-theory.perfect-subgroups.html#630" class="Bound">H</a><a id="772" class="Symbol">)</a>

  <a id="777" href="group-theory.perfect-subgroups.html#777" class="Function">is-perfect-Subgroup</a> <a id="797" class="Symbol">:</a> <a id="799" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="802" class="Symbol">(</a><a id="803" href="group-theory.perfect-subgroups.html#599" class="Bound">l1</a> <a id="806" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="808" href="group-theory.perfect-subgroups.html#602" class="Bound">l2</a><a id="810" class="Symbol">)</a>
  <a id="814" href="group-theory.perfect-subgroups.html#777" class="Function">is-perfect-Subgroup</a> <a id="834" class="Symbol">=</a> <a id="836" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="846" href="group-theory.perfect-subgroups.html#660" class="Function">is-perfect-prop-Subgroup</a>

  <a id="874" href="group-theory.perfect-subgroups.html#874" class="Function">is-prop-is-perfect-Subgroup</a> <a id="902" class="Symbol">:</a> <a id="904" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="912" href="group-theory.perfect-subgroups.html#777" class="Function">is-perfect-Subgroup</a>
  <a id="934" href="group-theory.perfect-subgroups.html#874" class="Function">is-prop-is-perfect-Subgroup</a> <a id="962" class="Symbol">=</a> <a id="964" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="982" href="group-theory.perfect-subgroups.html#660" class="Function">is-perfect-prop-Subgroup</a>
</pre>
## External links

A wikidata identifier was not available for this concept.
