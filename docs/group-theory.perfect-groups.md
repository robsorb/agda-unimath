# Perfect groups

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="group-theory.perfect-groups.html" class="Module">group-theory.perfect-groups</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="group-theory.commutator-subgroups.html" class="Module">group-theory.commutator-subgroups</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="group-theory.full-subgroups.html" class="Module">group-theory.full-subgroups</a>
<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="group-theory.groups.html" class="Module">group-theory.groups</a>
</pre>
</details>

## Idea

A [group](group-theory.groups.md) `G` is said to be **perfect** if its
[commutator subgroup](group-theory.commutator-subgroups.md) is a
[full](group-theory.full-subgroups.md) [subgroup](group-theory.subgroups.md).

## Definitions

### The predicate of being a perfect group

<pre class="Agda"><a id="621" class="Keyword">module</a> <a id="628" href="group-theory.perfect-groups.html#628" class="Module">_</a>
  <a id="632" class="Symbol">{</a><a id="633" href="group-theory.perfect-groups.html#633" class="Bound">l1</a> <a id="636" class="Symbol">:</a> <a id="638" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="643" class="Symbol">}</a> <a id="645" class="Symbol">(</a><a id="646" href="group-theory.perfect-groups.html#646" class="Bound">G</a> <a id="648" class="Symbol">:</a> <a id="650" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="656" href="group-theory.perfect-groups.html#633" class="Bound">l1</a><a id="658" class="Symbol">)</a>
  <a id="662" class="Keyword">where</a>

  <a id="671" href="group-theory.perfect-groups.html#671" class="Function">is-perfect-prop-Group</a> <a id="693" class="Symbol">:</a> <a id="695" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="700" href="group-theory.perfect-groups.html#633" class="Bound">l1</a>
  <a id="705" href="group-theory.perfect-groups.html#671" class="Function">is-perfect-prop-Group</a> <a id="727" class="Symbol">=</a> <a id="729" href="group-theory.full-subgroups.html#957" class="Function">is-full-prop-Subgroup</a> <a id="751" href="group-theory.perfect-groups.html#646" class="Bound">G</a> <a id="753" class="Symbol">(</a><a id="754" href="group-theory.commutator-subgroups.html#1519" class="Function">commutator-subgroup-Group</a> <a id="780" href="group-theory.perfect-groups.html#646" class="Bound">G</a><a id="781" class="Symbol">)</a>

  <a id="786" href="group-theory.perfect-groups.html#786" class="Function">is-perfect-Group</a> <a id="803" class="Symbol">:</a> <a id="805" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="808" href="group-theory.perfect-groups.html#633" class="Bound">l1</a>
  <a id="813" href="group-theory.perfect-groups.html#786" class="Function">is-perfect-Group</a> <a id="830" class="Symbol">=</a> <a id="832" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="842" href="group-theory.perfect-groups.html#671" class="Function">is-perfect-prop-Group</a>

  <a id="867" href="group-theory.perfect-groups.html#867" class="Function">is-prop-is-perfect-Group</a> <a id="892" class="Symbol">:</a> <a id="894" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="902" href="group-theory.perfect-groups.html#786" class="Function">is-perfect-Group</a>
  <a id="921" href="group-theory.perfect-groups.html#867" class="Function">is-prop-is-perfect-Group</a> <a id="946" class="Symbol">=</a> <a id="948" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="966" href="group-theory.perfect-groups.html#671" class="Function">is-perfect-prop-Group</a>
</pre>
## External links

- [Perfect group](https://ncatlab.org/nlab/show/perfect+group) at $n$Lab
- [Perfect group](https://en.wikipedia.org/wiki/Perfect_group) at Wikipedia

A wikidata identifier was not available for this concept.
