# Trivial subgroups

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="group-theory.trivial-subgroups.html" class="Module">group-theory.trivial-subgroups</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="278" class="Keyword">open</a> <a id="283" class="Keyword">import</a> <a id="290" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
</pre>
</details>

## Idea

A [subgroup](group-theory.subgroups.md) `H` of `G` is said to be **trivial** if
it only contains the unit element of `G`.

## Definitions

### The trivial subgroup

<pre class="Agda"><a id="512" class="Keyword">module</a> <a id="519" href="group-theory.trivial-subgroups.html#519" class="Module">_</a>
  <a id="523" class="Symbol">{</a><a id="524" href="group-theory.trivial-subgroups.html#524" class="Bound">l1</a> <a id="527" class="Symbol">:</a> <a id="529" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="534" class="Symbol">}</a> <a id="536" class="Symbol">(</a><a id="537" href="group-theory.trivial-subgroups.html#537" class="Bound">G</a> <a id="539" class="Symbol">:</a> <a id="541" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="547" href="group-theory.trivial-subgroups.html#524" class="Bound">l1</a><a id="549" class="Symbol">)</a>
  <a id="553" class="Keyword">where</a>

  <a id="562" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a> <a id="579" class="Symbol">:</a> <a id="581" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="590" href="group-theory.trivial-subgroups.html#524" class="Bound">l1</a> <a id="593" href="group-theory.trivial-subgroups.html#537" class="Bound">G</a>
  <a id="597" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="601" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a> <a id="618" href="group-theory.trivial-subgroups.html#618" class="Bound">x</a> <a id="620" class="Symbol">=</a> <a id="622" href="group-theory.groups.html#4247" class="Function">is-unit-prop-Group&#39;</a> <a id="642" href="group-theory.trivial-subgroups.html#537" class="Bound">G</a> <a id="644" href="group-theory.trivial-subgroups.html#618" class="Bound">x</a>
  <a id="648" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="652" class="Symbol">(</a><a id="653" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="657" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a><a id="673" class="Symbol">)</a> <a id="675" class="Symbol">=</a> <a id="677" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
  <a id="684" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="688" class="Symbol">(</a><a id="689" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="693" class="Symbol">(</a><a id="694" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="698" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a><a id="714" class="Symbol">))</a> <a id="717" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="722" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="727" class="Symbol">=</a>
    <a id="733" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="737" class="Symbol">(</a><a id="738" href="group-theory.groups.html#4398" class="Function">left-unit-law-mul-Group</a> <a id="762" href="group-theory.trivial-subgroups.html#537" class="Bound">G</a> <a id="764" class="Symbol">(</a><a id="765" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="776" href="group-theory.trivial-subgroups.html#537" class="Bound">G</a><a id="777" class="Symbol">))</a>
  <a id="782" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="786" class="Symbol">(</a><a id="787" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="791" class="Symbol">(</a><a id="792" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="796" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a><a id="812" class="Symbol">))</a> <a id="815" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="820" class="Symbol">=</a>
    <a id="826" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="830" class="Symbol">(</a><a id="831" href="group-theory.groups.html#6099" class="Function">inv-unit-Group</a> <a id="846" href="group-theory.trivial-subgroups.html#537" class="Bound">G</a><a id="847" class="Symbol">)</a>
</pre>
### The predicate of being a trivial subgroup

<pre class="Agda"><a id="909" class="Keyword">module</a> <a id="916" href="group-theory.trivial-subgroups.html#916" class="Module">_</a>
  <a id="920" class="Symbol">{</a><a id="921" href="group-theory.trivial-subgroups.html#921" class="Bound">l1</a> <a id="924" href="group-theory.trivial-subgroups.html#924" class="Bound">l2</a> <a id="927" class="Symbol">:</a> <a id="929" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="934" class="Symbol">}</a> <a id="936" class="Symbol">(</a><a id="937" href="group-theory.trivial-subgroups.html#937" class="Bound">G</a> <a id="939" class="Symbol">:</a> <a id="941" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="947" href="group-theory.trivial-subgroups.html#921" class="Bound">l1</a><a id="949" class="Symbol">)</a> <a id="951" class="Symbol">(</a><a id="952" href="group-theory.trivial-subgroups.html#952" class="Bound">H</a> <a id="954" class="Symbol">:</a> <a id="956" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="965" href="group-theory.trivial-subgroups.html#924" class="Bound">l2</a> <a id="968" href="group-theory.trivial-subgroups.html#937" class="Bound">G</a><a id="969" class="Symbol">)</a>
  <a id="973" class="Keyword">where</a>

  <a id="982" href="group-theory.trivial-subgroups.html#982" class="Function">is-trivial-Subgroup</a> <a id="1002" class="Symbol">:</a> <a id="1004" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1007" class="Symbol">(</a><a id="1008" href="group-theory.trivial-subgroups.html#921" class="Bound">l1</a> <a id="1011" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1013" href="group-theory.trivial-subgroups.html#924" class="Bound">l2</a><a id="1015" class="Symbol">)</a>
  <a id="1019" href="group-theory.trivial-subgroups.html#982" class="Function">is-trivial-Subgroup</a> <a id="1039" class="Symbol">=</a> <a id="1041" href="group-theory.subgroups.html#13941" class="Function">leq-Subgroup</a> <a id="1054" href="group-theory.trivial-subgroups.html#937" class="Bound">G</a> <a id="1056" href="group-theory.trivial-subgroups.html#952" class="Bound">H</a> <a id="1058" class="Symbol">(</a><a id="1059" href="group-theory.trivial-subgroups.html#562" class="Function">trivial-Subgroup</a> <a id="1076" href="group-theory.trivial-subgroups.html#937" class="Bound">G</a><a id="1077" class="Symbol">)</a>
</pre>