# Stabilizer groups

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="group-theory.stabilizer-groups.html" class="Module">group-theory.stabilizer-groups</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="285" class="Keyword">open</a> <a id="290" class="Keyword">import</a> <a id="297" href="group-theory.groups.html" class="Module">group-theory.groups</a>
</pre>
</details>

## Idea

Given a [`G`-set](group-theory.group-actions.md) `X`, the **stabilizer group**
at an element `x` of `X` is the [subgroup](group-theory.subgroups.md) of
elements `g` of `G` that keep `x` fixed.

## Definition

<pre class="Agda"><a id="560" class="Keyword">module</a> <a id="567" href="group-theory.stabilizer-groups.html#567" class="Module">_</a>
  <a id="571" class="Symbol">{</a><a id="572" href="group-theory.stabilizer-groups.html#572" class="Bound">l1</a> <a id="575" href="group-theory.stabilizer-groups.html#575" class="Bound">l2</a> <a id="578" class="Symbol">:</a> <a id="580" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="585" class="Symbol">}</a> <a id="587" class="Symbol">(</a><a id="588" href="group-theory.stabilizer-groups.html#588" class="Bound">G</a> <a id="590" class="Symbol">:</a> <a id="592" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="598" href="group-theory.stabilizer-groups.html#572" class="Bound">l1</a><a id="600" class="Symbol">)</a> <a id="602" class="Symbol">(</a><a id="603" href="group-theory.stabilizer-groups.html#603" class="Bound">X</a> <a id="605" class="Symbol">:</a> <a id="607" href="group-theory.group-actions.html#1098" class="Function">action-Group</a> <a id="620" href="group-theory.stabilizer-groups.html#588" class="Bound">G</a> <a id="622" href="group-theory.stabilizer-groups.html#575" class="Bound">l2</a><a id="624" class="Symbol">)</a>
  <a id="628" class="Keyword">where</a>

  <a id="637" href="group-theory.stabilizer-groups.html#637" class="Function">type-stabilizer-action-Group</a> <a id="666" class="Symbol">:</a> <a id="668" href="group-theory.group-actions.html#1351" class="Function">type-action-Group</a> <a id="686" href="group-theory.stabilizer-groups.html#588" class="Bound">G</a> <a id="688" href="group-theory.stabilizer-groups.html#603" class="Bound">X</a> <a id="690" class="Symbol">→</a> <a id="692" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="695" class="Symbol">(</a><a id="696" href="group-theory.stabilizer-groups.html#572" class="Bound">l1</a> <a id="699" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="701" href="group-theory.stabilizer-groups.html#575" class="Bound">l2</a><a id="703" class="Symbol">)</a>
  <a id="707" href="group-theory.stabilizer-groups.html#637" class="Function">type-stabilizer-action-Group</a> <a id="736" href="group-theory.stabilizer-groups.html#736" class="Bound">x</a> <a id="738" class="Symbol">=</a>
    <a id="744" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="746" class="Symbol">(</a><a id="747" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="758" href="group-theory.stabilizer-groups.html#588" class="Bound">G</a><a id="759" class="Symbol">)</a> <a id="761" class="Symbol">(λ</a> <a id="764" href="group-theory.stabilizer-groups.html#764" class="Bound">g</a> <a id="766" class="Symbol">→</a> <a id="768" href="group-theory.group-actions.html#1716" class="Function">mul-action-Group</a> <a id="785" href="group-theory.stabilizer-groups.html#588" class="Bound">G</a> <a id="787" href="group-theory.stabilizer-groups.html#603" class="Bound">X</a> <a id="789" href="group-theory.stabilizer-groups.html#764" class="Bound">g</a> <a id="791" href="group-theory.stabilizer-groups.html#736" class="Bound">x</a> <a id="793" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="795" href="group-theory.stabilizer-groups.html#736" class="Bound">x</a><a id="796" class="Symbol">)</a>
</pre>
## External links

- [stabilizer group](https://ncatlab.org/nlab/show/stabilizer+group) at $n$Lab
- [Fixed points and stabilizer subgroups](https://en.wikipedia.org/wiki/Group_action#Fixed_points_and_stabilizer_subgroups)
  at Wikipedia
- [Isotropy Group](https://mathworld.wolfram.com/IsotropyGroup.html) at Wolfram
  MathWorld
- [Isotropy group](https://encyclopediaofmath.org/wiki/Isotropy_group) at
  Encyclopedia of Mathematics
