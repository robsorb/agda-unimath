# Transitive group actions

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="group-theory.transitive-group-actions.html" class="Module">group-theory.transitive-group-actions</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="341" class="Keyword">open</a> <a id="346" class="Keyword">import</a> <a id="353" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="group-theory.groups.html" class="Module">group-theory.groups</a>
</pre>
</details>

## Idea

A [group](group-theory.groups.md) `G` is said to **act transitively** on a
[set](foundation-core.sets.md) `X` if for every `x : X` the map

```text
  g ↦ gx : G → X
```

is [surjective](foundation.surjective-maps.md). In other words, a
[group action](group-theory.group-actions.md) is transitive if any two elements
are in the same [orbit](group-theory.orbits-group-actions.md).

## Definitions

### The predicate of being a transitive `G`-set

<pre class="Agda"><a id="891" class="Keyword">module</a> <a id="898" href="group-theory.transitive-group-actions.html#898" class="Module">_</a>
  <a id="902" class="Symbol">{</a><a id="903" href="group-theory.transitive-group-actions.html#903" class="Bound">l1</a> <a id="906" href="group-theory.transitive-group-actions.html#906" class="Bound">l2</a> <a id="909" class="Symbol">:</a> <a id="911" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="916" class="Symbol">}</a> <a id="918" class="Symbol">(</a><a id="919" href="group-theory.transitive-group-actions.html#919" class="Bound">G</a> <a id="921" class="Symbol">:</a> <a id="923" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="929" href="group-theory.transitive-group-actions.html#903" class="Bound">l1</a><a id="931" class="Symbol">)</a> <a id="933" class="Symbol">(</a><a id="934" href="group-theory.transitive-group-actions.html#934" class="Bound">X</a> <a id="936" class="Symbol">:</a> <a id="938" href="group-theory.group-actions.html#1098" class="Function">action-Group</a> <a id="951" href="group-theory.transitive-group-actions.html#919" class="Bound">G</a> <a id="953" href="group-theory.transitive-group-actions.html#906" class="Bound">l2</a><a id="955" class="Symbol">)</a>
  <a id="959" class="Keyword">where</a>

  <a id="968" href="group-theory.transitive-group-actions.html#968" class="Function">is-transitive-prop-action-Group</a> <a id="1000" class="Symbol">:</a> <a id="1002" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1007" class="Symbol">(</a><a id="1008" href="group-theory.transitive-group-actions.html#903" class="Bound">l1</a> <a id="1011" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1013" href="group-theory.transitive-group-actions.html#906" class="Bound">l2</a><a id="1015" class="Symbol">)</a>
  <a id="1019" href="group-theory.transitive-group-actions.html#968" class="Function">is-transitive-prop-action-Group</a> <a id="1051" class="Symbol">=</a>
    <a id="1057" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1070" class="Symbol">(</a> <a id="1072" href="group-theory.group-actions.html#1351" class="Function">type-action-Group</a> <a id="1090" href="group-theory.transitive-group-actions.html#919" class="Bound">G</a> <a id="1092" href="group-theory.transitive-group-actions.html#934" class="Bound">X</a><a id="1093" class="Symbol">)</a>
      <a id="1101" class="Symbol">(</a> <a id="1103" class="Symbol">λ</a> <a id="1105" href="group-theory.transitive-group-actions.html#1105" class="Bound">x</a> <a id="1107" class="Symbol">→</a> <a id="1109" href="foundation.surjective-maps.html#2370" class="Function">is-surjective-Prop</a> <a id="1128" class="Symbol">(λ</a> <a id="1131" href="group-theory.transitive-group-actions.html#1131" class="Bound">g</a> <a id="1133" class="Symbol">→</a> <a id="1135" href="group-theory.group-actions.html#1716" class="Function">mul-action-Group</a> <a id="1152" href="group-theory.transitive-group-actions.html#919" class="Bound">G</a> <a id="1154" href="group-theory.transitive-group-actions.html#934" class="Bound">X</a> <a id="1156" href="group-theory.transitive-group-actions.html#1131" class="Bound">g</a> <a id="1158" href="group-theory.transitive-group-actions.html#1105" class="Bound">x</a><a id="1159" class="Symbol">))</a>

  <a id="1165" href="group-theory.transitive-group-actions.html#1165" class="Function">is-transitive-action-Group</a> <a id="1192" class="Symbol">:</a> <a id="1194" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1197" class="Symbol">(</a><a id="1198" href="group-theory.transitive-group-actions.html#903" class="Bound">l1</a> <a id="1201" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1203" href="group-theory.transitive-group-actions.html#906" class="Bound">l2</a><a id="1205" class="Symbol">)</a>
  <a id="1209" href="group-theory.transitive-group-actions.html#1165" class="Function">is-transitive-action-Group</a> <a id="1236" class="Symbol">=</a> <a id="1238" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1248" href="group-theory.transitive-group-actions.html#968" class="Function">is-transitive-prop-action-Group</a>

  <a id="1283" href="group-theory.transitive-group-actions.html#1283" class="Function">is-prop-is-transitive-action-Group</a> <a id="1318" class="Symbol">:</a> <a id="1320" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1328" href="group-theory.transitive-group-actions.html#1165" class="Function">is-transitive-action-Group</a>
  <a id="1357" href="group-theory.transitive-group-actions.html#1283" class="Function">is-prop-is-transitive-action-Group</a> <a id="1392" class="Symbol">=</a>
    <a id="1398" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1416" href="group-theory.transitive-group-actions.html#968" class="Function">is-transitive-prop-action-Group</a>
</pre>
## External links

- [transitive action](https://ncatlab.org/nlab/show/transitive+action) at $n$Lab
- [Transitivity properties of group actions](https://en.wikipedia.org/wiki/Group_action#Transitivity_properties)
  at Wikipedia
- [Transitive Group Action](https://mathworld.wolfram.com/TransitiveGroupAction.html)
  at Wolfram MathWorld
- [Transitive group action](https://groupprops.subwiki.org/wiki/Transitive_group_action)
  at Groupprops
