# Deloopable groups

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="higher-group-theory.deloopable-groups.html" class="Module">higher-group-theory.deloopable-groups</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="group-theory.groups.html" class="Module">group-theory.groups</a>

<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="higher-group-theory.deloopable-h-spaces.html" class="Module">higher-group-theory.deloopable-h-spaces</a>
</pre>
</details>

## Idea

A {{#concept "delooping" Disambiguation="group" Agda=delooping-Group}} of a
[group](group-theory.groups.md) `G` is a
[delooping](higher-group-theory.deloopable-h-spaces.md) of the underlying
[H-space](structured-types.h-spaces.md) of `G`. In other words, a delooping of a
group `G` consists of a [higher group](higher-group-theory.higher-groups.md)
`H`, which is defined to be a [pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md) type, equipped with an
[equivalence of H-spaces](structured-types.equivalences-h-spaces.md)
`G ≃ h-space-∞-Group H` from `G` to the underlying H-space of `H`.

## Definitions

### Deloopings of groups of a given universe level

<pre class="Agda"><a id="1031" class="Keyword">module</a> <a id="1038" href="higher-group-theory.deloopable-groups.html#1038" class="Module">_</a>
  <a id="1042" class="Symbol">{</a><a id="1043" href="higher-group-theory.deloopable-groups.html#1043" class="Bound">l1</a> <a id="1046" class="Symbol">:</a> <a id="1048" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1053" class="Symbol">}</a> <a id="1055" class="Symbol">(</a><a id="1056" href="higher-group-theory.deloopable-groups.html#1056" class="Bound">l2</a> <a id="1059" class="Symbol">:</a> <a id="1061" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1066" class="Symbol">)</a> <a id="1068" class="Symbol">(</a><a id="1069" href="higher-group-theory.deloopable-groups.html#1069" class="Bound">G</a> <a id="1071" class="Symbol">:</a> <a id="1073" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1079" href="higher-group-theory.deloopable-groups.html#1043" class="Bound">l1</a><a id="1081" class="Symbol">)</a>
  <a id="1085" class="Keyword">where</a>

  <a id="1094" href="higher-group-theory.deloopable-groups.html#1094" class="Function">delooping-Group-Level</a> <a id="1116" class="Symbol">:</a> <a id="1118" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1121" class="Symbol">(</a><a id="1122" href="higher-group-theory.deloopable-groups.html#1043" class="Bound">l1</a> <a id="1125" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1127" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1132" href="higher-group-theory.deloopable-groups.html#1056" class="Bound">l2</a><a id="1134" class="Symbol">)</a>
  <a id="1138" href="higher-group-theory.deloopable-groups.html#1094" class="Function">delooping-Group-Level</a> <a id="1160" class="Symbol">=</a> <a id="1162" href="higher-group-theory.deloopable-h-spaces.html#1114" class="Function">delooping-H-Space-Level</a> <a id="1186" href="higher-group-theory.deloopable-groups.html#1056" class="Bound">l2</a> <a id="1189" class="Symbol">(</a><a id="1190" href="group-theory.groups.html#4972" class="Function">h-space-Group</a> <a id="1204" href="higher-group-theory.deloopable-groups.html#1069" class="Bound">G</a><a id="1205" class="Symbol">)</a>
</pre>
### Deloopings of groups

<pre class="Agda"><a id="1246" class="Keyword">module</a> <a id="1253" href="higher-group-theory.deloopable-groups.html#1253" class="Module">_</a>
  <a id="1257" class="Symbol">{</a><a id="1258" href="higher-group-theory.deloopable-groups.html#1258" class="Bound">l1</a> <a id="1261" class="Symbol">:</a> <a id="1263" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1268" class="Symbol">}</a> <a id="1270" class="Symbol">(</a><a id="1271" href="higher-group-theory.deloopable-groups.html#1271" class="Bound">G</a> <a id="1273" class="Symbol">:</a> <a id="1275" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1281" href="higher-group-theory.deloopable-groups.html#1258" class="Bound">l1</a><a id="1283" class="Symbol">)</a>
  <a id="1287" class="Keyword">where</a>

  <a id="1296" href="higher-group-theory.deloopable-groups.html#1296" class="Function">delooping-Group</a> <a id="1312" class="Symbol">:</a> <a id="1314" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1317" class="Symbol">(</a><a id="1318" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1323" href="higher-group-theory.deloopable-groups.html#1258" class="Bound">l1</a><a id="1325" class="Symbol">)</a>
  <a id="1329" href="higher-group-theory.deloopable-groups.html#1296" class="Function">delooping-Group</a> <a id="1345" class="Symbol">=</a> <a id="1347" href="higher-group-theory.deloopable-groups.html#1094" class="Function">delooping-Group-Level</a> <a id="1369" href="higher-group-theory.deloopable-groups.html#1258" class="Bound">l1</a> <a id="1372" href="higher-group-theory.deloopable-groups.html#1271" class="Bound">G</a>
</pre>
## See also

- [Eilenberg-Mac Lane spaces](higher-group-theory.eilenberg-mac-lane-spaces.md)
