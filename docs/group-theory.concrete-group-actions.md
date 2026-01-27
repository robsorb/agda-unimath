# Concrete group actions

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
</pre>
</details>

## Idea

Given a [concrete group](group-theory.concrete-groups.md) `G`, a **concrete
action of** `G` on a type is defined to be a type family over `BG`. Given a type
family `X` over `BG`, the type being acted on is the type `X *`, and the action
of `G` on `X *` is given by transport.

## Definition

<pre class="Agda"><a id="662" class="Keyword">module</a> <a id="669" href="group-theory.concrete-group-actions.html#669" class="Module">_</a>
  <a id="673" class="Symbol">{</a><a id="674" href="group-theory.concrete-group-actions.html#674" class="Bound">l1</a> <a id="677" class="Symbol">:</a> <a id="679" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="684" class="Symbol">}</a> <a id="686" class="Symbol">(</a><a id="687" href="group-theory.concrete-group-actions.html#687" class="Bound">l2</a> <a id="690" class="Symbol">:</a> <a id="692" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="697" class="Symbol">)</a> <a id="699" class="Symbol">(</a><a id="700" href="group-theory.concrete-group-actions.html#700" class="Bound">G</a> <a id="702" class="Symbol">:</a> <a id="704" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="719" href="group-theory.concrete-group-actions.html#674" class="Bound">l1</a><a id="721" class="Symbol">)</a>
  <a id="725" class="Keyword">where</a>

  <a id="734" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="756" class="Symbol">:</a> <a id="758" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="761" class="Symbol">(</a><a id="762" href="group-theory.concrete-group-actions.html#674" class="Bound">l1</a> <a id="765" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="767" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="772" href="group-theory.concrete-group-actions.html#687" class="Bound">l2</a><a id="774" class="Symbol">)</a>
  <a id="778" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="800" class="Symbol">=</a> <a id="802" href="group-theory.concrete-groups.html#1503" class="Function">classifying-type-Concrete-Group</a> <a id="834" href="group-theory.concrete-group-actions.html#700" class="Bound">G</a> <a id="836" class="Symbol">→</a> <a id="838" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="842" href="group-theory.concrete-group-actions.html#687" class="Bound">l2</a>

<a id="846" class="Keyword">module</a> <a id="853" href="group-theory.concrete-group-actions.html#853" class="Module">_</a>
  <a id="857" class="Symbol">{</a><a id="858" href="group-theory.concrete-group-actions.html#858" class="Bound">l1</a> <a id="861" href="group-theory.concrete-group-actions.html#861" class="Bound">l2</a> <a id="864" class="Symbol">:</a> <a id="866" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="871" class="Symbol">}</a> <a id="873" class="Symbol">(</a><a id="874" href="group-theory.concrete-group-actions.html#874" class="Bound">G</a> <a id="876" class="Symbol">:</a> <a id="878" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="893" href="group-theory.concrete-group-actions.html#858" class="Bound">l1</a><a id="895" class="Symbol">)</a> <a id="897" class="Symbol">(</a><a id="898" href="group-theory.concrete-group-actions.html#898" class="Bound">X</a> <a id="900" class="Symbol">:</a> <a id="902" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="924" href="group-theory.concrete-group-actions.html#861" class="Bound">l2</a> <a id="927" href="group-theory.concrete-group-actions.html#874" class="Bound">G</a><a id="928" class="Symbol">)</a>
  <a id="932" class="Keyword">where</a>

  <a id="941" href="group-theory.concrete-group-actions.html#941" class="Function">set-action-Concrete-Group</a> <a id="967" class="Symbol">:</a> <a id="969" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="973" href="group-theory.concrete-group-actions.html#861" class="Bound">l2</a>
  <a id="978" href="group-theory.concrete-group-actions.html#941" class="Function">set-action-Concrete-Group</a> <a id="1004" class="Symbol">=</a> <a id="1006" href="group-theory.concrete-group-actions.html#898" class="Bound">X</a> <a id="1008" class="Symbol">(</a><a id="1009" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="1030" href="group-theory.concrete-group-actions.html#874" class="Bound">G</a><a id="1031" class="Symbol">)</a>

  <a id="1036" href="group-theory.concrete-group-actions.html#1036" class="Function">type-action-Concrete-Group</a> <a id="1063" class="Symbol">:</a> <a id="1065" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1068" href="group-theory.concrete-group-actions.html#861" class="Bound">l2</a>
  <a id="1073" href="group-theory.concrete-group-actions.html#1036" class="Function">type-action-Concrete-Group</a> <a id="1100" class="Symbol">=</a> <a id="1102" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1111" href="group-theory.concrete-group-actions.html#941" class="Function">set-action-Concrete-Group</a>

  <a id="1140" href="group-theory.concrete-group-actions.html#1140" class="Function">is-set-type-action-Concrete-Group</a> <a id="1174" class="Symbol">:</a> <a id="1176" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="1183" href="group-theory.concrete-group-actions.html#1036" class="Function">type-action-Concrete-Group</a>
  <a id="1212" href="group-theory.concrete-group-actions.html#1140" class="Function">is-set-type-action-Concrete-Group</a> <a id="1246" class="Symbol">=</a> <a id="1248" href="foundation-core.sets.html#1076" class="Function">is-set-type-Set</a> <a id="1264" href="group-theory.concrete-group-actions.html#941" class="Function">set-action-Concrete-Group</a>

  <a id="1293" href="group-theory.concrete-group-actions.html#1293" class="Function">mul-action-Concrete-Group</a> <a id="1319" class="Symbol">:</a>
    <a id="1325" href="group-theory.concrete-groups.html#2510" class="Function">type-Concrete-Group</a> <a id="1345" href="group-theory.concrete-group-actions.html#874" class="Bound">G</a> <a id="1347" class="Symbol">→</a>
    <a id="1353" href="group-theory.concrete-group-actions.html#1036" class="Function">type-action-Concrete-Group</a> <a id="1380" class="Symbol">→</a> <a id="1382" href="group-theory.concrete-group-actions.html#1036" class="Function">type-action-Concrete-Group</a>
  <a id="1411" href="group-theory.concrete-group-actions.html#1293" class="Function">mul-action-Concrete-Group</a> <a id="1437" href="group-theory.concrete-group-actions.html#1437" class="Bound">g</a> <a id="1439" href="group-theory.concrete-group-actions.html#1439" class="Bound">x</a> <a id="1441" class="Symbol">=</a> <a id="1443" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a> <a id="1446" class="Symbol">(</a><a id="1447" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="1456" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1458" href="group-theory.concrete-group-actions.html#898" class="Bound">X</a><a id="1459" class="Symbol">)</a> <a id="1461" href="group-theory.concrete-group-actions.html#1437" class="Bound">g</a> <a id="1463" href="group-theory.concrete-group-actions.html#1439" class="Bound">x</a>
</pre>