# Subsets of groups

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="group-theory.subsets-groups.html" class="Module">group-theory.subsets-groups</a> <a id="65" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="121" class="Keyword">open</a> <a id="126" class="Keyword">import</a> <a id="133" href="foundation.large-locale-of-subtypes.html" class="Module">foundation.large-locale-of-subtypes</a>
<a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="group-theory.groups.html" class="Module">group-theory.groups</a>

<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="order-theory.large-locales.html" class="Module">order-theory.large-locales</a>
<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>
</pre>
</details>

## Idea

A **subset** of a [group](group-theory.groups.md) `G` is a
[subtype](foundation.subtypes.md) of the underlying type of `G`. The
[large poset](order-theory.large-posets.md) of all subsets of `G` is called the
**powerset** of `G`.

## Definitions

### The large locale of subsets of a group

<pre class="Agda"><a id="671" class="Keyword">module</a> <a id="678" href="group-theory.subsets-groups.html#678" class="Module">_</a>
  <a id="682" class="Symbol">{</a><a id="683" href="group-theory.subsets-groups.html#683" class="Bound">l1</a> <a id="686" class="Symbol">:</a> <a id="688" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="693" class="Symbol">}</a> <a id="695" class="Symbol">(</a><a id="696" href="group-theory.subsets-groups.html#696" class="Bound">G</a> <a id="698" class="Symbol">:</a> <a id="700" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="706" href="group-theory.subsets-groups.html#683" class="Bound">l1</a><a id="708" class="Symbol">)</a>
  <a id="712" class="Keyword">where</a>

  <a id="721" href="group-theory.subsets-groups.html#721" class="Function">powerset-large-locale-Group</a> <a id="749" class="Symbol">:</a>
    <a id="755" href="order-theory.large-locales.html#1051" class="Function">Large-Locale</a> <a id="768" class="Symbol">(λ</a> <a id="771" href="group-theory.subsets-groups.html#771" class="Bound">l2</a> <a id="774" class="Symbol">→</a> <a id="776" href="group-theory.subsets-groups.html#683" class="Bound">l1</a> <a id="779" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="781" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="786" href="group-theory.subsets-groups.html#771" class="Bound">l2</a><a id="788" class="Symbol">)</a> <a id="790" class="Symbol">(λ</a> <a id="793" href="group-theory.subsets-groups.html#793" class="Bound">l2</a> <a id="796" href="group-theory.subsets-groups.html#796" class="Bound">l3</a> <a id="799" class="Symbol">→</a> <a id="801" href="group-theory.subsets-groups.html#683" class="Bound">l1</a> <a id="804" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="806" href="group-theory.subsets-groups.html#793" class="Bound">l2</a> <a id="809" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="811" href="group-theory.subsets-groups.html#796" class="Bound">l3</a><a id="813" class="Symbol">)</a> <a id="815" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="823" href="group-theory.subsets-groups.html#721" class="Function">powerset-large-locale-Group</a> <a id="851" class="Symbol">=</a> <a id="853" href="foundation.large-locale-of-subtypes.html#1106" class="Function">powerset-Large-Locale</a> <a id="875" class="Symbol">(</a><a id="876" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="887" href="group-theory.subsets-groups.html#696" class="Bound">G</a><a id="888" class="Symbol">)</a>
</pre>
### The large poset of subsets of a group

<pre class="Agda"><a id="946" class="Keyword">module</a> <a id="953" href="group-theory.subsets-groups.html#953" class="Module">_</a>
  <a id="957" class="Symbol">{</a><a id="958" href="group-theory.subsets-groups.html#958" class="Bound">l1</a> <a id="961" class="Symbol">:</a> <a id="963" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="968" class="Symbol">}</a> <a id="970" class="Symbol">(</a><a id="971" href="group-theory.subsets-groups.html#971" class="Bound">G</a> <a id="973" class="Symbol">:</a> <a id="975" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="981" href="group-theory.subsets-groups.html#958" class="Bound">l1</a><a id="983" class="Symbol">)</a>
  <a id="987" class="Keyword">where</a>

  <a id="996" href="group-theory.subsets-groups.html#996" class="Function">powerset-large-poset-Group</a> <a id="1023" class="Symbol">:</a>
    <a id="1029" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1041" class="Symbol">(λ</a> <a id="1044" href="group-theory.subsets-groups.html#1044" class="Bound">l2</a> <a id="1047" class="Symbol">→</a> <a id="1049" href="group-theory.subsets-groups.html#958" class="Bound">l1</a> <a id="1052" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1054" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1059" href="group-theory.subsets-groups.html#1044" class="Bound">l2</a><a id="1061" class="Symbol">)</a> <a id="1063" class="Symbol">(λ</a> <a id="1066" href="group-theory.subsets-groups.html#1066" class="Bound">l2</a> <a id="1069" href="group-theory.subsets-groups.html#1069" class="Bound">l3</a> <a id="1072" class="Symbol">→</a> <a id="1074" href="group-theory.subsets-groups.html#958" class="Bound">l1</a> <a id="1077" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1079" href="group-theory.subsets-groups.html#1066" class="Bound">l2</a> <a id="1082" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1084" href="group-theory.subsets-groups.html#1069" class="Bound">l3</a><a id="1086" class="Symbol">)</a>
  <a id="1090" href="group-theory.subsets-groups.html#996" class="Function">powerset-large-poset-Group</a> <a id="1117" class="Symbol">=</a>
    <a id="1123" href="order-theory.large-locales.html#1271" class="Function">large-poset-Large-Locale</a> <a id="1148" class="Symbol">(</a><a id="1149" href="group-theory.subsets-groups.html#721" class="Function">powerset-large-locale-Group</a> <a id="1177" href="group-theory.subsets-groups.html#971" class="Bound">G</a><a id="1178" class="Symbol">)</a>
</pre>
### Subsets of groups

<pre class="Agda"><a id="subset-Group"></a><a id="1216" href="group-theory.subsets-groups.html#1216" class="Function">subset-Group</a> <a id="1229" class="Symbol">:</a>
  <a id="1233" class="Symbol">(</a><a id="1234" href="group-theory.subsets-groups.html#1234" class="Bound">l</a> <a id="1236" class="Symbol">:</a> <a id="1238" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1243" class="Symbol">)</a> <a id="1245" class="Symbol">{</a><a id="1246" href="group-theory.subsets-groups.html#1246" class="Bound">l1</a> <a id="1249" class="Symbol">:</a> <a id="1251" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1256" class="Symbol">}</a> <a id="1258" class="Symbol">(</a><a id="1259" href="group-theory.subsets-groups.html#1259" class="Bound">G</a> <a id="1261" class="Symbol">:</a> <a id="1263" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1269" href="group-theory.subsets-groups.html#1246" class="Bound">l1</a><a id="1271" class="Symbol">)</a> <a id="1273" class="Symbol">→</a> <a id="1275" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1278" class="Symbol">(</a><a id="1279" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1284" href="group-theory.subsets-groups.html#1234" class="Bound">l</a> <a id="1286" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1288" href="group-theory.subsets-groups.html#1246" class="Bound">l1</a><a id="1290" class="Symbol">)</a>
<a id="1292" href="group-theory.subsets-groups.html#1216" class="Function">subset-Group</a> <a id="1305" href="group-theory.subsets-groups.html#1305" class="Bound">l</a> <a id="1307" href="group-theory.subsets-groups.html#1307" class="Bound">G</a> <a id="1309" class="Symbol">=</a> <a id="1311" href="order-theory.large-locales.html#1597" class="Function">type-Large-Locale</a> <a id="1329" class="Symbol">(</a><a id="1330" href="group-theory.subsets-groups.html#721" class="Function">powerset-large-locale-Group</a> <a id="1358" href="group-theory.subsets-groups.html#1307" class="Bound">G</a><a id="1359" class="Symbol">)</a> <a id="1361" href="group-theory.subsets-groups.html#1305" class="Bound">l</a>

<a id="is-set-subset-Group"></a><a id="1364" href="group-theory.subsets-groups.html#1364" class="Function">is-set-subset-Group</a> <a id="1384" class="Symbol">:</a>
  <a id="1388" class="Symbol">{</a><a id="1389" href="group-theory.subsets-groups.html#1389" class="Bound">l1</a> <a id="1392" href="group-theory.subsets-groups.html#1392" class="Bound">l2</a> <a id="1395" class="Symbol">:</a> <a id="1397" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1402" class="Symbol">}</a> <a id="1404" class="Symbol">(</a><a id="1405" href="group-theory.subsets-groups.html#1405" class="Bound">G</a> <a id="1407" class="Symbol">:</a> <a id="1409" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1415" href="group-theory.subsets-groups.html#1389" class="Bound">l1</a><a id="1417" class="Symbol">)</a> <a id="1419" class="Symbol">→</a> <a id="1421" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="1428" class="Symbol">(</a><a id="1429" href="group-theory.subsets-groups.html#1216" class="Function">subset-Group</a> <a id="1442" href="group-theory.subsets-groups.html#1392" class="Bound">l2</a> <a id="1445" href="group-theory.subsets-groups.html#1405" class="Bound">G</a><a id="1446" class="Symbol">)</a>
<a id="1448" href="group-theory.subsets-groups.html#1364" class="Function">is-set-subset-Group</a> <a id="1468" href="group-theory.subsets-groups.html#1468" class="Bound">G</a> <a id="1470" class="Symbol">=</a>
  <a id="1474" href="order-theory.large-locales.html#1684" class="Function">is-set-type-Large-Locale</a> <a id="1499" class="Symbol">(</a><a id="1500" href="group-theory.subsets-groups.html#721" class="Function">powerset-large-locale-Group</a> <a id="1528" href="group-theory.subsets-groups.html#1468" class="Bound">G</a><a id="1529" class="Symbol">)</a>
</pre>