# Normal subgroups of concrete groups

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="group-theory.normal-subgroups-concrete-groups.html" class="Module">group-theory.normal-subgroups-concrete-groups</a> <a id="101" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="group-theory.subgroups-concrete-groups.html" class="Module">group-theory.subgroups-concrete-groups</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="group-theory.transitive-concrete-group-actions.html" class="Module">group-theory.transitive-concrete-group-actions</a>
</pre>
</details>

## Idea

A normal subgroup is a fixed point of the conjugation action on the (large) set
of all subgroups

## Definition

<pre class="Agda"><a id="normal-subgroup-Concrete-Group"></a><a id="543" href="group-theory.normal-subgroups-concrete-groups.html#543" class="Function">normal-subgroup-Concrete-Group</a> <a id="574" class="Symbol">:</a>
  <a id="578" class="Symbol">{</a><a id="579" href="group-theory.normal-subgroups-concrete-groups.html#579" class="Bound">l1</a> <a id="582" class="Symbol">:</a> <a id="584" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="589" class="Symbol">}</a> <a id="591" class="Symbol">(</a><a id="592" href="group-theory.normal-subgroups-concrete-groups.html#592" class="Bound">l2</a> <a id="595" class="Symbol">:</a> <a id="597" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="602" class="Symbol">)</a> <a id="604" class="Symbol">(</a><a id="605" href="group-theory.normal-subgroups-concrete-groups.html#605" class="Bound">G</a> <a id="607" class="Symbol">:</a> <a id="609" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="624" href="group-theory.normal-subgroups-concrete-groups.html#579" class="Bound">l1</a><a id="626" class="Symbol">)</a> <a id="628" class="Symbol">→</a> <a id="630" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="633" class="Symbol">(</a><a id="634" href="group-theory.normal-subgroups-concrete-groups.html#579" class="Bound">l1</a> <a id="637" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="639" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="644" href="group-theory.normal-subgroups-concrete-groups.html#592" class="Bound">l2</a><a id="646" class="Symbol">)</a>
<a id="648" href="group-theory.normal-subgroups-concrete-groups.html#543" class="Function">normal-subgroup-Concrete-Group</a> <a id="679" href="group-theory.normal-subgroups-concrete-groups.html#679" class="Bound">l2</a> <a id="682" href="group-theory.normal-subgroups-concrete-groups.html#682" class="Bound">G</a> <a id="684" class="Symbol">=</a>
  <a id="688" class="Symbol">(</a><a id="689" href="group-theory.normal-subgroups-concrete-groups.html#689" class="Bound">u</a> <a id="691" class="Symbol">:</a> <a id="693" href="group-theory.concrete-groups.html#1503" class="Function">classifying-type-Concrete-Group</a> <a id="725" href="group-theory.normal-subgroups-concrete-groups.html#682" class="Bound">G</a><a id="726" class="Symbol">)</a> <a id="728" class="Symbol">→</a>
  <a id="732" href="group-theory.subgroups-concrete-groups.html#1245" class="Function">subgroup-action-Concrete-Group</a> <a id="763" href="group-theory.normal-subgroups-concrete-groups.html#679" class="Bound">l2</a> <a id="766" href="group-theory.normal-subgroups-concrete-groups.html#682" class="Bound">G</a> <a id="768" href="group-theory.normal-subgroups-concrete-groups.html#689" class="Bound">u</a>

<a id="771" class="Keyword">module</a> <a id="778" href="group-theory.normal-subgroups-concrete-groups.html#778" class="Module">_</a>
  <a id="782" class="Symbol">{</a><a id="783" href="group-theory.normal-subgroups-concrete-groups.html#783" class="Bound">l1</a> <a id="786" href="group-theory.normal-subgroups-concrete-groups.html#786" class="Bound">l2</a> <a id="789" class="Symbol">:</a> <a id="791" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="796" class="Symbol">}</a> <a id="798" class="Symbol">(</a><a id="799" href="group-theory.normal-subgroups-concrete-groups.html#799" class="Bound">G</a> <a id="801" class="Symbol">:</a> <a id="803" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="818" href="group-theory.normal-subgroups-concrete-groups.html#783" class="Bound">l1</a><a id="820" class="Symbol">)</a>
  <a id="824" class="Symbol">(</a><a id="825" href="group-theory.normal-subgroups-concrete-groups.html#825" class="Bound">H</a> <a id="827" class="Symbol">:</a> <a id="829" href="group-theory.normal-subgroups-concrete-groups.html#543" class="Function">normal-subgroup-Concrete-Group</a> <a id="860" href="group-theory.normal-subgroups-concrete-groups.html#786" class="Bound">l2</a> <a id="863" href="group-theory.normal-subgroups-concrete-groups.html#799" class="Bound">G</a><a id="864" class="Symbol">)</a>
  <a id="868" class="Keyword">where</a>

  <a id="877" href="group-theory.normal-subgroups-concrete-groups.html#877" class="Function">subgroup-normal-subgroup-Concrete-Group</a> <a id="917" class="Symbol">:</a> <a id="919" href="group-theory.subgroups-concrete-groups.html#1544" class="Function">subgroup-Concrete-Group</a> <a id="943" href="group-theory.normal-subgroups-concrete-groups.html#786" class="Bound">l2</a> <a id="946" href="group-theory.normal-subgroups-concrete-groups.html#799" class="Bound">G</a>
  <a id="950" href="group-theory.normal-subgroups-concrete-groups.html#877" class="Function">subgroup-normal-subgroup-Concrete-Group</a> <a id="990" class="Symbol">=</a> <a id="992" href="group-theory.normal-subgroups-concrete-groups.html#825" class="Bound">H</a> <a id="994" class="Symbol">(</a><a id="995" href="group-theory.concrete-groups.html#1633" class="Function">shape-Concrete-Group</a> <a id="1016" href="group-theory.normal-subgroups-concrete-groups.html#799" class="Bound">G</a><a id="1017" class="Symbol">)</a>

  <a id="1022" href="group-theory.normal-subgroups-concrete-groups.html#1022" class="Function">action-normal-subgroup-Concrete-Group</a> <a id="1060" class="Symbol">:</a> <a id="1062" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="1084" href="group-theory.normal-subgroups-concrete-groups.html#786" class="Bound">l2</a> <a id="1087" href="group-theory.normal-subgroups-concrete-groups.html#799" class="Bound">G</a>
  <a id="1091" href="group-theory.normal-subgroups-concrete-groups.html#1022" class="Function">action-normal-subgroup-Concrete-Group</a> <a id="1129" class="Symbol">=</a>
    <a id="1135" href="group-theory.subgroups-concrete-groups.html#1975" class="Function">action-subgroup-Concrete-Group</a> <a id="1166" href="group-theory.normal-subgroups-concrete-groups.html#799" class="Bound">G</a> <a id="1168" href="group-theory.normal-subgroups-concrete-groups.html#877" class="Function">subgroup-normal-subgroup-Concrete-Group</a>

  <a id="1211" href="group-theory.normal-subgroups-concrete-groups.html#1211" class="Function">transitive-action-normal-subgroup-Concrete-Group</a> <a id="1260" class="Symbol">:</a>
    <a id="1266" href="group-theory.transitive-concrete-group-actions.html#3853" class="Function">transitive-action-Concrete-Group</a> <a id="1299" href="group-theory.normal-subgroups-concrete-groups.html#786" class="Bound">l2</a> <a id="1302" href="group-theory.normal-subgroups-concrete-groups.html#799" class="Bound">G</a>
  <a id="1306" href="group-theory.normal-subgroups-concrete-groups.html#1211" class="Function">transitive-action-normal-subgroup-Concrete-Group</a> <a id="1355" class="Symbol">=</a>
    <a id="1361" href="group-theory.subgroups-concrete-groups.html#1834" class="Function">transitive-action-subgroup-Concrete-Group</a> <a id="1403" href="group-theory.normal-subgroups-concrete-groups.html#799" class="Bound">G</a>
      <a id="1411" class="Symbol">(</a> <a id="1413" href="group-theory.normal-subgroups-concrete-groups.html#877" class="Function">subgroup-normal-subgroup-Concrete-Group</a><a id="1452" class="Symbol">)</a>
</pre>