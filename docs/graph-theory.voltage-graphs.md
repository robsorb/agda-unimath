# Voltage graphs

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="graph-theory.voltage-graphs.html" class="Module">graph-theory.voltage-graphs</a> <a id="62" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="118" class="Keyword">open</a> <a id="123" class="Keyword">import</a> <a id="130" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>

<a id="244" class="Keyword">open</a> <a id="249" class="Keyword">import</a> <a id="256" href="group-theory.groups.html" class="Module">group-theory.groups</a>
</pre>
</details>

## Idea

A **voltage graph** is a [directed graph](graph-theory.directed-graphs.md) `G`
equipped with a [group](group-theory.groups.md) `Π`, which we call the **voltage
group**, and a labeling of the edges of `G` by elements of `Π`.

## Definition

<pre class="Agda"><a id="Voltage-Graph"></a><a id="550" href="graph-theory.voltage-graphs.html#550" class="Function">Voltage-Graph</a> <a id="564" class="Symbol">:</a>
  <a id="568" class="Symbol">{</a><a id="569" href="graph-theory.voltage-graphs.html#569" class="Bound">l1</a> <a id="572" class="Symbol">:</a> <a id="574" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="579" class="Symbol">}</a> <a id="581" class="Symbol">(</a><a id="582" href="graph-theory.voltage-graphs.html#582" class="Bound">l2</a> <a id="585" href="graph-theory.voltage-graphs.html#585" class="Bound">l3</a> <a id="588" class="Symbol">:</a> <a id="590" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="595" class="Symbol">)</a> <a id="597" class="Symbol">(</a><a id="598" href="graph-theory.voltage-graphs.html#598" class="Bound">Π</a> <a id="600" class="Symbol">:</a> <a id="602" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="608" href="graph-theory.voltage-graphs.html#569" class="Bound">l1</a><a id="610" class="Symbol">)</a> <a id="612" class="Symbol">→</a> <a id="614" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="617" class="Symbol">(</a><a id="618" href="graph-theory.voltage-graphs.html#569" class="Bound">l1</a> <a id="621" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="623" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="628" href="graph-theory.voltage-graphs.html#582" class="Bound">l2</a> <a id="631" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="633" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="638" href="graph-theory.voltage-graphs.html#585" class="Bound">l3</a><a id="640" class="Symbol">)</a>
<a id="642" href="graph-theory.voltage-graphs.html#550" class="Function">Voltage-Graph</a> <a id="656" href="graph-theory.voltage-graphs.html#656" class="Bound">l2</a> <a id="659" href="graph-theory.voltage-graphs.html#659" class="Bound">l3</a> <a id="662" href="graph-theory.voltage-graphs.html#662" class="Bound">Π</a> <a id="664" class="Symbol">=</a>
  <a id="668" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="670" class="Symbol">(</a> <a id="672" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="687" href="graph-theory.voltage-graphs.html#656" class="Bound">l2</a> <a id="690" href="graph-theory.voltage-graphs.html#659" class="Bound">l3</a><a id="692" class="Symbol">)</a>
    <a id="698" class="Symbol">(</a> <a id="700" class="Symbol">λ</a> <a id="702" href="graph-theory.voltage-graphs.html#702" class="Bound">G</a> <a id="704" class="Symbol">→</a>
      <a id="712" class="Symbol">{</a><a id="713" href="graph-theory.voltage-graphs.html#713" class="Bound">x</a> <a id="715" href="graph-theory.voltage-graphs.html#715" class="Bound">y</a> <a id="717" class="Symbol">:</a> <a id="719" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="741" href="graph-theory.voltage-graphs.html#702" class="Bound">G</a><a id="742" class="Symbol">}</a> <a id="744" class="Symbol">→</a>
      <a id="752" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="772" href="graph-theory.voltage-graphs.html#702" class="Bound">G</a> <a id="774" href="graph-theory.voltage-graphs.html#713" class="Bound">x</a> <a id="776" href="graph-theory.voltage-graphs.html#715" class="Bound">y</a> <a id="778" class="Symbol">→</a> <a id="780" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="791" href="graph-theory.voltage-graphs.html#662" class="Bound">Π</a><a id="792" class="Symbol">)</a>

<a id="795" class="Keyword">module</a> <a id="802" href="graph-theory.voltage-graphs.html#802" class="Module">_</a>
  <a id="806" class="Symbol">{</a><a id="807" href="graph-theory.voltage-graphs.html#807" class="Bound">l1</a> <a id="810" href="graph-theory.voltage-graphs.html#810" class="Bound">l2</a> <a id="813" href="graph-theory.voltage-graphs.html#813" class="Bound">l3</a> <a id="816" class="Symbol">:</a> <a id="818" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="823" class="Symbol">}</a> <a id="825" class="Symbol">(</a><a id="826" href="graph-theory.voltage-graphs.html#826" class="Bound">Π</a> <a id="828" class="Symbol">:</a> <a id="830" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="836" href="graph-theory.voltage-graphs.html#807" class="Bound">l1</a><a id="838" class="Symbol">)</a> <a id="840" class="Symbol">(</a><a id="841" href="graph-theory.voltage-graphs.html#841" class="Bound">G</a> <a id="843" class="Symbol">:</a> <a id="845" href="graph-theory.voltage-graphs.html#550" class="Function">Voltage-Graph</a> <a id="859" href="graph-theory.voltage-graphs.html#810" class="Bound">l2</a> <a id="862" href="graph-theory.voltage-graphs.html#813" class="Bound">l3</a> <a id="865" href="graph-theory.voltage-graphs.html#826" class="Bound">Π</a><a id="866" class="Symbol">)</a>
  <a id="870" class="Keyword">where</a>

  <a id="879" href="graph-theory.voltage-graphs.html#879" class="Function">graph-Voltage-Graph</a> <a id="899" class="Symbol">:</a> <a id="901" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="916" href="graph-theory.voltage-graphs.html#810" class="Bound">l2</a> <a id="919" href="graph-theory.voltage-graphs.html#813" class="Bound">l3</a>
  <a id="924" href="graph-theory.voltage-graphs.html#879" class="Function">graph-Voltage-Graph</a> <a id="944" class="Symbol">=</a> <a id="946" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="950" href="graph-theory.voltage-graphs.html#841" class="Bound">G</a>

  <a id="955" href="graph-theory.voltage-graphs.html#955" class="Function">vertex-Voltage-Graph</a> <a id="976" class="Symbol">:</a> <a id="978" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="981" href="graph-theory.voltage-graphs.html#810" class="Bound">l2</a>
  <a id="986" href="graph-theory.voltage-graphs.html#955" class="Function">vertex-Voltage-Graph</a> <a id="1007" class="Symbol">=</a> <a id="1009" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1031" href="graph-theory.voltage-graphs.html#879" class="Function">graph-Voltage-Graph</a>

  <a id="1054" href="graph-theory.voltage-graphs.html#1054" class="Function">edge-Voltage-Graph</a> <a id="1073" class="Symbol">:</a> <a id="1075" class="Symbol">(</a><a id="1076" href="graph-theory.voltage-graphs.html#1076" class="Bound">x</a> <a id="1078" href="graph-theory.voltage-graphs.html#1078" class="Bound">y</a> <a id="1080" class="Symbol">:</a> <a id="1082" href="graph-theory.voltage-graphs.html#955" class="Function">vertex-Voltage-Graph</a><a id="1102" class="Symbol">)</a> <a id="1104" class="Symbol">→</a> <a id="1106" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1109" href="graph-theory.voltage-graphs.html#813" class="Bound">l3</a>
  <a id="1114" href="graph-theory.voltage-graphs.html#1054" class="Function">edge-Voltage-Graph</a> <a id="1133" class="Symbol">=</a> <a id="1135" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="1155" href="graph-theory.voltage-graphs.html#879" class="Function">graph-Voltage-Graph</a>

  <a id="1178" href="graph-theory.voltage-graphs.html#1178" class="Function">voltage-Voltage-Graph</a> <a id="1200" class="Symbol">:</a>
    <a id="1206" class="Symbol">{</a><a id="1207" href="graph-theory.voltage-graphs.html#1207" class="Bound">x</a> <a id="1209" href="graph-theory.voltage-graphs.html#1209" class="Bound">y</a> <a id="1211" class="Symbol">:</a> <a id="1213" href="graph-theory.voltage-graphs.html#955" class="Function">vertex-Voltage-Graph</a><a id="1233" class="Symbol">}</a> <a id="1235" class="Symbol">→</a> <a id="1237" href="graph-theory.voltage-graphs.html#1054" class="Function">edge-Voltage-Graph</a> <a id="1256" href="graph-theory.voltage-graphs.html#1207" class="Bound">x</a> <a id="1258" href="graph-theory.voltage-graphs.html#1209" class="Bound">y</a> <a id="1260" class="Symbol">→</a> <a id="1262" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1273" href="graph-theory.voltage-graphs.html#826" class="Bound">Π</a>
  <a id="1277" href="graph-theory.voltage-graphs.html#1178" class="Function">voltage-Voltage-Graph</a> <a id="1299" class="Symbol">=</a> <a id="1301" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1305" href="graph-theory.voltage-graphs.html#841" class="Bound">G</a>
</pre>
## External links

- [Voltage graph](https://en.wikipedia.org/wiki/Voltage_graph) at Wikipedia
