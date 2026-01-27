# Planar binary trees

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="trees.planar-binary-trees.html" class="Module">trees.planar-binary-trees</a> <a id="65" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="121" class="Keyword">open</a> <a id="126" class="Keyword">import</a> <a id="133" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="trees.w-types.html" class="Module">trees.w-types</a>
</pre>
</details>

## Idea

A planar binary tree is a binary tree in which the branchings are labeled by the
booleans. The idea is that at any branching point in a planar binary tree, we
know which branch goes to the left and which branch goes to the right.

Planar binary trees are commonly called binary trees, but in univalent
mathematics it makes sense to recognize that the branching points in a binary
tree should not record which branch goes left and which branch goes right.

## Definitions

### The inductive definition of the type of planar binary trees

<pre class="Agda"><a id="863" class="Keyword">data</a> <a id="Planar-Bin-Tree"></a><a id="868" href="trees.planar-binary-trees.html#868" class="Datatype">Planar-Bin-Tree</a> <a id="884" class="Symbol">:</a> <a id="886" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="889" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="895" class="Keyword">where</a>
  <a id="Planar-Bin-Tree.root-PBT"></a><a id="903" href="trees.planar-binary-trees.html#903" class="InductiveConstructor">root-PBT</a> <a id="912" class="Symbol">:</a> <a id="914" href="trees.planar-binary-trees.html#868" class="Datatype">Planar-Bin-Tree</a>
  <a id="Planar-Bin-Tree.join-PBT"></a><a id="932" href="trees.planar-binary-trees.html#932" class="InductiveConstructor">join-PBT</a> <a id="941" class="Symbol">:</a> <a id="943" class="Symbol">(</a><a id="944" href="trees.planar-binary-trees.html#944" class="Bound">x</a> <a id="946" href="trees.planar-binary-trees.html#946" class="Bound">y</a> <a id="948" class="Symbol">:</a> <a id="950" href="trees.planar-binary-trees.html#868" class="Datatype">Planar-Bin-Tree</a><a id="965" class="Symbol">)</a> <a id="967" class="Symbol">→</a> <a id="969" href="trees.planar-binary-trees.html#868" class="Datatype">Planar-Bin-Tree</a>
</pre>
### The definition of the type of planar binary trees as a W-type

<pre class="Agda"><a id="PBT-𝕎"></a><a id="1065" href="trees.planar-binary-trees.html#1065" class="Function">PBT-𝕎</a> <a id="1071" class="Symbol">:</a> <a id="1073" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1076" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="1082" href="trees.planar-binary-trees.html#1065" class="Function">PBT-𝕎</a> <a id="1088" class="Symbol">=</a> <a id="1090" href="trees.w-types.html#1681" class="Datatype">𝕎</a> <a id="1092" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="1097" href="trees.planar-binary-trees.html#1109" class="Function">P</a>
  <a id="1101" class="Keyword">where</a>
  <a id="1109" href="trees.planar-binary-trees.html#1109" class="Function">P</a> <a id="1111" class="Symbol">:</a> <a id="1113" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="1118" class="Symbol">→</a> <a id="1120" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1123" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="1131" href="trees.planar-binary-trees.html#1109" class="Function">P</a> <a id="1133" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a> <a id="1138" class="Symbol">=</a> <a id="1140" href="foundation.booleans.html#1556" class="Datatype">bool</a>
  <a id="1147" href="trees.planar-binary-trees.html#1109" class="Function">P</a> <a id="1149" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="1155" class="Symbol">=</a> <a id="1157" href="foundation-core.empty-types.html#801" class="Datatype">empty</a>

<a id="root-PBT-𝕎"></a><a id="1164" href="trees.planar-binary-trees.html#1164" class="Function">root-PBT-𝕎</a> <a id="1175" class="Symbol">:</a> <a id="1177" href="trees.planar-binary-trees.html#1065" class="Function">PBT-𝕎</a>
<a id="1183" href="trees.planar-binary-trees.html#1164" class="Function">root-PBT-𝕎</a> <a id="1194" class="Symbol">=</a> <a id="1196" href="trees.w-types.html#2931" class="Function">constant-𝕎</a> <a id="1207" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="1213" href="foundation-core.function-types.html#307" class="Function">id</a>

<a id="join-PBT-𝕎"></a><a id="1217" href="trees.planar-binary-trees.html#1217" class="Function">join-PBT-𝕎</a> <a id="1228" class="Symbol">:</a> <a id="1230" class="Symbol">(</a><a id="1231" href="trees.planar-binary-trees.html#1231" class="Bound">x</a> <a id="1233" href="trees.planar-binary-trees.html#1233" class="Bound">y</a> <a id="1235" class="Symbol">:</a> <a id="1237" href="trees.planar-binary-trees.html#1065" class="Function">PBT-𝕎</a><a id="1242" class="Symbol">)</a> <a id="1244" class="Symbol">→</a> <a id="1246" href="trees.planar-binary-trees.html#1065" class="Function">PBT-𝕎</a>
<a id="1252" href="trees.planar-binary-trees.html#1217" class="Function">join-PBT-𝕎</a> <a id="1263" href="trees.planar-binary-trees.html#1263" class="Bound">x</a> <a id="1265" href="trees.planar-binary-trees.html#1265" class="Bound">y</a> <a id="1267" class="Symbol">=</a> <a id="1269" href="trees.w-types.html#1750" class="InductiveConstructor">tree-𝕎</a> <a id="1276" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a> <a id="1281" href="trees.planar-binary-trees.html#1293" class="Function">α</a>
  <a id="1285" class="Keyword">where</a>
  <a id="1293" href="trees.planar-binary-trees.html#1293" class="Function">α</a> <a id="1295" class="Symbol">:</a> <a id="1297" href="foundation.booleans.html#1556" class="Datatype">bool</a> <a id="1302" class="Symbol">→</a> <a id="1304" href="trees.planar-binary-trees.html#1065" class="Function">PBT-𝕎</a>
  <a id="1312" href="trees.planar-binary-trees.html#1293" class="Function">α</a> <a id="1314" href="foundation.booleans.html#1580" class="InductiveConstructor">true</a> <a id="1319" class="Symbol">=</a> <a id="1321" href="trees.planar-binary-trees.html#1263" class="Bound">x</a>
  <a id="1325" href="trees.planar-binary-trees.html#1293" class="Function">α</a> <a id="1327" href="foundation.booleans.html#1585" class="InductiveConstructor">false</a> <a id="1333" class="Symbol">=</a> <a id="1335" href="trees.planar-binary-trees.html#1265" class="Bound">y</a>
</pre>