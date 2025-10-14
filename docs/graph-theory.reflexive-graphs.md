# Reflexive graphs

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="foundation.binary-dependent-identifications.html" class="Module">foundation.binary-dependent-identifications</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation.reflexive-relations.html" class="Module">foundation.reflexive-relations</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="343" class="Keyword">open</a> <a id="348" class="Keyword">import</a> <a id="355" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
</pre>
</details>

## Idea

A {{#concept "reflexive graph" Agda=Reflexive-Graph}} is a
[directed graph](graph-theory.directed-graphs.md)
[equipped](foundation.structure.md) with a loop edge at every vertex.

## Definition

<pre class="Agda"><a id="Reflexive-Graph"></a><a id="613" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="629" class="Symbol">:</a> <a id="631" class="Symbol">(</a><a id="632" href="graph-theory.reflexive-graphs.html#632" class="Bound">l1</a> <a id="635" href="graph-theory.reflexive-graphs.html#635" class="Bound">l2</a> <a id="638" class="Symbol">:</a> <a id="640" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="645" class="Symbol">)</a> <a id="647" class="Symbol">→</a> <a id="649" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="652" class="Symbol">(</a><a id="653" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="658" href="graph-theory.reflexive-graphs.html#632" class="Bound">l1</a> <a id="661" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="663" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="668" href="graph-theory.reflexive-graphs.html#635" class="Bound">l2</a><a id="670" class="Symbol">)</a>
<a id="672" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="688" href="graph-theory.reflexive-graphs.html#688" class="Bound">l1</a> <a id="691" href="graph-theory.reflexive-graphs.html#691" class="Bound">l2</a> <a id="694" class="Symbol">=</a>
  <a id="698" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="700" class="Symbol">(</a> <a id="702" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="717" href="graph-theory.reflexive-graphs.html#688" class="Bound">l1</a> <a id="720" href="graph-theory.reflexive-graphs.html#691" class="Bound">l2</a><a id="722" class="Symbol">)</a>
    <a id="728" class="Symbol">(</a> <a id="730" class="Symbol">λ</a> <a id="732" href="graph-theory.reflexive-graphs.html#732" class="Bound">G</a> <a id="734" class="Symbol">→</a> <a id="736" class="Symbol">(</a><a id="737" href="graph-theory.reflexive-graphs.html#737" class="Bound">x</a> <a id="739" class="Symbol">:</a> <a id="741" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="763" href="graph-theory.reflexive-graphs.html#732" class="Bound">G</a><a id="764" class="Symbol">)</a> <a id="766" class="Symbol">→</a> <a id="768" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="788" href="graph-theory.reflexive-graphs.html#732" class="Bound">G</a> <a id="790" href="graph-theory.reflexive-graphs.html#737" class="Bound">x</a> <a id="792" href="graph-theory.reflexive-graphs.html#737" class="Bound">x</a><a id="793" class="Symbol">)</a>

<a id="796" class="Keyword">module</a> <a id="803" href="graph-theory.reflexive-graphs.html#803" class="Module">_</a>
  <a id="807" class="Symbol">{</a><a id="808" href="graph-theory.reflexive-graphs.html#808" class="Bound">l1</a> <a id="811" href="graph-theory.reflexive-graphs.html#811" class="Bound">l2</a> <a id="814" class="Symbol">:</a> <a id="816" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="821" class="Symbol">}</a> <a id="823" class="Symbol">(</a><a id="824" href="graph-theory.reflexive-graphs.html#824" class="Bound">G</a> <a id="826" class="Symbol">:</a> <a id="828" href="graph-theory.reflexive-graphs.html#613" class="Function">Reflexive-Graph</a> <a id="844" href="graph-theory.reflexive-graphs.html#808" class="Bound">l1</a> <a id="847" href="graph-theory.reflexive-graphs.html#811" class="Bound">l2</a><a id="849" class="Symbol">)</a>
  <a id="853" class="Keyword">where</a>

  <a id="862" href="graph-theory.reflexive-graphs.html#862" class="Function">directed-graph-Reflexive-Graph</a> <a id="893" class="Symbol">:</a> <a id="895" href="graph-theory.directed-graphs.html#1345" class="Function">Directed-Graph</a> <a id="910" href="graph-theory.reflexive-graphs.html#808" class="Bound">l1</a> <a id="913" href="graph-theory.reflexive-graphs.html#811" class="Bound">l2</a>
  <a id="918" href="graph-theory.reflexive-graphs.html#862" class="Function">directed-graph-Reflexive-Graph</a> <a id="949" class="Symbol">=</a> <a id="951" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="955" href="graph-theory.reflexive-graphs.html#824" class="Bound">G</a>

  <a id="960" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="983" class="Symbol">:</a> <a id="985" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="988" href="graph-theory.reflexive-graphs.html#808" class="Bound">l1</a>
  <a id="993" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="1016" class="Symbol">=</a> <a id="1018" href="graph-theory.directed-graphs.html#1524" class="Function">vertex-Directed-Graph</a> <a id="1040" href="graph-theory.reflexive-graphs.html#862" class="Function">directed-graph-Reflexive-Graph</a>

  <a id="1074" href="graph-theory.reflexive-graphs.html#1074" class="Function">edge-Reflexive-Graph</a> <a id="1095" class="Symbol">:</a> <a id="1097" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="1120" class="Symbol">→</a> <a id="1122" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a> <a id="1145" class="Symbol">→</a> <a id="1147" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1150" href="graph-theory.reflexive-graphs.html#811" class="Bound">l2</a>
  <a id="1155" href="graph-theory.reflexive-graphs.html#1074" class="Function">edge-Reflexive-Graph</a> <a id="1176" class="Symbol">=</a> <a id="1178" href="graph-theory.directed-graphs.html#1589" class="Function">edge-Directed-Graph</a> <a id="1198" href="graph-theory.reflexive-graphs.html#862" class="Function">directed-graph-Reflexive-Graph</a>

  <a id="1232" href="graph-theory.reflexive-graphs.html#1232" class="Function">refl-Reflexive-Graph</a> <a id="1253" class="Symbol">:</a> <a id="1255" class="Symbol">(</a><a id="1256" href="graph-theory.reflexive-graphs.html#1256" class="Bound">x</a> <a id="1258" class="Symbol">:</a> <a id="1260" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a><a id="1282" class="Symbol">)</a> <a id="1284" class="Symbol">→</a> <a id="1286" href="graph-theory.reflexive-graphs.html#1074" class="Function">edge-Reflexive-Graph</a> <a id="1307" href="graph-theory.reflexive-graphs.html#1256" class="Bound">x</a> <a id="1309" href="graph-theory.reflexive-graphs.html#1256" class="Bound">x</a>
  <a id="1313" href="graph-theory.reflexive-graphs.html#1232" class="Function">refl-Reflexive-Graph</a> <a id="1334" class="Symbol">=</a> <a id="1336" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1340" href="graph-theory.reflexive-graphs.html#824" class="Bound">G</a>

  <a id="1345" href="graph-theory.reflexive-graphs.html#1345" class="Function">edge-reflexive-relation-Reflexive-Graph</a> <a id="1385" class="Symbol">:</a>
    <a id="1391" href="foundation.reflexive-relations.html#654" class="Function">Reflexive-Relation</a> <a id="1410" href="graph-theory.reflexive-graphs.html#811" class="Bound">l2</a> <a id="1413" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a>
  <a id="1438" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1442" href="graph-theory.reflexive-graphs.html#1345" class="Function">edge-reflexive-relation-Reflexive-Graph</a> <a id="1482" class="Symbol">=</a> <a id="1484" href="graph-theory.reflexive-graphs.html#1074" class="Function">edge-Reflexive-Graph</a>
  <a id="1507" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1511" href="graph-theory.reflexive-graphs.html#1345" class="Function">edge-reflexive-relation-Reflexive-Graph</a> <a id="1551" class="Symbol">=</a> <a id="1553" href="graph-theory.reflexive-graphs.html#1232" class="Function">refl-Reflexive-Graph</a>

  <a id="1577" href="graph-theory.reflexive-graphs.html#1577" class="Function">binary-dependent-identification-refl-Reflexive-Graph</a> <a id="1630" class="Symbol">:</a>
    <a id="1636" class="Symbol">{</a><a id="1637" href="graph-theory.reflexive-graphs.html#1637" class="Bound">x</a> <a id="1639" href="graph-theory.reflexive-graphs.html#1639" class="Bound">y</a> <a id="1641" class="Symbol">:</a> <a id="1643" href="graph-theory.reflexive-graphs.html#960" class="Function">vertex-Reflexive-Graph</a><a id="1665" class="Symbol">}</a> <a id="1667" class="Symbol">(</a><a id="1668" href="graph-theory.reflexive-graphs.html#1668" class="Bound">p</a> <a id="1670" class="Symbol">:</a> <a id="1672" href="graph-theory.reflexive-graphs.html#1637" class="Bound">x</a> <a id="1674" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1676" href="graph-theory.reflexive-graphs.html#1639" class="Bound">y</a><a id="1677" class="Symbol">)</a> <a id="1679" class="Symbol">→</a>
    <a id="1685" href="foundation.binary-dependent-identifications.html#927" class="Function">binary-dependent-identification</a> <a id="1717" href="graph-theory.reflexive-graphs.html#1074" class="Function">edge-Reflexive-Graph</a> <a id="1738" href="graph-theory.reflexive-graphs.html#1668" class="Bound">p</a> <a id="1740" href="graph-theory.reflexive-graphs.html#1668" class="Bound">p</a>
      <a id="1748" class="Symbol">(</a> <a id="1750" href="graph-theory.reflexive-graphs.html#1232" class="Function">refl-Reflexive-Graph</a> <a id="1771" href="graph-theory.reflexive-graphs.html#1637" class="Bound">x</a><a id="1772" class="Symbol">)</a>
      <a id="1780" class="Symbol">(</a> <a id="1782" href="graph-theory.reflexive-graphs.html#1232" class="Function">refl-Reflexive-Graph</a> <a id="1803" href="graph-theory.reflexive-graphs.html#1639" class="Bound">y</a><a id="1804" class="Symbol">)</a>
  <a id="1808" href="graph-theory.reflexive-graphs.html#1577" class="Function">binary-dependent-identification-refl-Reflexive-Graph</a> <a id="1861" class="Symbol">=</a>
    <a id="1867" href="foundation.reflexive-relations.html#2516" class="Function">binary-dependent-identification-refl-Reflexive-Relation</a>
      <a id="1929" href="graph-theory.reflexive-graphs.html#1345" class="Function">edge-reflexive-relation-Reflexive-Graph</a>
</pre>
## See also

- [Large reflexive graphs](graph-theory.large-reflexive-graphs.md)
- [The universal reflexive graph](graph-theory.universal-reflexive-graph.md)

## External links

- [Reflexive graph](https://ncatlab.org/nlab/show/reflexive+graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Reflexive graph](https://mathworld.wolfram.com/ReflexiveGraph.html) at
  Wolfram MathWorld
