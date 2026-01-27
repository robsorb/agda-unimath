# The coalgebra of enriched directed trees

<pre class="Agda"><a id="53" class="Symbol">{-#</a> <a id="57" class="Keyword">OPTIONS</a> <a id="65" class="Pragma">--lossy-unification</a> <a id="85" class="Symbol">#-}</a>

<a id="90" class="Keyword">module</a> <a id="97" href="trees.coalgebra-of-enriched-directed-trees.html" class="Module">trees.coalgebra-of-enriched-directed-trees</a> <a id="140" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="trees.coalgebras-polynomial-endofunctors.html" class="Module">trees.coalgebras-polynomial-endofunctors</a>
<a id="333" class="Keyword">open</a> <a id="338" class="Keyword">import</a> <a id="345" href="trees.enriched-directed-trees.html" class="Module">trees.enriched-directed-trees</a>
<a id="375" class="Keyword">open</a> <a id="380" class="Keyword">import</a> <a id="387" href="trees.fibers-enriched-directed-trees.html" class="Module">trees.fibers-enriched-directed-trees</a>
<a id="424" class="Keyword">open</a> <a id="429" class="Keyword">import</a> <a id="436" href="trees.polynomial-endofunctors.html" class="Module">trees.polynomial-endofunctors</a>
</pre>
</details>

## Idea

Using the fibers of base elements, the type of enriched directed trees has the
structure of a coalgebra for the polynomial endofunctor

```text
  X ↦ Σ (a : A), B a → X.
```

## Definition

<pre class="Agda"><a id="690" class="Keyword">module</a> <a id="697" href="trees.coalgebra-of-enriched-directed-trees.html#697" class="Module">_</a>
  <a id="701" class="Symbol">{</a><a id="702" href="trees.coalgebra-of-enriched-directed-trees.html#702" class="Bound">l1</a> <a id="705" href="trees.coalgebra-of-enriched-directed-trees.html#705" class="Bound">l2</a> <a id="708" class="Symbol">:</a> <a id="710" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="715" class="Symbol">}</a> <a id="717" class="Symbol">(</a><a id="718" href="trees.coalgebra-of-enriched-directed-trees.html#718" class="Bound">l3</a> <a id="721" class="Symbol">:</a> <a id="723" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="728" class="Symbol">)</a> <a id="730" class="Symbol">(</a><a id="731" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="733" class="Symbol">:</a> <a id="735" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="738" href="trees.coalgebra-of-enriched-directed-trees.html#702" class="Bound">l1</a><a id="740" class="Symbol">)</a> <a id="742" class="Symbol">(</a><a id="743" href="trees.coalgebra-of-enriched-directed-trees.html#743" class="Bound">B</a> <a id="745" class="Symbol">:</a> <a id="747" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="749" class="Symbol">→</a> <a id="751" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="754" href="trees.coalgebra-of-enriched-directed-trees.html#705" class="Bound">l2</a><a id="756" class="Symbol">)</a>
  <a id="760" class="Keyword">where</a>

  <a id="769" href="trees.coalgebra-of-enriched-directed-trees.html#769" class="Function">structure-coalgebra-Enriched-Directed-Tree</a> <a id="812" class="Symbol">:</a>
    <a id="818" href="trees.enriched-directed-trees.html#1284" class="Function">Enriched-Directed-Tree</a> <a id="841" href="trees.coalgebra-of-enriched-directed-trees.html#718" class="Bound">l3</a> <a id="844" href="trees.coalgebra-of-enriched-directed-trees.html#718" class="Bound">l3</a> <a id="847" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="849" href="trees.coalgebra-of-enriched-directed-trees.html#743" class="Bound">B</a> <a id="851" class="Symbol">→</a>
    <a id="857" href="trees.polynomial-endofunctors.html#1314" class="Function">type-polynomial-endofunctor</a> <a id="885" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="887" href="trees.coalgebra-of-enriched-directed-trees.html#743" class="Bound">B</a> <a id="889" class="Symbol">(</a><a id="890" href="trees.enriched-directed-trees.html#1284" class="Function">Enriched-Directed-Tree</a> <a id="913" href="trees.coalgebra-of-enriched-directed-trees.html#718" class="Bound">l3</a> <a id="916" href="trees.coalgebra-of-enriched-directed-trees.html#718" class="Bound">l3</a> <a id="919" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="921" href="trees.coalgebra-of-enriched-directed-trees.html#743" class="Bound">B</a><a id="922" class="Symbol">)</a>
  <a id="926" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="930" class="Symbol">(</a><a id="931" href="trees.coalgebra-of-enriched-directed-trees.html#769" class="Function">structure-coalgebra-Enriched-Directed-Tree</a> <a id="974" href="trees.coalgebra-of-enriched-directed-trees.html#974" class="Bound">T</a><a id="975" class="Symbol">)</a> <a id="977" class="Symbol">=</a>
    <a id="983" href="trees.enriched-directed-trees.html#10653" class="Function">shape-root-Enriched-Directed-Tree</a> <a id="1017" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="1019" href="trees.coalgebra-of-enriched-directed-trees.html#743" class="Bound">B</a> <a id="1021" href="trees.coalgebra-of-enriched-directed-trees.html#974" class="Bound">T</a>
  <a id="1025" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1029" class="Symbol">(</a><a id="1030" href="trees.coalgebra-of-enriched-directed-trees.html#769" class="Function">structure-coalgebra-Enriched-Directed-Tree</a> <a id="1073" href="trees.coalgebra-of-enriched-directed-trees.html#1073" class="Bound">T</a><a id="1074" class="Symbol">)</a> <a id="1076" class="Symbol">=</a>
    <a id="1082" href="trees.fibers-enriched-directed-trees.html#8975" class="Function">fiber-base-Enriched-Directed-Tree</a> <a id="1116" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="1118" href="trees.coalgebra-of-enriched-directed-trees.html#743" class="Bound">B</a> <a id="1120" href="trees.coalgebra-of-enriched-directed-trees.html#1073" class="Bound">T</a>

  <a id="1125" href="trees.coalgebra-of-enriched-directed-trees.html#1125" class="Function">coalgebra-Enriched-Directed-Tree</a> <a id="1158" class="Symbol">:</a>
    <a id="1164" href="trees.coalgebras-polynomial-endofunctors.html#529" class="Function">coalgebra-polynomial-endofunctor</a> <a id="1197" class="Symbol">(</a><a id="1198" href="trees.coalgebra-of-enriched-directed-trees.html#702" class="Bound">l1</a> <a id="1201" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1203" href="trees.coalgebra-of-enriched-directed-trees.html#705" class="Bound">l2</a> <a id="1206" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1208" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1213" href="trees.coalgebra-of-enriched-directed-trees.html#718" class="Bound">l3</a><a id="1215" class="Symbol">)</a> <a id="1217" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="1219" href="trees.coalgebra-of-enriched-directed-trees.html#743" class="Bound">B</a>
  <a id="1223" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1227" href="trees.coalgebra-of-enriched-directed-trees.html#1125" class="Function">coalgebra-Enriched-Directed-Tree</a> <a id="1260" class="Symbol">=</a> <a id="1262" href="trees.enriched-directed-trees.html#1284" class="Function">Enriched-Directed-Tree</a> <a id="1285" href="trees.coalgebra-of-enriched-directed-trees.html#718" class="Bound">l3</a> <a id="1288" href="trees.coalgebra-of-enriched-directed-trees.html#718" class="Bound">l3</a> <a id="1291" href="trees.coalgebra-of-enriched-directed-trees.html#731" class="Bound">A</a> <a id="1293" href="trees.coalgebra-of-enriched-directed-trees.html#743" class="Bound">B</a>
  <a id="1297" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1301" href="trees.coalgebra-of-enriched-directed-trees.html#1125" class="Function">coalgebra-Enriched-Directed-Tree</a> <a id="1334" class="Symbol">=</a>
    <a id="1340" href="trees.coalgebra-of-enriched-directed-trees.html#769" class="Function">structure-coalgebra-Enriched-Directed-Tree</a>
</pre>