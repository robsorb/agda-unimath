# Coalgebras of polynomial endofunctors

<pre class="Agda"><a id="50" class="Keyword">module</a> <a id="57" href="trees.coalgebras-polynomial-endofunctors.html" class="Module">trees.coalgebras-polynomial-endofunctors</a> <a id="98" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="198" class="Keyword">open</a> <a id="203" class="Keyword">import</a> <a id="210" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="trees.polynomial-endofunctors.html" class="Module">trees.polynomial-endofunctors</a>
</pre>
</details>

## Idea

**Coalgebras** for polynomial endofunctors are types `X` equipped with a
function

```text
  X → Σ (a : A), B a → X
```

## Definitions

<pre class="Agda"><a id="451" class="Keyword">module</a> <a id="458" href="trees.coalgebras-polynomial-endofunctors.html#458" class="Module">_</a>
  <a id="462" class="Symbol">{</a><a id="463" href="trees.coalgebras-polynomial-endofunctors.html#463" class="Bound">l1</a> <a id="466" href="trees.coalgebras-polynomial-endofunctors.html#466" class="Bound">l2</a> <a id="469" class="Symbol">:</a> <a id="471" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="476" class="Symbol">}</a> <a id="478" class="Symbol">(</a><a id="479" href="trees.coalgebras-polynomial-endofunctors.html#479" class="Bound">l</a> <a id="481" class="Symbol">:</a> <a id="483" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="488" class="Symbol">)</a> <a id="490" class="Symbol">(</a><a id="491" href="trees.coalgebras-polynomial-endofunctors.html#491" class="Bound">A</a> <a id="493" class="Symbol">:</a> <a id="495" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="498" href="trees.coalgebras-polynomial-endofunctors.html#463" class="Bound">l1</a><a id="500" class="Symbol">)</a> <a id="502" class="Symbol">(</a><a id="503" href="trees.coalgebras-polynomial-endofunctors.html#503" class="Bound">B</a> <a id="505" class="Symbol">:</a> <a id="507" href="trees.coalgebras-polynomial-endofunctors.html#491" class="Bound">A</a> <a id="509" class="Symbol">→</a> <a id="511" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="514" href="trees.coalgebras-polynomial-endofunctors.html#466" class="Bound">l2</a><a id="516" class="Symbol">)</a>
  <a id="520" class="Keyword">where</a>

  <a id="529" href="trees.coalgebras-polynomial-endofunctors.html#529" class="Function">coalgebra-polynomial-endofunctor</a> <a id="562" class="Symbol">:</a> <a id="564" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="567" class="Symbol">(</a><a id="568" href="trees.coalgebras-polynomial-endofunctors.html#463" class="Bound">l1</a> <a id="571" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="573" href="trees.coalgebras-polynomial-endofunctors.html#466" class="Bound">l2</a> <a id="576" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="578" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="583" href="trees.coalgebras-polynomial-endofunctors.html#479" class="Bound">l</a><a id="584" class="Symbol">)</a>
  <a id="588" href="trees.coalgebras-polynomial-endofunctors.html#529" class="Function">coalgebra-polynomial-endofunctor</a> <a id="621" class="Symbol">=</a>
    <a id="627" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="629" class="Symbol">(</a><a id="630" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="633" href="trees.coalgebras-polynomial-endofunctors.html#479" class="Bound">l</a><a id="634" class="Symbol">)</a> <a id="636" class="Symbol">(λ</a> <a id="639" href="trees.coalgebras-polynomial-endofunctors.html#639" class="Bound">X</a> <a id="641" class="Symbol">→</a> <a id="643" href="trees.coalgebras-polynomial-endofunctors.html#639" class="Bound">X</a> <a id="645" class="Symbol">→</a> <a id="647" href="trees.polynomial-endofunctors.html#1314" class="Function">type-polynomial-endofunctor</a> <a id="675" href="trees.coalgebras-polynomial-endofunctors.html#491" class="Bound">A</a> <a id="677" href="trees.coalgebras-polynomial-endofunctors.html#503" class="Bound">B</a> <a id="679" href="trees.coalgebras-polynomial-endofunctors.html#639" class="Bound">X</a><a id="680" class="Symbol">)</a>

<a id="683" class="Keyword">module</a> <a id="690" href="trees.coalgebras-polynomial-endofunctors.html#690" class="Module">_</a>
  <a id="694" class="Symbol">{</a><a id="695" href="trees.coalgebras-polynomial-endofunctors.html#695" class="Bound">l1</a> <a id="698" href="trees.coalgebras-polynomial-endofunctors.html#698" class="Bound">l2</a> <a id="701" href="trees.coalgebras-polynomial-endofunctors.html#701" class="Bound">l3</a> <a id="704" class="Symbol">:</a> <a id="706" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="711" class="Symbol">}</a> <a id="713" class="Symbol">{</a><a id="714" href="trees.coalgebras-polynomial-endofunctors.html#714" class="Bound">A</a> <a id="716" class="Symbol">:</a> <a id="718" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="721" href="trees.coalgebras-polynomial-endofunctors.html#695" class="Bound">l1</a><a id="723" class="Symbol">}</a> <a id="725" class="Symbol">{</a><a id="726" href="trees.coalgebras-polynomial-endofunctors.html#726" class="Bound">B</a> <a id="728" class="Symbol">:</a> <a id="730" href="trees.coalgebras-polynomial-endofunctors.html#714" class="Bound">A</a> <a id="732" class="Symbol">→</a> <a id="734" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="737" href="trees.coalgebras-polynomial-endofunctors.html#698" class="Bound">l2</a><a id="739" class="Symbol">}</a>
  <a id="743" class="Symbol">(</a><a id="744" href="trees.coalgebras-polynomial-endofunctors.html#744" class="Bound">X</a> <a id="746" class="Symbol">:</a> <a id="748" href="trees.coalgebras-polynomial-endofunctors.html#529" class="Function">coalgebra-polynomial-endofunctor</a> <a id="781" href="trees.coalgebras-polynomial-endofunctors.html#701" class="Bound">l3</a> <a id="784" href="trees.coalgebras-polynomial-endofunctors.html#714" class="Bound">A</a> <a id="786" href="trees.coalgebras-polynomial-endofunctors.html#726" class="Bound">B</a><a id="787" class="Symbol">)</a>
  <a id="791" class="Keyword">where</a>

  <a id="800" href="trees.coalgebras-polynomial-endofunctors.html#800" class="Function">type-coalgebra-polynomial-endofunctor</a> <a id="838" class="Symbol">:</a> <a id="840" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="843" href="trees.coalgebras-polynomial-endofunctors.html#701" class="Bound">l3</a>
  <a id="848" href="trees.coalgebras-polynomial-endofunctors.html#800" class="Function">type-coalgebra-polynomial-endofunctor</a> <a id="886" class="Symbol">=</a> <a id="888" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="892" href="trees.coalgebras-polynomial-endofunctors.html#744" class="Bound">X</a>

  <a id="897" href="trees.coalgebras-polynomial-endofunctors.html#897" class="Function">structure-coalgebra-polynomial-endofunctor</a> <a id="940" class="Symbol">:</a>
    <a id="946" href="trees.coalgebras-polynomial-endofunctors.html#800" class="Function">type-coalgebra-polynomial-endofunctor</a> <a id="984" class="Symbol">→</a>
    <a id="990" href="trees.polynomial-endofunctors.html#1314" class="Function">type-polynomial-endofunctor</a> <a id="1018" href="trees.coalgebras-polynomial-endofunctors.html#714" class="Bound">A</a> <a id="1020" href="trees.coalgebras-polynomial-endofunctors.html#726" class="Bound">B</a> <a id="1022" href="trees.coalgebras-polynomial-endofunctors.html#800" class="Function">type-coalgebra-polynomial-endofunctor</a>
  <a id="1062" href="trees.coalgebras-polynomial-endofunctors.html#897" class="Function">structure-coalgebra-polynomial-endofunctor</a> <a id="1105" class="Symbol">=</a> <a id="1107" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1111" href="trees.coalgebras-polynomial-endofunctors.html#744" class="Bound">X</a>

  <a id="1116" href="trees.coalgebras-polynomial-endofunctors.html#1116" class="Function">shape-coalgebra-polynomial-endofunctor</a> <a id="1155" class="Symbol">:</a>
    <a id="1161" href="trees.coalgebras-polynomial-endofunctors.html#800" class="Function">type-coalgebra-polynomial-endofunctor</a> <a id="1199" class="Symbol">→</a> <a id="1201" href="trees.coalgebras-polynomial-endofunctors.html#714" class="Bound">A</a>
  <a id="1205" href="trees.coalgebras-polynomial-endofunctors.html#1116" class="Function">shape-coalgebra-polynomial-endofunctor</a> <a id="1244" href="trees.coalgebras-polynomial-endofunctors.html#1244" class="Bound">x</a> <a id="1246" class="Symbol">=</a>
    <a id="1252" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1256" class="Symbol">(</a><a id="1257" href="trees.coalgebras-polynomial-endofunctors.html#897" class="Function">structure-coalgebra-polynomial-endofunctor</a> <a id="1300" href="trees.coalgebras-polynomial-endofunctors.html#1244" class="Bound">x</a><a id="1301" class="Symbol">)</a>

  <a id="1306" href="trees.coalgebras-polynomial-endofunctors.html#1306" class="Function">component-coalgebra-polynomial-endofunctor</a> <a id="1349" class="Symbol">:</a>
    <a id="1355" class="Symbol">(</a><a id="1356" href="trees.coalgebras-polynomial-endofunctors.html#1356" class="Bound">x</a> <a id="1358" class="Symbol">:</a> <a id="1360" href="trees.coalgebras-polynomial-endofunctors.html#800" class="Function">type-coalgebra-polynomial-endofunctor</a><a id="1397" class="Symbol">)</a> <a id="1399" class="Symbol">→</a>
    <a id="1405" href="trees.coalgebras-polynomial-endofunctors.html#726" class="Bound">B</a> <a id="1407" class="Symbol">(</a><a id="1408" href="trees.coalgebras-polynomial-endofunctors.html#1116" class="Function">shape-coalgebra-polynomial-endofunctor</a> <a id="1447" href="trees.coalgebras-polynomial-endofunctors.html#1356" class="Bound">x</a><a id="1448" class="Symbol">)</a> <a id="1450" class="Symbol">→</a>
    <a id="1456" href="trees.coalgebras-polynomial-endofunctors.html#800" class="Function">type-coalgebra-polynomial-endofunctor</a>
  <a id="1496" href="trees.coalgebras-polynomial-endofunctors.html#1306" class="Function">component-coalgebra-polynomial-endofunctor</a> <a id="1539" href="trees.coalgebras-polynomial-endofunctors.html#1539" class="Bound">x</a> <a id="1541" class="Symbol">=</a>
    <a id="1547" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1551" class="Symbol">(</a><a id="1552" href="trees.coalgebras-polynomial-endofunctors.html#897" class="Function">structure-coalgebra-polynomial-endofunctor</a> <a id="1595" href="trees.coalgebras-polynomial-endofunctors.html#1539" class="Bound">x</a><a id="1596" class="Symbol">)</a>
</pre>