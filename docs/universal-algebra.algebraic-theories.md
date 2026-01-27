# Algebraic theories

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="universal-algebra.algebraic-theories.html" class="Module">universal-algebra.algebraic-theories</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="universal-algebra.abstract-equations-over-signatures.html" class="Module">universal-algebra.abstract-equations-over-signatures</a>
<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="universal-algebra.signatures.html" class="Module">universal-algebra.signatures</a>
</pre>
</details>

## Idea

An algebraic theory is a collection of abstract equations over a signature `σ`
that we consider to 'hold' in the theory. It is algebraic in the sense that we
only require equations involving function symbols from the signature, in
contrast to, say, requiring additional types of relations.

## Definitions

### Theories

<pre class="Agda"><a id="676" class="Keyword">module</a> <a id="683" href="universal-algebra.algebraic-theories.html#683" class="Module">_</a>
  <a id="687" class="Symbol">{</a><a id="688" href="universal-algebra.algebraic-theories.html#688" class="Bound">l1</a> <a id="691" class="Symbol">:</a> <a id="693" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="698" class="Symbol">}</a> <a id="700" class="Symbol">(</a><a id="701" href="universal-algebra.algebraic-theories.html#701" class="Bound">σ</a> <a id="703" class="Symbol">:</a> <a id="705" href="universal-algebra.signatures.html#506" class="Function">signature</a> <a id="715" href="universal-algebra.algebraic-theories.html#688" class="Bound">l1</a><a id="717" class="Symbol">)</a>
  <a id="721" class="Keyword">where</a>

  <a id="730" href="universal-algebra.algebraic-theories.html#730" class="Function">Theory</a> <a id="737" class="Symbol">:</a> <a id="739" class="Symbol">(</a><a id="740" href="universal-algebra.algebraic-theories.html#740" class="Bound">l2</a> <a id="743" class="Symbol">:</a> <a id="745" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="750" class="Symbol">)</a> <a id="752" class="Symbol">→</a> <a id="754" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="757" class="Symbol">(</a><a id="758" href="universal-algebra.algebraic-theories.html#688" class="Bound">l1</a> <a id="761" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="763" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="768" href="universal-algebra.algebraic-theories.html#740" class="Bound">l2</a><a id="770" class="Symbol">)</a>
  <a id="774" href="universal-algebra.algebraic-theories.html#730" class="Function">Theory</a> <a id="781" href="universal-algebra.algebraic-theories.html#781" class="Bound">l2</a> <a id="784" class="Symbol">=</a> <a id="786" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="788" class="Symbol">(</a><a id="789" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="792" href="universal-algebra.algebraic-theories.html#781" class="Bound">l2</a><a id="794" class="Symbol">)</a> <a id="796" class="Symbol">(λ</a> <a id="799" href="universal-algebra.algebraic-theories.html#799" class="Bound">B</a> <a id="801" class="Symbol">→</a> <a id="803" class="Symbol">(</a><a id="804" href="universal-algebra.algebraic-theories.html#799" class="Bound">B</a> <a id="806" class="Symbol">→</a> <a id="808" href="universal-algebra.abstract-equations-over-signatures.html#727" class="Function">Abstract-Equation</a> <a id="826" href="universal-algebra.algebraic-theories.html#701" class="Bound">σ</a><a id="827" class="Symbol">))</a>

  <a id="833" href="universal-algebra.algebraic-theories.html#833" class="Function">index-Theory</a> <a id="846" class="Symbol">:</a> <a id="848" class="Symbol">{</a><a id="849" href="universal-algebra.algebraic-theories.html#849" class="Bound">l2</a> <a id="852" class="Symbol">:</a> <a id="854" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="859" class="Symbol">}</a> <a id="861" class="Symbol">→</a> <a id="863" href="universal-algebra.algebraic-theories.html#730" class="Function">Theory</a> <a id="870" href="universal-algebra.algebraic-theories.html#849" class="Bound">l2</a> <a id="873" class="Symbol">→</a> <a id="875" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="878" href="universal-algebra.algebraic-theories.html#849" class="Bound">l2</a>
  <a id="883" href="universal-algebra.algebraic-theories.html#833" class="Function">index-Theory</a> <a id="896" class="Symbol">=</a> <a id="898" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="905" href="universal-algebra.algebraic-theories.html#905" class="Function">index-Abstract-Equation-Theory</a> <a id="936" class="Symbol">:</a>
    <a id="942" class="Symbol">{</a><a id="943" href="universal-algebra.algebraic-theories.html#943" class="Bound">l2</a> <a id="946" class="Symbol">:</a> <a id="948" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="953" class="Symbol">}</a> <a id="955" class="Symbol">(</a><a id="956" href="universal-algebra.algebraic-theories.html#956" class="Bound">Th</a> <a id="959" class="Symbol">:</a> <a id="961" href="universal-algebra.algebraic-theories.html#730" class="Function">Theory</a> <a id="968" href="universal-algebra.algebraic-theories.html#943" class="Bound">l2</a><a id="970" class="Symbol">)</a> <a id="972" class="Symbol">→</a> <a id="974" class="Symbol">(</a><a id="975" href="universal-algebra.algebraic-theories.html#833" class="Function">index-Theory</a> <a id="988" href="universal-algebra.algebraic-theories.html#956" class="Bound">Th</a><a id="990" class="Symbol">)</a> <a id="992" class="Symbol">→</a> <a id="994" href="universal-algebra.abstract-equations-over-signatures.html#727" class="Function">Abstract-Equation</a> <a id="1012" href="universal-algebra.algebraic-theories.html#701" class="Bound">σ</a>
  <a id="1016" href="universal-algebra.algebraic-theories.html#905" class="Function">index-Abstract-Equation-Theory</a> <a id="1047" href="universal-algebra.algebraic-theories.html#1047" class="Bound">Th</a> <a id="1050" href="universal-algebra.algebraic-theories.html#1050" class="Bound">e</a> <a id="1052" class="Symbol">=</a> <a id="1054" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1058" href="universal-algebra.algebraic-theories.html#1047" class="Bound">Th</a> <a id="1061" href="universal-algebra.algebraic-theories.html#1050" class="Bound">e</a>
</pre>