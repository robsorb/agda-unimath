# Alkynes

<pre class="Agda"><a id="20" class="Keyword">module</a> <a id="27" href="organic-chemistry.alkynes.html" class="Module">organic-chemistry.alkynes</a> <a id="53" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="109" class="Keyword">open</a> <a id="114" class="Keyword">import</a> <a id="121" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="207" class="Keyword">open</a> <a id="212" class="Keyword">import</a> <a id="219" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="241" class="Keyword">open</a> <a id="246" class="Keyword">import</a> <a id="253" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="organic-chemistry.hydrocarbons.html" class="Module">organic-chemistry.hydrocarbons</a>
<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="organic-chemistry.saturated-carbons.html" class="Module">organic-chemistry.saturated-carbons</a>

<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
</pre>
</details>

## Idea

An **n-alkyne** is a hydrocarbon equipped with a choice of $n$ carbons, each of
which has a triple bond.

## Definition

<pre class="Agda"><a id="n-alkyne"></a><a id="577" href="organic-chemistry.alkynes.html#577" class="Function">n-alkyne</a> <a id="586" class="Symbol">:</a> <a id="588" class="Symbol">{</a><a id="589" href="organic-chemistry.alkynes.html#589" class="Bound">l1</a> <a id="592" href="organic-chemistry.alkynes.html#592" class="Bound">l2</a> <a id="595" class="Symbol">:</a> <a id="597" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="602" class="Symbol">}</a> <a id="604" class="Symbol">→</a> <a id="606" href="organic-chemistry.hydrocarbons.html#1569" class="Function">hydrocarbon</a> <a id="618" href="organic-chemistry.alkynes.html#589" class="Bound">l1</a> <a id="621" href="organic-chemistry.alkynes.html#592" class="Bound">l2</a> <a id="624" class="Symbol">→</a> <a id="626" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="628" class="Symbol">→</a> <a id="630" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="633" class="Symbol">(</a><a id="634" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="639" href="organic-chemistry.alkynes.html#589" class="Bound">l1</a> <a id="642" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="644" href="organic-chemistry.alkynes.html#592" class="Bound">l2</a><a id="646" class="Symbol">)</a>
<a id="648" href="organic-chemistry.alkynes.html#577" class="Function">n-alkyne</a> <a id="657" class="Symbol">{</a><a id="658" href="organic-chemistry.alkynes.html#658" class="Bound">l1</a><a id="660" class="Symbol">}</a> <a id="662" class="Symbol">{</a><a id="663" href="organic-chemistry.alkynes.html#663" class="Bound">l2</a><a id="665" class="Symbol">}</a> <a id="667" href="organic-chemistry.alkynes.html#667" class="Bound">H</a> <a id="669" href="organic-chemistry.alkynes.html#669" class="Bound">n</a> <a id="671" class="Symbol">=</a>
  <a id="675" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="677" class="Symbol">(</a> <a id="679" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="703" href="organic-chemistry.alkynes.html#658" class="Bound">l1</a> <a id="706" href="organic-chemistry.alkynes.html#669" class="Bound">n</a><a id="707" class="Symbol">)</a>
    <a id="713" class="Symbol">(</a> <a id="715" class="Symbol">λ</a> <a id="717" href="organic-chemistry.alkynes.html#717" class="Bound">carbons</a> <a id="725" class="Symbol">→</a>
      <a id="733" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="735" class="Symbol">(</a> <a id="737" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="766" href="organic-chemistry.alkynes.html#669" class="Bound">n</a> <a id="768" href="organic-chemistry.alkynes.html#717" class="Bound">carbons</a> <a id="776" href="foundation-core.embeddings.html#1627" class="Function Operator">↪</a> <a id="778" href="organic-chemistry.hydrocarbons.html#2862" class="Function">vertex-hydrocarbon</a> <a id="797" href="organic-chemistry.alkynes.html#667" class="Bound">H</a><a id="798" class="Symbol">)</a>
        <a id="808" class="Symbol">(</a> <a id="810" class="Symbol">λ</a> <a id="812" href="organic-chemistry.alkynes.html#812" class="Bound">embed-carbons</a> <a id="826" class="Symbol">→</a>
          <a id="838" class="Symbol">(</a><a id="839" href="organic-chemistry.alkynes.html#839" class="Bound">c</a> <a id="841" class="Symbol">:</a> <a id="843" href="univalent-combinatorics.finite-types.html#3442" class="Function">type-Type-With-Cardinality-ℕ</a> <a id="872" href="organic-chemistry.alkynes.html#669" class="Bound">n</a> <a id="874" href="organic-chemistry.alkynes.html#717" class="Bound">carbons</a><a id="881" class="Symbol">)</a> <a id="883" class="Symbol">→</a>
          <a id="895" href="organic-chemistry.saturated-carbons.html#1884" class="Function">has-triple-bond-hydrocarbon</a> <a id="923" href="organic-chemistry.alkynes.html#667" class="Bound">H</a> <a id="925" class="Symbol">(</a><a id="926" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="930" href="organic-chemistry.alkynes.html#812" class="Bound">embed-carbons</a> <a id="944" href="organic-chemistry.alkynes.html#839" class="Bound">c</a><a id="945" class="Symbol">)))</a>
</pre>