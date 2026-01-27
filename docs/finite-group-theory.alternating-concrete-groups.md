# Alternating concrete groups

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="finite-group-theory.alternating-concrete-groups.html" class="Module">finite-group-theory.alternating-concrete-groups</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="205" class="Keyword">open</a> <a id="210" class="Keyword">import</a> <a id="217" href="finite-group-theory.cartier-delooping-sign-homomorphism.html" class="Module">finite-group-theory.cartier-delooping-sign-homomorphism</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="finite-group-theory.finite-type-groups.html" class="Module">finite-group-theory.finite-type-groups</a>

<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="365" class="Keyword">open</a> <a id="370" class="Keyword">import</a> <a id="377" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="406" class="Keyword">open</a> <a id="411" class="Keyword">import</a> <a id="418" href="group-theory.kernels-homomorphisms-concrete-groups.html" class="Module">group-theory.kernels-homomorphisms-concrete-groups</a>
</pre>
</details>

## Idea

The alternating concrete groups are the kernels of the concrete sign
homomorphism

## Definition

<pre class="Agda"><a id="601" class="Keyword">module</a> <a id="608" href="finite-group-theory.alternating-concrete-groups.html#608" class="Module">_</a>
  <a id="612" class="Symbol">(</a><a id="613" href="finite-group-theory.alternating-concrete-groups.html#613" class="Bound">n</a> <a id="615" class="Symbol">:</a> <a id="617" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="618" class="Symbol">)</a>
  <a id="622" class="Keyword">where</a>

  <a id="631" href="finite-group-theory.alternating-concrete-groups.html#631" class="Function">alternating-Concrete-Group</a> <a id="658" class="Symbol">:</a> <a id="660" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="675" class="Symbol">(</a><a id="676" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="681" class="Symbol">(</a><a id="682" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="687" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="692" class="Symbol">))</a>
  <a id="697" href="finite-group-theory.alternating-concrete-groups.html#631" class="Function">alternating-Concrete-Group</a> <a id="724" class="Symbol">=</a>
    <a id="730" href="group-theory.kernels-homomorphisms-concrete-groups.html#3275" class="Function">concrete-group-kernel-hom-Concrete-Group</a>
      <a id="777" class="Symbol">(</a> <a id="779" href="finite-group-theory.finite-type-groups.html#3080" class="Function">Type-With-Cardinality-ℕ-Concrete-Group</a> <a id="818" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="824" href="finite-group-theory.alternating-concrete-groups.html#613" class="Bound">n</a><a id="825" class="Symbol">)</a>
      <a id="833" class="Symbol">(</a> <a id="835" href="finite-group-theory.finite-type-groups.html#3080" class="Function">Type-With-Cardinality-ℕ-Concrete-Group</a> <a id="874" class="Symbol">(</a><a id="875" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="880" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="885" class="Symbol">)</a> <a id="887" class="Number">2</a><a id="888" class="Symbol">)</a>
      <a id="896" class="Symbol">(</a> <a id="898" href="finite-group-theory.cartier-delooping-sign-homomorphism.html#4839" class="Function">cartier-delooping-sign</a> <a id="921" href="finite-group-theory.alternating-concrete-groups.html#613" class="Bound">n</a><a id="922" class="Symbol">)</a>
</pre>