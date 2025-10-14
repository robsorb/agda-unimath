# Alternating groups

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="finite-group-theory.alternating-groups.html" class="Module">finite-group-theory.alternating-groups</a> <a id="77" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="133" class="Keyword">open</a> <a id="138" class="Keyword">import</a> <a id="145" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="finite-group-theory.sign-homomorphism.html" class="Module">finite-group-theory.sign-homomorphism</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="group-theory.kernels-homomorphisms-groups.html" class="Module">group-theory.kernels-homomorphisms-groups</a>
<a id="324" class="Keyword">open</a> <a id="329" class="Keyword">import</a> <a id="336" href="group-theory.symmetric-groups.html" class="Module">group-theory.symmetric-groups</a>

<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="416" class="Keyword">open</a> <a id="421" class="Keyword">import</a> <a id="428" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

The alternating group on a finite set `X` is the group of even permutations of
`X`, i.e. it is the kernel of the sign homomorphism `Aut(X) → Aut(2)`.

## Definition

<pre class="Agda"><a id="674" class="Keyword">module</a> <a id="681" href="finite-group-theory.alternating-groups.html#681" class="Module">_</a>
  <a id="685" class="Symbol">{</a><a id="686" href="finite-group-theory.alternating-groups.html#686" class="Bound">l</a><a id="687" class="Symbol">}</a> <a id="689" class="Symbol">(</a><a id="690" href="finite-group-theory.alternating-groups.html#690" class="Bound">n</a> <a id="692" class="Symbol">:</a> <a id="694" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="695" class="Symbol">)</a> <a id="697" class="Symbol">(</a><a id="698" href="finite-group-theory.alternating-groups.html#698" class="Bound">X</a> <a id="700" class="Symbol">:</a> <a id="702" href="univalent-combinatorics.finite-types.html#3324" class="Function">Type-With-Cardinality-ℕ</a> <a id="726" href="finite-group-theory.alternating-groups.html#686" class="Bound">l</a> <a id="728" href="finite-group-theory.alternating-groups.html#690" class="Bound">n</a><a id="729" class="Symbol">)</a>
  <a id="733" class="Keyword">where</a>
  <a id="741" href="finite-group-theory.alternating-groups.html#741" class="Function">alternating-Group</a> <a id="759" class="Symbol">:</a> <a id="761" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="767" href="finite-group-theory.alternating-groups.html#686" class="Bound">l</a>
  <a id="771" href="finite-group-theory.alternating-groups.html#741" class="Function">alternating-Group</a> <a id="789" class="Symbol">=</a> <a id="791" href="group-theory.kernels-homomorphisms-groups.html#2551" class="Function">group-kernel-hom-Group</a>
    <a id="818" class="Symbol">(</a> <a id="820" href="group-theory.symmetric-groups.html#2342" class="Function">symmetric-Group</a> <a id="836" class="Symbol">(</a><a id="837" href="univalent-combinatorics.finite-types.html#14579" class="Function">set-Type-With-Cardinality-ℕ</a> <a id="865" href="finite-group-theory.alternating-groups.html#690" class="Bound">n</a> <a id="867" href="finite-group-theory.alternating-groups.html#698" class="Bound">X</a><a id="868" class="Symbol">))</a>
    <a id="875" class="Symbol">(</a> <a id="877" href="group-theory.symmetric-groups.html#2342" class="Function">symmetric-Group</a> <a id="893" class="Symbol">(</a><a id="894" href="univalent-combinatorics.standard-finite-types.html#2084" class="Function">Fin-Set</a> <a id="902" class="Number">2</a><a id="903" class="Symbol">))</a>
    <a id="910" class="Symbol">(</a> <a id="912" href="finite-group-theory.sign-homomorphism.html#13844" class="Function">sign-homomorphism</a> <a id="930" href="finite-group-theory.alternating-groups.html#690" class="Bound">n</a> <a id="932" href="finite-group-theory.alternating-groups.html#698" class="Bound">X</a><a id="933" class="Symbol">)</a>
</pre>