# Abstract equations over signatures

<pre class="Agda"><a id="47" class="Keyword">module</a> <a id="54" href="universal-algebra.abstract-equations-over-signatures.html" class="Module">universal-algebra.abstract-equations-over-signatures</a> <a id="107" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="163" class="Keyword">open</a> <a id="168" class="Keyword">import</a> <a id="175" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="universal-algebra.signatures.html" class="Module">universal-algebra.signatures</a>
<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="universal-algebra.terms-over-signatures.html" class="Module">universal-algebra.terms-over-signatures</a>
</pre>
</details>

## Idea

An **abstract equation** over a signature `σ` is a statement of a form "`x`
equals `y`", where `x` and `y` are terms over `σ`. Thus, the data of an abstract
equation is simply two terms over a common signature.

## Definitions

### Abstract equations

<pre class="Agda"><a id="673" class="Keyword">module</a> <a id="680" href="universal-algebra.abstract-equations-over-signatures.html#680" class="Module">_</a>
  <a id="684" class="Symbol">{</a><a id="685" href="universal-algebra.abstract-equations-over-signatures.html#685" class="Bound">l1</a> <a id="688" class="Symbol">:</a> <a id="690" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="695" class="Symbol">}</a> <a id="697" class="Symbol">(</a><a id="698" href="universal-algebra.abstract-equations-over-signatures.html#698" class="Bound">σ</a> <a id="700" class="Symbol">:</a> <a id="702" href="universal-algebra.signatures.html#506" class="Function">signature</a> <a id="712" href="universal-algebra.abstract-equations-over-signatures.html#685" class="Bound">l1</a><a id="714" class="Symbol">)</a>
  <a id="718" class="Keyword">where</a>

  <a id="727" href="universal-algebra.abstract-equations-over-signatures.html#727" class="Function">Abstract-Equation</a> <a id="745" class="Symbol">:</a> <a id="747" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="750" href="universal-algebra.abstract-equations-over-signatures.html#685" class="Bound">l1</a>
  <a id="755" href="universal-algebra.abstract-equations-over-signatures.html#727" class="Function">Abstract-Equation</a> <a id="773" class="Symbol">=</a> <a id="775" href="universal-algebra.terms-over-signatures.html#1111" class="Datatype">Term</a> <a id="780" href="universal-algebra.abstract-equations-over-signatures.html#698" class="Bound">σ</a> <a id="782" href="foundation-core.cartesian-product-types.html#585" class="Function Operator">×</a> <a id="784" href="universal-algebra.terms-over-signatures.html#1111" class="Datatype">Term</a> <a id="789" href="universal-algebra.abstract-equations-over-signatures.html#698" class="Bound">σ</a>

  <a id="794" href="universal-algebra.abstract-equations-over-signatures.html#794" class="Function">lhs-Abstract-Equation</a> <a id="816" class="Symbol">:</a> <a id="818" href="universal-algebra.abstract-equations-over-signatures.html#727" class="Function">Abstract-Equation</a> <a id="836" class="Symbol">→</a> <a id="838" href="universal-algebra.terms-over-signatures.html#1111" class="Datatype">Term</a> <a id="843" href="universal-algebra.abstract-equations-over-signatures.html#698" class="Bound">σ</a>
  <a id="847" href="universal-algebra.abstract-equations-over-signatures.html#794" class="Function">lhs-Abstract-Equation</a> <a id="869" class="Symbol">=</a> <a id="871" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="878" href="universal-algebra.abstract-equations-over-signatures.html#878" class="Function">rhs-Abstract-Equation</a> <a id="900" class="Symbol">:</a> <a id="902" href="universal-algebra.abstract-equations-over-signatures.html#727" class="Function">Abstract-Equation</a> <a id="920" class="Symbol">→</a> <a id="922" href="universal-algebra.terms-over-signatures.html#1111" class="Datatype">Term</a> <a id="927" href="universal-algebra.abstract-equations-over-signatures.html#698" class="Bound">σ</a>
  <a id="931" href="universal-algebra.abstract-equations-over-signatures.html#878" class="Function">rhs-Abstract-Equation</a> <a id="953" class="Symbol">=</a> <a id="955" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>