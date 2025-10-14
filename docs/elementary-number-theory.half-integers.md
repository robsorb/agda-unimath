# The half-integers

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="elementary-number-theory.half-integers.html" class="Module">elementary-number-theory.half-integers</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>

<a id="234" class="Keyword">open</a> <a id="239" class="Keyword">import</a> <a id="246" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

The **half-integers** are the numbers of the form `x + ½`, where `x : ℤ`.

## Definition

### The half-integers

<pre class="Agda"><a id="ℤ+½"></a><a id="459" href="elementary-number-theory.half-integers.html#459" class="Function">ℤ+½</a> <a id="463" class="Symbol">:</a> <a id="465" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="468" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="474" href="elementary-number-theory.half-integers.html#459" class="Function">ℤ+½</a> <a id="478" class="Symbol">=</a> <a id="480" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a>
</pre>
### The disjoint union of the half-integers with the integers

<pre class="Agda"><a id="½ℤ"></a><a id="558" href="elementary-number-theory.half-integers.html#558" class="Function">½ℤ</a> <a id="561" class="Symbol">:</a> <a id="563" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="566" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
<a id="572" href="elementary-number-theory.half-integers.html#558" class="Function">½ℤ</a> <a id="575" class="Symbol">=</a> <a id="577" href="elementary-number-theory.half-integers.html#459" class="Function">ℤ+½</a> <a id="581" href="foundation-core.coproduct-types.html#389" class="Datatype Operator">+</a> <a id="583" href="elementary-number-theory.integers.html#1293" class="Function">ℤ</a>
</pre>
### The zero element of `½ℤ`

<pre class="Agda"><a id="zero-½ℤ"></a><a id="628" href="elementary-number-theory.half-integers.html#628" class="Function">zero-½ℤ</a> <a id="636" class="Symbol">:</a> <a id="638" href="elementary-number-theory.half-integers.html#558" class="Function">½ℤ</a>
<a id="641" href="elementary-number-theory.half-integers.html#628" class="Function">zero-½ℤ</a> <a id="649" class="Symbol">=</a> <a id="651" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="655" href="elementary-number-theory.integers.html#1569" class="Function">zero-ℤ</a>
</pre>
### Addition on `½ℤ`

<pre class="Agda"><a id="add-½ℤ"></a><a id="697" href="elementary-number-theory.half-integers.html#697" class="Function">add-½ℤ</a> <a id="704" class="Symbol">:</a> <a id="706" href="elementary-number-theory.half-integers.html#558" class="Function">½ℤ</a> <a id="709" class="Symbol">→</a> <a id="711" href="elementary-number-theory.half-integers.html#558" class="Function">½ℤ</a> <a id="714" class="Symbol">→</a> <a id="716" href="elementary-number-theory.half-integers.html#558" class="Function">½ℤ</a>
<a id="719" href="elementary-number-theory.half-integers.html#697" class="Function">add-½ℤ</a> <a id="726" class="Symbol">(</a><a id="727" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="731" href="elementary-number-theory.half-integers.html#731" class="Bound">x</a><a id="732" class="Symbol">)</a> <a id="734" class="Symbol">(</a><a id="735" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="739" href="elementary-number-theory.half-integers.html#739" class="Bound">y</a><a id="740" class="Symbol">)</a> <a id="742" class="Symbol">=</a> <a id="744" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="748" class="Symbol">(</a><a id="749" href="elementary-number-theory.integers.html#2848" class="Function">succ-ℤ</a> <a id="756" class="Symbol">(</a><a id="757" href="elementary-number-theory.half-integers.html#731" class="Bound">x</a> <a id="759" href="elementary-number-theory.addition-integers.html#1604" class="Function Operator">+ℤ</a> <a id="762" href="elementary-number-theory.half-integers.html#739" class="Bound">y</a><a id="763" class="Symbol">))</a>
<a id="766" href="elementary-number-theory.half-integers.html#697" class="Function">add-½ℤ</a> <a id="773" class="Symbol">(</a><a id="774" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="778" href="elementary-number-theory.half-integers.html#778" class="Bound">x</a><a id="779" class="Symbol">)</a> <a id="781" class="Symbol">(</a><a id="782" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="786" href="elementary-number-theory.half-integers.html#786" class="Bound">y</a><a id="787" class="Symbol">)</a> <a id="789" class="Symbol">=</a> <a id="791" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="795" class="Symbol">(</a><a id="796" href="elementary-number-theory.half-integers.html#778" class="Bound">x</a> <a id="798" href="elementary-number-theory.addition-integers.html#1604" class="Function Operator">+ℤ</a> <a id="801" href="elementary-number-theory.half-integers.html#786" class="Bound">y</a><a id="802" class="Symbol">)</a>
<a id="804" href="elementary-number-theory.half-integers.html#697" class="Function">add-½ℤ</a> <a id="811" class="Symbol">(</a><a id="812" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="816" href="elementary-number-theory.half-integers.html#816" class="Bound">x</a><a id="817" class="Symbol">)</a> <a id="819" class="Symbol">(</a><a id="820" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="824" href="elementary-number-theory.half-integers.html#824" class="Bound">y</a><a id="825" class="Symbol">)</a> <a id="827" class="Symbol">=</a> <a id="829" href="foundation-core.coproduct-types.html#458" class="InductiveConstructor">inl</a> <a id="833" class="Symbol">(</a><a id="834" href="elementary-number-theory.half-integers.html#816" class="Bound">x</a> <a id="836" href="elementary-number-theory.addition-integers.html#1604" class="Function Operator">+ℤ</a> <a id="839" href="elementary-number-theory.half-integers.html#824" class="Bound">y</a><a id="840" class="Symbol">)</a>
<a id="842" href="elementary-number-theory.half-integers.html#697" class="Function">add-½ℤ</a> <a id="849" class="Symbol">(</a><a id="850" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="854" href="elementary-number-theory.half-integers.html#854" class="Bound">x</a><a id="855" class="Symbol">)</a> <a id="857" class="Symbol">(</a><a id="858" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="862" href="elementary-number-theory.half-integers.html#862" class="Bound">y</a><a id="863" class="Symbol">)</a> <a id="865" class="Symbol">=</a> <a id="867" href="foundation-core.coproduct-types.html#476" class="InductiveConstructor">inr</a> <a id="871" class="Symbol">(</a><a id="872" href="elementary-number-theory.half-integers.html#854" class="Bound">x</a> <a id="874" href="elementary-number-theory.addition-integers.html#1604" class="Function Operator">+ℤ</a> <a id="877" href="elementary-number-theory.half-integers.html#862" class="Bound">y</a><a id="878" class="Symbol">)</a>

<a id="881" class="Keyword">infixl</a> <a id="888" class="Number">35</a> <a id="891" href="elementary-number-theory.half-integers.html#897" class="Function Operator">_+½ℤ_</a>
<a id="_+½ℤ_"></a><a id="897" href="elementary-number-theory.half-integers.html#897" class="Function Operator">_+½ℤ_</a> <a id="903" class="Symbol">=</a> <a id="905" href="elementary-number-theory.half-integers.html#697" class="Function">add-½ℤ</a>
</pre>