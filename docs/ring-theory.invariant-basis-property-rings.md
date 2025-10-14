# The invariant basis property of rings

<pre class="Agda"><a id="50" class="Keyword">module</a> <a id="57" href="ring-theory.invariant-basis-property-rings.html" class="Module">ring-theory.invariant-basis-property-rings</a> <a id="100" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="210" class="Keyword">open</a> <a id="215" class="Keyword">import</a> <a id="222" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="288" class="Keyword">open</a> <a id="293" class="Keyword">import</a> <a id="300" href="ring-theory.dependent-products-rings.html" class="Module">ring-theory.dependent-products-rings</a>
<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="ring-theory.isomorphisms-rings.html" class="Module">ring-theory.isomorphisms-rings</a>
<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>

<a id="411" class="Keyword">open</a> <a id="416" class="Keyword">import</a> <a id="423" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

A ring R is said to satisfy the invariant basis property if `R^m ≅ R^n` implies
`m = n` for any two natural numbers `m` and `n`.

## Definition

<pre class="Agda"><a id="invariant-basis-property-Ring"></a><a id="648" href="ring-theory.invariant-basis-property-rings.html#648" class="Function">invariant-basis-property-Ring</a> <a id="678" class="Symbol">:</a>
  <a id="682" class="Symbol">{</a><a id="683" href="ring-theory.invariant-basis-property-rings.html#683" class="Bound">l1</a> <a id="686" class="Symbol">:</a> <a id="688" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="693" class="Symbol">}</a> <a id="695" class="Symbol">→</a> <a id="697" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="702" href="ring-theory.invariant-basis-property-rings.html#683" class="Bound">l1</a> <a id="705" class="Symbol">→</a> <a id="707" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="710" href="ring-theory.invariant-basis-property-rings.html#683" class="Bound">l1</a>
<a id="713" href="ring-theory.invariant-basis-property-rings.html#648" class="Function">invariant-basis-property-Ring</a> <a id="743" href="ring-theory.invariant-basis-property-rings.html#743" class="Bound">R</a> <a id="745" class="Symbol">=</a>
  <a id="749" class="Symbol">(</a><a id="750" href="ring-theory.invariant-basis-property-rings.html#750" class="Bound">m</a> <a id="752" href="ring-theory.invariant-basis-property-rings.html#752" class="Bound">n</a> <a id="754" class="Symbol">:</a> <a id="756" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="757" class="Symbol">)</a> <a id="759" class="Symbol">→</a>
  <a id="763" href="ring-theory.isomorphisms-rings.html#3857" class="Function">iso-Ring</a> <a id="772" class="Symbol">(</a><a id="773" href="ring-theory.dependent-products-rings.html#4234" class="Function">Π-Ring</a> <a id="780" class="Symbol">(</a><a id="781" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="785" href="ring-theory.invariant-basis-property-rings.html#750" class="Bound">m</a><a id="786" class="Symbol">)</a> <a id="788" class="Symbol">(λ</a> <a id="791" href="ring-theory.invariant-basis-property-rings.html#791" class="Bound">i</a> <a id="793" class="Symbol">→</a> <a id="795" href="ring-theory.invariant-basis-property-rings.html#743" class="Bound">R</a><a id="796" class="Symbol">))</a> <a id="799" class="Symbol">(</a><a id="800" href="ring-theory.dependent-products-rings.html#4234" class="Function">Π-Ring</a> <a id="807" class="Symbol">(</a><a id="808" href="univalent-combinatorics.standard-finite-types.html#2192" class="Function">Fin</a> <a id="812" href="ring-theory.invariant-basis-property-rings.html#752" class="Bound">n</a><a id="813" class="Symbol">)</a> <a id="815" class="Symbol">(λ</a> <a id="818" href="ring-theory.invariant-basis-property-rings.html#818" class="Bound">i</a> <a id="820" class="Symbol">→</a> <a id="822" href="ring-theory.invariant-basis-property-rings.html#743" class="Bound">R</a><a id="823" class="Symbol">))</a> <a id="826" class="Symbol">→</a>
  <a id="830" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a> <a id="833" href="ring-theory.invariant-basis-property-rings.html#750" class="Bound">m</a> <a id="835" href="ring-theory.invariant-basis-property-rings.html#752" class="Bound">n</a>
</pre>