# The Ackermann function

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="elementary-number-theory.ackermann-function.html" class="Module">elementary-number-theory.ackermann-function</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
</pre>
</details>

## Idea

The
{{#concept "Ackermann-Péter function" WD="Ackermann function" WDID=Q341835 Agda=ackermann-péter-ℕ}}
is a fast growing binary operation on the
[natural numbers](elementary-number-theory.natural-numbers.md).

## Definition

### The Ackermann-Péter function

<pre class="Agda"><a id="ackermann-péter-ℕ"></a><a id="489" href="elementary-number-theory.ackermann-function.html#489" class="Function">ackermann-péter-ℕ</a> <a id="507" class="Symbol">:</a> <a id="509" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="511" class="Symbol">→</a> <a id="513" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="515" class="Symbol">→</a> <a id="517" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="519" href="elementary-number-theory.ackermann-function.html#489" class="Function">ackermann-péter-ℕ</a> <a id="537" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="544" href="elementary-number-theory.ackermann-function.html#544" class="Bound">n</a> <a id="546" class="Symbol">=</a>
  <a id="550" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="557" href="elementary-number-theory.ackermann-function.html#544" class="Bound">n</a>
<a id="559" href="elementary-number-theory.ackermann-function.html#489" class="Function">ackermann-péter-ℕ</a> <a id="577" class="Symbol">(</a><a id="578" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="585" href="elementary-number-theory.ackermann-function.html#585" class="Bound">m</a><a id="586" class="Symbol">)</a> <a id="588" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="595" class="Symbol">=</a>
  <a id="599" href="elementary-number-theory.ackermann-function.html#489" class="Function">ackermann-péter-ℕ</a> <a id="617" href="elementary-number-theory.ackermann-function.html#585" class="Bound">m</a> <a id="619" class="Number">1</a>
<a id="621" href="elementary-number-theory.ackermann-function.html#489" class="Function">ackermann-péter-ℕ</a> <a id="639" class="Symbol">(</a><a id="640" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="647" href="elementary-number-theory.ackermann-function.html#647" class="Bound">m</a><a id="648" class="Symbol">)</a> <a id="650" class="Symbol">(</a><a id="651" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="658" href="elementary-number-theory.ackermann-function.html#658" class="Bound">n</a><a id="659" class="Symbol">)</a> <a id="661" class="Symbol">=</a>
  <a id="665" href="elementary-number-theory.ackermann-function.html#489" class="Function">ackermann-péter-ℕ</a> <a id="683" href="elementary-number-theory.ackermann-function.html#647" class="Bound">m</a> <a id="685" class="Symbol">(</a><a id="686" href="elementary-number-theory.ackermann-function.html#489" class="Function">ackermann-péter-ℕ</a> <a id="704" class="Symbol">(</a><a id="705" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="712" href="elementary-number-theory.ackermann-function.html#647" class="Bound">m</a><a id="713" class="Symbol">)</a> <a id="715" href="elementary-number-theory.ackermann-function.html#658" class="Bound">n</a><a id="716" class="Symbol">)</a>
</pre>
### The simplified Ackermann function

<pre class="Agda"><a id="simplified-ackermann-ℕ"></a><a id="770" href="elementary-number-theory.ackermann-function.html#770" class="Function">simplified-ackermann-ℕ</a> <a id="793" class="Symbol">:</a> <a id="795" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="797" class="Symbol">→</a> <a id="799" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a>
<a id="801" href="elementary-number-theory.ackermann-function.html#770" class="Function">simplified-ackermann-ℕ</a> <a id="824" href="elementary-number-theory.ackermann-function.html#824" class="Bound">n</a> <a id="826" class="Symbol">=</a> <a id="828" href="elementary-number-theory.ackermann-function.html#489" class="Function">ackermann-péter-ℕ</a> <a id="846" href="elementary-number-theory.ackermann-function.html#824" class="Bound">n</a> <a id="848" href="elementary-number-theory.ackermann-function.html#824" class="Bound">n</a>
</pre>