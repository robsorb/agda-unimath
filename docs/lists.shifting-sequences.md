# Shifting sequences

<pre class="Agda"><a id="31" class="Keyword">module</a> <a id="38" href="lists.shifting-sequences.html" class="Module">lists.shifting-sequences</a> <a id="63" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="119" class="Keyword">open</a> <a id="124" class="Keyword">import</a> <a id="131" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Given a sequence `f : ℕ → A` and an element `a : A` we define
`shift-ℕ a f : ℕ → A` by

```text
  shift-ℕ a f zero-ℕ := a
  shift-ℕ a f (succ-ℕ n) := f n
```

## Definition

<pre class="Agda"><a id="shift-ℕ"></a><a id="420" href="lists.shifting-sequences.html#420" class="Function">shift-ℕ</a> <a id="428" class="Symbol">:</a> <a id="430" class="Symbol">{</a><a id="431" href="lists.shifting-sequences.html#431" class="Bound">l</a> <a id="433" class="Symbol">:</a> <a id="435" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="440" class="Symbol">}</a> <a id="442" class="Symbol">{</a><a id="443" href="lists.shifting-sequences.html#443" class="Bound">A</a> <a id="445" class="Symbol">:</a> <a id="447" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="450" href="lists.shifting-sequences.html#431" class="Bound">l</a><a id="451" class="Symbol">}</a> <a id="453" class="Symbol">(</a><a id="454" href="lists.shifting-sequences.html#454" class="Bound">a</a> <a id="456" class="Symbol">:</a> <a id="458" href="lists.shifting-sequences.html#443" class="Bound">A</a><a id="459" class="Symbol">)</a> <a id="461" class="Symbol">(</a><a id="462" href="lists.shifting-sequences.html#462" class="Bound">f</a> <a id="464" class="Symbol">:</a> <a id="466" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="468" class="Symbol">→</a> <a id="470" href="lists.shifting-sequences.html#443" class="Bound">A</a><a id="471" class="Symbol">)</a> <a id="473" class="Symbol">→</a> <a id="475" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="477" class="Symbol">→</a> <a id="479" href="lists.shifting-sequences.html#443" class="Bound">A</a>
<a id="481" href="lists.shifting-sequences.html#420" class="Function">shift-ℕ</a> <a id="489" href="lists.shifting-sequences.html#489" class="Bound">a</a> <a id="491" href="lists.shifting-sequences.html#491" class="Bound">f</a> <a id="493" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="500" class="Symbol">=</a> <a id="502" href="lists.shifting-sequences.html#489" class="Bound">a</a>
<a id="504" href="lists.shifting-sequences.html#420" class="Function">shift-ℕ</a> <a id="512" href="lists.shifting-sequences.html#512" class="Bound">a</a> <a id="514" href="lists.shifting-sequences.html#514" class="Bound">f</a> <a id="516" class="Symbol">(</a><a id="517" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="524" href="lists.shifting-sequences.html#524" class="Bound">n</a><a id="525" class="Symbol">)</a> <a id="527" class="Symbol">=</a> <a id="529" href="lists.shifting-sequences.html#514" class="Bound">f</a> <a id="531" href="lists.shifting-sequences.html#524" class="Bound">n</a>
</pre>