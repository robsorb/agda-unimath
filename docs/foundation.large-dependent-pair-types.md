# Large dependent pair types

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="foundation.large-dependent-pair-types.html" class="Module">foundation.large-dependent-pair-types</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

When `B` is a family of large types over `A`, then we can form the large type of
pairs `pairω a b` consisting of an element `a : A` and an element `b : B a`.
Such pairs are called dependent pairs, since the type of the second component
depends on the first component.

## Definition

<pre class="Agda"><a id="497" class="Keyword">record</a> <a id="Σω"></a><a id="504" href="foundation.large-dependent-pair-types.html#504" class="Record">Σω</a> <a id="507" class="Symbol">(</a><a id="508" href="foundation.large-dependent-pair-types.html#508" class="Bound">A</a> <a id="510" class="Symbol">:</a> <a id="512" href="Agda.Primitive.html#512" class="Primitive">UUω</a><a id="515" class="Symbol">)</a> <a id="517" class="Symbol">(</a><a id="518" href="foundation.large-dependent-pair-types.html#518" class="Bound">B</a> <a id="520" class="Symbol">:</a> <a id="522" href="foundation.large-dependent-pair-types.html#508" class="Bound">A</a> <a id="524" class="Symbol">→</a> <a id="526" href="Agda.Primitive.html#512" class="Primitive">UUω</a><a id="529" class="Symbol">)</a> <a id="531" class="Symbol">:</a> <a id="533" href="Agda.Primitive.html#512" class="Primitive">UUω</a> <a id="537" class="Keyword">where</a>
  <a id="545" class="Keyword">constructor</a> <a id="pairω"></a><a id="557" href="foundation.large-dependent-pair-types.html#557" class="InductiveConstructor">pairω</a>
  <a id="565" class="Keyword">field</a>
    <a id="Σω.prω1"></a><a id="575" href="foundation.large-dependent-pair-types.html#575" class="Field">prω1</a> <a id="580" class="Symbol">:</a> <a id="582" href="foundation.large-dependent-pair-types.html#508" class="Bound">A</a>
    <a id="Σω.prω2"></a><a id="588" href="foundation.large-dependent-pair-types.html#588" class="Field">prω2</a> <a id="593" class="Symbol">:</a> <a id="595" href="foundation.large-dependent-pair-types.html#518" class="Bound">B</a> <a id="597" href="foundation.large-dependent-pair-types.html#575" class="Field">prω1</a>

<a id="603" class="Keyword">open</a> <a id="608" href="foundation.large-dependent-pair-types.html#504" class="Module">Σω</a> <a id="611" class="Keyword">public</a>

<a id="619" class="Keyword">infixr</a> <a id="626" class="Number">3</a> <a id="628" href="foundation.large-dependent-pair-types.html#641" class="InductiveConstructor Operator">_,ω_</a>
<a id="633" class="Keyword">pattern</a> <a id="_,ω_"></a><a id="641" href="foundation.large-dependent-pair-types.html#641" class="InductiveConstructor Operator">_,ω_</a> <a id="646" href="foundation.large-dependent-pair-types.html#658" class="Bound">a</a> <a id="648" href="foundation.large-dependent-pair-types.html#660" class="Bound">b</a> <a id="650" class="Symbol">=</a> <a id="652" href="foundation.large-dependent-pair-types.html#557" class="InductiveConstructor">pairω</a> <a id="658" href="foundation.large-dependent-pair-types.html#658" class="Bound">a</a> <a id="660" href="foundation.large-dependent-pair-types.html#660" class="Bound">b</a>
</pre>
### Families on dependent pair types

<pre class="Agda"><a id="713" class="Keyword">module</a> <a id="720" href="foundation.large-dependent-pair-types.html#720" class="Module">_</a>
  <a id="724" class="Symbol">{</a><a id="725" href="foundation.large-dependent-pair-types.html#725" class="Bound">l</a> <a id="727" class="Symbol">:</a> <a id="729" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="734" class="Symbol">}</a> <a id="736" class="Symbol">{</a><a id="737" href="foundation.large-dependent-pair-types.html#737" class="Bound">A</a> <a id="739" class="Symbol">:</a> <a id="741" href="Agda.Primitive.html#512" class="Primitive">UUω</a><a id="744" class="Symbol">}</a> <a id="746" class="Symbol">{</a><a id="747" href="foundation.large-dependent-pair-types.html#747" class="Bound">B</a> <a id="749" class="Symbol">:</a> <a id="751" href="foundation.large-dependent-pair-types.html#737" class="Bound">A</a> <a id="753" class="Symbol">→</a> <a id="755" href="Agda.Primitive.html#512" class="Primitive">UUω</a><a id="758" class="Symbol">}</a>
  <a id="762" class="Keyword">where</a>

  <a id="771" href="foundation.large-dependent-pair-types.html#771" class="Function">fam-Σω</a> <a id="778" class="Symbol">:</a> <a id="780" class="Symbol">((</a><a id="782" href="foundation.large-dependent-pair-types.html#782" class="Bound">x</a> <a id="784" class="Symbol">:</a> <a id="786" href="foundation.large-dependent-pair-types.html#737" class="Bound">A</a><a id="787" class="Symbol">)</a> <a id="789" class="Symbol">→</a> <a id="791" href="foundation.large-dependent-pair-types.html#747" class="Bound">B</a> <a id="793" href="foundation.large-dependent-pair-types.html#782" class="Bound">x</a> <a id="795" class="Symbol">→</a> <a id="797" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="800" href="foundation.large-dependent-pair-types.html#725" class="Bound">l</a><a id="801" class="Symbol">)</a> <a id="803" class="Symbol">→</a> <a id="805" href="foundation.large-dependent-pair-types.html#504" class="Record">Σω</a> <a id="808" href="foundation.large-dependent-pair-types.html#737" class="Bound">A</a> <a id="810" href="foundation.large-dependent-pair-types.html#747" class="Bound">B</a> <a id="812" class="Symbol">→</a> <a id="814" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="817" href="foundation.large-dependent-pair-types.html#725" class="Bound">l</a>
  <a id="821" href="foundation.large-dependent-pair-types.html#771" class="Function">fam-Σω</a> <a id="828" href="foundation.large-dependent-pair-types.html#828" class="Bound">C</a> <a id="830" class="Symbol">(</a><a id="831" href="foundation.large-dependent-pair-types.html#557" class="InductiveConstructor">pairω</a> <a id="837" href="foundation.large-dependent-pair-types.html#837" class="Bound">x</a> <a id="839" href="foundation.large-dependent-pair-types.html#839" class="Bound">y</a><a id="840" class="Symbol">)</a> <a id="842" class="Symbol">=</a> <a id="844" href="foundation.large-dependent-pair-types.html#828" class="Bound">C</a> <a id="846" href="foundation.large-dependent-pair-types.html#837" class="Bound">x</a> <a id="848" href="foundation.large-dependent-pair-types.html#839" class="Bound">y</a>
</pre>