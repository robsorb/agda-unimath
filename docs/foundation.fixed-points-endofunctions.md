# Fixed points of endofunctions

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="foundation.fixed-points-endofunctions.html" class="Module">foundation.fixed-points-endofunctions</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

Given an [endofunction](foundation-core.endomorphisms.md) `f : A → A`, the type
of {{#concept "fixed points"}} is the type of elements `x : A` such that
`f x ＝ x`.

## Definitions

<pre class="Agda"><a id="485" class="Keyword">module</a> <a id="492" href="foundation.fixed-points-endofunctions.html#492" class="Module">_</a>
  <a id="496" class="Symbol">{</a><a id="497" href="foundation.fixed-points-endofunctions.html#497" class="Bound">l</a> <a id="499" class="Symbol">:</a> <a id="501" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="506" class="Symbol">}</a> <a id="508" class="Symbol">{</a><a id="509" href="foundation.fixed-points-endofunctions.html#509" class="Bound">A</a> <a id="511" class="Symbol">:</a> <a id="513" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="516" href="foundation.fixed-points-endofunctions.html#497" class="Bound">l</a><a id="517" class="Symbol">}</a> <a id="519" class="Symbol">(</a><a id="520" href="foundation.fixed-points-endofunctions.html#520" class="Bound">f</a> <a id="522" class="Symbol">:</a> <a id="524" href="foundation.fixed-points-endofunctions.html#509" class="Bound">A</a> <a id="526" class="Symbol">→</a> <a id="528" href="foundation.fixed-points-endofunctions.html#509" class="Bound">A</a><a id="529" class="Symbol">)</a>
  <a id="533" class="Keyword">where</a>

  <a id="542" href="foundation.fixed-points-endofunctions.html#542" class="Function">fixed-point</a> <a id="554" class="Symbol">:</a> <a id="556" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="559" href="foundation.fixed-points-endofunctions.html#497" class="Bound">l</a>
  <a id="563" href="foundation.fixed-points-endofunctions.html#542" class="Function">fixed-point</a> <a id="575" class="Symbol">=</a> <a id="577" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="579" href="foundation.fixed-points-endofunctions.html#509" class="Bound">A</a> <a id="581" class="Symbol">(λ</a> <a id="584" href="foundation.fixed-points-endofunctions.html#584" class="Bound">x</a> <a id="586" class="Symbol">→</a> <a id="588" href="foundation.fixed-points-endofunctions.html#520" class="Bound">f</a> <a id="590" href="foundation.fixed-points-endofunctions.html#584" class="Bound">x</a> <a id="592" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="594" href="foundation.fixed-points-endofunctions.html#584" class="Bound">x</a><a id="595" class="Symbol">)</a>

  <a id="600" href="foundation.fixed-points-endofunctions.html#600" class="Function">fixed-point&#39;</a> <a id="613" class="Symbol">:</a> <a id="615" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="618" href="foundation.fixed-points-endofunctions.html#497" class="Bound">l</a>
  <a id="622" href="foundation.fixed-points-endofunctions.html#600" class="Function">fixed-point&#39;</a> <a id="635" class="Symbol">=</a> <a id="637" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="639" href="foundation.fixed-points-endofunctions.html#509" class="Bound">A</a> <a id="641" class="Symbol">(λ</a> <a id="644" href="foundation.fixed-points-endofunctions.html#644" class="Bound">x</a> <a id="646" class="Symbol">→</a> <a id="648" href="foundation.fixed-points-endofunctions.html#644" class="Bound">x</a> <a id="650" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="652" href="foundation.fixed-points-endofunctions.html#520" class="Bound">f</a> <a id="654" href="foundation.fixed-points-endofunctions.html#644" class="Bound">x</a><a id="655" class="Symbol">)</a>
</pre>