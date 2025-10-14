# Bands

<pre class="Agda"><a id="18" class="Keyword">module</a> <a id="25" href="foundation.bands.html" class="Module">foundation.bands</a> <a id="42" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="98" class="Keyword">open</a> <a id="103" class="Keyword">import</a> <a id="110" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
</pre>
</details>

## Idea

A **band** from $X$ to $Y$ is an element of the
[set-truncation](foundation.set-truncations.md) of the type of
[equivalences](foundation-core.equivalences.md) from $X$ to $Y$.

## Definition

<pre class="Agda"><a id="band"></a><a id="444" href="foundation.bands.html#444" class="Function">band</a> <a id="449" class="Symbol">:</a> <a id="451" class="Symbol">{</a><a id="452" href="foundation.bands.html#452" class="Bound">l1</a> <a id="455" href="foundation.bands.html#455" class="Bound">l2</a> <a id="458" class="Symbol">:</a> <a id="460" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="465" class="Symbol">}</a> <a id="467" class="Symbol">→</a> <a id="469" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="472" href="foundation.bands.html#452" class="Bound">l1</a> <a id="475" class="Symbol">→</a> <a id="477" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="480" href="foundation.bands.html#455" class="Bound">l2</a> <a id="483" class="Symbol">→</a> <a id="485" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="488" class="Symbol">(</a><a id="489" href="foundation.bands.html#452" class="Bound">l1</a> <a id="492" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="494" href="foundation.bands.html#455" class="Bound">l2</a><a id="496" class="Symbol">)</a>
<a id="498" href="foundation.bands.html#444" class="Function">band</a> <a id="503" href="foundation.bands.html#503" class="Bound">A</a> <a id="505" href="foundation.bands.html#505" class="Bound">B</a> <a id="507" class="Symbol">=</a> <a id="509" href="foundation.set-truncations.html#2028" class="Function">type-trunc-Set</a> <a id="524" class="Symbol">(</a><a id="525" href="foundation.bands.html#503" class="Bound">A</a> <a id="527" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="529" href="foundation.bands.html#505" class="Bound">B</a><a id="530" class="Symbol">)</a>

<a id="unit-band"></a><a id="533" href="foundation.bands.html#533" class="Function">unit-band</a> <a id="543" class="Symbol">:</a> <a id="545" class="Symbol">{</a><a id="546" href="foundation.bands.html#546" class="Bound">l1</a> <a id="549" href="foundation.bands.html#549" class="Bound">l2</a> <a id="552" class="Symbol">:</a> <a id="554" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="559" class="Symbol">}</a> <a id="561" class="Symbol">{</a><a id="562" href="foundation.bands.html#562" class="Bound">A</a> <a id="564" class="Symbol">:</a> <a id="566" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="569" href="foundation.bands.html#546" class="Bound">l1</a><a id="571" class="Symbol">}</a> <a id="573" class="Symbol">{</a><a id="574" href="foundation.bands.html#574" class="Bound">B</a> <a id="576" class="Symbol">:</a> <a id="578" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="581" href="foundation.bands.html#549" class="Bound">l2</a><a id="583" class="Symbol">}</a> <a id="585" class="Symbol">→</a> <a id="587" class="Symbol">(</a><a id="588" href="foundation.bands.html#562" class="Bound">A</a> <a id="590" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="592" href="foundation.bands.html#574" class="Bound">B</a><a id="593" class="Symbol">)</a> <a id="595" class="Symbol">→</a> <a id="597" href="foundation.bands.html#444" class="Function">band</a> <a id="602" href="foundation.bands.html#562" class="Bound">A</a> <a id="604" href="foundation.bands.html#574" class="Bound">B</a>
<a id="606" href="foundation.bands.html#533" class="Function">unit-band</a> <a id="616" class="Symbol">=</a> <a id="618" href="foundation.set-truncations.html#2227" class="Function">unit-trunc-Set</a>

<a id="refl-band"></a><a id="634" href="foundation.bands.html#634" class="Function">refl-band</a> <a id="644" class="Symbol">:</a> <a id="646" class="Symbol">{</a><a id="647" href="foundation.bands.html#647" class="Bound">l</a> <a id="649" class="Symbol">:</a> <a id="651" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="656" class="Symbol">}</a> <a id="658" class="Symbol">(</a><a id="659" href="foundation.bands.html#659" class="Bound">A</a> <a id="661" class="Symbol">:</a> <a id="663" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="666" href="foundation.bands.html#647" class="Bound">l</a><a id="667" class="Symbol">)</a> <a id="669" class="Symbol">→</a> <a id="671" href="foundation.bands.html#444" class="Function">band</a> <a id="676" href="foundation.bands.html#659" class="Bound">A</a> <a id="678" href="foundation.bands.html#659" class="Bound">A</a>
<a id="680" href="foundation.bands.html#634" class="Function">refl-band</a> <a id="690" href="foundation.bands.html#690" class="Bound">A</a> <a id="692" class="Symbol">=</a> <a id="694" href="foundation.bands.html#533" class="Function">unit-band</a> <a id="704" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
</pre>