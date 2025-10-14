# Total partial elements

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="foundation.total-partial-elements.html" class="Module">foundation.total-partial-elements</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.partial-elements.html" class="Module">foundation.partial-elements</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A [partial element](foundation.partial-elements.md) `a` of `A` is said to be
{{#concept "total" Disambiguation="partial element" Agda=total-partial-element}}
if it is defined. The type of total partial elements of `A` is
[equivalent](foundation-core.equivalences.md) to the type `A`.

## Definitions

### The type of total partial elements

<pre class="Agda"><a id="total-partial-element"></a><a id="630" href="foundation.total-partial-elements.html#630" class="Function">total-partial-element</a> <a id="652" class="Symbol">:</a>
  <a id="656" class="Symbol">{</a><a id="657" href="foundation.total-partial-elements.html#657" class="Bound">l1</a> <a id="660" class="Symbol">:</a> <a id="662" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="667" class="Symbol">}</a> <a id="669" class="Symbol">(</a><a id="670" href="foundation.total-partial-elements.html#670" class="Bound">l2</a> <a id="673" class="Symbol">:</a> <a id="675" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="680" class="Symbol">)</a> <a id="682" class="Symbol">(</a><a id="683" href="foundation.total-partial-elements.html#683" class="Bound">A</a> <a id="685" class="Symbol">:</a> <a id="687" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="690" href="foundation.total-partial-elements.html#657" class="Bound">l1</a><a id="692" class="Symbol">)</a> <a id="694" class="Symbol">→</a> <a id="696" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="699" class="Symbol">(</a><a id="700" href="foundation.total-partial-elements.html#657" class="Bound">l1</a> <a id="703" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="705" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="710" href="foundation.total-partial-elements.html#670" class="Bound">l2</a><a id="712" class="Symbol">)</a>
<a id="714" href="foundation.total-partial-elements.html#630" class="Function">total-partial-element</a> <a id="736" href="foundation.total-partial-elements.html#736" class="Bound">l2</a> <a id="739" href="foundation.total-partial-elements.html#739" class="Bound">A</a> <a id="741" class="Symbol">=</a>
  <a id="745" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="747" class="Symbol">(</a><a id="748" href="foundation.partial-elements.html#1254" class="Function">partial-element</a> <a id="764" href="foundation.total-partial-elements.html#736" class="Bound">l2</a> <a id="767" href="foundation.total-partial-elements.html#739" class="Bound">A</a><a id="768" class="Symbol">)</a> <a id="770" href="foundation.partial-elements.html#1550" class="Function">is-defined-partial-element</a>
</pre>