# Sequences

<pre class="Agda"><a id="22" class="Keyword">module</a> <a id="29" href="lists.sequences.html" class="Module">lists.sequences</a> <a id="45" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="101" class="Keyword">open</a> <a id="106" class="Keyword">import</a> <a id="113" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="141" class="Keyword">open</a> <a id="146" class="Keyword">import</a> <a id="153" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>

<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="lists.dependent-sequences.html" class="Module">lists.dependent-sequences</a>
</pre>
</details>

## Idea

A {{#concept "sequence" Agda=sequence}} of elements of type `A` is a map `ℕ → A`
from the [natural numbers](elementary-number-theory.natural-numbers.md) into
`A`.

For a list of number sequences from the
[On-Line Encyclopedia of Integer Sequences](https://oeis.org) {{#cite oeis}}
that are formalized in agda-unimath, see the page
[`literature.oeis`](literature.oeis.md).

## Definition

### Sequences of elements of a type

<pre class="Agda"><a id="sequence"></a><a id="682" href="lists.sequences.html#682" class="Function">sequence</a> <a id="691" class="Symbol">:</a> <a id="693" class="Symbol">{</a><a id="694" href="lists.sequences.html#694" class="Bound">l</a> <a id="696" class="Symbol">:</a> <a id="698" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="703" class="Symbol">}</a> <a id="705" class="Symbol">→</a> <a id="707" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="710" href="lists.sequences.html#694" class="Bound">l</a> <a id="712" class="Symbol">→</a> <a id="714" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="717" href="lists.sequences.html#694" class="Bound">l</a>
<a id="719" href="lists.sequences.html#682" class="Function">sequence</a> <a id="728" href="lists.sequences.html#728" class="Bound">A</a> <a id="730" class="Symbol">=</a> <a id="732" href="lists.dependent-sequences.html#473" class="Function">dependent-sequence</a> <a id="751" class="Symbol">(λ</a> <a id="754" href="lists.sequences.html#754" class="Bound">_</a> <a id="756" class="Symbol">→</a> <a id="758" href="lists.sequences.html#728" class="Bound">A</a><a id="759" class="Symbol">)</a>
</pre>
### Functorial action on maps of sequences

<pre class="Agda"><a id="map-sequence"></a><a id="818" href="lists.sequences.html#818" class="Function">map-sequence</a> <a id="831" class="Symbol">:</a>
  <a id="835" class="Symbol">{</a><a id="836" href="lists.sequences.html#836" class="Bound">l1</a> <a id="839" href="lists.sequences.html#839" class="Bound">l2</a> <a id="842" class="Symbol">:</a> <a id="844" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="849" class="Symbol">}</a> <a id="851" class="Symbol">{</a><a id="852" href="lists.sequences.html#852" class="Bound">A</a> <a id="854" class="Symbol">:</a> <a id="856" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="859" href="lists.sequences.html#836" class="Bound">l1</a><a id="861" class="Symbol">}</a> <a id="863" class="Symbol">{</a><a id="864" href="lists.sequences.html#864" class="Bound">B</a> <a id="866" class="Symbol">:</a> <a id="868" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="871" href="lists.sequences.html#839" class="Bound">l2</a><a id="873" class="Symbol">}</a> <a id="875" class="Symbol">→</a> <a id="877" class="Symbol">(</a><a id="878" href="lists.sequences.html#852" class="Bound">A</a> <a id="880" class="Symbol">→</a> <a id="882" href="lists.sequences.html#864" class="Bound">B</a><a id="883" class="Symbol">)</a> <a id="885" class="Symbol">→</a> <a id="887" href="lists.sequences.html#682" class="Function">sequence</a> <a id="896" href="lists.sequences.html#852" class="Bound">A</a> <a id="898" class="Symbol">→</a> <a id="900" href="lists.sequences.html#682" class="Function">sequence</a> <a id="909" href="lists.sequences.html#864" class="Bound">B</a>
<a id="911" href="lists.sequences.html#818" class="Function">map-sequence</a> <a id="924" href="lists.sequences.html#924" class="Bound">f</a> <a id="926" href="lists.sequences.html#926" class="Bound">a</a> <a id="928" class="Symbol">=</a> <a id="930" href="lists.sequences.html#924" class="Bound">f</a> <a id="932" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="934" href="lists.sequences.html#926" class="Bound">a</a>
</pre>
## References

{{#bibliography}}
