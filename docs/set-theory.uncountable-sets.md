# Uncountable sets

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="set-theory.uncountable-sets.html" class="Module">set-theory.uncountable-sets</a> <a id="64" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="120" class="Keyword">open</a> <a id="125" class="Keyword">import</a> <a id="132" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="152" class="Keyword">open</a> <a id="157" class="Keyword">import</a> <a id="164" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="set-theory.countable-sets.html" class="Module">set-theory.countable-sets</a>
</pre>
</details>

## Idea

A [set](foundation-core.sets.md) `X` is
{{#concept "uncountable" Disambiguation="set" Agda=is-uncountable WD="uncountable set" WDID=Q1128796}}
if `X` is not [empty](foundation-core.empty-types.md) and there is
[no](foundation-core.negation.md) [surjection](foundation.surjective-maps.md)
`ℕ ↠ X`. In other words, if `X` is not
[countable](set-theory.countable-sets.md).

## Definition

<pre class="Agda"><a id="is-uncountable-Prop"></a><a id="714" href="set-theory.uncountable-sets.html#714" class="Function">is-uncountable-Prop</a> <a id="734" class="Symbol">:</a> <a id="736" class="Symbol">{</a><a id="737" href="set-theory.uncountable-sets.html#737" class="Bound">l</a> <a id="739" class="Symbol">:</a> <a id="741" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="746" class="Symbol">}</a> <a id="748" class="Symbol">→</a> <a id="750" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="754" href="set-theory.uncountable-sets.html#737" class="Bound">l</a> <a id="756" class="Symbol">→</a> <a id="758" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="763" href="set-theory.uncountable-sets.html#737" class="Bound">l</a>
<a id="765" href="set-theory.uncountable-sets.html#714" class="Function">is-uncountable-Prop</a> <a id="785" href="set-theory.uncountable-sets.html#785" class="Bound">X</a> <a id="787" class="Symbol">=</a> <a id="789" href="foundation.negation.html#981" class="Function">neg-Prop</a> <a id="798" class="Symbol">(</a><a id="799" href="set-theory.countable-sets.html#2689" class="Function">is-countable-Prop</a> <a id="817" href="set-theory.uncountable-sets.html#785" class="Bound">X</a><a id="818" class="Symbol">)</a>

<a id="is-uncountable"></a><a id="821" href="set-theory.uncountable-sets.html#821" class="Function">is-uncountable</a> <a id="836" class="Symbol">:</a> <a id="838" class="Symbol">{</a><a id="839" href="set-theory.uncountable-sets.html#839" class="Bound">l</a> <a id="841" class="Symbol">:</a> <a id="843" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="848" class="Symbol">}</a> <a id="850" class="Symbol">→</a> <a id="852" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="856" href="set-theory.uncountable-sets.html#839" class="Bound">l</a> <a id="858" class="Symbol">→</a> <a id="860" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="863" href="set-theory.uncountable-sets.html#839" class="Bound">l</a>
<a id="865" href="set-theory.uncountable-sets.html#821" class="Function">is-uncountable</a> <a id="880" href="set-theory.uncountable-sets.html#880" class="Bound">X</a> <a id="882" class="Symbol">=</a> <a id="884" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="894" class="Symbol">(</a><a id="895" href="set-theory.uncountable-sets.html#714" class="Function">is-uncountable-Prop</a> <a id="915" href="set-theory.uncountable-sets.html#880" class="Bound">X</a><a id="916" class="Symbol">)</a>

<a id="is-prop-is-uncountable"></a><a id="919" href="set-theory.uncountable-sets.html#919" class="Function">is-prop-is-uncountable</a> <a id="942" class="Symbol">:</a> <a id="944" class="Symbol">{</a><a id="945" href="set-theory.uncountable-sets.html#945" class="Bound">l</a> <a id="947" class="Symbol">:</a> <a id="949" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="954" class="Symbol">}</a> <a id="956" class="Symbol">(</a><a id="957" href="set-theory.uncountable-sets.html#957" class="Bound">X</a> <a id="959" class="Symbol">:</a> <a id="961" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="965" href="set-theory.uncountable-sets.html#945" class="Bound">l</a><a id="966" class="Symbol">)</a> <a id="968" class="Symbol">→</a> <a id="970" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="978" class="Symbol">(</a><a id="979" href="set-theory.uncountable-sets.html#821" class="Function">is-uncountable</a> <a id="994" href="set-theory.uncountable-sets.html#957" class="Bound">X</a><a id="995" class="Symbol">)</a>
<a id="997" href="set-theory.uncountable-sets.html#919" class="Function">is-prop-is-uncountable</a> <a id="1020" href="set-theory.uncountable-sets.html#1020" class="Bound">X</a> <a id="1022" class="Symbol">=</a> <a id="1024" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1042" class="Symbol">(</a><a id="1043" href="set-theory.uncountable-sets.html#714" class="Function">is-uncountable-Prop</a> <a id="1063" href="set-theory.uncountable-sets.html#1020" class="Bound">X</a><a id="1064" class="Symbol">)</a>
</pre>
## External links

- [Uncountable set](https://en.wikipedia.org/wiki/Uncountable_set) at Wikipedia
