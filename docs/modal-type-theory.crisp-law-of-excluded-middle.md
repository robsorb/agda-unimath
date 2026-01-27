# The crisp law of excluded middle

<pre class="Agda"><a id="45" class="Symbol">{-#</a> <a id="49" class="Keyword">OPTIONS</a> <a id="57" class="Pragma">--cohesion</a> <a id="68" class="Pragma">--flat-split</a> <a id="81" class="Symbol">#-}</a>

<a id="86" class="Keyword">module</a> <a id="93" href="modal-type-theory.crisp-law-of-excluded-middle.html" class="Module">modal-type-theory.crisp-law-of-excluded-middle</a> <a id="140" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="235" class="Keyword">open</a> <a id="240" class="Keyword">import</a> <a id="247" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="foundation-core.decidable-propositions.html" class="Module">foundation-core.decidable-propositions</a>
<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

The {{#concept "crisp law of excluded middle" Agda=Crisp-LEM}} asserts that any
[crisp](modal-type-theory.crisp-types.md)
[proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

<pre class="Agda"><a id="Crisp-LEM"></a><a id="681" href="modal-type-theory.crisp-law-of-excluded-middle.html#681" class="Function">Crisp-LEM</a> <a id="691" class="Symbol">:</a> <a id="693" class="Symbol">(@</a>♭ <a id="697" href="modal-type-theory.crisp-law-of-excluded-middle.html#697" class="Bound">l</a> <a id="699" class="Symbol">:</a> <a id="701" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="706" class="Symbol">)</a> <a id="708" class="Symbol">→</a> <a id="710" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="713" class="Symbol">(</a><a id="714" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="719" href="modal-type-theory.crisp-law-of-excluded-middle.html#697" class="Bound">l</a><a id="720" class="Symbol">)</a>
<a id="722" href="modal-type-theory.crisp-law-of-excluded-middle.html#681" class="Function">Crisp-LEM</a> <a id="732" href="modal-type-theory.crisp-law-of-excluded-middle.html#732" class="Bound">l</a> <a id="734" class="Symbol">=</a> <a id="736" class="Symbol">(@</a>♭ <a id="740" href="modal-type-theory.crisp-law-of-excluded-middle.html#740" class="Bound">P</a> <a id="742" class="Symbol">:</a> <a id="744" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="749" href="modal-type-theory.crisp-law-of-excluded-middle.html#732" class="Bound">l</a><a id="750" class="Symbol">)</a> <a id="752" class="Symbol">→</a> <a id="754" href="foundation.decidable-types.html#1859" class="Function">is-decidable</a> <a id="767" class="Symbol">(</a><a id="768" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="778" href="modal-type-theory.crisp-law-of-excluded-middle.html#740" class="Bound">P</a><a id="779" class="Symbol">)</a>
</pre>
## Properties

### Given crisp LEM, we obtain a map from crisp propositions to decidable propositions

<pre class="Agda"><a id="decidable-prop-Crisp-Prop"></a><a id="897" href="modal-type-theory.crisp-law-of-excluded-middle.html#897" class="Function">decidable-prop-Crisp-Prop</a> <a id="923" class="Symbol">:</a>
  <a id="927" class="Symbol">{@</a>♭ <a id="931" href="modal-type-theory.crisp-law-of-excluded-middle.html#931" class="Bound">l</a> <a id="933" class="Symbol">:</a> <a id="935" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="940" class="Symbol">}</a> <a id="942" class="Symbol">→</a> <a id="944" href="modal-type-theory.crisp-law-of-excluded-middle.html#681" class="Function">Crisp-LEM</a> <a id="954" href="modal-type-theory.crisp-law-of-excluded-middle.html#931" class="Bound">l</a> <a id="956" class="Symbol">→</a> <a id="958" class="Symbol">@</a>♭ <a id="961" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="966" href="modal-type-theory.crisp-law-of-excluded-middle.html#931" class="Bound">l</a> <a id="968" class="Symbol">→</a> <a id="970" href="foundation-core.decidable-propositions.html#2498" class="Function">Decidable-Prop</a> <a id="985" href="modal-type-theory.crisp-law-of-excluded-middle.html#931" class="Bound">l</a>
<a id="987" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="991" class="Symbol">(</a><a id="992" href="modal-type-theory.crisp-law-of-excluded-middle.html#897" class="Function">decidable-prop-Crisp-Prop</a> <a id="1018" href="modal-type-theory.crisp-law-of-excluded-middle.html#1018" class="Bound">lem</a> <a id="1022" href="modal-type-theory.crisp-law-of-excluded-middle.html#1022" class="Bound">P</a><a id="1023" class="Symbol">)</a> <a id="1025" class="Symbol">=</a> <a id="1027" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1037" href="modal-type-theory.crisp-law-of-excluded-middle.html#1022" class="Bound">P</a>
<a id="1039" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1043" class="Symbol">(</a><a id="1044" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1048" class="Symbol">(</a><a id="1049" href="modal-type-theory.crisp-law-of-excluded-middle.html#897" class="Function">decidable-prop-Crisp-Prop</a> <a id="1075" href="modal-type-theory.crisp-law-of-excluded-middle.html#1075" class="Bound">lem</a> <a id="1079" href="modal-type-theory.crisp-law-of-excluded-middle.html#1079" class="Bound">P</a><a id="1080" class="Symbol">))</a> <a id="1083" class="Symbol">=</a> <a id="1085" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1103" href="modal-type-theory.crisp-law-of-excluded-middle.html#1079" class="Bound">P</a>
<a id="1105" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1109" class="Symbol">(</a><a id="1110" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1114" class="Symbol">(</a><a id="1115" href="modal-type-theory.crisp-law-of-excluded-middle.html#897" class="Function">decidable-prop-Crisp-Prop</a> <a id="1141" href="modal-type-theory.crisp-law-of-excluded-middle.html#1141" class="Bound">lem</a> <a id="1145" href="modal-type-theory.crisp-law-of-excluded-middle.html#1145" class="Bound">P</a><a id="1146" class="Symbol">))</a> <a id="1149" class="Symbol">=</a> <a id="1151" href="modal-type-theory.crisp-law-of-excluded-middle.html#1141" class="Bound">lem</a> <a id="1155" href="modal-type-theory.crisp-law-of-excluded-middle.html#1145" class="Bound">P</a>
</pre>
## See also

- [The law of excluded middle](foundation.law-of-excluded-middle.md)

## References

{{#bibliography}} {{#reference Shu18}}
