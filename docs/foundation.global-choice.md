# Global choice

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="foundation.global-choice.html" class="Module">foundation.global-choice</a> <a id="58" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="114" class="Keyword">open</a> <a id="119" class="Keyword">import</a> <a id="126" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="158" class="Keyword">open</a> <a id="163" class="Keyword">import</a> <a id="170" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="foundation.hilberts-epsilon-operators.html" class="Module">foundation.hilberts-epsilon-operators</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="foundation-core.negation.html" class="Module">foundation-core.negation</a>

<a id="389" class="Keyword">open</a> <a id="394" class="Keyword">import</a> <a id="401" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="441" class="Keyword">open</a> <a id="446" class="Keyword">import</a> <a id="453" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
</pre>
</details>

## Idea

**Global choice** is the principle that there is a map from `type-trunc-Prop A`
back into `A`, for any type `A`. Here, we say that a type `A` _satisfies global
choice_ if there is such a map.

## Definition

### The global choice principle

<pre class="Agda"><a id="Global-Choice"></a><a id="774" href="foundation.global-choice.html#774" class="Function">Global-Choice</a> <a id="788" class="Symbol">:</a> <a id="790" class="Symbol">(</a><a id="791" href="foundation.global-choice.html#791" class="Bound">l</a> <a id="793" class="Symbol">:</a> <a id="795" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="800" class="Symbol">)</a> <a id="802" class="Symbol">→</a> <a id="804" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="807" class="Symbol">(</a><a id="808" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="813" href="foundation.global-choice.html#791" class="Bound">l</a><a id="814" class="Symbol">)</a>
<a id="816" href="foundation.global-choice.html#774" class="Function">Global-Choice</a> <a id="830" href="foundation.global-choice.html#830" class="Bound">l</a> <a id="832" class="Symbol">=</a> <a id="834" class="Symbol">(</a><a id="835" href="foundation.global-choice.html#835" class="Bound">A</a> <a id="837" class="Symbol">:</a> <a id="839" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="842" href="foundation.global-choice.html#830" class="Bound">l</a><a id="843" class="Symbol">)</a> <a id="845" class="Symbol">→</a> <a id="847" href="foundation.hilberts-epsilon-operators.html#716" class="Function">ε-operator-Hilbert</a> <a id="866" href="foundation.global-choice.html#835" class="Bound">A</a>
</pre>
## Properties

### The global choice principle is inconsistent in agda-unimath

<pre class="Agda"><a id="961" class="Keyword">abstract</a>
  <a id="no-global-choice"></a><a id="972" href="foundation.global-choice.html#972" class="Function">no-global-choice</a> <a id="989" class="Symbol">:</a>
    <a id="995" class="Symbol">{</a><a id="996" href="foundation.global-choice.html#996" class="Bound">l</a> <a id="998" class="Symbol">:</a> <a id="1000" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1005" class="Symbol">}</a> <a id="1007" class="Symbol">→</a> <a id="1009" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="1011" class="Symbol">(</a><a id="1012" href="foundation.global-choice.html#774" class="Function">Global-Choice</a> <a id="1026" href="foundation.global-choice.html#996" class="Bound">l</a><a id="1027" class="Symbol">)</a>
  <a id="1031" href="foundation.global-choice.html#972" class="Function">no-global-choice</a> <a id="1048" href="foundation.global-choice.html#1048" class="Bound">f</a> <a id="1050" class="Symbol">=</a>
    <a id="1056" href="univalent-combinatorics.2-element-types.html#17344" class="Function">no-section-type-2-Element-Type</a>
      <a id="1093" class="Symbol">(</a> <a id="1095" class="Symbol">λ</a> <a id="1097" href="foundation.global-choice.html#1097" class="Bound">X</a> <a id="1099" class="Symbol">→</a>
        <a id="1109" href="foundation.global-choice.html#1048" class="Bound">f</a> <a id="1111" class="Symbol">(</a><a id="1112" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1116" href="foundation.global-choice.html#1097" class="Bound">X</a><a id="1117" class="Symbol">)</a> <a id="1119" class="Symbol">(</a><a id="1120" href="foundation.functoriality-propositional-truncation.html#1256" class="Function">map-trunc-Prop</a> <a id="1135" class="Symbol">(λ</a> <a id="1138" href="foundation.global-choice.html#1138" class="Bound">e</a> <a id="1140" class="Symbol">→</a> <a id="1142" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="1152" href="foundation.global-choice.html#1138" class="Bound">e</a> <a id="1154" class="Symbol">(</a><a id="1155" href="univalent-combinatorics.standard-finite-types.html#5750" class="Function">zero-Fin</a> <a id="1164" class="Number">1</a><a id="1165" class="Symbol">))</a> <a id="1168" class="Symbol">(</a><a id="1169" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1173" href="foundation.global-choice.html#1097" class="Bound">X</a><a id="1174" class="Symbol">)))</a>
</pre>