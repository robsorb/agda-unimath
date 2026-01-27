# Radical ideals of rings

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="ring-theory.radical-ideals-rings.html" class="Module">ring-theory.radical-ideals-rings</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="208" class="Keyword">open</a> <a id="213" class="Keyword">import</a> <a id="220" href="ring-theory.ideals-rings.html" class="Module">ring-theory.ideals-rings</a>
<a id="245" class="Keyword">open</a> <a id="250" class="Keyword">import</a> <a id="257" href="ring-theory.invertible-elements-rings.html" class="Module">ring-theory.invertible-elements-rings</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

A radical ideal in a ring R is an ideal I such that `1 + x` is a multiplicative
unit for every `x ∈ I`.

## Definition

<pre class="Agda"><a id="479" class="Keyword">module</a> <a id="486" href="ring-theory.radical-ideals-rings.html#486" class="Module">_</a>
  <a id="490" class="Symbol">{</a><a id="491" href="ring-theory.radical-ideals-rings.html#491" class="Bound">l1</a> <a id="494" href="ring-theory.radical-ideals-rings.html#494" class="Bound">l2</a> <a id="497" class="Symbol">:</a> <a id="499" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="504" class="Symbol">}</a> <a id="506" class="Symbol">(</a><a id="507" href="ring-theory.radical-ideals-rings.html#507" class="Bound">R</a> <a id="509" class="Symbol">:</a> <a id="511" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="516" href="ring-theory.radical-ideals-rings.html#491" class="Bound">l1</a><a id="518" class="Symbol">)</a> <a id="520" class="Symbol">(</a><a id="521" href="ring-theory.radical-ideals-rings.html#521" class="Bound">I</a> <a id="523" class="Symbol">:</a> <a id="525" href="ring-theory.ideals-rings.html#1957" class="Function">ideal-Ring</a> <a id="536" href="ring-theory.radical-ideals-rings.html#494" class="Bound">l2</a> <a id="539" href="ring-theory.radical-ideals-rings.html#507" class="Bound">R</a><a id="540" class="Symbol">)</a>
  <a id="544" class="Keyword">where</a>

  <a id="553" href="ring-theory.radical-ideals-rings.html#553" class="Function">is-radical-ideal-prop-Ring</a> <a id="580" class="Symbol">:</a> <a id="582" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="587" class="Symbol">(</a><a id="588" href="ring-theory.radical-ideals-rings.html#491" class="Bound">l1</a> <a id="591" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="593" href="ring-theory.radical-ideals-rings.html#494" class="Bound">l2</a><a id="595" class="Symbol">)</a>
  <a id="599" href="ring-theory.radical-ideals-rings.html#553" class="Function">is-radical-ideal-prop-Ring</a> <a id="626" class="Symbol">=</a>
    <a id="632" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="645" class="Symbol">(</a> <a id="647" href="ring-theory.ideals-rings.html#2334" class="Function">type-ideal-Ring</a> <a id="663" href="ring-theory.radical-ideals-rings.html#507" class="Bound">R</a> <a id="665" href="ring-theory.radical-ideals-rings.html#521" class="Bound">I</a><a id="666" class="Symbol">)</a>
      <a id="674" class="Symbol">(</a> <a id="676" class="Symbol">λ</a> <a id="678" href="ring-theory.radical-ideals-rings.html#678" class="Bound">x</a> <a id="680" class="Symbol">→</a>
        <a id="690" href="ring-theory.invertible-elements-rings.html#5042" class="Function">is-invertible-element-prop-Ring</a> <a id="722" href="ring-theory.radical-ideals-rings.html#507" class="Bound">R</a>
          <a id="734" class="Symbol">(</a> <a id="736" href="ring-theory.rings.html#2861" class="Function">add-Ring</a> <a id="745" href="ring-theory.radical-ideals-rings.html#507" class="Bound">R</a> <a id="747" class="Symbol">(</a><a id="748" href="ring-theory.rings.html#12077" class="Function">one-Ring</a> <a id="757" href="ring-theory.radical-ideals-rings.html#507" class="Bound">R</a><a id="758" class="Symbol">)</a> <a id="760" class="Symbol">(</a><a id="761" href="ring-theory.ideals-rings.html#2425" class="Function">inclusion-ideal-Ring</a> <a id="782" href="ring-theory.radical-ideals-rings.html#507" class="Bound">R</a> <a id="784" href="ring-theory.radical-ideals-rings.html#521" class="Bound">I</a> <a id="786" href="ring-theory.radical-ideals-rings.html#678" class="Bound">x</a><a id="787" class="Symbol">)))</a>

  <a id="794" href="ring-theory.radical-ideals-rings.html#794" class="Function">is-radical-ideal-Ring</a> <a id="816" class="Symbol">:</a> <a id="818" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="821" class="Symbol">(</a><a id="822" href="ring-theory.radical-ideals-rings.html#491" class="Bound">l1</a> <a id="825" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="827" href="ring-theory.radical-ideals-rings.html#494" class="Bound">l2</a><a id="829" class="Symbol">)</a>
  <a id="833" href="ring-theory.radical-ideals-rings.html#794" class="Function">is-radical-ideal-Ring</a> <a id="855" class="Symbol">=</a>
    <a id="861" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="871" href="ring-theory.radical-ideals-rings.html#553" class="Function">is-radical-ideal-prop-Ring</a>

  <a id="901" href="ring-theory.radical-ideals-rings.html#901" class="Function">is-prop-is-radical-ideal-Ring</a> <a id="931" class="Symbol">:</a>
    <a id="937" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="945" href="ring-theory.radical-ideals-rings.html#794" class="Function">is-radical-ideal-Ring</a>
  <a id="969" href="ring-theory.radical-ideals-rings.html#901" class="Function">is-prop-is-radical-ideal-Ring</a> <a id="999" class="Symbol">=</a>
    <a id="1005" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1023" href="ring-theory.radical-ideals-rings.html#553" class="Function">is-radical-ideal-prop-Ring</a>
</pre>