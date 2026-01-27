# Bottom elements in preorders

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="order-theory.bottom-elements-preorders.html" class="Module">order-theory.bottom-elements-preorders</a> <a id="87" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="143" class="Keyword">open</a> <a id="148" class="Keyword">import</a> <a id="155" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
</pre>
</details>

## Idea

A **bottom element** in a preorder `P` is an element `b` such that `b ≤ x` holds
for every element `x : P`.

## Definition

<pre class="Agda"><a id="456" class="Keyword">module</a> <a id="463" href="order-theory.bottom-elements-preorders.html#463" class="Module">_</a>
  <a id="467" class="Symbol">{</a><a id="468" href="order-theory.bottom-elements-preorders.html#468" class="Bound">l1</a> <a id="471" href="order-theory.bottom-elements-preorders.html#471" class="Bound">l2</a> <a id="474" class="Symbol">:</a> <a id="476" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="481" class="Symbol">}</a> <a id="483" class="Symbol">(</a><a id="484" href="order-theory.bottom-elements-preorders.html#484" class="Bound">X</a> <a id="486" class="Symbol">:</a> <a id="488" href="order-theory.preorders.html#1073" class="Function">Preorder</a> <a id="497" href="order-theory.bottom-elements-preorders.html#468" class="Bound">l1</a> <a id="500" href="order-theory.bottom-elements-preorders.html#471" class="Bound">l2</a><a id="502" class="Symbol">)</a>
  <a id="506" class="Keyword">where</a>

  <a id="515" href="order-theory.bottom-elements-preorders.html#515" class="Function">is-bottom-element-Preorder-Prop</a> <a id="547" class="Symbol">:</a> <a id="549" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="563" href="order-theory.bottom-elements-preorders.html#484" class="Bound">X</a> <a id="565" class="Symbol">→</a> <a id="567" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="572" class="Symbol">(</a><a id="573" href="order-theory.bottom-elements-preorders.html#468" class="Bound">l1</a> <a id="576" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="578" href="order-theory.bottom-elements-preorders.html#471" class="Bound">l2</a><a id="580" class="Symbol">)</a>
  <a id="584" href="order-theory.bottom-elements-preorders.html#515" class="Function">is-bottom-element-Preorder-Prop</a> <a id="616" href="order-theory.bottom-elements-preorders.html#616" class="Bound">x</a> <a id="618" class="Symbol">=</a>
    <a id="624" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="631" class="Symbol">(</a><a id="632" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="646" href="order-theory.bottom-elements-preorders.html#484" class="Bound">X</a><a id="647" class="Symbol">)</a> <a id="649" class="Symbol">(</a><a id="650" href="order-theory.preorders.html#1322" class="Function">leq-prop-Preorder</a> <a id="668" href="order-theory.bottom-elements-preorders.html#484" class="Bound">X</a> <a id="670" href="order-theory.bottom-elements-preorders.html#616" class="Bound">x</a><a id="671" class="Symbol">)</a>

  <a id="676" href="order-theory.bottom-elements-preorders.html#676" class="Function">is-bottom-element-Preorder</a> <a id="703" class="Symbol">:</a> <a id="705" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="719" href="order-theory.bottom-elements-preorders.html#484" class="Bound">X</a> <a id="721" class="Symbol">→</a> <a id="723" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="726" class="Symbol">(</a><a id="727" href="order-theory.bottom-elements-preorders.html#468" class="Bound">l1</a> <a id="730" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="732" href="order-theory.bottom-elements-preorders.html#471" class="Bound">l2</a><a id="734" class="Symbol">)</a>
  <a id="738" href="order-theory.bottom-elements-preorders.html#676" class="Function">is-bottom-element-Preorder</a> <a id="765" href="order-theory.bottom-elements-preorders.html#765" class="Bound">x</a> <a id="767" class="Symbol">=</a> <a id="769" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="779" class="Symbol">(</a><a id="780" href="order-theory.bottom-elements-preorders.html#515" class="Function">is-bottom-element-Preorder-Prop</a> <a id="812" href="order-theory.bottom-elements-preorders.html#765" class="Bound">x</a><a id="813" class="Symbol">)</a>

  <a id="818" href="order-theory.bottom-elements-preorders.html#818" class="Function">is-prop-is-bottom-element-Preorder</a> <a id="853" class="Symbol">:</a>
    <a id="859" class="Symbol">(</a><a id="860" href="order-theory.bottom-elements-preorders.html#860" class="Bound">x</a> <a id="862" class="Symbol">:</a> <a id="864" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="878" href="order-theory.bottom-elements-preorders.html#484" class="Bound">X</a><a id="879" class="Symbol">)</a> <a id="881" class="Symbol">→</a> <a id="883" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="891" class="Symbol">(</a><a id="892" href="order-theory.bottom-elements-preorders.html#676" class="Function">is-bottom-element-Preorder</a> <a id="919" href="order-theory.bottom-elements-preorders.html#860" class="Bound">x</a><a id="920" class="Symbol">)</a>
  <a id="924" href="order-theory.bottom-elements-preorders.html#818" class="Function">is-prop-is-bottom-element-Preorder</a> <a id="959" href="order-theory.bottom-elements-preorders.html#959" class="Bound">x</a> <a id="961" class="Symbol">=</a>
    <a id="967" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="985" class="Symbol">(</a><a id="986" href="order-theory.bottom-elements-preorders.html#515" class="Function">is-bottom-element-Preorder-Prop</a> <a id="1018" href="order-theory.bottom-elements-preorders.html#959" class="Bound">x</a><a id="1019" class="Symbol">)</a>

  <a id="1024" href="order-theory.bottom-elements-preorders.html#1024" class="Function">has-bottom-element-Preorder</a> <a id="1052" class="Symbol">:</a> <a id="1054" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1057" class="Symbol">(</a><a id="1058" href="order-theory.bottom-elements-preorders.html#468" class="Bound">l1</a> <a id="1061" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1063" href="order-theory.bottom-elements-preorders.html#471" class="Bound">l2</a><a id="1065" class="Symbol">)</a>
  <a id="1069" href="order-theory.bottom-elements-preorders.html#1024" class="Function">has-bottom-element-Preorder</a> <a id="1097" class="Symbol">=</a> <a id="1099" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1101" class="Symbol">(</a><a id="1102" href="order-theory.preorders.html#1273" class="Function">type-Preorder</a> <a id="1116" href="order-theory.bottom-elements-preorders.html#484" class="Bound">X</a><a id="1117" class="Symbol">)</a> <a id="1119" href="order-theory.bottom-elements-preorders.html#676" class="Function">is-bottom-element-Preorder</a>
</pre>