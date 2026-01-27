# Rational modules

<pre class="Agda"><a id="29" class="Symbol">{-#</a> <a id="33" class="Keyword">OPTIONS</a> <a id="41" class="Pragma">--lossy-unification</a> <a id="61" class="Symbol">#-}</a>

<a id="66" class="Keyword">module</a> <a id="73" href="linear-algebra.rational-modules.html" class="Module">linear-algebra.rational-modules</a> <a id="105" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="161" class="Keyword">open</a> <a id="166" class="Keyword">import</a> <a id="173" href="elementary-number-theory.positive-integers.html" class="Module">elementary-number-theory.positive-integers</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="elementary-number-theory.ring-of-rational-numbers.html" class="Module">elementary-number-theory.ring-of-rational-numbers</a>

<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="397" class="Keyword">open</a> <a id="402" class="Keyword">import</a> <a id="409" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="455" class="Keyword">open</a> <a id="460" class="Keyword">import</a> <a id="467" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="499" class="Keyword">open</a> <a id="504" class="Keyword">import</a> <a id="511" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="535" class="Keyword">open</a> <a id="540" class="Keyword">import</a> <a id="547" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="567" class="Keyword">open</a> <a id="572" class="Keyword">import</a> <a id="579" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="622" class="Keyword">open</a> <a id="627" class="Keyword">import</a> <a id="634" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="662" class="Keyword">open</a> <a id="667" class="Keyword">import</a> <a id="674" href="group-theory.abelian-groups.html" class="Module">group-theory.abelian-groups</a>
<a id="702" class="Keyword">open</a> <a id="707" class="Keyword">import</a> <a id="714" href="group-theory.endomorphism-rings-abelian-groups.html" class="Module">group-theory.endomorphism-rings-abelian-groups</a>
<a id="761" class="Keyword">open</a> <a id="766" class="Keyword">import</a> <a id="773" href="group-theory.homomorphisms-abelian-groups.html" class="Module">group-theory.homomorphisms-abelian-groups</a>
<a id="815" class="Keyword">open</a> <a id="820" class="Keyword">import</a> <a id="827" href="group-theory.integer-multiples-of-elements-abelian-groups.html" class="Module">group-theory.integer-multiples-of-elements-abelian-groups</a>
<a id="885" class="Keyword">open</a> <a id="890" class="Keyword">import</a> <a id="897" href="group-theory.isomorphisms-abelian-groups.html" class="Module">group-theory.isomorphisms-abelian-groups</a>

<a id="939" class="Keyword">open</a> <a id="944" class="Keyword">import</a> <a id="951" href="linear-algebra.left-modules-rings.html" class="Module">linear-algebra.left-modules-rings</a>
<a id="985" class="Keyword">open</a> <a id="990" class="Keyword">import</a> <a id="997" href="linear-algebra.right-modules-rings.html" class="Module">linear-algebra.right-modules-rings</a>

<a id="1033" class="Keyword">open</a> <a id="1038" class="Keyword">import</a> <a id="1045" href="ring-theory.homomorphisms-rings.html" class="Module">ring-theory.homomorphisms-rings</a>
<a id="1077" class="Keyword">open</a> <a id="1082" class="Keyword">import</a> <a id="1089" href="ring-theory.invertible-elements-rings.html" class="Module">ring-theory.invertible-elements-rings</a>
<a id="1127" class="Keyword">open</a> <a id="1132" class="Keyword">import</a> <a id="1139" href="ring-theory.opposite-ring-extensions-rational-numbers.html" class="Module">ring-theory.opposite-ring-extensions-rational-numbers</a>
<a id="1193" class="Keyword">open</a> <a id="1198" class="Keyword">import</a> <a id="1205" href="ring-theory.opposite-rings.html" class="Module">ring-theory.opposite-rings</a>
<a id="1232" class="Keyword">open</a> <a id="1237" class="Keyword">import</a> <a id="1244" href="ring-theory.ring-extensions-rational-numbers.html" class="Module">ring-theory.ring-extensions-rational-numbers</a>
<a id="1289" class="Keyword">open</a> <a id="1294" class="Keyword">import</a> <a id="1301" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

A {{#concept "rational module" Agda=Rational-Module}} is an
[abelian group](group-theory.abelian-groups.md) whose
[ring of endomorphisms](group-theory.endomorphism-rings-abelian-groups.md) is a
[ring extension of `ℚ`](ring-theory.ring-extensions-rational-numbers.md). I.e.,
the [initial ring homomorphism](elementary-number-theory.ring-of-integers.md) in
its ring of endomorphisms [inverts](ring-theory.localizations-rings.md) the
[positive integers](elementary-number-theory.positive-integers.md).

This condition is [logically equivalent](foundation.logical-equivalences.md) to
the following [propositions](foundation.propositions.md):

- it is a [left module](linear-algebra.left-modules-rings.md) over the
  [ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md);
- it is a [right module](linear-algebra.right-modules-rings.md) over the
  [ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md).

**Note:** Because `ℚ` is a
[discrete field](commutative-algebra.discrete-fields.md), rational modules are
the vector spaces on the
[field of rational numbers](elementary-number-theory.field-of-rational-numbers.md).

## Definitions

### The predicate on abelian groups of being a rational module

<pre class="Agda"><a id="2601" class="Keyword">module</a> <a id="2608" href="linear-algebra.rational-modules.html#2608" class="Module">_</a>
  <a id="2612" class="Symbol">{</a><a id="2613" href="linear-algebra.rational-modules.html#2613" class="Bound">l</a> <a id="2615" class="Symbol">:</a> <a id="2617" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2622" class="Symbol">}</a> <a id="2624" class="Symbol">(</a><a id="2625" href="linear-algebra.rational-modules.html#2625" class="Bound">A</a> <a id="2627" class="Symbol">:</a> <a id="2629" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="2632" href="linear-algebra.rational-modules.html#2613" class="Bound">l</a><a id="2633" class="Symbol">)</a>
  <a id="2637" class="Keyword">where</a>

  <a id="2646" href="linear-algebra.rational-modules.html#2646" class="Function">is-rational-module-prop-Ab</a> <a id="2673" class="Symbol">:</a> <a id="2675" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2680" href="linear-algebra.rational-modules.html#2613" class="Bound">l</a>
  <a id="2684" href="linear-algebra.rational-modules.html#2646" class="Function">is-rational-module-prop-Ab</a> <a id="2711" class="Symbol">=</a>
    <a id="2717" href="ring-theory.ring-extensions-rational-numbers.html#3044" class="Function">is-rational-extension-prop-Ring</a> <a id="2749" class="Symbol">(</a><a id="2750" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="2771" href="linear-algebra.rational-modules.html#2625" class="Bound">A</a><a id="2772" class="Symbol">)</a>

  <a id="2777" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a> <a id="2799" class="Symbol">:</a> <a id="2801" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2804" href="linear-algebra.rational-modules.html#2613" class="Bound">l</a>
  <a id="2808" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a> <a id="2830" class="Symbol">=</a>
    <a id="2836" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2846" href="linear-algebra.rational-modules.html#2646" class="Function">is-rational-module-prop-Ab</a>

  <a id="2876" href="linear-algebra.rational-modules.html#2876" class="Function">is-prop-is-rational-module-Ab</a> <a id="2906" class="Symbol">:</a>
    <a id="2912" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2920" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a>
  <a id="2944" href="linear-algebra.rational-modules.html#2876" class="Function">is-prop-is-rational-module-Ab</a> <a id="2974" class="Symbol">=</a>
    <a id="2980" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2998" href="linear-algebra.rational-modules.html#2646" class="Function">is-rational-module-prop-Ab</a>
</pre>
### The type of rational modules

<pre class="Agda"><a id="Rational-Module"></a><a id="3072" href="linear-algebra.rational-modules.html#3072" class="Function">Rational-Module</a> <a id="3088" class="Symbol">:</a> <a id="3090" class="Symbol">(</a><a id="3091" href="linear-algebra.rational-modules.html#3091" class="Bound">l</a> <a id="3093" class="Symbol">:</a> <a id="3095" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3100" class="Symbol">)</a> <a id="3102" class="Symbol">→</a> <a id="3104" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3107" class="Symbol">(</a><a id="3108" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3113" href="linear-algebra.rational-modules.html#3091" class="Bound">l</a><a id="3114" class="Symbol">)</a>
<a id="3116" href="linear-algebra.rational-modules.html#3072" class="Function">Rational-Module</a> <a id="3132" href="linear-algebra.rational-modules.html#3132" class="Bound">l</a> <a id="3134" class="Symbol">=</a> <a id="3136" href="foundation-core.subtypes.html#1776" class="Function">type-subtype</a> <a id="3149" href="linear-algebra.rational-modules.html#2646" class="Function">is-rational-module-prop-Ab</a>

<a id="3177" class="Keyword">module</a> <a id="3184" href="linear-algebra.rational-modules.html#3184" class="Module">_</a>
  <a id="3188" class="Symbol">{</a><a id="3189" href="linear-algebra.rational-modules.html#3189" class="Bound">l</a> <a id="3191" class="Symbol">:</a> <a id="3193" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3198" class="Symbol">}</a> <a id="3200" class="Symbol">(</a><a id="3201" href="linear-algebra.rational-modules.html#3201" class="Bound">M</a> <a id="3203" class="Symbol">:</a> <a id="3205" href="linear-algebra.rational-modules.html#3072" class="Function">Rational-Module</a> <a id="3221" href="linear-algebra.rational-modules.html#3189" class="Bound">l</a><a id="3222" class="Symbol">)</a>
  <a id="3226" class="Keyword">where</a>

  <a id="3235" href="linear-algebra.rational-modules.html#3235" class="Function">ab-Rational-Module</a> <a id="3254" class="Symbol">:</a> <a id="3256" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="3259" href="linear-algebra.rational-modules.html#3189" class="Bound">l</a>
  <a id="3263" href="linear-algebra.rational-modules.html#3235" class="Function">ab-Rational-Module</a> <a id="3282" class="Symbol">=</a> <a id="3284" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3288" href="linear-algebra.rational-modules.html#3201" class="Bound">M</a>

  <a id="3293" href="linear-algebra.rational-modules.html#3293" class="Function">is-rational-extension-endomorphism-ring-ab-Rational-Module</a> <a id="3352" class="Symbol">:</a>
    <a id="3358" href="ring-theory.ring-extensions-rational-numbers.html#3240" class="Function">is-rational-extension-Ring</a> <a id="3385" class="Symbol">(</a><a id="3386" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="3407" href="linear-algebra.rational-modules.html#3235" class="Function">ab-Rational-Module</a><a id="3425" class="Symbol">)</a>
  <a id="3429" href="linear-algebra.rational-modules.html#3293" class="Function">is-rational-extension-endomorphism-ring-ab-Rational-Module</a> <a id="3488" class="Symbol">=</a> <a id="3490" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3494" href="linear-algebra.rational-modules.html#3201" class="Bound">M</a>

  <a id="3499" href="linear-algebra.rational-modules.html#3499" class="Function">rational-extension-ring-endomorphism-Rational-Module</a> <a id="3552" class="Symbol">:</a>
    <a id="3558" href="ring-theory.ring-extensions-rational-numbers.html#3568" class="Function">Rational-Extension-Ring</a> <a id="3582" href="linear-algebra.rational-modules.html#3189" class="Bound">l</a>
  <a id="3586" href="linear-algebra.rational-modules.html#3499" class="Function">rational-extension-ring-endomorphism-Rational-Module</a> <a id="3639" class="Symbol">=</a>
    <a id="3645" class="Symbol">(</a> <a id="3647" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="3668" href="linear-algebra.rational-modules.html#3235" class="Function">ab-Rational-Module</a> <a id="3687" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="3695" href="linear-algebra.rational-modules.html#3293" class="Function">is-rational-extension-endomorphism-ring-ab-Rational-Module</a><a id="3753" class="Symbol">)</a>
</pre>
### The predicate on abelian groups of being a left module on the rationals

<pre class="Agda"><a id="3845" class="Keyword">module</a> <a id="3852" href="linear-algebra.rational-modules.html#3852" class="Module">_</a>
  <a id="3856" class="Symbol">{</a><a id="3857" href="linear-algebra.rational-modules.html#3857" class="Bound">l</a> <a id="3859" class="Symbol">:</a> <a id="3861" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3866" class="Symbol">}</a> <a id="3868" class="Symbol">(</a><a id="3869" href="linear-algebra.rational-modules.html#3869" class="Bound">A</a> <a id="3871" class="Symbol">:</a> <a id="3873" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="3876" href="linear-algebra.rational-modules.html#3857" class="Bound">l</a><a id="3877" class="Symbol">)</a>
  <a id="3881" class="Keyword">where</a>

  <a id="3890" href="linear-algebra.rational-modules.html#3890" class="Function">is-rational-left-module-Ab</a> <a id="3917" class="Symbol">:</a> <a id="3919" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3922" href="linear-algebra.rational-modules.html#3857" class="Bound">l</a>
  <a id="3926" href="linear-algebra.rational-modules.html#3890" class="Function">is-rational-left-module-Ab</a> <a id="3953" class="Symbol">=</a>
    <a id="3959" href="ring-theory.homomorphisms-rings.html#3643" class="Function">hom-Ring</a> <a id="3968" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="3975" class="Symbol">(</a><a id="3976" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="3997" href="linear-algebra.rational-modules.html#3869" class="Bound">A</a><a id="3998" class="Symbol">)</a>

  <a id="4003" href="linear-algebra.rational-modules.html#4003" class="Function">is-prop-is-rational-left-module-Ab</a> <a id="4038" class="Symbol">:</a>
    <a id="4044" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="4052" href="linear-algebra.rational-modules.html#3890" class="Function">is-rational-left-module-Ab</a>
  <a id="4081" href="linear-algebra.rational-modules.html#4003" class="Function">is-prop-is-rational-left-module-Ab</a> <a id="4116" class="Symbol">=</a>
    <a id="4122" href="ring-theory.ring-extensions-rational-numbers.html#39875" class="Function">is-prop-has-rational-hom-Ring</a> <a id="4152" class="Symbol">(</a><a id="4153" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="4174" href="linear-algebra.rational-modules.html#3869" class="Bound">A</a><a id="4175" class="Symbol">)</a>

  <a id="4180" href="linear-algebra.rational-modules.html#4180" class="Function">subtype-is-rational-left-module</a> <a id="4212" class="Symbol">:</a> <a id="4214" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4219" href="linear-algebra.rational-modules.html#3857" class="Bound">l</a>
  <a id="4223" href="linear-algebra.rational-modules.html#4180" class="Function">subtype-is-rational-left-module</a> <a id="4255" class="Symbol">=</a>
    <a id="4261" class="Symbol">(</a> <a id="4263" href="linear-algebra.rational-modules.html#3890" class="Function">is-rational-left-module-Ab</a> <a id="4290" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="4298" href="linear-algebra.rational-modules.html#4003" class="Function">is-prop-is-rational-left-module-Ab</a><a id="4332" class="Symbol">)</a>
</pre>
### The predicate on abelian groups of being a right module on the rationals

<pre class="Agda"><a id="4425" class="Keyword">module</a> <a id="4432" href="linear-algebra.rational-modules.html#4432" class="Module">_</a>
  <a id="4436" class="Symbol">{</a><a id="4437" href="linear-algebra.rational-modules.html#4437" class="Bound">l</a> <a id="4439" class="Symbol">:</a> <a id="4441" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4446" class="Symbol">}</a> <a id="4448" class="Symbol">(</a><a id="4449" href="linear-algebra.rational-modules.html#4449" class="Bound">A</a> <a id="4451" class="Symbol">:</a> <a id="4453" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="4456" href="linear-algebra.rational-modules.html#4437" class="Bound">l</a><a id="4457" class="Symbol">)</a>
  <a id="4461" class="Keyword">where</a>

  <a id="4470" href="linear-algebra.rational-modules.html#4470" class="Function">is-rational-right-module-Ab</a> <a id="4498" class="Symbol">:</a> <a id="4500" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4503" href="linear-algebra.rational-modules.html#4437" class="Bound">l</a>
  <a id="4507" href="linear-algebra.rational-modules.html#4470" class="Function">is-rational-right-module-Ab</a> <a id="4535" class="Symbol">=</a>
    <a id="4541" href="ring-theory.homomorphisms-rings.html#3643" class="Function">hom-Ring</a> <a id="4550" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="4557" class="Symbol">(</a><a id="4558" href="ring-theory.opposite-rings.html#487" class="Function">op-Ring</a> <a id="4566" class="Symbol">(</a><a id="4567" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="4588" href="linear-algebra.rational-modules.html#4449" class="Bound">A</a><a id="4589" class="Symbol">))</a>

  <a id="4595" href="linear-algebra.rational-modules.html#4595" class="Function">is-prop-is-rational-right-module-Ab</a> <a id="4631" class="Symbol">:</a>
    <a id="4637" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="4645" href="linear-algebra.rational-modules.html#4470" class="Function">is-rational-right-module-Ab</a>
  <a id="4675" href="linear-algebra.rational-modules.html#4595" class="Function">is-prop-is-rational-right-module-Ab</a> <a id="4711" class="Symbol">=</a>
    <a id="4717" href="ring-theory.ring-extensions-rational-numbers.html#39875" class="Function">is-prop-has-rational-hom-Ring</a> <a id="4747" class="Symbol">(</a><a id="4748" href="ring-theory.opposite-rings.html#487" class="Function">op-Ring</a> <a id="4756" class="Symbol">(</a><a id="4757" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="4778" href="linear-algebra.rational-modules.html#4449" class="Bound">A</a><a id="4779" class="Symbol">))</a>

  <a id="4785" href="linear-algebra.rational-modules.html#4785" class="Function">subtype-is-rational-right-module</a> <a id="4818" class="Symbol">:</a> <a id="4820" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="4825" href="linear-algebra.rational-modules.html#4437" class="Bound">l</a>
  <a id="4829" href="linear-algebra.rational-modules.html#4785" class="Function">subtype-is-rational-right-module</a> <a id="4862" class="Symbol">=</a>
    <a id="4868" class="Symbol">(</a> <a id="4870" href="linear-algebra.rational-modules.html#4470" class="Function">is-rational-right-module-Ab</a> <a id="4898" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
      <a id="4906" href="linear-algebra.rational-modules.html#4595" class="Function">is-prop-is-rational-right-module-Ab</a><a id="4941" class="Symbol">)</a>
</pre>
## Properties

### The type of rational modules is equivalent to the type of left modules over the ring of rational numbers

<pre class="Agda"><a id="5081" class="Keyword">module</a> <a id="5088" href="linear-algebra.rational-modules.html#5088" class="Module">_</a>
  <a id="5092" class="Symbol">{</a><a id="5093" href="linear-algebra.rational-modules.html#5093" class="Bound">l</a> <a id="5095" class="Symbol">:</a> <a id="5097" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5102" class="Symbol">}</a> <a id="5104" class="Symbol">(</a><a id="5105" href="linear-algebra.rational-modules.html#5105" class="Bound">A</a> <a id="5107" class="Symbol">:</a> <a id="5109" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="5112" href="linear-algebra.rational-modules.html#5093" class="Bound">l</a><a id="5113" class="Symbol">)</a>
  <a id="5117" class="Keyword">where</a>

  <a id="5126" href="linear-algebra.rational-modules.html#5126" class="Function">is-rational-module-is-rational-left-module-Ab</a> <a id="5172" class="Symbol">:</a>
    <a id="5178" href="linear-algebra.rational-modules.html#3890" class="Function">is-rational-left-module-Ab</a> <a id="5205" href="linear-algebra.rational-modules.html#5105" class="Bound">A</a> <a id="5207" class="Symbol">→</a>
    <a id="5213" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a> <a id="5235" href="linear-algebra.rational-modules.html#5105" class="Bound">A</a>
  <a id="5239" href="linear-algebra.rational-modules.html#5126" class="Function">is-rational-module-is-rational-left-module-Ab</a> <a id="5285" href="linear-algebra.rational-modules.html#5285" class="Bound">H</a> <a id="5287" class="Symbol">=</a>
    <a id="5293" href="ring-theory.ring-extensions-rational-numbers.html#12385" class="Function">is-rational-extension-has-rational-hom-Ring</a>
      <a id="5343" class="Symbol">(</a> <a id="5345" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="5366" href="linear-algebra.rational-modules.html#5105" class="Bound">A</a><a id="5367" class="Symbol">)</a>
      <a id="5375" class="Symbol">(</a> <a id="5377" href="linear-algebra.rational-modules.html#5285" class="Bound">H</a><a id="5378" class="Symbol">)</a>

  <a id="5383" href="linear-algebra.rational-modules.html#5383" class="Function">is-rational-left-module-is-rational-module-Ab</a> <a id="5429" class="Symbol">:</a>
    <a id="5435" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a> <a id="5457" href="linear-algebra.rational-modules.html#5105" class="Bound">A</a> <a id="5459" class="Symbol">→</a>
    <a id="5465" href="linear-algebra.rational-modules.html#3890" class="Function">is-rational-left-module-Ab</a> <a id="5492" href="linear-algebra.rational-modules.html#5105" class="Bound">A</a>
  <a id="5496" href="linear-algebra.rational-modules.html#5383" class="Function">is-rational-left-module-is-rational-module-Ab</a> <a id="5542" href="linear-algebra.rational-modules.html#5542" class="Bound">H</a> <a id="5544" class="Symbol">=</a>
    <a id="5550" href="ring-theory.ring-extensions-rational-numbers.html#44086" class="Function">initial-hom-Rational-Extension-Ring</a> <a id="5586" class="Symbol">(</a><a id="5587" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="5608" href="linear-algebra.rational-modules.html#5105" class="Bound">A</a> <a id="5610" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5612" href="linear-algebra.rational-modules.html#5542" class="Bound">H</a><a id="5613" class="Symbol">)</a>

<a id="5616" class="Keyword">module</a> <a id="5623" href="linear-algebra.rational-modules.html#5623" class="Module">_</a>
  <a id="5627" class="Symbol">{</a><a id="5628" href="linear-algebra.rational-modules.html#5628" class="Bound">l</a> <a id="5630" class="Symbol">:</a> <a id="5632" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5637" class="Symbol">}</a>
  <a id="5641" class="Keyword">where</a>

  <a id="5650" href="linear-algebra.rational-modules.html#5650" class="Function">equiv-left-module-Rational-Module</a> <a id="5684" class="Symbol">:</a>
    <a id="5690" href="linear-algebra.left-modules-rings.html#1651" class="Function">left-module-Ring</a> <a id="5707" href="linear-algebra.rational-modules.html#5628" class="Bound">l</a> <a id="5709" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="5716" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="5718" href="linear-algebra.rational-modules.html#3072" class="Function">Rational-Module</a> <a id="5734" href="linear-algebra.rational-modules.html#5628" class="Bound">l</a>
  <a id="5738" href="linear-algebra.rational-modules.html#5650" class="Function">equiv-left-module-Rational-Module</a> <a id="5772" class="Symbol">=</a>
    <a id="5778" href="foundation-core.subtypes.html#8676" class="Function">equiv-type-subtype</a>
      <a id="5803" class="Symbol">(</a> <a id="5805" href="linear-algebra.rational-modules.html#4003" class="Function">is-prop-is-rational-left-module-Ab</a><a id="5839" class="Symbol">)</a>
      <a id="5847" class="Symbol">(</a> <a id="5849" href="linear-algebra.rational-modules.html#2876" class="Function">is-prop-is-rational-module-Ab</a><a id="5878" class="Symbol">)</a>
      <a id="5886" class="Symbol">(</a> <a id="5888" href="linear-algebra.rational-modules.html#5126" class="Function">is-rational-module-is-rational-left-module-Ab</a><a id="5933" class="Symbol">)</a>
      <a id="5941" class="Symbol">(</a> <a id="5943" href="linear-algebra.rational-modules.html#5383" class="Function">is-rational-left-module-is-rational-module-Ab</a><a id="5988" class="Symbol">)</a>
</pre>
### A rational module is a left module over the ring of rational numbers

<pre class="Agda"><a id="6077" class="Keyword">module</a> <a id="6084" href="linear-algebra.rational-modules.html#6084" class="Module">_</a>
  <a id="6088" class="Symbol">{</a><a id="6089" href="linear-algebra.rational-modules.html#6089" class="Bound">l</a> <a id="6091" class="Symbol">:</a> <a id="6093" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6098" class="Symbol">}</a> <a id="6100" class="Symbol">(</a><a id="6101" href="linear-algebra.rational-modules.html#6101" class="Bound">M</a> <a id="6103" class="Symbol">:</a> <a id="6105" href="linear-algebra.rational-modules.html#3072" class="Function">Rational-Module</a> <a id="6121" href="linear-algebra.rational-modules.html#6089" class="Bound">l</a><a id="6122" class="Symbol">)</a>
  <a id="6126" class="Keyword">where</a>

  <a id="6135" href="linear-algebra.rational-modules.html#6135" class="Function">left-module-Rational-Module</a> <a id="6163" class="Symbol">:</a> <a id="6165" href="linear-algebra.left-modules-rings.html#1651" class="Function">left-module-Ring</a> <a id="6182" href="linear-algebra.rational-modules.html#6089" class="Bound">l</a> <a id="6184" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a>
  <a id="6193" href="linear-algebra.rational-modules.html#6135" class="Function">left-module-Rational-Module</a> <a id="6221" class="Symbol">=</a>
    <a id="6227" href="foundation-core.functoriality-dependent-pair-types.html#1778" class="Function">tot</a> <a id="6231" href="linear-algebra.rational-modules.html#5383" class="Function">is-rational-left-module-is-rational-module-Ab</a> <a id="6277" href="linear-algebra.rational-modules.html#6101" class="Bound">M</a>
</pre>
### The type of rational modules is equivalent to the type of right modules over the ring of rational numbers

<pre class="Agda"><a id="6403" class="Keyword">module</a> <a id="6410" href="linear-algebra.rational-modules.html#6410" class="Module">_</a>
  <a id="6414" class="Symbol">{</a><a id="6415" href="linear-algebra.rational-modules.html#6415" class="Bound">l</a> <a id="6417" class="Symbol">:</a> <a id="6419" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6424" class="Symbol">}</a> <a id="6426" class="Symbol">(</a><a id="6427" href="linear-algebra.rational-modules.html#6427" class="Bound">A</a> <a id="6429" class="Symbol">:</a> <a id="6431" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="6434" href="linear-algebra.rational-modules.html#6415" class="Bound">l</a><a id="6435" class="Symbol">)</a>
  <a id="6439" class="Keyword">where</a>

  <a id="6448" href="linear-algebra.rational-modules.html#6448" class="Function">is-rational-module-is-rational-right-module-Ab</a> <a id="6495" class="Symbol">:</a>
    <a id="6501" href="linear-algebra.rational-modules.html#4470" class="Function">is-rational-right-module-Ab</a> <a id="6529" href="linear-algebra.rational-modules.html#6427" class="Bound">A</a> <a id="6531" class="Symbol">→</a>
    <a id="6537" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a> <a id="6559" href="linear-algebra.rational-modules.html#6427" class="Bound">A</a>
  <a id="6563" href="linear-algebra.rational-modules.html#6448" class="Function">is-rational-module-is-rational-right-module-Ab</a> <a id="6610" href="linear-algebra.rational-modules.html#6610" class="Bound">H</a> <a id="6612" class="Symbol">=</a>
    <a id="6618" href="ring-theory.opposite-ring-extensions-rational-numbers.html#1369" class="Function">is-rational-extension-is-rational-extension-op-Ring</a>
      <a id="6676" class="Symbol">(</a> <a id="6678" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="6699" href="linear-algebra.rational-modules.html#6427" class="Bound">A</a><a id="6700" class="Symbol">)</a>
      <a id="6708" class="Symbol">(</a> <a id="6710" href="ring-theory.ring-extensions-rational-numbers.html#12385" class="Function">is-rational-extension-has-rational-hom-Ring</a>
        <a id="6762" class="Symbol">(</a> <a id="6764" href="ring-theory.opposite-rings.html#487" class="Function">op-Ring</a> <a id="6772" class="Symbol">(</a><a id="6773" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="6794" href="linear-algebra.rational-modules.html#6427" class="Bound">A</a><a id="6795" class="Symbol">))</a>
        <a id="6806" class="Symbol">(</a> <a id="6808" href="linear-algebra.rational-modules.html#6610" class="Bound">H</a><a id="6809" class="Symbol">))</a>

  <a id="6815" href="linear-algebra.rational-modules.html#6815" class="Function">is-rational-right-module-is-rational-module-Ab</a> <a id="6862" class="Symbol">:</a>
    <a id="6868" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a> <a id="6890" href="linear-algebra.rational-modules.html#6427" class="Bound">A</a> <a id="6892" class="Symbol">→</a>
    <a id="6898" href="linear-algebra.rational-modules.html#4470" class="Function">is-rational-right-module-Ab</a> <a id="6926" href="linear-algebra.rational-modules.html#6427" class="Bound">A</a>
  <a id="6930" href="linear-algebra.rational-modules.html#6815" class="Function">is-rational-right-module-is-rational-module-Ab</a> <a id="6977" href="linear-algebra.rational-modules.html#6977" class="Bound">H</a> <a id="6979" class="Symbol">=</a>
    <a id="6985" href="ring-theory.ring-extensions-rational-numbers.html#44086" class="Function">initial-hom-Rational-Extension-Ring</a>
      <a id="7027" class="Symbol">(</a> <a id="7029" href="ring-theory.opposite-ring-extensions-rational-numbers.html#1921" class="Function">op-Rational-Extension-Ring</a> <a id="7056" class="Symbol">(</a><a id="7057" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="7078" href="linear-algebra.rational-modules.html#6427" class="Bound">A</a> <a id="7080" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="7082" href="linear-algebra.rational-modules.html#6977" class="Bound">H</a><a id="7083" class="Symbol">))</a>

<a id="7087" class="Keyword">module</a> <a id="7094" href="linear-algebra.rational-modules.html#7094" class="Module">_</a>
  <a id="7098" class="Symbol">{</a><a id="7099" href="linear-algebra.rational-modules.html#7099" class="Bound">l</a> <a id="7101" class="Symbol">:</a> <a id="7103" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7108" class="Symbol">}</a>
  <a id="7112" class="Keyword">where</a>

  <a id="7121" href="linear-algebra.rational-modules.html#7121" class="Function">equiv-right-module-Rational-Module</a> <a id="7156" class="Symbol">:</a>
    <a id="7162" href="linear-algebra.right-modules-rings.html#1235" class="Function">right-module-Ring</a> <a id="7180" href="linear-algebra.rational-modules.html#7099" class="Bound">l</a> <a id="7182" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a> <a id="7189" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="7191" href="linear-algebra.rational-modules.html#3072" class="Function">Rational-Module</a> <a id="7207" href="linear-algebra.rational-modules.html#7099" class="Bound">l</a>
  <a id="7211" href="linear-algebra.rational-modules.html#7121" class="Function">equiv-right-module-Rational-Module</a> <a id="7246" class="Symbol">=</a>
    <a id="7252" href="foundation-core.subtypes.html#8676" class="Function">equiv-type-subtype</a>
      <a id="7277" class="Symbol">(</a> <a id="7279" href="linear-algebra.rational-modules.html#4595" class="Function">is-prop-is-rational-right-module-Ab</a><a id="7314" class="Symbol">)</a>
      <a id="7322" class="Symbol">(</a> <a id="7324" href="linear-algebra.rational-modules.html#2876" class="Function">is-prop-is-rational-module-Ab</a><a id="7353" class="Symbol">)</a>
      <a id="7361" class="Symbol">(</a> <a id="7363" href="linear-algebra.rational-modules.html#6448" class="Function">is-rational-module-is-rational-right-module-Ab</a><a id="7409" class="Symbol">)</a>
      <a id="7417" class="Symbol">(</a> <a id="7419" href="linear-algebra.rational-modules.html#6815" class="Function">is-rational-right-module-is-rational-module-Ab</a><a id="7465" class="Symbol">)</a>
</pre>
### A rational module is a right module over the ring of rational numbers

<pre class="Agda"><a id="7555" class="Keyword">module</a> <a id="7562" href="linear-algebra.rational-modules.html#7562" class="Module">_</a>
  <a id="7566" class="Symbol">{</a><a id="7567" href="linear-algebra.rational-modules.html#7567" class="Bound">l</a> <a id="7569" class="Symbol">:</a> <a id="7571" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7576" class="Symbol">}</a> <a id="7578" class="Symbol">(</a><a id="7579" href="linear-algebra.rational-modules.html#7579" class="Bound">M</a> <a id="7581" class="Symbol">:</a> <a id="7583" href="linear-algebra.rational-modules.html#3072" class="Function">Rational-Module</a> <a id="7599" href="linear-algebra.rational-modules.html#7567" class="Bound">l</a><a id="7600" class="Symbol">)</a>
  <a id="7604" class="Keyword">where</a>

  <a id="7613" href="linear-algebra.rational-modules.html#7613" class="Function">right-module-Rational-Module</a> <a id="7642" class="Symbol">:</a> <a id="7644" href="linear-algebra.right-modules-rings.html#1235" class="Function">right-module-Ring</a> <a id="7662" href="linear-algebra.rational-modules.html#7567" class="Bound">l</a> <a id="7664" href="elementary-number-theory.ring-of-rational-numbers.html#1885" class="Function">ring-ℚ</a>
  <a id="7673" href="linear-algebra.rational-modules.html#7613" class="Function">right-module-Rational-Module</a> <a id="7702" class="Symbol">=</a>
    <a id="7708" href="foundation-core.functoriality-dependent-pair-types.html#1778" class="Function">tot</a> <a id="7712" href="linear-algebra.rational-modules.html#6815" class="Function">is-rational-right-module-is-rational-module-Ab</a> <a id="7759" href="linear-algebra.rational-modules.html#7579" class="Bound">M</a>
</pre>
### An abelian group is a rational module if and only if the actions of positive integers are automorphisms

<pre class="Agda"><a id="7883" class="Keyword">module</a> <a id="7890" href="linear-algebra.rational-modules.html#7890" class="Module">_</a>
  <a id="7894" class="Symbol">{</a><a id="7895" href="linear-algebra.rational-modules.html#7895" class="Bound">l</a> <a id="7897" class="Symbol">:</a> <a id="7899" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7904" class="Symbol">}</a> <a id="7906" class="Symbol">(</a><a id="7907" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="7909" class="Symbol">:</a> <a id="7911" href="group-theory.abelian-groups.html#2530" class="Function">Ab</a> <a id="7914" href="linear-algebra.rational-modules.html#7895" class="Bound">l</a><a id="7915" class="Symbol">)</a>
  <a id="7919" class="Keyword">where</a>

  <a id="7928" href="linear-algebra.rational-modules.html#7928" class="Function">is-iso-positive-integer-multiple-is-rational-module-Ab</a> <a id="7983" class="Symbol">:</a>
    <a id="7989" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a> <a id="8011" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8013" class="Symbol">→</a>
    <a id="8019" class="Symbol">(</a><a id="8020" href="linear-algebra.rational-modules.html#8020" class="Bound">k</a> <a id="8022" class="Symbol">:</a> <a id="8024" href="elementary-number-theory.positive-integers.html#2479" class="Function">ℤ⁺</a><a id="8026" class="Symbol">)</a> <a id="8028" class="Symbol">→</a>
    <a id="8034" href="group-theory.isomorphisms-abelian-groups.html#1236" class="Function">is-iso-Ab</a> <a id="8044" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8046" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8048" class="Symbol">(</a><a id="8049" href="group-theory.integer-multiples-of-elements-abelian-groups.html#7196" class="Function">hom-integer-multiple-Ab</a> <a id="8073" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8075" class="Symbol">(</a><a id="8076" href="elementary-number-theory.positive-integers.html#2659" class="Function">int-positive-ℤ</a> <a id="8091" href="linear-algebra.rational-modules.html#8020" class="Bound">k</a><a id="8092" class="Symbol">))</a>
  <a id="8097" href="linear-algebra.rational-modules.html#7928" class="Function">is-iso-positive-integer-multiple-is-rational-module-Ab</a> <a id="8152" href="linear-algebra.rational-modules.html#8152" class="Bound">H</a> <a id="8154" href="linear-algebra.rational-modules.html#8154" class="Bound">k</a> <a id="8156" class="Symbol">=</a>
    <a id="8162" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a>
      <a id="8171" class="Symbol">(</a> <a id="8173" href="group-theory.isomorphisms-abelian-groups.html#1236" class="Function">is-iso-Ab</a> <a id="8183" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8185" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a><a id="8186" class="Symbol">)</a>
      <a id="8194" class="Symbol">(</a> <a id="8196" href="group-theory.endomorphism-rings-abelian-groups.html#2549" class="Function">htpy-initial-hom-integer-multiple-endomorphism-ring-Ab</a>
        <a id="8259" class="Symbol">(</a> <a id="8261" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a><a id="8262" class="Symbol">)</a>
        <a id="8272" class="Symbol">(</a> <a id="8274" href="elementary-number-theory.positive-integers.html#2659" class="Function">int-positive-ℤ</a> <a id="8289" href="linear-algebra.rational-modules.html#8154" class="Bound">k</a><a id="8290" class="Symbol">))</a>
      <a id="8299" class="Symbol">(</a> <a id="8301" href="foundation.dependent-pair-types.html#873" class="Function">ind-Σ</a>
        <a id="8315" class="Symbol">(</a> <a id="8317" href="linear-algebra.rational-modules.html#3293" class="Function">is-rational-extension-endomorphism-ring-ab-Rational-Module</a> <a id="8376" class="Symbol">(</a><a id="8377" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8379" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="8381" href="linear-algebra.rational-modules.html#8152" class="Bound">H</a><a id="8382" class="Symbol">))</a>
        <a id="8393" class="Symbol">(</a> <a id="8395" href="linear-algebra.rational-modules.html#8154" class="Bound">k</a><a id="8396" class="Symbol">))</a>

  <a id="8402" href="linear-algebra.rational-modules.html#8402" class="Function">is-rational-left-module-is-iso-positive-integer-multiple-Ab</a> <a id="8462" class="Symbol">:</a>
    <a id="8468" class="Symbol">((</a><a id="8470" href="linear-algebra.rational-modules.html#8470" class="Bound">k</a> <a id="8472" class="Symbol">:</a> <a id="8474" href="elementary-number-theory.positive-integers.html#2479" class="Function">ℤ⁺</a><a id="8476" class="Symbol">)</a> <a id="8478" class="Symbol">→</a> <a id="8480" href="group-theory.isomorphisms-abelian-groups.html#1236" class="Function">is-iso-Ab</a> <a id="8490" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8492" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8494" class="Symbol">(</a><a id="8495" href="group-theory.integer-multiples-of-elements-abelian-groups.html#7196" class="Function">hom-integer-multiple-Ab</a> <a id="8519" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8521" class="Symbol">(</a><a id="8522" href="elementary-number-theory.positive-integers.html#2659" class="Function">int-positive-ℤ</a> <a id="8537" href="linear-algebra.rational-modules.html#8470" class="Bound">k</a><a id="8538" class="Symbol">)))</a> <a id="8542" class="Symbol">→</a>
    <a id="8548" href="linear-algebra.rational-modules.html#2777" class="Function">is-rational-module-Ab</a> <a id="8570" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a>
  <a id="8574" href="linear-algebra.rational-modules.html#8402" class="Function">is-rational-left-module-is-iso-positive-integer-multiple-Ab</a>
    <a id="8638" href="linear-algebra.rational-modules.html#8638" class="Bound">H</a> <a id="8640" href="linear-algebra.rational-modules.html#8640" class="Bound">k</a> <a id="8642" href="linear-algebra.rational-modules.html#8642" class="Bound">k&gt;0</a> <a id="8646" class="Symbol">=</a>
    <a id="8652" href="foundation.transport-along-identifications.html#1082" class="Function">inv-tr</a>
      <a id="8665" class="Symbol">(</a> <a id="8667" href="ring-theory.invertible-elements-rings.html#3693" class="Function">is-invertible-element-Ring</a> <a id="8694" class="Symbol">(</a><a id="8695" href="group-theory.endomorphism-rings-abelian-groups.html#1288" class="Function">endomorphism-ring-Ab</a> <a id="8716" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a><a id="8717" class="Symbol">))</a>
      <a id="8726" class="Symbol">(</a> <a id="8728" href="group-theory.endomorphism-rings-abelian-groups.html#2549" class="Function">htpy-initial-hom-integer-multiple-endomorphism-ring-Ab</a> <a id="8783" href="linear-algebra.rational-modules.html#7907" class="Bound">M</a> <a id="8785" href="linear-algebra.rational-modules.html#8640" class="Bound">k</a><a id="8786" class="Symbol">)</a>
      <a id="8794" class="Symbol">(</a> <a id="8796" href="foundation.dependent-pair-types.html#1278" class="Function">ev-pair</a> <a id="8804" href="linear-algebra.rational-modules.html#8638" class="Bound">H</a> <a id="8806" href="linear-algebra.rational-modules.html#8640" class="Bound">k</a> <a id="8808" href="linear-algebra.rational-modules.html#8642" class="Bound">k&gt;0</a><a id="8811" class="Symbol">)</a>
</pre>
## External links

- [rational vector space](https://ncatlab.org/nlab/show/rational+vector+space)
  at $n$Lab
