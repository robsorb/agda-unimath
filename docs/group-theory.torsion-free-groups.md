# Torsion-free groups

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="group-theory.torsion-free-groups.html" class="Module">group-theory.torsion-free-groups</a> <a id="72" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="128" class="Keyword">open</a> <a id="133" class="Keyword">import</a> <a id="140" href="elementary-number-theory.group-of-integers.html" class="Module">elementary-number-theory.group-of-integers</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="elementary-number-theory.nonzero-integers.html" class="Module">elementary-number-theory.nonzero-integers</a>

<a id="238" class="Keyword">open</a> <a id="243" class="Keyword">import</a> <a id="250" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="383" class="Keyword">open</a> <a id="388" class="Keyword">import</a> <a id="395" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="419" class="Keyword">open</a> <a id="424" class="Keyword">import</a> <a id="431" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="469" class="Keyword">open</a> <a id="474" class="Keyword">import</a> <a id="481" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="530" class="Keyword">open</a> <a id="535" class="Keyword">import</a> <a id="542" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="568" class="Keyword">open</a> <a id="573" class="Keyword">import</a> <a id="580" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="612" class="Keyword">open</a> <a id="617" class="Keyword">import</a> <a id="624" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="648" class="Keyword">open</a> <a id="653" class="Keyword">import</a> <a id="660" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="676" class="Keyword">open</a> <a id="681" class="Keyword">import</a> <a id="688" href="foundation.singleton-subtypes.html" class="Module">foundation.singleton-subtypes</a>
<a id="718" class="Keyword">open</a> <a id="723" class="Keyword">import</a> <a id="730" href="foundation.standard-pullbacks.html" class="Module">foundation.standard-pullbacks</a>
<a id="760" class="Keyword">open</a> <a id="765" class="Keyword">import</a> <a id="772" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="800" class="Keyword">open</a> <a id="805" class="Keyword">import</a> <a id="812" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="832" class="Keyword">open</a> <a id="837" class="Keyword">import</a> <a id="844" href="group-theory.integer-powers-of-elements-groups.html" class="Module">group-theory.integer-powers-of-elements-groups</a>
<a id="891" class="Keyword">open</a> <a id="896" class="Keyword">import</a> <a id="903" href="group-theory.orders-of-elements-groups.html" class="Module">group-theory.orders-of-elements-groups</a>
<a id="942" class="Keyword">open</a> <a id="947" class="Keyword">import</a> <a id="954" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
<a id="977" class="Keyword">open</a> <a id="982" class="Keyword">import</a> <a id="989" href="group-theory.torsion-elements-groups.html" class="Module">group-theory.torsion-elements-groups</a>
</pre>
</details>

## Idea

A **torsion-free group** is a [group](group-theory.groups.md) `G` in which any
element of finite [order](group-theory.orders-of-elements-groups.md) is the
identity element. In other words, torsion-free groups are groups in which the
condition

```text
  ∀ (k : nonzero-ℤ), xᵏ ＝ 1 → x ＝ 1
```

holds for all elements `x : G`. This condition can be formulated in several
[equivalent](foundation.logical-equivalences.md) ways:

1. `∀ (k : nonzero-ℤ), xᵏ ＝ 1 → x ＝ 1`.
2. The [subset](group-theory.subsets-groups.md) of `G` of
   [torsion elements](group-theory.torsion-elements-groups.md) is a
   [singleton subtype](foundation.singleton-subtypes.md).
3. The map `p` in the [pullback square](foundation-core.pullbacks.md)
   ```text
             q
       · ---------> Prop
       | ⌟            |
      p|              | P ↦ {k : ℤ ∣ (k ＝ 0) ∨ P}
       ∨              ∨
       G -------> Subgroup ℤ
          order
   ```
   is an [equivalence](foundation.equivalences.md).

## Definitions

### The predicate of being a torsion-free group

<pre class="Agda"><a id="2098" class="Keyword">module</a> <a id="2105" href="group-theory.torsion-free-groups.html#2105" class="Module">_</a>
  <a id="2109" class="Symbol">{</a><a id="2110" href="group-theory.torsion-free-groups.html#2110" class="Bound">l1</a> <a id="2113" class="Symbol">:</a> <a id="2115" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2120" class="Symbol">}</a> <a id="2122" class="Symbol">(</a><a id="2123" href="group-theory.torsion-free-groups.html#2123" class="Bound">G</a> <a id="2125" class="Symbol">:</a> <a id="2127" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="2133" href="group-theory.torsion-free-groups.html#2110" class="Bound">l1</a><a id="2135" class="Symbol">)</a>
  <a id="2139" class="Keyword">where</a>

  <a id="2148" href="group-theory.torsion-free-groups.html#2148" class="Function">is-torsion-free-prop-Group</a> <a id="2175" class="Symbol">:</a> <a id="2177" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2182" href="group-theory.torsion-free-groups.html#2110" class="Bound">l1</a>
  <a id="2187" href="group-theory.torsion-free-groups.html#2148" class="Function">is-torsion-free-prop-Group</a> <a id="2214" class="Symbol">=</a>
    <a id="2220" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="2233" class="Symbol">(</a> <a id="2235" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="2246" href="group-theory.torsion-free-groups.html#2123" class="Bound">G</a><a id="2247" class="Symbol">)</a>
      <a id="2255" class="Symbol">(</a> <a id="2257" class="Symbol">λ</a> <a id="2259" href="group-theory.torsion-free-groups.html#2259" class="Bound">x</a> <a id="2261" class="Symbol">→</a>
        <a id="2271" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
          <a id="2288" class="Symbol">(</a> <a id="2290" href="elementary-number-theory.nonzero-integers.html#1074" class="Function">nonzero-ℤ</a><a id="2299" class="Symbol">)</a>
          <a id="2311" class="Symbol">(</a> <a id="2313" class="Symbol">λ</a> <a id="2315" href="group-theory.torsion-free-groups.html#2315" class="Bound">k</a> <a id="2317" class="Symbol">→</a>
            <a id="2331" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a>
              <a id="2359" class="Symbol">(</a> <a id="2361" href="group-theory.integer-powers-of-elements-groups.html#1634" class="Function">integer-power-Group</a> <a id="2381" href="group-theory.torsion-free-groups.html#2123" class="Bound">G</a> <a id="2383" class="Symbol">(</a><a id="2384" href="elementary-number-theory.nonzero-integers.html#1177" class="Function">int-nonzero-ℤ</a> <a id="2398" href="group-theory.torsion-free-groups.html#2315" class="Bound">k</a><a id="2399" class="Symbol">)</a> <a id="2401" href="group-theory.torsion-free-groups.html#2259" class="Bound">x</a> <a id="2403" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2405" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="2416" href="group-theory.torsion-free-groups.html#2123" class="Bound">G</a><a id="2417" class="Symbol">)</a>
              <a id="2433" class="Symbol">(</a> <a id="2435" href="foundation-core.sets.html#1141" class="Function">Id-Prop</a> <a id="2443" class="Symbol">(</a><a id="2444" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="2454" href="group-theory.torsion-free-groups.html#2123" class="Bound">G</a><a id="2455" class="Symbol">)</a> <a id="2457" href="group-theory.torsion-free-groups.html#2259" class="Bound">x</a> <a id="2459" class="Symbol">(</a><a id="2460" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="2471" href="group-theory.torsion-free-groups.html#2123" class="Bound">G</a><a id="2472" class="Symbol">))))</a>

  <a id="2480" href="group-theory.torsion-free-groups.html#2480" class="Function">is-torsion-free-Group</a> <a id="2502" class="Symbol">:</a> <a id="2504" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2507" href="group-theory.torsion-free-groups.html#2110" class="Bound">l1</a>
  <a id="2512" href="group-theory.torsion-free-groups.html#2480" class="Function">is-torsion-free-Group</a> <a id="2534" class="Symbol">=</a> <a id="2536" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2546" href="group-theory.torsion-free-groups.html#2148" class="Function">is-torsion-free-prop-Group</a>

  <a id="2576" href="group-theory.torsion-free-groups.html#2576" class="Function">is-prop-is-torsion-free-Group</a> <a id="2606" class="Symbol">:</a> <a id="2608" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2616" href="group-theory.torsion-free-groups.html#2480" class="Function">is-torsion-free-Group</a>
  <a id="2640" href="group-theory.torsion-free-groups.html#2576" class="Function">is-prop-is-torsion-free-Group</a> <a id="2670" class="Symbol">=</a> <a id="2672" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2690" href="group-theory.torsion-free-groups.html#2148" class="Function">is-torsion-free-prop-Group</a>
</pre>
### The predicate that a group has a unique torsion element

<pre class="Agda"><a id="2791" class="Keyword">module</a> <a id="2798" href="group-theory.torsion-free-groups.html#2798" class="Module">_</a>
  <a id="2802" class="Symbol">{</a><a id="2803" href="group-theory.torsion-free-groups.html#2803" class="Bound">l1</a> <a id="2806" class="Symbol">:</a> <a id="2808" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2813" class="Symbol">}</a> <a id="2815" class="Symbol">(</a><a id="2816" href="group-theory.torsion-free-groups.html#2816" class="Bound">G</a> <a id="2818" class="Symbol">:</a> <a id="2820" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="2826" href="group-theory.torsion-free-groups.html#2803" class="Bound">l1</a><a id="2828" class="Symbol">)</a>
  <a id="2832" class="Keyword">where</a>

  <a id="2841" href="group-theory.torsion-free-groups.html#2841" class="Function">has-unique-torsion-element-prop-Group</a> <a id="2879" class="Symbol">:</a> <a id="2881" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2886" href="group-theory.torsion-free-groups.html#2803" class="Bound">l1</a>
  <a id="2891" href="group-theory.torsion-free-groups.html#2841" class="Function">has-unique-torsion-element-prop-Group</a> <a id="2929" class="Symbol">=</a>
    <a id="2935" href="foundation.singleton-subtypes.html#1894" class="Function">is-singleton-subtype-Prop</a> <a id="2961" class="Symbol">(</a><a id="2962" href="group-theory.torsion-elements-groups.html#1490" class="Function">is-torsion-element-prop-Group</a> <a id="2992" href="group-theory.torsion-free-groups.html#2816" class="Bound">G</a><a id="2993" class="Symbol">)</a>

  <a id="2998" href="group-theory.torsion-free-groups.html#2998" class="Function">has-unique-torsion-element-Group</a> <a id="3031" class="Symbol">:</a> <a id="3033" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3036" href="group-theory.torsion-free-groups.html#2803" class="Bound">l1</a>
  <a id="3041" href="group-theory.torsion-free-groups.html#2998" class="Function">has-unique-torsion-element-Group</a> <a id="3074" class="Symbol">=</a>
    <a id="3080" href="foundation.singleton-subtypes.html#2001" class="Function">is-singleton-subtype</a> <a id="3101" class="Symbol">(</a><a id="3102" href="group-theory.torsion-elements-groups.html#1490" class="Function">is-torsion-element-prop-Group</a> <a id="3132" href="group-theory.torsion-free-groups.html#2816" class="Bound">G</a><a id="3133" class="Symbol">)</a>

  <a id="3138" href="group-theory.torsion-free-groups.html#3138" class="Function">is-prop-has-unique-torsion-element-Group</a> <a id="3179" class="Symbol">:</a>
    <a id="3185" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3193" href="group-theory.torsion-free-groups.html#2998" class="Function">has-unique-torsion-element-Group</a>
  <a id="3228" href="group-theory.torsion-free-groups.html#3138" class="Function">is-prop-has-unique-torsion-element-Group</a> <a id="3269" class="Symbol">=</a>
    <a id="3275" href="foundation.singleton-subtypes.html#2101" class="Function">is-prop-is-singleton-subtype</a> <a id="3304" class="Symbol">(</a><a id="3305" href="group-theory.torsion-elements-groups.html#1490" class="Function">is-torsion-element-prop-Group</a> <a id="3335" href="group-theory.torsion-free-groups.html#2816" class="Bound">G</a><a id="3336" class="Symbol">)</a>
</pre>
### The predicate that the first projection of the pullback of `Prop lzero → Subgroup ℤ` along `order : G → Subgroup ℤ` is an equivalence

<pre class="Agda"><a id="3490" class="Keyword">module</a> <a id="3497" href="group-theory.torsion-free-groups.html#3497" class="Module">_</a>
  <a id="3501" class="Symbol">{</a><a id="3502" href="group-theory.torsion-free-groups.html#3502" class="Bound">l1</a> <a id="3505" class="Symbol">:</a> <a id="3507" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3512" class="Symbol">}</a> <a id="3514" class="Symbol">(</a><a id="3515" href="group-theory.torsion-free-groups.html#3515" class="Bound">G</a> <a id="3517" class="Symbol">:</a> <a id="3519" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="3525" href="group-theory.torsion-free-groups.html#3502" class="Bound">l1</a><a id="3527" class="Symbol">)</a>
  <a id="3531" class="Keyword">where</a>

  <a id="3540" href="group-theory.torsion-free-groups.html#3540" class="Function">is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Group</a> <a id="3605" class="Symbol">:</a>
    <a id="3611" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="3616" class="Symbol">(</a><a id="3617" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3622" href="group-theory.torsion-free-groups.html#3502" class="Bound">l1</a><a id="3624" class="Symbol">)</a>
  <a id="3628" href="group-theory.torsion-free-groups.html#3540" class="Function">is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Group</a> <a id="3693" class="Symbol">=</a>
    <a id="3699" href="foundation.equivalences.html#5072" class="Function">is-equiv-Prop</a>
      <a id="3719" class="Symbol">(</a> <a id="3721" href="foundation.standard-pullbacks.html#2371" class="Function">vertical-map-standard-pullback</a>
        <a id="3760" class="Symbol">{</a> <a id="3762" class="Argument">f</a> <a id="3764" class="Symbol">=</a> <a id="3766" href="group-theory.orders-of-elements-groups.html#1558" class="Function">subgroup-order-element-Group</a> <a id="3795" href="group-theory.torsion-free-groups.html#3515" class="Bound">G</a><a id="3796" class="Symbol">}</a>
        <a id="3806" class="Symbol">{</a> <a id="3808" class="Argument">g</a> <a id="3810" class="Symbol">=</a> <a id="3812" href="group-theory.subgroups.html#24206" class="Function">subgroup-Prop</a> <a id="3826" href="elementary-number-theory.group-of-integers.html#703" class="Function">ℤ-Group</a><a id="3833" class="Symbol">})</a>

  <a id="3839" href="group-theory.torsion-free-groups.html#3839" class="Function">is-equiv-first-projection-pullback-subgroup-prop-Group</a> <a id="3894" class="Symbol">:</a> <a id="3896" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3899" class="Symbol">(</a><a id="3900" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3905" href="group-theory.torsion-free-groups.html#3502" class="Bound">l1</a><a id="3907" class="Symbol">)</a>
  <a id="3911" href="group-theory.torsion-free-groups.html#3839" class="Function">is-equiv-first-projection-pullback-subgroup-prop-Group</a> <a id="3966" class="Symbol">=</a>
    <a id="3972" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="3982" href="group-theory.torsion-free-groups.html#3540" class="Function">is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Group</a>

  <a id="4050" href="group-theory.torsion-free-groups.html#4050" class="Function">is-prop-is-equiv-first-projection-pullback-subgroup-prop-Group</a> <a id="4113" class="Symbol">:</a>
    <a id="4119" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="4127" href="group-theory.torsion-free-groups.html#3839" class="Function">is-equiv-first-projection-pullback-subgroup-prop-Group</a>
  <a id="4184" href="group-theory.torsion-free-groups.html#4050" class="Function">is-prop-is-equiv-first-projection-pullback-subgroup-prop-Group</a> <a id="4247" class="Symbol">=</a>
    <a id="4253" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a>
      <a id="4277" class="Symbol">(</a> <a id="4279" href="group-theory.torsion-free-groups.html#3540" class="Function">is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Group</a><a id="4343" class="Symbol">)</a>
</pre>
## Properties

### The two definitions of torsion-free groups are equivalent

<pre class="Agda"><a id="4436" class="Keyword">module</a> <a id="4443" href="group-theory.torsion-free-groups.html#4443" class="Module">_</a>
  <a id="4447" class="Symbol">{</a><a id="4448" href="group-theory.torsion-free-groups.html#4448" class="Bound">l1</a> <a id="4451" class="Symbol">:</a> <a id="4453" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4458" class="Symbol">}</a> <a id="4460" class="Symbol">(</a><a id="4461" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a> <a id="4463" class="Symbol">:</a> <a id="4465" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="4471" href="group-theory.torsion-free-groups.html#4448" class="Bound">l1</a><a id="4473" class="Symbol">)</a>
  <a id="4477" class="Keyword">where</a>

  <a id="4486" href="group-theory.torsion-free-groups.html#4486" class="Function">is-torsion-free-has-unique-torsion-element-Group</a> <a id="4535" class="Symbol">:</a>
    <a id="4541" href="group-theory.torsion-free-groups.html#2998" class="Function">has-unique-torsion-element-Group</a> <a id="4574" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a> <a id="4576" class="Symbol">→</a> <a id="4578" href="group-theory.torsion-free-groups.html#2480" class="Function">is-torsion-free-Group</a> <a id="4600" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a>
  <a id="4604" href="group-theory.torsion-free-groups.html#4486" class="Function">is-torsion-free-has-unique-torsion-element-Group</a> <a id="4653" href="group-theory.torsion-free-groups.html#4653" class="Bound">H</a> <a id="4655" href="group-theory.torsion-free-groups.html#4655" class="Bound">x</a> <a id="4657" href="group-theory.torsion-free-groups.html#4657" class="Bound">k</a> <a id="4659" href="group-theory.torsion-free-groups.html#4659" class="Bound">p</a> <a id="4661" class="Symbol">=</a>
    <a id="4667" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4670" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4674" class="Symbol">(</a><a id="4675" href="foundation-core.contractible-types.html#1197" class="Function">eq-is-contr</a> <a id="4687" href="group-theory.torsion-free-groups.html#4653" class="Bound">H</a> <a id="4689" class="Symbol">{</a><a id="4690" href="group-theory.torsion-free-groups.html#4655" class="Bound">x</a> <a id="4692" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4694" href="foundation.existential-quantification.html#4482" class="Function">intro-exists</a> <a id="4707" href="group-theory.torsion-free-groups.html#4657" class="Bound">k</a> <a id="4709" href="group-theory.torsion-free-groups.html#4659" class="Bound">p</a><a id="4710" class="Symbol">}</a> <a id="4712" class="Symbol">{</a><a id="4713" href="group-theory.torsion-elements-groups.html#2471" class="Function">unit-torsion-element-Group</a> <a id="4740" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a><a id="4741" class="Symbol">})</a>

  <a id="4747" class="Keyword">abstract</a>
    <a id="4760" href="group-theory.torsion-free-groups.html#4760" class="Function">has-unique-torsion-element-is-torsion-free-Group</a> <a id="4809" class="Symbol">:</a>
      <a id="4817" href="group-theory.torsion-free-groups.html#2480" class="Function">is-torsion-free-Group</a> <a id="4839" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a> <a id="4841" class="Symbol">→</a> <a id="4843" href="group-theory.torsion-free-groups.html#2998" class="Function">has-unique-torsion-element-Group</a> <a id="4876" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a>
    <a id="4882" href="group-theory.torsion-free-groups.html#4760" class="Function">has-unique-torsion-element-is-torsion-free-Group</a> <a id="4931" href="group-theory.torsion-free-groups.html#4931" class="Bound">H</a> <a id="4933" class="Symbol">=</a>
      <a id="4941" href="foundation.fundamental-theorem-of-identity-types.html#2310" class="Function">fundamental-theorem-id&#39;</a>
        <a id="4973" class="Symbol">(</a> <a id="4975" class="Symbol">λ</a> <a id="4977" class="Keyword">where</a> <a id="4983" href="group-theory.torsion-free-groups.html#4983" class="Bound">x</a> <a id="4985" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="4990" class="Symbol">→</a> <a id="4992" href="group-theory.torsion-elements-groups.html#2278" class="Function">is-torsion-element-unit-Group</a> <a id="5022" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a><a id="5023" class="Symbol">)</a>
        <a id="5033" class="Symbol">(</a> <a id="5035" class="Symbol">λ</a> <a id="5037" href="group-theory.torsion-free-groups.html#5037" class="Bound">x</a> <a id="5039" class="Symbol">→</a>
          <a id="5051" href="foundation.logical-equivalences.html#4351" class="Function">is-equiv-has-converse-is-prop</a>
            <a id="5093" class="Symbol">(</a> <a id="5095" href="group-theory.groups.html#2640" class="Function">is-set-type-Group</a> <a id="5113" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a> <a id="5115" class="Symbol">(</a><a id="5116" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="5127" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a><a id="5128" class="Symbol">)</a> <a id="5130" href="group-theory.torsion-free-groups.html#5037" class="Bound">x</a><a id="5131" class="Symbol">)</a>
            <a id="5145" class="Symbol">(</a> <a id="5147" href="group-theory.torsion-elements-groups.html#1789" class="Function">is-prop-is-torsion-element-Group</a> <a id="5180" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a> <a id="5182" href="group-theory.torsion-free-groups.html#5037" class="Bound">x</a><a id="5183" class="Symbol">)</a>
            <a id="5197" class="Symbol">(</a> <a id="5199" href="foundation.existential-quantification.html#5948" class="Function">elim-exists</a>
              <a id="5225" class="Symbol">(</a> <a id="5227" href="foundation-core.sets.html#1141" class="Function">Id-Prop</a> <a id="5235" class="Symbol">(</a><a id="5236" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="5246" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a><a id="5247" class="Symbol">)</a> <a id="5249" class="Symbol">(</a><a id="5250" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="5261" href="group-theory.torsion-free-groups.html#4461" class="Bound">G</a><a id="5262" class="Symbol">)</a> <a id="5264" href="group-theory.torsion-free-groups.html#5037" class="Bound">x</a><a id="5265" class="Symbol">)</a>
              <a id="5281" class="Symbol">(</a> <a id="5283" class="Symbol">λ</a> <a id="5285" href="group-theory.torsion-free-groups.html#5285" class="Bound">k</a> <a id="5287" href="group-theory.torsion-free-groups.html#5287" class="Bound">p</a> <a id="5289" class="Symbol">→</a> <a id="5291" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="5295" class="Symbol">(</a><a id="5296" href="group-theory.torsion-free-groups.html#4931" class="Bound">H</a> <a id="5298" href="group-theory.torsion-free-groups.html#5037" class="Bound">x</a> <a id="5300" href="group-theory.torsion-free-groups.html#5285" class="Bound">k</a> <a id="5302" href="group-theory.torsion-free-groups.html#5287" class="Bound">p</a><a id="5303" class="Symbol">))))</a>
</pre>