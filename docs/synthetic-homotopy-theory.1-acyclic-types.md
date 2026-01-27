# `1`-acyclic types

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="synthetic-homotopy-theory.1-acyclic-types.html" class="Module">synthetic-homotopy-theory.1-acyclic-types</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.0-connected-types.html" class="Module">foundation.0-connected-types</a>
<a id="176" class="Keyword">open</a> <a id="181" class="Keyword">import</a> <a id="188" href="foundation.binary-transport.html" class="Module">foundation.binary-transport</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.constant-maps.html" class="Module">foundation.constant-maps</a>
<a id="253" class="Keyword">open</a> <a id="258" class="Keyword">import</a> <a id="265" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="339" class="Keyword">open</a> <a id="344" class="Keyword">import</a> <a id="351" href="foundation.diagonal-maps-of-types.html" class="Module">foundation.diagonal-maps-of-types</a>
<a id="385" class="Keyword">open</a> <a id="390" class="Keyword">import</a> <a id="397" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="421" class="Keyword">open</a> <a id="426" class="Keyword">import</a> <a id="433" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="468" class="Keyword">open</a> <a id="473" class="Keyword">import</a> <a id="480" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="506" class="Keyword">open</a> <a id="511" class="Keyword">import</a> <a id="518" href="foundation.inhabited-types.html" class="Module">foundation.inhabited-types</a>
<a id="545" class="Keyword">open</a> <a id="550" class="Keyword">import</a> <a id="557" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="583" class="Keyword">open</a> <a id="588" class="Keyword">import</a> <a id="595" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="619" class="Keyword">open</a> <a id="624" class="Keyword">import</a> <a id="631" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="658" class="Keyword">open</a> <a id="663" class="Keyword">import</a> <a id="670" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="686" class="Keyword">open</a> <a id="691" class="Keyword">import</a> <a id="698" href="foundation.truncated-types.html" class="Module">foundation.truncated-types</a>
<a id="725" class="Keyword">open</a> <a id="730" class="Keyword">import</a> <a id="737" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="766" class="Keyword">open</a> <a id="771" class="Keyword">import</a> <a id="778" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="806" class="Keyword">open</a> <a id="811" class="Keyword">import</a> <a id="818" href="synthetic-homotopy-theory.0-acyclic-types.html" class="Module">synthetic-homotopy-theory.0-acyclic-types</a>
<a id="860" class="Keyword">open</a> <a id="865" class="Keyword">import</a> <a id="872" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
<a id="910" class="Keyword">open</a> <a id="915" class="Keyword">import</a> <a id="922" href="synthetic-homotopy-theory.truncated-acyclic-maps.html" class="Module">synthetic-homotopy-theory.truncated-acyclic-maps</a>
<a id="971" class="Keyword">open</a> <a id="976" class="Keyword">import</a> <a id="983" href="synthetic-homotopy-theory.truncated-acyclic-types.html" class="Module">synthetic-homotopy-theory.truncated-acyclic-types</a>
</pre>
</details>

## Idea

A type is **`1`-acyclic** if its
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`1`-connected](foundation.connected-types.md).

We can characterize the `1`-acyclic types as the
[`0`-connected types](foundation.0-connected-types.md).

In one direction, our proof relies on the following group-theoretic fact: the
map of [generators](group-theory.generating-elements-groups.md) from a
[set](foundation-core.sets.md) `X` to the free group on `X` is
[injective](foundation-core.injective-maps.md). This is proved constructively in
{{#cite MRR88}} by Mines, Richman and Ruitenburg, and carried out in HoTT/UF and
formalized in Agda in {{#cite BCDE21}} by Bezem, Coquand, Dybjer, and Escardó.

Translated to [concrete groups](group-theory.concrete-groups.md) this means that
for every set `X`, we have a [pointed](structured-types.pointed-types.md)
[`1`-type](foundation-core.1-types.md) `pt : BG` together with an injection
`gen : X → pt ＝ pt`. (Actually, `BG` is `0`-connected as well, but we don't use
this in our proof below.)

A construction on the level of concrete groups can be found in the recent
preprint by David Wärn {{#cite Warn23draft}}.

For the time being, we haven't formalized this group-theoretic fact; instead we
label it as an explicit assumption of our proof.

## Definition

<pre class="Agda"><a id="2380" class="Keyword">module</a> <a id="2387" href="synthetic-homotopy-theory.1-acyclic-types.html#2387" class="Module">_</a>
  <a id="2391" class="Symbol">{</a><a id="2392" href="synthetic-homotopy-theory.1-acyclic-types.html#2392" class="Bound">l</a> <a id="2394" class="Symbol">:</a> <a id="2396" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2401" class="Symbol">}</a> <a id="2403" class="Symbol">(</a><a id="2404" href="synthetic-homotopy-theory.1-acyclic-types.html#2404" class="Bound">A</a> <a id="2406" class="Symbol">:</a> <a id="2408" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2411" href="synthetic-homotopy-theory.1-acyclic-types.html#2392" class="Bound">l</a><a id="2412" class="Symbol">)</a>
  <a id="2416" class="Keyword">where</a>

  <a id="2425" href="synthetic-homotopy-theory.1-acyclic-types.html#2425" class="Function">is-1-acyclic-Prop</a> <a id="2443" class="Symbol">:</a> <a id="2445" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2450" href="synthetic-homotopy-theory.1-acyclic-types.html#2392" class="Bound">l</a>
  <a id="2454" href="synthetic-homotopy-theory.1-acyclic-types.html#2425" class="Function">is-1-acyclic-Prop</a> <a id="2472" class="Symbol">=</a> <a id="2474" href="synthetic-homotopy-theory.truncated-acyclic-types.html#840" class="Function">is-truncated-acyclic-Prop</a> <a id="2500" class="Symbol">(</a><a id="2501" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a><a id="2506" class="Symbol">)</a> <a id="2508" href="synthetic-homotopy-theory.1-acyclic-types.html#2404" class="Bound">A</a>

  <a id="2513" href="synthetic-homotopy-theory.1-acyclic-types.html#2513" class="Function">is-1-acyclic</a> <a id="2526" class="Symbol">:</a> <a id="2528" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2531" href="synthetic-homotopy-theory.1-acyclic-types.html#2392" class="Bound">l</a>
  <a id="2535" href="synthetic-homotopy-theory.1-acyclic-types.html#2513" class="Function">is-1-acyclic</a> <a id="2548" class="Symbol">=</a> <a id="2550" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2560" href="synthetic-homotopy-theory.1-acyclic-types.html#2425" class="Function">is-1-acyclic-Prop</a>

  <a id="2581" href="synthetic-homotopy-theory.1-acyclic-types.html#2581" class="Function">is-prop-is-1-acyclic</a> <a id="2602" class="Symbol">:</a> <a id="2604" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2612" href="synthetic-homotopy-theory.1-acyclic-types.html#2513" class="Function">is-1-acyclic</a>
  <a id="2627" href="synthetic-homotopy-theory.1-acyclic-types.html#2581" class="Function">is-prop-is-1-acyclic</a> <a id="2648" class="Symbol">=</a> <a id="2650" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2668" href="synthetic-homotopy-theory.1-acyclic-types.html#2425" class="Function">is-1-acyclic-Prop</a>
</pre>
## Properties

### Every `0`-connected type is `1`-acyclic

<pre class="Agda"><a id="2759" class="Keyword">module</a> <a id="2766" href="synthetic-homotopy-theory.1-acyclic-types.html#2766" class="Module">_</a>
  <a id="2770" class="Symbol">{</a><a id="2771" href="synthetic-homotopy-theory.1-acyclic-types.html#2771" class="Bound">l</a> <a id="2773" class="Symbol">:</a> <a id="2775" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2780" class="Symbol">}</a> <a id="2782" class="Symbol">(</a><a id="2783" href="synthetic-homotopy-theory.1-acyclic-types.html#2783" class="Bound">A</a> <a id="2785" class="Symbol">:</a> <a id="2787" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2790" href="synthetic-homotopy-theory.1-acyclic-types.html#2771" class="Bound">l</a><a id="2791" class="Symbol">)</a>
  <a id="2795" class="Keyword">where</a>

  <a id="2804" href="synthetic-homotopy-theory.1-acyclic-types.html#2804" class="Function">is-1-acyclic-is-0-connected</a> <a id="2832" class="Symbol">:</a> <a id="2834" href="foundation.0-connected-types.html#1548" class="Function">is-0-connected</a> <a id="2849" href="synthetic-homotopy-theory.1-acyclic-types.html#2783" class="Bound">A</a> <a id="2851" class="Symbol">→</a> <a id="2853" href="synthetic-homotopy-theory.1-acyclic-types.html#2513" class="Function">is-1-acyclic</a> <a id="2866" href="synthetic-homotopy-theory.1-acyclic-types.html#2783" class="Bound">A</a>
  <a id="2870" href="synthetic-homotopy-theory.1-acyclic-types.html#2804" class="Function">is-1-acyclic-is-0-connected</a> <a id="2898" class="Symbol">=</a> <a id="2900" href="synthetic-homotopy-theory.truncated-acyclic-types.html#2487" class="Function">is-truncated-acyclic-succ-is-connected</a>
</pre>
### Every `1`-acyclic type is `0`-connected

As explained at the top "Idea" section, we turn the necessary group-theoretic
fact into an explicit assumption of our proof.

<pre class="Agda"><a id="3123" class="Keyword">private</a>
  <a id="3133" class="Keyword">record</a>
    <a id="concrete-group-assumption&#39;"></a><a id="3144" href="synthetic-homotopy-theory.1-acyclic-types.html#3144" class="Record">concrete-group-assumption&#39;</a> <a id="3171" class="Symbol">{</a><a id="3172" href="synthetic-homotopy-theory.1-acyclic-types.html#3172" class="Bound">l</a> <a id="3174" class="Symbol">:</a> <a id="3176" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3181" class="Symbol">}</a> <a id="3183" class="Symbol">(</a><a id="3184" href="synthetic-homotopy-theory.1-acyclic-types.html#3184" class="Bound">A</a> <a id="3186" class="Symbol">:</a> <a id="3188" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3191" href="synthetic-homotopy-theory.1-acyclic-types.html#3172" class="Bound">l</a><a id="3192" class="Symbol">)</a> <a id="3194" class="Symbol">:</a> <a id="3196" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3199" class="Symbol">(</a><a id="3200" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3205" href="synthetic-homotopy-theory.1-acyclic-types.html#3172" class="Bound">l</a><a id="3206" class="Symbol">)</a>
    <a id="3212" class="Keyword">where</a>
    <a id="3222" class="Keyword">field</a>
      <a id="concrete-group-assumption&#39;.BG"></a><a id="3234" href="synthetic-homotopy-theory.1-acyclic-types.html#3234" class="Field">BG</a> <a id="3237" class="Symbol">:</a> <a id="3239" href="foundation-core.truncated-types.html#1603" class="Function">Truncated-Type</a> <a id="3254" href="synthetic-homotopy-theory.1-acyclic-types.html#3172" class="Bound">l</a> <a id="3256" class="Symbol">(</a><a id="3257" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a><a id="3262" class="Symbol">)</a>
      <a id="concrete-group-assumption&#39;.pt"></a><a id="3270" href="synthetic-homotopy-theory.1-acyclic-types.html#3270" class="Field">pt</a> <a id="3273" class="Symbol">:</a> <a id="3275" href="foundation-core.truncated-types.html#1736" class="Function">type-Truncated-Type</a> <a id="3295" href="synthetic-homotopy-theory.1-acyclic-types.html#3234" class="Field">BG</a>
      <a id="concrete-group-assumption&#39;.gen"></a><a id="3304" href="synthetic-homotopy-theory.1-acyclic-types.html#3304" class="Field">gen</a> <a id="3308" class="Symbol">:</a> <a id="3310" href="synthetic-homotopy-theory.1-acyclic-types.html#3184" class="Bound">A</a> <a id="3312" class="Symbol">→</a> <a id="3314" href="synthetic-homotopy-theory.loop-spaces.html#1040" class="Function">type-Ω</a> <a id="3321" class="Symbol">(</a><a id="3322" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="3327" class="Symbol">(</a><a id="3328" href="foundation-core.truncated-types.html#1736" class="Function">type-Truncated-Type</a> <a id="3348" href="synthetic-homotopy-theory.1-acyclic-types.html#3234" class="Field">BG</a><a id="3350" class="Symbol">)</a> <a id="3352" href="synthetic-homotopy-theory.1-acyclic-types.html#3270" class="Field">pt</a><a id="3354" class="Symbol">)</a>
      <a id="concrete-group-assumption&#39;.is-injective-gen"></a><a id="3362" href="synthetic-homotopy-theory.1-acyclic-types.html#3362" class="Field">is-injective-gen</a> <a id="3379" class="Symbol">:</a> <a id="3381" href="foundation-core.injective-maps.html#1182" class="Function">is-injective</a> <a id="3394" href="synthetic-homotopy-theory.1-acyclic-types.html#3304" class="Field">gen</a>

  <a id="concrete-group-assumption"></a><a id="3401" href="synthetic-homotopy-theory.1-acyclic-types.html#3401" class="Function">concrete-group-assumption</a> <a id="3427" class="Symbol">:</a> <a id="3429" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="3435" href="synthetic-homotopy-theory.1-acyclic-types.html#3401" class="Function">concrete-group-assumption</a> <a id="3461" class="Symbol">=</a>
    <a id="3467" class="Symbol">{</a><a id="3468" href="synthetic-homotopy-theory.1-acyclic-types.html#3468" class="Bound">l</a> <a id="3470" class="Symbol">:</a> <a id="3472" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3477" class="Symbol">}</a> <a id="3479" class="Symbol">(</a><a id="3480" href="synthetic-homotopy-theory.1-acyclic-types.html#3480" class="Bound">A</a> <a id="3482" class="Symbol">:</a> <a id="3484" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3487" href="synthetic-homotopy-theory.1-acyclic-types.html#3468" class="Bound">l</a><a id="3488" class="Symbol">)</a> <a id="3490" class="Symbol">→</a> <a id="3492" href="synthetic-homotopy-theory.1-acyclic-types.html#3144" class="Record">concrete-group-assumption&#39;</a> <a id="3519" href="synthetic-homotopy-theory.1-acyclic-types.html#3480" class="Bound">A</a>

<a id="3522" class="Keyword">module</a> <a id="3529" href="synthetic-homotopy-theory.1-acyclic-types.html#3529" class="Module">_</a>
  <a id="3533" class="Symbol">(</a><a id="3534" href="synthetic-homotopy-theory.1-acyclic-types.html#3534" class="Bound">cga</a> <a id="3538" class="Symbol">:</a> <a id="3540" href="synthetic-homotopy-theory.1-acyclic-types.html#3401" class="Function">concrete-group-assumption</a><a id="3565" class="Symbol">)</a>
  <a id="3569" class="Keyword">where</a>

  <a id="3578" href="synthetic-homotopy-theory.1-acyclic-types.html#3578" class="Function">is-contr-is-1-acyclic-is-set</a> <a id="3607" class="Symbol">:</a>
    <a id="3613" class="Symbol">{</a><a id="3614" href="synthetic-homotopy-theory.1-acyclic-types.html#3614" class="Bound">l</a> <a id="3616" class="Symbol">:</a> <a id="3618" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3623" class="Symbol">}</a> <a id="3625" class="Symbol">(</a><a id="3626" href="synthetic-homotopy-theory.1-acyclic-types.html#3626" class="Bound">A</a> <a id="3628" class="Symbol">:</a> <a id="3630" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3633" href="synthetic-homotopy-theory.1-acyclic-types.html#3614" class="Bound">l</a><a id="3634" class="Symbol">)</a> <a id="3636" class="Symbol">→</a>
    <a id="3642" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="3649" href="synthetic-homotopy-theory.1-acyclic-types.html#3626" class="Bound">A</a> <a id="3651" class="Symbol">→</a> <a id="3653" href="synthetic-homotopy-theory.1-acyclic-types.html#2513" class="Function">is-1-acyclic</a> <a id="3666" href="synthetic-homotopy-theory.1-acyclic-types.html#3626" class="Bound">A</a> <a id="3668" class="Symbol">→</a> <a id="3670" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="3679" href="synthetic-homotopy-theory.1-acyclic-types.html#3626" class="Bound">A</a>
  <a id="3683" href="synthetic-homotopy-theory.1-acyclic-types.html#3578" class="Function">is-contr-is-1-acyclic-is-set</a> <a id="3712" href="synthetic-homotopy-theory.1-acyclic-types.html#3712" class="Bound">A</a> <a id="3714" href="synthetic-homotopy-theory.1-acyclic-types.html#3714" class="Bound">s</a> <a id="3716" href="synthetic-homotopy-theory.1-acyclic-types.html#3716" class="Bound">ac</a> <a id="3719" class="Symbol">=</a>
    <a id="3725" class="Keyword">let</a> <a id="3729" class="Keyword">open</a> <a id="3734" href="synthetic-homotopy-theory.1-acyclic-types.html#3144" class="Module">concrete-group-assumption&#39;</a> <a id="3761" class="Symbol">(</a><a id="3762" href="synthetic-homotopy-theory.1-acyclic-types.html#3534" class="Bound">cga</a> <a id="3766" href="synthetic-homotopy-theory.1-acyclic-types.html#3712" class="Bound">A</a><a id="3767" class="Symbol">)</a> <a id="3769" class="Keyword">in</a>
    <a id="3776" href="foundation.inhabited-types.html#6656" class="Function">is-contr-is-inhabited-is-prop</a>
      <a id="3812" class="Symbol">(</a> <a id="3814" href="foundation-core.propositions.html#2210" class="Function">is-prop-all-elements-equal</a>
        <a id="3849" class="Symbol">(</a> <a id="3851" class="Symbol">λ</a> <a id="3853" href="synthetic-homotopy-theory.1-acyclic-types.html#3853" class="Bound">x</a> <a id="3855" href="synthetic-homotopy-theory.1-acyclic-types.html#3855" class="Bound">y</a> <a id="3857" class="Symbol">→</a>
          <a id="3869" href="synthetic-homotopy-theory.1-acyclic-types.html#3362" class="Function">is-injective-gen</a>
            <a id="3898" class="Symbol">(</a> <a id="3900" href="foundation.binary-transport.html#801" class="Function">binary-tr</a>
              <a id="3924" class="Symbol">(</a> <a id="3926" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a><a id="3928" class="Symbol">)</a>
              <a id="3944" class="Symbol">(</a> <a id="3946" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a>
                <a id="3970" class="Symbol">(</a> <a id="3972" href="foundation-core.equivalences.html#8153" class="Function">is-section-map-inv-equiv</a>
                  <a id="4015" class="Symbol">(</a> <a id="4017" class="Symbol">(</a> <a id="4019" href="foundation.diagonal-maps-of-types.html#1405" class="Function">diagonal-exponential</a>
                      <a id="4062" class="Symbol">(</a> <a id="4064" href="synthetic-homotopy-theory.loop-spaces.html#1040" class="Function">type-Ω</a> <a id="4071" class="Symbol">(</a><a id="4072" href="foundation-core.truncated-types.html#1736" class="Function">type-Truncated-Type</a> <a id="4092" href="synthetic-homotopy-theory.1-acyclic-types.html#3234" class="Function">BG</a> <a id="4095" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4097" href="synthetic-homotopy-theory.1-acyclic-types.html#3270" class="Function">pt</a><a id="4099" class="Symbol">))</a>
                      <a id="4124" class="Symbol">(</a> <a id="4126" href="synthetic-homotopy-theory.1-acyclic-types.html#3712" class="Bound">A</a><a id="4127" class="Symbol">))</a> <a id="4130" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
                    <a id="4152" class="Symbol">(</a> <a id="4154" href="synthetic-homotopy-theory.truncated-acyclic-maps.html#7122" class="Function">is-equiv-diagonal-exponential-Id-is-acyclic-Truncated-Type</a>
                      <a id="4235" class="Symbol">(</a> <a id="4237" href="synthetic-homotopy-theory.1-acyclic-types.html#3712" class="Bound">A</a><a id="4238" class="Symbol">)</a>
                      <a id="4262" class="Symbol">(</a> <a id="4264" href="synthetic-homotopy-theory.1-acyclic-types.html#3716" class="Bound">ac</a><a id="4266" class="Symbol">)</a>
                      <a id="4290" class="Symbol">(</a> <a id="4292" href="synthetic-homotopy-theory.1-acyclic-types.html#3234" class="Function">BG</a><a id="4294" class="Symbol">)</a>
                      <a id="4318" class="Symbol">(</a> <a id="4320" href="synthetic-homotopy-theory.1-acyclic-types.html#3270" class="Function">pt</a><a id="4322" class="Symbol">)</a>
                      <a id="4346" class="Symbol">(</a> <a id="4348" href="synthetic-homotopy-theory.1-acyclic-types.html#3270" class="Function">pt</a><a id="4350" class="Symbol">)))</a>
                  <a id="4372" class="Symbol">(</a> <a id="4374" href="synthetic-homotopy-theory.1-acyclic-types.html#3304" class="Function">gen</a><a id="4377" class="Symbol">))</a>
                <a id="4396" class="Symbol">(</a> <a id="4398" href="synthetic-homotopy-theory.1-acyclic-types.html#3853" class="Bound">x</a><a id="4399" class="Symbol">))</a>
              <a id="4416" class="Symbol">(</a> <a id="4418" href="foundation.function-extensionality.html#1896" class="Function">htpy-eq</a>
                <a id="4442" class="Symbol">(</a> <a id="4444" href="foundation-core.equivalences.html#8153" class="Function">is-section-map-inv-equiv</a>
                  <a id="4487" class="Symbol">(</a> <a id="4489" class="Symbol">(</a> <a id="4491" href="foundation.diagonal-maps-of-types.html#1405" class="Function">diagonal-exponential</a>
                      <a id="4534" class="Symbol">(</a> <a id="4536" href="synthetic-homotopy-theory.loop-spaces.html#1040" class="Function">type-Ω</a> <a id="4543" class="Symbol">(</a><a id="4544" href="foundation-core.truncated-types.html#1736" class="Function">type-Truncated-Type</a> <a id="4564" href="synthetic-homotopy-theory.1-acyclic-types.html#3234" class="Function">BG</a> <a id="4567" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="4569" href="synthetic-homotopy-theory.1-acyclic-types.html#3270" class="Function">pt</a><a id="4571" class="Symbol">))</a>
                      <a id="4596" class="Symbol">(</a> <a id="4598" href="synthetic-homotopy-theory.1-acyclic-types.html#3712" class="Bound">A</a><a id="4599" class="Symbol">))</a> <a id="4602" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
                    <a id="4624" class="Symbol">(</a> <a id="4626" href="synthetic-homotopy-theory.truncated-acyclic-maps.html#7122" class="Function">is-equiv-diagonal-exponential-Id-is-acyclic-Truncated-Type</a>
                      <a id="4707" class="Symbol">(</a> <a id="4709" href="synthetic-homotopy-theory.1-acyclic-types.html#3712" class="Bound">A</a><a id="4710" class="Symbol">)</a>
                      <a id="4734" class="Symbol">(</a> <a id="4736" href="synthetic-homotopy-theory.1-acyclic-types.html#3716" class="Bound">ac</a><a id="4738" class="Symbol">)</a>
                      <a id="4762" class="Symbol">(</a> <a id="4764" href="synthetic-homotopy-theory.1-acyclic-types.html#3234" class="Function">BG</a><a id="4766" class="Symbol">)</a>
                      <a id="4790" class="Symbol">(</a> <a id="4792" href="synthetic-homotopy-theory.1-acyclic-types.html#3270" class="Function">pt</a><a id="4794" class="Symbol">)</a>
                      <a id="4818" class="Symbol">(</a> <a id="4820" href="synthetic-homotopy-theory.1-acyclic-types.html#3270" class="Function">pt</a><a id="4822" class="Symbol">)))</a>
                  <a id="4844" class="Symbol">(</a> <a id="4846" href="synthetic-homotopy-theory.1-acyclic-types.html#3304" class="Function">gen</a><a id="4849" class="Symbol">))</a>
                <a id="4868" class="Symbol">(</a> <a id="4870" href="synthetic-homotopy-theory.1-acyclic-types.html#3855" class="Bound">y</a><a id="4871" class="Symbol">))</a>
              <a id="4888" class="Symbol">(</a> <a id="4890" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="4894" class="Symbol">))))</a>
      <a id="4905" class="Symbol">(</a> <a id="4907" href="synthetic-homotopy-theory.0-acyclic-types.html#1480" class="Function">is-inhabited-is-0-acyclic</a>
        <a id="4941" class="Symbol">(</a> <a id="4943" href="synthetic-homotopy-theory.truncated-acyclic-types.html#3204" class="Function">is-truncated-acyclic-is-truncated-acyclic-succ</a> <a id="4990" href="synthetic-homotopy-theory.1-acyclic-types.html#3716" class="Bound">ac</a><a id="4992" class="Symbol">))</a>

  <a id="4998" href="synthetic-homotopy-theory.1-acyclic-types.html#4998" class="Function">is-0-connected-is-1-acyclic</a> <a id="5026" class="Symbol">:</a>
    <a id="5032" class="Symbol">{</a><a id="5033" href="synthetic-homotopy-theory.1-acyclic-types.html#5033" class="Bound">l</a> <a id="5035" class="Symbol">:</a> <a id="5037" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5042" class="Symbol">}</a> <a id="5044" class="Symbol">(</a><a id="5045" href="synthetic-homotopy-theory.1-acyclic-types.html#5045" class="Bound">A</a> <a id="5047" class="Symbol">:</a> <a id="5049" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5052" href="synthetic-homotopy-theory.1-acyclic-types.html#5033" class="Bound">l</a><a id="5053" class="Symbol">)</a> <a id="5055" class="Symbol">→</a>
    <a id="5061" href="synthetic-homotopy-theory.1-acyclic-types.html#2513" class="Function">is-1-acyclic</a> <a id="5074" href="synthetic-homotopy-theory.1-acyclic-types.html#5045" class="Bound">A</a> <a id="5076" class="Symbol">→</a> <a id="5078" href="foundation.0-connected-types.html#1548" class="Function">is-0-connected</a> <a id="5093" href="synthetic-homotopy-theory.1-acyclic-types.html#5045" class="Bound">A</a>
  <a id="5097" href="synthetic-homotopy-theory.1-acyclic-types.html#4998" class="Function">is-0-connected-is-1-acyclic</a> <a id="5125" href="synthetic-homotopy-theory.1-acyclic-types.html#5125" class="Bound">A</a> <a id="5127" href="synthetic-homotopy-theory.1-acyclic-types.html#5127" class="Bound">ac</a> <a id="5130" class="Symbol">=</a>
    <a id="5136" href="synthetic-homotopy-theory.1-acyclic-types.html#3578" class="Function">is-contr-is-1-acyclic-is-set</a>
      <a id="5171" class="Symbol">(</a> <a id="5173" href="foundation.set-truncations.html#2028" class="Function">type-trunc-Set</a> <a id="5188" href="synthetic-homotopy-theory.1-acyclic-types.html#5125" class="Bound">A</a><a id="5189" class="Symbol">)</a>
      <a id="5197" class="Symbol">(</a> <a id="5199" href="foundation.set-truncations.html#2107" class="Function">is-set-type-trunc-Set</a><a id="5220" class="Symbol">)</a>
      <a id="5228" class="Symbol">(</a> <a id="5230" href="synthetic-homotopy-theory.truncated-acyclic-maps.html#13913" class="Function">is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succ</a> <a id="5293" href="synthetic-homotopy-theory.1-acyclic-types.html#5125" class="Bound">A</a> <a id="5295" href="synthetic-homotopy-theory.1-acyclic-types.html#5127" class="Bound">ac</a><a id="5297" class="Symbol">)</a>
</pre>
## References

{{#bibliography}}

## See also

- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
