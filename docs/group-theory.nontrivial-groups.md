# Nontrivial groups

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="group-theory.nontrivial-groups.html" class="Module">group-theory.nontrivial-groups</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="269" class="Keyword">open</a> <a id="274" class="Keyword">import</a> <a id="281" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="373" class="Keyword">open</a> <a id="378" class="Keyword">import</a> <a id="385" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="423" class="Keyword">open</a> <a id="428" class="Keyword">import</a> <a id="435" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="461" class="Keyword">open</a> <a id="466" class="Keyword">import</a> <a id="473" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="499" class="Keyword">open</a> <a id="504" class="Keyword">import</a> <a id="511" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="543" class="Keyword">open</a> <a id="548" class="Keyword">import</a> <a id="555" href="foundation.negated-equality.html" class="Module">foundation.negated-equality</a>
<a id="583" class="Keyword">open</a> <a id="588" class="Keyword">import</a> <a id="595" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="615" class="Keyword">open</a> <a id="620" class="Keyword">import</a> <a id="627" href="foundation.propositional-extensionality.html" class="Module">foundation.propositional-extensionality</a>
<a id="667" class="Keyword">open</a> <a id="672" class="Keyword">import</a> <a id="679" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="716" class="Keyword">open</a> <a id="721" class="Keyword">import</a> <a id="728" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="752" class="Keyword">open</a> <a id="757" class="Keyword">import</a> <a id="764" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="780" class="Keyword">open</a> <a id="785" class="Keyword">import</a> <a id="792" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="813" class="Keyword">open</a> <a id="818" class="Keyword">import</a> <a id="825" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="853" class="Keyword">open</a> <a id="858" class="Keyword">import</a> <a id="865" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="885" class="Keyword">open</a> <a id="890" class="Keyword">import</a> <a id="897" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
<a id="920" class="Keyword">open</a> <a id="925" class="Keyword">import</a> <a id="932" href="group-theory.trivial-groups.html" class="Module">group-theory.trivial-groups</a>
</pre>
</details>

## Idea

A [group](group-theory.groups.md) is said to be **nontrivial** if there
[exists](foundation.existential-quantification.md) a nonidentity element.

## Definitions

### The predicate of being a nontrivial group

<pre class="Agda"><a id="1204" class="Keyword">module</a> <a id="1211" href="group-theory.nontrivial-groups.html#1211" class="Module">_</a>
  <a id="1215" class="Symbol">{</a><a id="1216" href="group-theory.nontrivial-groups.html#1216" class="Bound">l1</a> <a id="1219" class="Symbol">:</a> <a id="1221" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1226" class="Symbol">}</a> <a id="1228" class="Symbol">(</a><a id="1229" href="group-theory.nontrivial-groups.html#1229" class="Bound">G</a> <a id="1231" class="Symbol">:</a> <a id="1233" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1239" href="group-theory.nontrivial-groups.html#1216" class="Bound">l1</a><a id="1241" class="Symbol">)</a>
  <a id="1245" class="Keyword">where</a>

  <a id="1254" href="group-theory.nontrivial-groups.html#1254" class="Function">is-nontrivial-prop-Group</a> <a id="1279" class="Symbol">:</a> <a id="1281" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1286" href="group-theory.nontrivial-groups.html#1216" class="Bound">l1</a>
  <a id="1291" href="group-theory.nontrivial-groups.html#1254" class="Function">is-nontrivial-prop-Group</a> <a id="1316" class="Symbol">=</a>
    <a id="1322" href="foundation.existential-quantification.html#3654" class="Function">exists-structure-Prop</a> <a id="1344" class="Symbol">(</a><a id="1345" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1356" href="group-theory.nontrivial-groups.html#1229" class="Bound">G</a><a id="1357" class="Symbol">)</a> <a id="1359" class="Symbol">(λ</a> <a id="1362" href="group-theory.nontrivial-groups.html#1362" class="Bound">g</a> <a id="1364" class="Symbol">→</a> <a id="1366" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="1377" href="group-theory.nontrivial-groups.html#1229" class="Bound">G</a> <a id="1379" href="foundation.negated-equality.html#733" class="Function Operator">≠</a> <a id="1381" href="group-theory.nontrivial-groups.html#1362" class="Bound">g</a><a id="1382" class="Symbol">)</a>

  <a id="1387" href="group-theory.nontrivial-groups.html#1387" class="Function">is-nontrivial-Group</a> <a id="1407" class="Symbol">:</a> <a id="1409" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1412" href="group-theory.nontrivial-groups.html#1216" class="Bound">l1</a>
  <a id="1417" href="group-theory.nontrivial-groups.html#1387" class="Function">is-nontrivial-Group</a> <a id="1437" class="Symbol">=</a>
    <a id="1443" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1453" href="group-theory.nontrivial-groups.html#1254" class="Function">is-nontrivial-prop-Group</a>

  <a id="1481" href="group-theory.nontrivial-groups.html#1481" class="Function">is-prop-is-nontrivial-Group</a> <a id="1509" class="Symbol">:</a>
    <a id="1515" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1523" href="group-theory.nontrivial-groups.html#1387" class="Function">is-nontrivial-Group</a>
  <a id="1545" href="group-theory.nontrivial-groups.html#1481" class="Function">is-prop-is-nontrivial-Group</a> <a id="1573" class="Symbol">=</a>
    <a id="1579" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1597" href="group-theory.nontrivial-groups.html#1254" class="Function">is-nontrivial-prop-Group</a>
</pre>
### The predicate of not being the trivial group

<pre class="Agda"><a id="1685" class="Keyword">module</a> <a id="1692" href="group-theory.nontrivial-groups.html#1692" class="Module">_</a>
  <a id="1696" class="Symbol">{</a><a id="1697" href="group-theory.nontrivial-groups.html#1697" class="Bound">l1</a> <a id="1700" class="Symbol">:</a> <a id="1702" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1707" class="Symbol">}</a> <a id="1709" class="Symbol">(</a><a id="1710" href="group-theory.nontrivial-groups.html#1710" class="Bound">G</a> <a id="1712" class="Symbol">:</a> <a id="1714" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1720" href="group-theory.nontrivial-groups.html#1697" class="Bound">l1</a><a id="1722" class="Symbol">)</a>
  <a id="1726" class="Keyword">where</a>

  <a id="1735" href="group-theory.nontrivial-groups.html#1735" class="Function">is-not-trivial-prop-Group</a> <a id="1761" class="Symbol">:</a> <a id="1763" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1768" href="group-theory.nontrivial-groups.html#1697" class="Bound">l1</a>
  <a id="1773" href="group-theory.nontrivial-groups.html#1735" class="Function">is-not-trivial-prop-Group</a> <a id="1799" class="Symbol">=</a>
    <a id="1805" href="foundation.negation.html#897" class="Function">neg-type-Prop</a> <a id="1819" class="Symbol">((</a><a id="1821" href="group-theory.nontrivial-groups.html#1821" class="Bound">x</a> <a id="1823" class="Symbol">:</a> <a id="1825" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1836" href="group-theory.nontrivial-groups.html#1710" class="Bound">G</a><a id="1837" class="Symbol">)</a> <a id="1839" class="Symbol">→</a> <a id="1841" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="1852" href="group-theory.nontrivial-groups.html#1710" class="Bound">G</a> <a id="1854" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1856" href="group-theory.nontrivial-groups.html#1821" class="Bound">x</a><a id="1857" class="Symbol">)</a>

  <a id="1862" href="group-theory.nontrivial-groups.html#1862" class="Function">is-not-trivial-Group</a> <a id="1883" class="Symbol">:</a> <a id="1885" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1888" href="group-theory.nontrivial-groups.html#1697" class="Bound">l1</a>
  <a id="1893" href="group-theory.nontrivial-groups.html#1862" class="Function">is-not-trivial-Group</a> <a id="1914" class="Symbol">=</a>
    <a id="1920" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1930" href="group-theory.nontrivial-groups.html#1735" class="Function">is-not-trivial-prop-Group</a>

  <a id="1959" href="group-theory.nontrivial-groups.html#1959" class="Function">is-prop-is-not-trivial-Group</a> <a id="1988" class="Symbol">:</a>
    <a id="1994" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2002" href="group-theory.nontrivial-groups.html#1862" class="Function">is-not-trivial-Group</a>
  <a id="2025" href="group-theory.nontrivial-groups.html#1959" class="Function">is-prop-is-not-trivial-Group</a> <a id="2054" class="Symbol">=</a>
    <a id="2060" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2078" href="group-theory.nontrivial-groups.html#1735" class="Function">is-not-trivial-prop-Group</a>
</pre>
## Properties

### A group is not a trivial group if and only if it satisfies the predicate of not being trivial

**Proof:** The proposition `¬ (is-trivial-Group G)` holds if and only if `G` is
not contractible, which holds if and only if `¬ ((x : G) → 1 ＝ x)`.

<pre class="Agda"><a id="2380" class="Keyword">module</a> <a id="2387" href="group-theory.nontrivial-groups.html#2387" class="Module">_</a>
  <a id="2391" class="Symbol">{</a><a id="2392" href="group-theory.nontrivial-groups.html#2392" class="Bound">l1</a> <a id="2395" class="Symbol">:</a> <a id="2397" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2402" class="Symbol">}</a> <a id="2404" class="Symbol">(</a><a id="2405" href="group-theory.nontrivial-groups.html#2405" class="Bound">G</a> <a id="2407" class="Symbol">:</a> <a id="2409" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="2415" href="group-theory.nontrivial-groups.html#2392" class="Bound">l1</a><a id="2417" class="Symbol">)</a>
  <a id="2421" class="Keyword">where</a>

  <a id="2430" href="group-theory.nontrivial-groups.html#2430" class="Function">neg-is-trivial-is-not-trivial-Group</a> <a id="2466" class="Symbol">:</a>
    <a id="2472" href="group-theory.nontrivial-groups.html#1862" class="Function">is-not-trivial-Group</a> <a id="2493" href="group-theory.nontrivial-groups.html#2405" class="Bound">G</a> <a id="2495" class="Symbol">→</a> <a id="2497" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2499" class="Symbol">(</a><a id="2500" href="group-theory.trivial-groups.html#1187" class="Function">is-trivial-Group</a> <a id="2517" href="group-theory.nontrivial-groups.html#2405" class="Bound">G</a><a id="2518" class="Symbol">)</a>
  <a id="2522" href="group-theory.nontrivial-groups.html#2430" class="Function">neg-is-trivial-is-not-trivial-Group</a> <a id="2558" href="group-theory.nontrivial-groups.html#2558" class="Bound">H</a> <a id="2560" href="group-theory.nontrivial-groups.html#2560" class="Bound">p</a> <a id="2562" class="Symbol">=</a> <a id="2564" href="group-theory.nontrivial-groups.html#2558" class="Bound">H</a> <a id="2566" class="Symbol">(λ</a> <a id="2569" href="group-theory.nontrivial-groups.html#2569" class="Bound">x</a> <a id="2571" class="Symbol">→</a> <a id="2573" href="foundation-core.contractible-types.html#1197" class="Function">eq-is-contr</a> <a id="2585" href="group-theory.nontrivial-groups.html#2560" class="Bound">p</a><a id="2586" class="Symbol">)</a>

  <a id="2591" href="group-theory.nontrivial-groups.html#2591" class="Function">is-not-trivial-neg-is-trivial-Group</a> <a id="2627" class="Symbol">:</a>
    <a id="2633" href="foundation-core.negation.html#595" class="Function Operator">¬</a> <a id="2635" class="Symbol">(</a><a id="2636" href="group-theory.trivial-groups.html#1187" class="Function">is-trivial-Group</a> <a id="2653" href="group-theory.nontrivial-groups.html#2405" class="Bound">G</a><a id="2654" class="Symbol">)</a> <a id="2656" class="Symbol">→</a> <a id="2658" href="group-theory.nontrivial-groups.html#1862" class="Function">is-not-trivial-Group</a> <a id="2679" href="group-theory.nontrivial-groups.html#2405" class="Bound">G</a>
  <a id="2683" href="group-theory.nontrivial-groups.html#2591" class="Function">is-not-trivial-neg-is-trivial-Group</a> <a id="2719" href="group-theory.nontrivial-groups.html#2719" class="Bound">H</a> <a id="2721" href="group-theory.nontrivial-groups.html#2721" class="Bound">p</a> <a id="2723" class="Symbol">=</a> <a id="2725" href="group-theory.nontrivial-groups.html#2719" class="Bound">H</a> <a id="2727" class="Symbol">(</a><a id="2728" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="2739" href="group-theory.nontrivial-groups.html#2405" class="Bound">G</a> <a id="2741" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2743" href="group-theory.nontrivial-groups.html#2721" class="Bound">p</a><a id="2744" class="Symbol">)</a>
</pre>
### The map `subgroup-Prop G : Prop → Subgroup G` is an embedding for any nontrivial group

Recall that the subgroup `subgroup-Prop G P` associated to a proposition `P` was
defined in [`group-theory.subgroups`](group-theory.subgroups.md).

**Proof:** Suppose that `G` is a nontrivial group and `x` is a group element
such that `1 ≠ x`. Then `subgroup-Prop G P ＝ subgroup-Prop G Q` if and only if
`x ∈ subgroup-Prop G P ⇔ x ∈ subgroup-Prop G Q`, which holds if and only if
`P ⇔ Q` since `x` is assumed to be a nonidentity element. This shows that
`subgroup-Prop G : Prop → Subgroup G` is an injective map. Since it is an
injective maps between sets, it follows that `subgroup-Prop G` is an embedding.

<pre class="Agda"><a id="3460" class="Keyword">module</a> <a id="3467" href="group-theory.nontrivial-groups.html#3467" class="Module">_</a>
  <a id="3471" class="Symbol">{</a><a id="3472" href="group-theory.nontrivial-groups.html#3472" class="Bound">l1</a> <a id="3475" href="group-theory.nontrivial-groups.html#3475" class="Bound">l2</a> <a id="3478" class="Symbol">:</a> <a id="3480" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3485" class="Symbol">}</a> <a id="3487" class="Symbol">(</a><a id="3488" href="group-theory.nontrivial-groups.html#3488" class="Bound">G</a> <a id="3490" class="Symbol">:</a> <a id="3492" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="3498" href="group-theory.nontrivial-groups.html#3472" class="Bound">l1</a><a id="3500" class="Symbol">)</a>
  <a id="3504" class="Keyword">where</a>

  <a id="3513" class="Keyword">abstract</a>
    <a id="3526" href="group-theory.nontrivial-groups.html#3526" class="Function">is-emb-subgroup-prop-is-nontrivial-Group</a> <a id="3567" class="Symbol">:</a>
      <a id="3575" href="group-theory.nontrivial-groups.html#1387" class="Function">is-nontrivial-Group</a> <a id="3595" href="group-theory.nontrivial-groups.html#3488" class="Bound">G</a> <a id="3597" class="Symbol">→</a> <a id="3599" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="3606" class="Symbol">(</a><a id="3607" href="group-theory.subgroups.html#24206" class="Function">subgroup-Prop</a> <a id="3621" class="Symbol">{</a><a id="3622" class="Argument">l2</a> <a id="3625" class="Symbol">=</a> <a id="3627" href="group-theory.nontrivial-groups.html#3475" class="Bound">l2</a><a id="3629" class="Symbol">}</a> <a id="3631" href="group-theory.nontrivial-groups.html#3488" class="Bound">G</a><a id="3632" class="Symbol">)</a>
    <a id="3638" href="group-theory.nontrivial-groups.html#3526" class="Function">is-emb-subgroup-prop-is-nontrivial-Group</a> <a id="3679" href="group-theory.nontrivial-groups.html#3679" class="Bound">H</a> <a id="3681" class="Symbol">=</a>
      <a id="3689" href="foundation.propositional-truncations.html#6198" class="Function">apply-universal-property-trunc-Prop</a> <a id="3725" href="group-theory.nontrivial-groups.html#3679" class="Bound">H</a>
        <a id="3735" class="Symbol">(</a> <a id="3737" href="foundation.embeddings.html#1620" class="Function">is-emb-Prop</a> <a id="3749" class="Symbol">_)</a>
        <a id="3760" class="Symbol">(</a> <a id="3762" class="Symbol">λ</a> <a id="3764" class="Symbol">(</a><a id="3765" href="group-theory.nontrivial-groups.html#3765" class="Bound">x</a> <a id="3767" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3769" href="group-theory.nontrivial-groups.html#3769" class="Bound">f</a><a id="3770" class="Symbol">)</a> <a id="3772" class="Symbol">→</a>
          <a id="3784" href="foundation.injective-maps.html#2001" class="Function">is-emb-is-injective</a>
            <a id="3816" class="Symbol">(</a> <a id="3818" href="group-theory.subgroups.html#16817" class="Function">is-set-Subgroup</a> <a id="3834" href="group-theory.nontrivial-groups.html#3488" class="Bound">G</a><a id="3835" class="Symbol">)</a>
            <a id="3849" class="Symbol">(</a> <a id="3851" class="Symbol">λ</a> <a id="3853" class="Symbol">{</a><a id="3854" href="group-theory.nontrivial-groups.html#3854" class="Bound">P</a><a id="3855" class="Symbol">}</a> <a id="3857" class="Symbol">{</a><a id="3858" href="group-theory.nontrivial-groups.html#3858" class="Bound">Q</a><a id="3859" class="Symbol">}</a> <a id="3861" href="group-theory.nontrivial-groups.html#3861" class="Bound">α</a> <a id="3863" class="Symbol">→</a>
              <a id="3879" href="foundation.propositional-extensionality.html#2809" class="Function">eq-iff</a>
                <a id="3902" class="Symbol">(</a> <a id="3904" class="Symbol">λ</a> <a id="3906" href="group-theory.nontrivial-groups.html#3906" class="Bound">p</a> <a id="3908" class="Symbol">→</a>
                  <a id="3928" href="foundation.disjunction.html#7376" class="Function">map-left-unit-law-disjunction-is-empty-Prop</a>
                    <a id="3992" class="Symbol">(</a> <a id="3994" href="foundation-core.sets.html#1141" class="Function">Id-Prop</a> <a id="4002" class="Symbol">(</a><a id="4003" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="4013" href="group-theory.nontrivial-groups.html#3488" class="Bound">G</a><a id="4014" class="Symbol">)</a> <a id="4016" class="Symbol">_</a> <a id="4018" class="Symbol">_)</a>
                    <a id="4041" class="Symbol">(</a> <a id="4043" href="group-theory.nontrivial-groups.html#3858" class="Bound">Q</a><a id="4044" class="Symbol">)</a>
                    <a id="4066" class="Symbol">(</a> <a id="4068" href="group-theory.nontrivial-groups.html#3769" class="Bound">f</a><a id="4069" class="Symbol">)</a>
                    <a id="4091" class="Symbol">(</a> <a id="4093" href="foundation.logical-equivalences.html#2234" class="Function">forward-implication</a>
                      <a id="4135" class="Symbol">(</a> <a id="4137" href="foundation.logical-equivalences.html#6668" class="Function">iff-eq</a> <a id="4144" class="Symbol">(</a><a id="4145" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4148" class="Symbol">(λ</a> <a id="4151" href="group-theory.nontrivial-groups.html#4151" class="Bound">T</a> <a id="4153" class="Symbol">→</a> <a id="4155" href="group-theory.subgroups.html#4129" class="Function">subset-Subgroup</a> <a id="4171" href="group-theory.nontrivial-groups.html#3488" class="Bound">G</a> <a id="4173" href="group-theory.nontrivial-groups.html#4151" class="Bound">T</a> <a id="4175" href="group-theory.nontrivial-groups.html#3765" class="Bound">x</a><a id="4176" class="Symbol">)</a> <a id="4178" href="group-theory.nontrivial-groups.html#3861" class="Bound">α</a><a id="4179" class="Symbol">))</a>
                      <a id="4204" class="Symbol">(</a> <a id="4206" href="foundation.disjunction.html#4292" class="Function">inr-disjunction</a> <a id="4222" href="group-theory.nontrivial-groups.html#3906" class="Bound">p</a><a id="4223" class="Symbol">)))</a>
                <a id="4243" class="Symbol">(</a> <a id="4245" class="Symbol">λ</a> <a id="4247" href="group-theory.nontrivial-groups.html#4247" class="Bound">q</a> <a id="4249" class="Symbol">→</a>
                  <a id="4269" href="foundation.disjunction.html#7376" class="Function">map-left-unit-law-disjunction-is-empty-Prop</a>
                    <a id="4333" class="Symbol">(</a> <a id="4335" href="foundation-core.sets.html#1141" class="Function">Id-Prop</a> <a id="4343" class="Symbol">(</a><a id="4344" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="4354" href="group-theory.nontrivial-groups.html#3488" class="Bound">G</a><a id="4355" class="Symbol">)</a> <a id="4357" class="Symbol">_</a> <a id="4359" class="Symbol">_)</a>
                    <a id="4382" class="Symbol">(</a> <a id="4384" href="group-theory.nontrivial-groups.html#3854" class="Bound">P</a><a id="4385" class="Symbol">)</a>
                    <a id="4407" class="Symbol">(</a> <a id="4409" href="group-theory.nontrivial-groups.html#3769" class="Bound">f</a><a id="4410" class="Symbol">)</a>
                    <a id="4432" class="Symbol">(</a> <a id="4434" href="foundation.logical-equivalences.html#2295" class="Function">backward-implication</a>
                      <a id="4477" class="Symbol">(</a> <a id="4479" href="foundation.logical-equivalences.html#6668" class="Function">iff-eq</a> <a id="4486" class="Symbol">(</a><a id="4487" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="4490" class="Symbol">(λ</a> <a id="4493" href="group-theory.nontrivial-groups.html#4493" class="Bound">T</a> <a id="4495" class="Symbol">→</a> <a id="4497" href="group-theory.subgroups.html#4129" class="Function">subset-Subgroup</a> <a id="4513" href="group-theory.nontrivial-groups.html#3488" class="Bound">G</a> <a id="4515" href="group-theory.nontrivial-groups.html#4493" class="Bound">T</a> <a id="4517" href="group-theory.nontrivial-groups.html#3765" class="Bound">x</a><a id="4518" class="Symbol">)</a> <a id="4520" href="group-theory.nontrivial-groups.html#3861" class="Bound">α</a><a id="4521" class="Symbol">))</a>
                      <a id="4546" class="Symbol">(</a> <a id="4548" href="foundation.disjunction.html#4292" class="Function">inr-disjunction</a> <a id="4564" href="group-theory.nontrivial-groups.html#4247" class="Bound">q</a><a id="4565" class="Symbol">)))))</a>
</pre>
### If the map `subgroup-Prop G : Prop lzero → Subgroup l1 G` is an embedding, then `G` is not a trivial group

**Proof:** Suppose that `subgroup-Prop G : Prop lzero → Subgroup l1 G` is an
embedding, and by way of contradiction suppose that `G` is trivial. Then it
follows that `Subgroup l1 G` is contractible. Since `subgroup-Prop G` is assumed
to be an embedding, it follows that `Prop lzero` is contractible. This
contradicts the fact that `Prop lzero` contains the distinct propositions
`empty-Prop` and `unit-Prop`.

Note: Our handling of universe levels might be too restrictive here.

<pre class="Agda"><a id="5176" class="Keyword">module</a> <a id="5183" href="group-theory.nontrivial-groups.html#5183" class="Module">_</a>
  <a id="5187" class="Symbol">{</a><a id="5188" href="group-theory.nontrivial-groups.html#5188" class="Bound">l1</a> <a id="5191" class="Symbol">:</a> <a id="5193" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5198" class="Symbol">}</a> <a id="5200" class="Symbol">(</a><a id="5201" href="group-theory.nontrivial-groups.html#5201" class="Bound">G</a> <a id="5203" class="Symbol">:</a> <a id="5205" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="5211" href="group-theory.nontrivial-groups.html#5188" class="Bound">l1</a><a id="5213" class="Symbol">)</a>
  <a id="5217" class="Keyword">where</a>

  <a id="5226" href="group-theory.nontrivial-groups.html#5226" class="Function">is-not-trivial-is-emb-subgroup-Prop</a> <a id="5262" class="Symbol">:</a>
    <a id="5268" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="5275" class="Symbol">(</a><a id="5276" href="group-theory.subgroups.html#24206" class="Function">subgroup-Prop</a> <a id="5290" class="Symbol">{</a><a id="5291" class="Argument">l2</a> <a id="5294" class="Symbol">=</a> <a id="5296" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="5301" class="Symbol">}</a> <a id="5303" href="group-theory.nontrivial-groups.html#5201" class="Bound">G</a><a id="5304" class="Symbol">)</a> <a id="5306" class="Symbol">→</a> <a id="5308" href="group-theory.nontrivial-groups.html#1862" class="Function">is-not-trivial-Group</a> <a id="5329" href="group-theory.nontrivial-groups.html#5201" class="Bound">G</a>
  <a id="5333" href="group-theory.nontrivial-groups.html#5226" class="Function">is-not-trivial-is-emb-subgroup-Prop</a> <a id="5369" href="group-theory.nontrivial-groups.html#5369" class="Bound">H</a> <a id="5371" href="group-theory.nontrivial-groups.html#5371" class="Bound">K</a> <a id="5373" class="Symbol">=</a>
    <a id="5379" href="foundation.logical-equivalences.html#2295" class="Function">backward-implication</a>
      <a id="5406" class="Symbol">(</a> <a id="5408" href="foundation.logical-equivalences.html#6668" class="Function">iff-eq</a>
        <a id="5423" class="Symbol">(</a> <a id="5425" href="foundation-core.injective-maps.html#3323" class="Function">is-injective-is-emb</a> <a id="5445" href="group-theory.nontrivial-groups.html#5369" class="Bound">H</a>
          <a id="5457" class="Symbol">{</a> <a id="5459" class="Argument">x</a> <a id="5461" class="Symbol">=</a> <a id="5463" href="foundation-core.empty-types.html#2409" class="Function">empty-Prop</a><a id="5473" class="Symbol">}</a>
          <a id="5485" class="Symbol">{</a> <a id="5487" class="Argument">y</a> <a id="5489" class="Symbol">=</a> <a id="5491" href="foundation.unit-type.html#4620" class="Function">unit-Prop</a><a id="5500" class="Symbol">}</a>
          <a id="5512" class="Symbol">(</a> <a id="5514" href="foundation-core.contractible-types.html#1197" class="Function">eq-is-contr</a> <a id="5526" class="Symbol">(</a><a id="5527" href="group-theory.trivial-groups.html#1859" class="Function">is-contr-subgroup-is-trivial-Group</a> <a id="5562" href="group-theory.nontrivial-groups.html#5201" class="Bound">G</a> <a id="5564" class="Symbol">(_</a> <a id="5567" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="5569" href="group-theory.nontrivial-groups.html#5371" class="Bound">K</a><a id="5570" class="Symbol">)))))</a>
      <a id="5582" class="Symbol">(</a> <a id="5584" href="foundation.unit-type.html#995" class="InductiveConstructor">star</a><a id="5588" class="Symbol">)</a>
</pre>