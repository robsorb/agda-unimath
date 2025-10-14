# Trivial concrete groups

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="group-theory.trivial-concrete-groups.html" class="Module">group-theory.trivial-concrete-groups</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="299" class="Keyword">open</a> <a id="304" class="Keyword">import</a> <a id="311" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>

<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="higher-group-theory.trivial-higher-groups.html" class="Module">higher-group-theory.trivial-higher-groups</a>
</pre>
</details>

## Idea

A [concrete group](group-theory.concrete-groups.md) `G` is **trivial** if its
classifying type is contractible.

## Definitions

### Trivial higher groups

<pre class="Agda"><a id="658" class="Keyword">module</a> <a id="665" href="group-theory.trivial-concrete-groups.html#665" class="Module">_</a>
  <a id="669" class="Symbol">{</a><a id="670" href="group-theory.trivial-concrete-groups.html#670" class="Bound">l</a> <a id="672" class="Symbol">:</a> <a id="674" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="679" class="Symbol">}</a> <a id="681" class="Symbol">(</a><a id="682" href="group-theory.trivial-concrete-groups.html#682" class="Bound">G</a> <a id="684" class="Symbol">:</a> <a id="686" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="701" href="group-theory.trivial-concrete-groups.html#670" class="Bound">l</a><a id="702" class="Symbol">)</a>
  <a id="706" class="Keyword">where</a>

  <a id="715" href="group-theory.trivial-concrete-groups.html#715" class="Function">is-trivial-prop-Concrete-Group</a> <a id="746" class="Symbol">:</a> <a id="748" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="753" href="group-theory.trivial-concrete-groups.html#670" class="Bound">l</a>
  <a id="757" href="group-theory.trivial-concrete-groups.html#715" class="Function">is-trivial-prop-Concrete-Group</a> <a id="788" class="Symbol">=</a>
    <a id="794" href="higher-group-theory.trivial-higher-groups.html#663" class="Function">is-trivial-prop-∞-Group</a> <a id="818" class="Symbol">(</a><a id="819" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="842" href="group-theory.trivial-concrete-groups.html#682" class="Bound">G</a><a id="843" class="Symbol">)</a>

  <a id="848" href="group-theory.trivial-concrete-groups.html#848" class="Function">is-trivial-Concrete-Group</a> <a id="874" class="Symbol">:</a> <a id="876" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="879" href="group-theory.trivial-concrete-groups.html#670" class="Bound">l</a>
  <a id="883" href="group-theory.trivial-concrete-groups.html#848" class="Function">is-trivial-Concrete-Group</a> <a id="909" class="Symbol">=</a> <a id="911" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="921" href="group-theory.trivial-concrete-groups.html#715" class="Function">is-trivial-prop-Concrete-Group</a>

  <a id="955" href="group-theory.trivial-concrete-groups.html#955" class="Function">is-property-is-trivial-Concrete-Group</a> <a id="993" class="Symbol">:</a> <a id="995" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1003" class="Symbol">(</a><a id="1004" href="group-theory.trivial-concrete-groups.html#848" class="Function">is-trivial-Concrete-Group</a><a id="1029" class="Symbol">)</a>
  <a id="1033" href="group-theory.trivial-concrete-groups.html#955" class="Function">is-property-is-trivial-Concrete-Group</a> <a id="1071" class="Symbol">=</a>
    <a id="1077" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1095" href="group-theory.trivial-concrete-groups.html#715" class="Function">is-trivial-prop-Concrete-Group</a>
</pre>
### Higher groups with contractible classifying type

<pre class="Agda"><a id="1193" class="Keyword">module</a> <a id="1200" href="group-theory.trivial-concrete-groups.html#1200" class="Module">_</a>
  <a id="1204" class="Symbol">{</a><a id="1205" href="group-theory.trivial-concrete-groups.html#1205" class="Bound">l</a> <a id="1207" class="Symbol">:</a> <a id="1209" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1214" class="Symbol">}</a> <a id="1216" class="Symbol">(</a><a id="1217" href="group-theory.trivial-concrete-groups.html#1217" class="Bound">G</a> <a id="1219" class="Symbol">:</a> <a id="1221" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="1236" href="group-theory.trivial-concrete-groups.html#1205" class="Bound">l</a><a id="1237" class="Symbol">)</a>
  <a id="1241" class="Keyword">where</a>

  <a id="1250" href="group-theory.trivial-concrete-groups.html#1250" class="Function">has-contractible-classifying-type-prop-Concrete-Group</a> <a id="1304" class="Symbol">:</a> <a id="1306" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1311" href="group-theory.trivial-concrete-groups.html#1205" class="Bound">l</a>
  <a id="1315" href="group-theory.trivial-concrete-groups.html#1250" class="Function">has-contractible-classifying-type-prop-Concrete-Group</a> <a id="1369" class="Symbol">=</a>
    <a id="1375" href="higher-group-theory.trivial-higher-groups.html#1100" class="Function">has-contractible-classifying-type-prop-∞-Group</a> <a id="1422" class="Symbol">(</a><a id="1423" href="group-theory.concrete-groups.html#1268" class="Function">∞-group-Concrete-Group</a> <a id="1446" href="group-theory.trivial-concrete-groups.html#1217" class="Bound">G</a><a id="1447" class="Symbol">)</a>

  <a id="1452" href="group-theory.trivial-concrete-groups.html#1452" class="Function">has-contractible-classifying-type-Concrete-Group</a> <a id="1501" class="Symbol">:</a> <a id="1503" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1506" href="group-theory.trivial-concrete-groups.html#1205" class="Bound">l</a>
  <a id="1510" href="group-theory.trivial-concrete-groups.html#1452" class="Function">has-contractible-classifying-type-Concrete-Group</a> <a id="1559" class="Symbol">=</a>
    <a id="1565" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1575" href="group-theory.trivial-concrete-groups.html#1250" class="Function">has-contractible-classifying-type-prop-Concrete-Group</a>

  <a id="1632" href="group-theory.trivial-concrete-groups.html#1632" class="Function">is-property-has-contractible-classifying-type-Concrete-Group</a> <a id="1693" class="Symbol">:</a>
    <a id="1699" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1707" class="Symbol">(</a><a id="1708" href="group-theory.trivial-concrete-groups.html#1452" class="Function">has-contractible-classifying-type-Concrete-Group</a><a id="1756" class="Symbol">)</a>
  <a id="1760" href="group-theory.trivial-concrete-groups.html#1632" class="Function">is-property-has-contractible-classifying-type-Concrete-Group</a> <a id="1821" class="Symbol">=</a>
    <a id="1827" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1845" href="group-theory.trivial-concrete-groups.html#1250" class="Function">has-contractible-classifying-type-prop-Concrete-Group</a>
</pre>
### The trivial concrete group

<pre class="Agda"><a id="trivial-Concrete-Group"></a><a id="1944" href="group-theory.trivial-concrete-groups.html#1944" class="Function">trivial-Concrete-Group</a> <a id="1967" class="Symbol">:</a> <a id="1969" class="Symbol">{</a><a id="1970" href="group-theory.trivial-concrete-groups.html#1970" class="Bound">l</a> <a id="1972" class="Symbol">:</a> <a id="1974" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1979" class="Symbol">}</a> <a id="1981" class="Symbol">→</a> <a id="1983" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="1998" href="group-theory.trivial-concrete-groups.html#1970" class="Bound">l</a>
<a id="2000" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2004" href="group-theory.trivial-concrete-groups.html#1944" class="Function">trivial-Concrete-Group</a> <a id="2027" class="Symbol">=</a> <a id="2029" href="higher-group-theory.trivial-higher-groups.html#1698" class="Function">trivial-∞-Group</a>
<a id="2045" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2049" href="group-theory.trivial-concrete-groups.html#1944" class="Function">trivial-Concrete-Group</a> <a id="2072" class="Symbol">=</a>
  <a id="2076" href="foundation.contractible-types.html#4079" class="Function">is-trunc-is-contr</a> <a id="2094" class="Symbol">(</a><a id="2095" href="foundation-core.truncation-levels.html#710" class="Function">one-𝕋</a><a id="2100" class="Symbol">)</a> <a id="2102" class="Symbol">(</a><a id="2103" href="foundation.unit-type.html#2180" class="Function">is-contr-raise-unit</a><a id="2122" class="Symbol">)</a> <a id="2124" class="Symbol">(</a><a id="2125" href="foundation.unit-type.html#1606" class="Function">raise-star</a><a id="2135" class="Symbol">)</a> <a id="2137" class="Symbol">(</a><a id="2138" href="foundation.unit-type.html#1606" class="Function">raise-star</a><a id="2148" class="Symbol">)</a>

<a id="has-contractible-classifying-type-trivial-Concrete-Group"></a><a id="2151" href="group-theory.trivial-concrete-groups.html#2151" class="Function">has-contractible-classifying-type-trivial-Concrete-Group</a> <a id="2208" class="Symbol">:</a>
  <a id="2212" class="Symbol">{</a><a id="2213" href="group-theory.trivial-concrete-groups.html#2213" class="Bound">l</a> <a id="2215" class="Symbol">:</a> <a id="2217" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2222" class="Symbol">}</a> <a id="2224" class="Symbol">→</a>
  <a id="2228" href="group-theory.trivial-concrete-groups.html#1452" class="Function">has-contractible-classifying-type-Concrete-Group</a> <a id="2277" class="Symbol">(</a><a id="2278" href="group-theory.trivial-concrete-groups.html#1944" class="Function">trivial-Concrete-Group</a> <a id="2301" class="Symbol">{</a><a id="2302" href="group-theory.trivial-concrete-groups.html#2213" class="Bound">l</a><a id="2303" class="Symbol">})</a>
<a id="2306" href="group-theory.trivial-concrete-groups.html#2151" class="Function">has-contractible-classifying-type-trivial-Concrete-Group</a> <a id="2363" class="Symbol">=</a>
  <a id="2367" href="higher-group-theory.trivial-higher-groups.html#1916" class="Function">has-contractible-classifying-type-trivial-∞-Group</a>
</pre>
## Properties

### Having contractible classifying type is equivalent to having contractible underlying type

This remains to be formalized.
