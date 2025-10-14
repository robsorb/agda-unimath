# Epimorphisms in groups

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="group-theory.epimorphisms-groups.html" class="Module">group-theory.epimorphisms-groups</a> <a id="75" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="131" class="Keyword">open</a> <a id="136" class="Keyword">import</a> <a id="143" href="category-theory.epimorphisms-in-large-precategories.html" class="Module">category-theory.epimorphisms-in-large-precategories</a>

<a id="196" class="Keyword">open</a> <a id="201" class="Keyword">import</a> <a id="208" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="304" class="Keyword">open</a> <a id="309" class="Keyword">import</a> <a id="316" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
<a id="350" class="Keyword">open</a> <a id="355" class="Keyword">import</a> <a id="362" href="group-theory.isomorphisms-groups.html" class="Module">group-theory.isomorphisms-groups</a>
<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="group-theory.precategory-of-groups.html" class="Module">group-theory.precategory-of-groups</a>
</pre>
</details>

## Idea

A [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` is an
**epimorphism** if the precomposition function

```text
  - ∘ f : hom-set-Group H K → hom-set-Group G K
```

is an [embedding](foundation.embeddings.md) for any
[group](group-theory.groups.md) `K`. In other words, `f` is an epimorphism if
for any two group homomorphisms `g h : H → K` we have that `g ∘ f = h ∘ f`
implies `g = h`.

## Definition

<pre class="Agda"><a id="902" class="Keyword">module</a> <a id="909" href="group-theory.epimorphisms-groups.html#909" class="Module">_</a>
  <a id="913" class="Symbol">{</a><a id="914" href="group-theory.epimorphisms-groups.html#914" class="Bound">l1</a> <a id="917" href="group-theory.epimorphisms-groups.html#917" class="Bound">l2</a> <a id="920" class="Symbol">:</a> <a id="922" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="927" class="Symbol">}</a> <a id="929" class="Symbol">(</a><a id="930" href="group-theory.epimorphisms-groups.html#930" class="Bound">l3</a> <a id="933" class="Symbol">:</a> <a id="935" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="940" class="Symbol">)</a> <a id="942" class="Symbol">(</a><a id="943" href="group-theory.epimorphisms-groups.html#943" class="Bound">G</a> <a id="945" class="Symbol">:</a> <a id="947" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="953" href="group-theory.epimorphisms-groups.html#914" class="Bound">l1</a><a id="955" class="Symbol">)</a>
  <a id="959" class="Symbol">(</a><a id="960" href="group-theory.epimorphisms-groups.html#960" class="Bound">H</a> <a id="962" class="Symbol">:</a> <a id="964" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="970" href="group-theory.epimorphisms-groups.html#917" class="Bound">l2</a><a id="972" class="Symbol">)</a> <a id="974" class="Symbol">(</a><a id="975" href="group-theory.epimorphisms-groups.html#975" class="Bound">f</a> <a id="977" class="Symbol">:</a> <a id="979" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="989" href="group-theory.epimorphisms-groups.html#943" class="Bound">G</a> <a id="991" href="group-theory.epimorphisms-groups.html#960" class="Bound">H</a><a id="992" class="Symbol">)</a>
  <a id="996" class="Keyword">where</a>

  <a id="1005" href="group-theory.epimorphisms-groups.html#1005" class="Function">is-epi-prop-hom-Group</a> <a id="1027" class="Symbol">:</a> <a id="1029" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1034" class="Symbol">(</a><a id="1035" href="group-theory.epimorphisms-groups.html#914" class="Bound">l1</a> <a id="1038" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1040" href="group-theory.epimorphisms-groups.html#917" class="Bound">l2</a> <a id="1043" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1045" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1050" href="group-theory.epimorphisms-groups.html#930" class="Bound">l3</a><a id="1052" class="Symbol">)</a>
  <a id="1056" href="group-theory.epimorphisms-groups.html#1005" class="Function">is-epi-prop-hom-Group</a> <a id="1078" class="Symbol">=</a>
    <a id="1084" href="category-theory.epimorphisms-in-large-precategories.html#940" class="Function">is-epi-prop-Large-Precategory</a> <a id="1114" href="group-theory.precategory-of-groups.html#743" class="Function">Group-Large-Precategory</a> <a id="1138" href="group-theory.epimorphisms-groups.html#930" class="Bound">l3</a> <a id="1141" href="group-theory.epimorphisms-groups.html#943" class="Bound">G</a> <a id="1143" href="group-theory.epimorphisms-groups.html#960" class="Bound">H</a> <a id="1145" href="group-theory.epimorphisms-groups.html#975" class="Bound">f</a>

  <a id="1150" href="group-theory.epimorphisms-groups.html#1150" class="Function">is-epi-hom-Group</a> <a id="1167" class="Symbol">:</a> <a id="1169" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1172" class="Symbol">(</a><a id="1173" href="group-theory.epimorphisms-groups.html#914" class="Bound">l1</a> <a id="1176" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1178" href="group-theory.epimorphisms-groups.html#917" class="Bound">l2</a> <a id="1181" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1183" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1188" href="group-theory.epimorphisms-groups.html#930" class="Bound">l3</a><a id="1190" class="Symbol">)</a>
  <a id="1194" href="group-theory.epimorphisms-groups.html#1150" class="Function">is-epi-hom-Group</a> <a id="1211" class="Symbol">=</a> <a id="1213" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1223" href="group-theory.epimorphisms-groups.html#1005" class="Function">is-epi-prop-hom-Group</a>

  <a id="1248" href="group-theory.epimorphisms-groups.html#1248" class="Function">is-prop-is-epi-hom-Group</a> <a id="1273" class="Symbol">:</a> <a id="1275" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1283" href="group-theory.epimorphisms-groups.html#1150" class="Function">is-epi-hom-Group</a>
  <a id="1302" href="group-theory.epimorphisms-groups.html#1248" class="Function">is-prop-is-epi-hom-Group</a> <a id="1327" class="Symbol">=</a> <a id="1329" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1347" href="group-theory.epimorphisms-groups.html#1005" class="Function">is-epi-prop-hom-Group</a>
</pre>
## Properties

### Isomorphisms are epimorphisms

<pre class="Agda"><a id="1432" class="Keyword">module</a> <a id="1439" href="group-theory.epimorphisms-groups.html#1439" class="Module">_</a>
  <a id="1443" class="Symbol">{</a><a id="1444" href="group-theory.epimorphisms-groups.html#1444" class="Bound">l1</a> <a id="1447" href="group-theory.epimorphisms-groups.html#1447" class="Bound">l2</a> <a id="1450" class="Symbol">:</a> <a id="1452" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1457" class="Symbol">}</a> <a id="1459" class="Symbol">(</a><a id="1460" href="group-theory.epimorphisms-groups.html#1460" class="Bound">l3</a> <a id="1463" class="Symbol">:</a> <a id="1465" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1470" class="Symbol">)</a> <a id="1472" class="Symbol">(</a><a id="1473" href="group-theory.epimorphisms-groups.html#1473" class="Bound">G</a> <a id="1475" class="Symbol">:</a> <a id="1477" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1483" href="group-theory.epimorphisms-groups.html#1444" class="Bound">l1</a><a id="1485" class="Symbol">)</a>
  <a id="1489" class="Symbol">(</a><a id="1490" href="group-theory.epimorphisms-groups.html#1490" class="Bound">H</a> <a id="1492" class="Symbol">:</a> <a id="1494" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1500" href="group-theory.epimorphisms-groups.html#1447" class="Bound">l2</a><a id="1502" class="Symbol">)</a> <a id="1504" class="Symbol">(</a><a id="1505" href="group-theory.epimorphisms-groups.html#1505" class="Bound">f</a> <a id="1507" class="Symbol">:</a> <a id="1509" href="group-theory.isomorphisms-groups.html#3368" class="Function">iso-Group</a> <a id="1519" href="group-theory.epimorphisms-groups.html#1473" class="Bound">G</a> <a id="1521" href="group-theory.epimorphisms-groups.html#1490" class="Bound">H</a><a id="1522" class="Symbol">)</a>
  <a id="1526" class="Keyword">where</a>

  <a id="1535" href="group-theory.epimorphisms-groups.html#1535" class="Function">is-epi-iso-Group</a> <a id="1552" class="Symbol">:</a> <a id="1554" href="group-theory.epimorphisms-groups.html#1150" class="Function">is-epi-hom-Group</a> <a id="1571" href="group-theory.epimorphisms-groups.html#1460" class="Bound">l3</a> <a id="1574" href="group-theory.epimorphisms-groups.html#1473" class="Bound">G</a> <a id="1576" href="group-theory.epimorphisms-groups.html#1490" class="Bound">H</a> <a id="1578" class="Symbol">(</a><a id="1579" href="group-theory.isomorphisms-groups.html#3464" class="Function">hom-iso-Group</a> <a id="1593" href="group-theory.epimorphisms-groups.html#1473" class="Bound">G</a> <a id="1595" href="group-theory.epimorphisms-groups.html#1490" class="Bound">H</a> <a id="1597" href="group-theory.epimorphisms-groups.html#1505" class="Bound">f</a><a id="1598" class="Symbol">)</a>
  <a id="1602" href="group-theory.epimorphisms-groups.html#1535" class="Function">is-epi-iso-Group</a> <a id="1619" class="Symbol">=</a>
    <a id="1625" href="category-theory.epimorphisms-in-large-precategories.html#1746" class="Function">is-epi-iso-Large-Precategory</a> <a id="1654" href="group-theory.precategory-of-groups.html#743" class="Function">Group-Large-Precategory</a> <a id="1678" href="group-theory.epimorphisms-groups.html#1460" class="Bound">l3</a> <a id="1681" href="group-theory.epimorphisms-groups.html#1473" class="Bound">G</a> <a id="1683" href="group-theory.epimorphisms-groups.html#1490" class="Bound">H</a> <a id="1685" href="group-theory.epimorphisms-groups.html#1505" class="Bound">f</a>
</pre>
### A group homomorphism is surjective if and only if it is an epimorphism

**Proof using the law of excluded middle:** The forward direction of this claim
is the easier of the two directions, and this part of the proof doesn't require
the [law of excluded middle](foundation.law-of-excluded-middle.md). If `f` is
[surjective](foundation.surjective-maps.md) and `g h : H → K` are two group
homomorphisms such that `g ∘ f ＝ h ∘ f`, then to show that `g ＝ h` it suffices
to show that `g y ＝ h y` for any `y : H`. Since we are proving a
[proposition](foundation.propositions.md) and `f` is assumed to be surjective,
we may assume `x : G` equipped with an
[identification](foundation.identity-types.md) `f x ＝ y`. It therefore suffices
to show that `g (f x) ＝ h (f x)`, which was assumed.

For the converse, suppose that `f : G → H` is an epimorphism and consider the
[image subgroup](group-theory.images-of-group-homomorphisms.md) `I := im f` of
`H`. We first show that `I` is [normal](group-theory.normal-subgroups.md), and
then we show that `I ＝ H`.

In order to show that `I` is normal, we want to show that `I` has only one
conjugacy class, namely itself. Consider the group `K` of permutations of the
set of [conjugate](group-theory.conjugation.md)
[subgroups](group-theory.subgroups.md) of the subgroup `I` of `H`. There is a
group homomorphism `α : H → K` given by `h ↦ J ↦ hJh⁻¹`, where `J` ranges over
the conjugacy classes of `I`. Notice that `I` itself is a fixed point of the
conjugation operation `J ↦ f(x)Jf(x)⁻¹`, i.e., `I` is a fixed point of
`α(f(x))`. We claim that there is another homomorphism `β : H → K` given by
`h ↦ α(h) ∘ (I h⁻¹Ih)`, where we precompose with the
[transposition](finite-group-theory.transpositions.md) `(I h⁻¹Ih)`. This
transposition is defined using the law of excluded middle. However, note that
`I` is always a fixed point of `β(h)`, for any `h : H`. Furthermore, we have
`α(f(x)) ＝ β(f(x))`. Therefore it follows from the assumption that `f` is an
epimorphism that `α ＝ β`. In other words, `I` is a fixed point of any
conjugation operation `J ↦ hJh⁻¹`. We conclude that `I` is normal.

Since `I` is normal, we may consider the
[quotient group](group-theory.quotient-groups.md) `H/I`. Now we observe that the
quotient map maps `f(x)` to the unit of `H/I`. Using the assumption that `f` is
an epimorphism once more, we conclude that the quotient map `H → H/I` is the
[trivial homomorphism](group-theory.trivial-group-homomorphisms.md). Therefore
it follows that `I ＝ H`. This completes the proof.
