# Idempotents in Intensional Type Theory

This file collects references to formalization of constructions and theorems
from {{#cite Shu17}}.

<pre class="Agda"><a id="151" class="Keyword">module</a> <a id="158" href="literature.idempotents-in-intensional-type-theory.html" class="Module">literature.idempotents-in-intensional-type-theory</a> <a id="208" class="Keyword">where</a>
</pre>
## 1 Introduction

The introduction section gives an introduction to the problem at hand and
motivates its study in univalent foundations.

<pre class="Agda"><a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="group-theory.groups.html" class="Module">group-theory.groups</a> <a id="399" class="Keyword">using</a>
  <a id="407" class="Symbol">(</a> <a id="409" href="group-theory.groups.html#2346" class="Function">Group</a>
  <a id="417" class="Symbol">)</a>

<a id="420" class="Keyword">open</a> <a id="425" class="Keyword">import</a> <a id="432" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a> <a id="466" class="Keyword">using</a>
  <a id="474" class="Symbol">(</a> <a id="476" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a>
  <a id="486" class="Symbol">)</a>
</pre>
## 2 Some notation and terminology

The second section introduces basic notions from homotopy type theory.

<pre class="Agda"><a id="609" class="Keyword">open</a> <a id="614" class="Keyword">import</a> <a id="621" href="foundation.dependent-function-types.html" class="Module">foundation.dependent-function-types</a> <a id="657" class="Comment">-- &quot;dependent products&quot;</a>

<a id="682" class="Keyword">open</a> <a id="687" class="Keyword">import</a> <a id="694" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a> <a id="726" class="Comment">-- &quot;dependent sums&quot;</a>

<a id="747" class="Keyword">open</a> <a id="752" class="Keyword">import</a> <a id="759" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="785" class="Keyword">using</a>
  <a id="793" class="Symbol">(</a> <a id="795" href="foundation-core.identity-types.html#2713" class="Function Operator">_＝_</a> <a id="799" class="Comment">-- &quot;identity type, its elements are paths&quot;</a>
  <a id="844" class="Symbol">;</a> <a id="846" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="851" class="Comment">-- &quot;the canonical elements of the identity types&quot;</a>
  <a id="903" class="Symbol">;</a> <a id="905" href="foundation-core.identity-types.html#6114" class="Function">concat</a> <a id="912" class="Comment">-- &quot;transitivity of paths&quot;</a>
  <a id="941" class="Symbol">;</a> <a id="943" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="947" class="Comment">-- &quot;symmetry of paths&quot;</a>
  <a id="972" class="Symbol">;</a> <a id="974" href="foundation-core.identity-types.html#3722" class="Function">ind-Id</a> <a id="981" class="Comment">-- &quot;eliminator of the identity type&quot;</a>
  <a id="1020" class="Symbol">)</a>

<a id="1023" class="Keyword">open</a> <a id="1028" class="Keyword">import</a> <a id="1035" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a> <a id="1082" class="Keyword">using</a>
  <a id="1090" class="Symbol">(</a> <a id="1092" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="1095" class="Comment">-- &quot;action of functions on paths&quot;</a>
  <a id="1131" class="Symbol">;</a> <a id="1133" href="foundation.action-on-identifications-functions.html#1124" class="Function">ap-comp</a> <a id="1141" class="Comment">-- &quot;functoriality of `ap` with respect to function composition&quot;</a>
  <a id="1207" class="Symbol">;</a> <a id="1209" href="foundation.action-on-identifications-functions.html#1903" class="Function">ap-concat</a> <a id="1219" class="Comment">-- &quot;functoriality of `ap` with respect to transitivity of paths&quot;</a>
  <a id="1286" class="Symbol">)</a>
</pre>
The preferred definition for propositions in the library, `is-prop`, are types
whose identity types are [contractible](foundation-core.contractible-types.md).

<pre class="Agda"><a id="1461" class="Keyword">open</a> <a id="1466" class="Keyword">import</a> <a id="1473" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a> <a id="1502" class="Keyword">using</a>
  <a id="1510" class="Symbol">(</a> <a id="1512" href="foundation-core.propositions.html#2015" class="Function">all-elements-equal</a> <a id="1531" class="Comment">-- &quot;mere proposition&quot;</a>
  <a id="1555" class="Symbol">;</a> <a id="1557" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1565" class="Comment">-- all identity types are contractible</a>
  <a id="1606" class="Symbol">)</a>
</pre>
The preferred definition for sets in the library, `is-set` are types whose
identity types are propositions in the preferred sense of the library. While the
same relation holds for the definitions used in the article, we note that it
does not extend one dimension lower to contractible types as our scheme does.

<pre class="Agda"><a id="1933" class="Keyword">open</a> <a id="1938" class="Keyword">import</a> <a id="1945" href="foundation-core.sets.html" class="Module">foundation-core.sets</a> <a id="1966" class="Keyword">using</a>
  <a id="1974" class="Symbol">(</a> <a id="1976" href="foundation-core.sets.html#2399" class="Function">has-uip</a> <a id="1984" class="Comment">-- &quot;satisfies uip&quot;</a>
  <a id="2005" class="Symbol">;</a> <a id="2007" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="2014" class="Comment">-- all identity types are propositions</a>
  <a id="2055" class="Symbol">)</a>

<a id="2058" class="Keyword">open</a> <a id="2063" class="Keyword">import</a> <a id="2070" href="foundation.homotopies.html" class="Module">foundation.homotopies</a> <a id="2092" class="Keyword">using</a>
  <a id="2100" class="Symbol">(</a> <a id="2102" href="foundation-core.homotopies.html#2535" class="Function Operator">_~_</a> <a id="2106" class="Comment">-- &quot;homotopy&quot;</a>
  <a id="2122" class="Symbol">;</a> <a id="2124" href="foundation-core.homotopies.html#7052" class="Function">nat-htpy</a> <a id="2133" class="Comment">-- &quot;naturality of homotopies&quot;</a>
  <a id="2165" class="Symbol">)</a>
</pre>
The preferred notion of equivalence in the library coincides with the example
given in the article: an equivalence is a function equipped with a left inverse
and a right inverse.

<pre class="Agda"><a id="2360" class="Keyword">open</a> <a id="2365" class="Keyword">import</a> <a id="2372" href="foundation.equivalences.html" class="Module">foundation.equivalences</a> <a id="2396" class="Keyword">using</a>
  <a id="2404" class="Symbol">(</a> <a id="2406" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="2415" class="Comment">-- &quot;type of equivalence proofs&quot;</a>
  <a id="2449" class="Symbol">;</a> <a id="2451" href="foundation-core.equivalences.html#2490" class="Function">equiv</a> <a id="2457" class="Comment">-- &quot;type of equivalences&quot;</a>
  <a id="2485" class="Symbol">;</a> <a id="2487" href="foundation.equivalences.html#4907" class="Function">is-property-is-equiv</a> <a id="2508" class="Comment">-- &quot;the type of equivalence proofs is a mere proposition&quot;</a>
  <a id="2568" class="Symbol">)</a>

<a id="2571" class="Keyword">open</a> <a id="2576" class="Keyword">import</a> <a id="2583" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a> <a id="2618" class="Keyword">using</a>
  <a id="2626" class="Symbol">(</a> <a id="2628" href="foundation.function-extensionality.html#4206" class="Function">funext</a> <a id="2635" class="Comment">-- &quot;the function extensionality axiom&quot;</a>
  <a id="2676" class="Symbol">)</a>

<a id="2679" class="Keyword">open</a> <a id="2684" class="Keyword">import</a> <a id="2691" href="foundation.univalence.html" class="Module">foundation.univalence</a> <a id="2713" class="Keyword">using</a>
  <a id="2721" class="Symbol">(</a> <a id="2723" href="foundation-core.univalence.html#1454" class="Function">equiv-eq</a> <a id="2732" class="Comment">-- &quot;the canonical map `(A ＝ B) → (A ≃ B)`&quot;</a>
  <a id="2777" class="Symbol">;</a> <a id="2779" href="foundation.univalence.html#2111" class="Function">univalence</a> <a id="2790" class="Comment">-- &quot;the univalence axiom&quot;</a>
  <a id="2818" class="Symbol">)</a>

<a id="2821" class="Keyword">open</a> <a id="2826" class="Keyword">import</a> <a id="2833" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a> <a id="2870" class="Keyword">using</a>
  <a id="2878" class="Symbol">(</a> <a id="2880" href="foundation.propositional-truncations.html#1662" class="Function Operator">║_║₋₁</a> <a id="2886" class="Comment">-- &quot;propositional truncation&quot;</a>
  <a id="2918" class="Symbol">;</a> <a id="2920" href="foundation.propositional-truncations.html#1721" class="Function">unit-trunc-Prop</a> <a id="2936" class="Comment">-- &quot;the map `A → ║ A ║₋₁`&quot;</a>
  <a id="2965" class="Symbol">;</a> <a id="2967" href="foundation.propositional-truncations.html#5490" class="Function">universal-property-trunc-Prop</a> <a id="2997" class="Comment">-- &quot;the universal property of propositional truncation&quot;</a>
  <a id="3055" class="Symbol">)</a>

<a id="3058" class="Keyword">open</a> <a id="3063" class="Keyword">import</a> <a id="3070" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a> <a id="3099" class="Keyword">using</a>
  <a id="3107" class="Symbol">(</a> <a id="3109" href="foundation.mere-equivalences.html#960" class="Function">mere-equiv</a> <a id="3120" class="Comment">-- &quot;merely equivalent&quot;</a>
  <a id="3145" class="Symbol">)</a>

<a id="3148" class="Keyword">open</a> <a id="3153" class="Keyword">import</a> <a id="3160" href="foundation.univalence-implies-function-extensionality.html" class="Module">foundation.univalence-implies-function-extensionality</a> <a id="3214" class="Keyword">using</a>
  <a id="3222" class="Symbol">(</a> <a id="3224" href="foundation.univalence-implies-function-extensionality.html#1735" class="Function">funext-univalence</a> <a id="3242" class="Comment">-- &quot;univalence implies function extensionality&quot;</a>
  <a id="3292" class="Symbol">)</a>

<a id="3295" class="Comment">-- MISSING: propositional truncations imply function extensionality</a>

<a id="3364" class="Keyword">open</a> <a id="3369" class="Keyword">import</a> <a id="3376" href="foundation.equality-cartesian-product-types.html" class="Module">foundation.equality-cartesian-product-types</a> <a id="3420" class="Keyword">using</a>
  <a id="3428" class="Symbol">(</a> <a id="3430" href="foundation.equality-cartesian-product-types.html#1050" class="Function">Eq-product</a> <a id="3441" class="Comment">-- observational equality on pairs</a>
  <a id="3478" class="Symbol">;</a> <a id="3480" href="foundation.equality-cartesian-product-types.html#2374" class="Function">equiv-pair-eq</a> <a id="3494" class="Comment">-- &quot;characterization of the identity types of cartesian product type formation&quot;</a>
  <a id="3576" class="Symbol">)</a>
</pre>
## 3 Some pre-idempotents that split

In this section, definitions of "pre-idempotents", "split idempotents" and
"quasi-idempotents" are given, and basic relations between them are established.

**Definition 3.1.** Pre-idempotents.

The library's preferred terminology for "a pre-idempotent" is "an idempotent".
We reserve the terminology "a coherent idempotent" for what in the article is
referred to as "a (fully coherent) idempotent".

<pre class="Agda"><a id="4030" class="Keyword">open</a> <a id="4035" class="Keyword">import</a> <a id="4042" href="foundation.endomorphisms.html" class="Module">foundation.endomorphisms</a> <a id="4067" class="Keyword">using</a>
  <a id="4075" class="Symbol">(</a> <a id="4077" href="foundation-core.endomorphisms.html#506" class="Function">endo</a> <a id="4082" class="Comment">-- &quot;endofunction&quot;</a>
  <a id="4102" class="Symbol">)</a>

<a id="4105" class="Keyword">open</a> <a id="4110" class="Keyword">import</a> <a id="4117" href="foundation.idempotent-maps.html" class="Module">foundation.idempotent-maps</a> <a id="4144" class="Keyword">using</a>
  <a id="4152" class="Symbol">(</a> <a id="4154" href="foundation.idempotent-maps.html#2443" class="Function">is-idempotent</a> <a id="4168" class="Comment">-- &quot;idempotency witness&quot;</a>
  <a id="4195" class="Symbol">;</a> <a id="4197" href="foundation.idempotent-maps.html#2583" class="Function">idempotent-map</a> <a id="4212" class="Comment">-- &quot;pre-idempotent (map)&quot;</a>
  <a id="4240" class="Symbol">)</a>
</pre>
**Definition 3.2.** Retracts and splittings.

<pre class="Agda"><a id="4301" class="Keyword">open</a> <a id="4306" class="Keyword">import</a> <a id="4313" href="foundation.retracts-of-types.html" class="Module">foundation.retracts-of-types</a> <a id="4342" class="Keyword">using</a>
  <a id="4350" class="Symbol">(</a> <a id="4352" href="foundation-core.retracts-of-types.html#2736" class="Function">retracts</a> <a id="4361" class="Comment">-- &quot;retracts of a type&quot;</a>
  <a id="4387" class="Symbol">;</a> <a id="4389" href="foundation-core.retracts-of-types.html#1637" class="Function">retract</a> <a id="4397" class="Comment">-- &quot;type of retracts between two types&quot;</a>
  <a id="4439" class="Symbol">)</a>

<a id="4442" class="Keyword">open</a> <a id="4447" class="Keyword">import</a> <a id="4454" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a> <a id="4487" class="Keyword">using</a>
  <a id="4495" class="Symbol">(</a> <a id="4497" href="foundation.split-idempotent-maps.html#3054" class="Function">is-split-idempotent</a> <a id="4517" class="Comment">-- &quot;splitting of an endofunction&quot;</a>
  <a id="4553" class="Symbol">)</a>
</pre>
**Lemma 3.3.** If $f$ has a splitting, then it is pre-idempotent.

<pre class="Agda"><a id="4635" class="Keyword">open</a> <a id="4640" class="Keyword">import</a> <a id="4647" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a> <a id="4680" class="Keyword">using</a>
  <a id="4688" class="Symbol">(</a> <a id="4690" href="foundation.split-idempotent-maps.html#16860" class="Function">is-idempotent-is-split-idempotent</a>
  <a id="4726" class="Symbol">)</a>
</pre>
**Lemma 3.4.** The type associated to a splitting of a map is unique up to
equivalence.

<pre class="Agda"><a id="4830" class="Keyword">open</a> <a id="4835" class="Keyword">import</a> <a id="4842" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a> <a id="4875" class="Keyword">using</a>
  <a id="4883" class="Symbol">(</a> <a id="4885" href="foundation.split-idempotent-maps.html#10634" class="Function">essentially-unique-splitting-type-is-split-idempotent</a>
  <a id="4941" class="Symbol">)</a>
</pre>
**Definition 3.5.** Quasi-idempotents.

The library's preferred terminology for "a quasi-idempotent" is "a quasicoherent
idempotent".

<pre class="Agda"><a id="5091" class="Keyword">open</a> <a id="5096" class="Keyword">import</a> <a id="5103" href="foundation.quasicoherently-idempotent-maps.html" class="Module">foundation.quasicoherently-idempotent-maps</a> <a id="5146" class="Keyword">using</a>
  <a id="5154" class="Symbol">(</a> <a id="5156" href="foundation.quasicoherently-idempotent-maps.html#2385" class="Function">is-quasicoherently-idempotent</a> <a id="5186" class="Comment">-- &quot;the type of witnesses of quasi-idempotence&quot;</a>
  <a id="5236" class="Symbol">;</a> <a id="5238" href="foundation.quasicoherently-idempotent-maps.html#2985" class="Function">quasicoherently-idempotent-map</a> <a id="5269" class="Comment">-- &quot;the type of quasi-idempotents&quot;</a>
  <a id="5306" class="Symbol">)</a>
</pre>
**Lemma 3.6.** If $f$ has a splitting, then it is a quasi-idempotent.

<pre class="Agda"><a id="5392" class="Keyword">open</a> <a id="5397" class="Keyword">import</a> <a id="5404" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a> <a id="5437" class="Keyword">using</a>
  <a id="5445" class="Symbol">(</a> <a id="5447" href="foundation.split-idempotent-maps.html#18562" class="Function">is-quasicoherently-idempotent-is-split-idempotent</a>
  <a id="5499" class="Symbol">)</a>
</pre>
**Theorem 3.7.** If $X$ is a set, then any pre-idempotent on $X$ has a
splitting.

<pre class="Agda"><a id="5597" class="Keyword">open</a> <a id="5602" class="Keyword">import</a> <a id="5609" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a> <a id="5642" class="Keyword">using</a>
  <a id="5650" class="Symbol">(</a> <a id="5652" href="foundation.split-idempotent-maps.html#21093" class="Function">is-split-idempotent-is-idempotent-is-set</a>
  <a id="5695" class="Symbol">)</a>
</pre>
**Example 3.8.**

> This example is not formalized.

**Theorem 3.9.** If a pre-idempotent is weakly constant, then it has a
splitting.

<pre class="Agda"><a id="5846" class="Keyword">open</a> <a id="5851" class="Keyword">import</a> <a id="5858" href="foundation.weakly-constant-maps.html" class="Module">foundation.weakly-constant-maps</a> <a id="5890" class="Keyword">using</a>
  <a id="5898" class="Symbol">(</a> <a id="5900" href="foundation.weakly-constant-maps.html#1265" class="Function">is-weakly-constant-map</a> <a id="5923" class="Comment">-- &quot;the type of witnesses that a map is weakly constant&quot;</a>
  <a id="5982" class="Symbol">;</a> <a id="5984" href="foundation.weakly-constant-maps.html#1465" class="Function">weakly-constant-map</a> <a id="6004" class="Comment">-- &quot;the type of weakly constant maps&quot;</a>
  <a id="6044" class="Symbol">)</a>

<a id="6047" class="Keyword">open</a> <a id="6052" class="Keyword">import</a> <a id="6059" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a> <a id="6092" class="Keyword">using</a>
  <a id="6100" class="Symbol">(</a> <a id="6102" href="foundation.split-idempotent-maps.html#23781" class="Function">is-split-idempotent-is-weakly-constant-map-is-idempotent</a>
  <a id="6161" class="Symbol">)</a>
</pre>
**Theorem 3.10.** An endofunction $f$ has a splitting in which the section $s$
is an embedding if and only if it is pre-idempotent and the type $f(x) = x$
admits a weakly constant endofunction for all $x$.

<pre class="Agda"><a id="6383" class="Keyword">open</a> <a id="6388" class="Keyword">import</a> <a id="6395" href="foundation.sections.html" class="Module">foundation.sections</a> <a id="6415" class="Keyword">using</a>
  <a id="6423" class="Symbol">(</a> <a id="6425" href="foundation-core.sections.html#1194" class="Function">is-section</a> <a id="6436" class="Comment">-- &quot;the type of witnesses that a map is a section to a map&quot;</a>
  <a id="6498" class="Symbol">;</a> <a id="6500" href="foundation-core.sections.html#1373" class="Function">section</a> <a id="6508" class="Comment">-- &quot;the type of sections of a map&quot;</a>
  <a id="6545" class="Symbol">)</a>

<a id="6548" class="Keyword">open</a> <a id="6553" class="Keyword">import</a> <a id="6560" href="foundation.embeddings.html" class="Module">foundation.embeddings</a> <a id="6582" class="Keyword">using</a>
  <a id="6590" class="Symbol">(</a> <a id="6592" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="6599" class="Comment">-- &quot;the type of witnesses that a map is an embedding&quot;</a>
  <a id="6655" class="Symbol">;</a> <a id="6657" href="foundation-core.embeddings.html#1627" class="Function Operator">_↪_</a> <a id="6661" class="Comment">-- &quot;the type of embeddings between two types&quot;</a>
  <a id="6709" class="Symbol">)</a>
</pre>
> The proof remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

## 4 A pre-idempotent that doesn't split

In this section, assuming univalence and propositional truncations, an example
is given of a pre-idempotent map that does not split or extend to a
quasi-idempotent. Such a map is constructed on the
[connected component of the universe](foundation.connected-components-universes.md)
at the [cantor space](set-theory.cantor-space.md), i.e., its classifying space.

> This section remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

**Example 4.1.** An example of an idempotence witness that cannot be extended to
a coherent system of idempotence data.

<pre class="Agda"><a id="7457" class="Comment">-- TODO</a>
</pre>
**Definition 4.2.** The Cantor space.

<pre class="Agda"><a id="7517" class="Keyword">open</a> <a id="7522" class="Keyword">import</a> <a id="7529" href="set-theory.cantor-space.html" class="Module">set-theory.cantor-space</a> <a id="7553" class="Keyword">using</a>
  <a id="7561" class="Symbol">(</a> <a id="7563" href="set-theory.cantor-space.html#1210" class="Function">cantor-space</a> <a id="7576" class="Comment">-- &quot;C&quot;</a>
  <a id="7585" class="Symbol">)</a>
</pre>
**Lemma 4.3.** Assuming function extensionality, `C ≃ (C + C)`.

<pre class="Agda"><a id="7665" class="Comment">-- TODO</a>
</pre>
**Definition 4.5.** $B\operatorname{Aut}({-})$.

<pre class="Agda"><a id="7735" class="Keyword">open</a> <a id="7740" class="Keyword">import</a> <a id="7747" href="foundation.connected-components-universes.html" class="Module">foundation.connected-components-universes</a> <a id="7789" class="Keyword">using</a>
  <a id="7797" class="Symbol">(</a> <a id="7799" href="foundation.connected-components-universes.html#1854" class="Function">component-UU</a> <a id="7812" class="Comment">-- &quot;BAut(-)&quot;</a>
  <a id="7827" class="Symbol">)</a>
</pre>
**Theorem 4.6.** There exists a pre-idempotent on $B\operatorname{Aut}(C)$ that
does not split.

<pre class="Agda"><a id="7939" class="Comment">-- TODO</a>
</pre>
**Corollary 4.7.** It is impossible to prove in MLTT that all pre-idempotents
split, or even that all pre-idempotents are quasi-idempotent.

The previous theorem shows that in MLTT with univalence and propositional
truncations the statement that all pre-idempotents split is false. Thus if it
were provable in MLTT then MLTT with univalence and propositional truncations
would be inconsistent, but it is not.

## 5 All quasi-idempotents split

In this section it is shown that, assuming function extensionality, every
quasi-idempotent map splits.

**Example 5.1.** A naïve attempt.

> This example is not formalized.

Sequential colimits of types.

<pre class="Agda"><a id="8609" class="Keyword">open</a> <a id="8614" class="Keyword">import</a> <a id="8621" href="synthetic-homotopy-theory.sequential-diagrams.html" class="Module">synthetic-homotopy-theory.sequential-diagrams</a> <a id="8667" class="Keyword">using</a>
  <a id="8675" class="Symbol">(</a> <a id="8677" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a>
  <a id="8698" class="Symbol">)</a>

<a id="8701" class="Keyword">open</a> <a id="8706" class="Keyword">import</a> <a id="8713" href="synthetic-homotopy-theory.sequential-colimits.html" class="Module">synthetic-homotopy-theory.sequential-colimits</a> <a id="8759" class="Keyword">using</a>
  <a id="8767" class="Symbol">(</a> <a id="8769" href="synthetic-homotopy-theory.sequential-colimits.html#4019" class="Function">standard-sequential-colimit</a>
  <a id="8799" class="Symbol">)</a>
</pre>
Sequential limits of types.

<pre class="Agda"><a id="8843" class="Keyword">open</a> <a id="8848" class="Keyword">import</a> <a id="8855" href="foundation.inverse-sequential-diagrams.html" class="Module">foundation.inverse-sequential-diagrams</a> <a id="8894" class="Keyword">using</a>
  <a id="8902" class="Symbol">(</a> <a id="8904" href="foundation.inverse-sequential-diagrams.html#1208" class="Function">inverse-sequential-diagram</a>
  <a id="8933" class="Symbol">)</a>

<a id="8936" class="Keyword">open</a> <a id="8941" class="Keyword">import</a> <a id="8948" href="foundation.sequential-limits.html" class="Module">foundation.sequential-limits</a> <a id="8977" class="Keyword">using</a>
  <a id="8985" class="Symbol">(</a> <a id="8987" href="foundation.sequential-limits.html#2101" class="Function">standard-sequential-limit</a>
  <a id="9015" class="Symbol">)</a>
</pre>
**Lemma 5.2.** Characterization of the identity types of sequential limit
formation.

The formalization generalizes the result of the paper by considering general
inverse sequential diagrams rather than those that are constantly $f$. Also note
that compared to the paper, the coherences in the formalization are transposed.

<pre class="Agda"><a id="9355" class="Keyword">open</a> <a id="9360" class="Keyword">import</a> <a id="9367" href="foundation.sequential-limits.html" class="Module">foundation.sequential-limits</a> <a id="9396" class="Keyword">using</a>
  <a id="9404" class="Symbol">(</a> <a id="9406" href="foundation.sequential-limits.html#5555" class="Function">Eq-standard-sequential-limit</a> <a id="9435" class="Comment">-- observational equality on standard sequential limits</a>
  <a id="9493" class="Symbol">;</a> <a id="9495" href="foundation.sequential-limits.html#6912" class="Function">extensionality-standard-sequential-limit</a>
  <a id="9538" class="Symbol">)</a>
</pre>
**Theorem 5.3.** Assuming function extensionality, any quasi-idempotent splits.

<pre class="Agda"><a id="9634" class="Keyword">open</a> <a id="9639" class="Keyword">import</a> <a id="9646" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a> <a id="9679" class="Keyword">using</a>
  <a id="9687" class="Symbol">(</a> <a id="9689" href="foundation.split-idempotent-maps.html#39540" class="Function">is-split-idempotent-is-quasicoherently-idempotent</a>
  <a id="9741" class="Symbol">)</a>
</pre>
**Remark 5.4.** Components of the construction.

<pre class="Agda"><a id="9805" class="Keyword">open</a> <a id="9810" class="Keyword">import</a> <a id="9817" href="foundation.split-idempotent-maps.html" class="Module">foundation.split-idempotent-maps</a> <a id="9850" class="Keyword">using</a>
  <a id="9858" class="Symbol">(</a> <a id="9860" href="foundation.split-idempotent-maps.html#24431" class="Function">inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent&#39;</a>
  <a id="9935" class="Symbol">;</a> <a id="9937" href="foundation.split-idempotent-maps.html#24648" class="Function">splitting-type-is-quasicoherently-idempotent&#39;</a>
  <a id="9985" class="Symbol">;</a> <a id="9987" href="foundation.split-idempotent-maps.html#24866" class="Function">inclusion-splitting-type-is-quasicoherently-idempotent&#39;</a>
  <a id="10045" class="Symbol">;</a> <a id="10047" href="foundation.split-idempotent-maps.html#25380" class="Function">map-retraction-splitting-type-is-quasicoherently-idempotent&#39;</a>
  <a id="10110" class="Symbol">;</a> <a id="10112" href="foundation.split-idempotent-maps.html#25608" class="Function">htpy-is-split-idempotent-is-quasicoherently-idempotent&#39;</a> <a id="10168" class="Comment">-- &quot;requires function extensionality&quot;</a>
  <a id="10208" class="Symbol">)</a>
</pre>
## 6 Splitting is a retraction

In this section it is shown, assuming the univalence axiom, that the type of
splittings of a pre-idempotent map is a retract of the type of extensions to
quasi-idempotence.

> This section remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

**Lemma 6.3.** Characterization of the identity types of retract formation.

<pre class="Agda"><a id="10611" class="Keyword">open</a> <a id="10616" class="Keyword">import</a> <a id="10623" href="foundation.retracts-of-types.html" class="Module">foundation.retracts-of-types</a> <a id="10652" class="Keyword">using</a>
  <a id="10660" class="Symbol">(</a> <a id="10662" href="foundation.retracts-of-types.html#3532" class="Function">equiv-retracts</a> <a id="10677" class="Comment">-- observational equality on retracts</a>
  <a id="10717" class="Symbol">;</a> <a id="10719" href="foundation.retracts-of-types.html#5377" class="Function">extensionality-retracts</a>
  <a id="10745" class="Symbol">)</a>
</pre>
## 7 Splitting is not an equivalence

In this section, it is argued that there may be more quasi-idempotence witnesses
than splittings of a map.

> This section remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

## 8 The double classifying space of 2

In this section, an explicit example of a type with more quasi-idempotents than
splittings are worked out using the univalence axiom and propositional
truncations, proving Theorem 7.4 from the previous section.

> This section remains to be formalized.
> [#1103](https://github.com/UniMath/agda-unimath/issues/1103)

## 9 Coherent idempotents

In this section, assuming function extensionality, a "homotopy-correct"
definition of coherently idempotent maps is given.

**Definition 9.1.** (Fully coherent) idempotents.

<pre class="Agda"><a id="11570" class="Keyword">open</a> <a id="11575" class="Keyword">import</a> <a id="11582" href="foundation.coherently-idempotent-maps.html" class="Module">foundation.coherently-idempotent-maps</a> <a id="11620" class="Keyword">using</a>
  <a id="11628" class="Symbol">(</a> <a id="11630" href="foundation.coherently-idempotent-maps.html#1848" class="Function">is-coherently-idempotent</a> <a id="11655" class="Comment">-- &quot;type of (fully coherent) idempotence witnesses&quot;</a>
  <a id="11709" class="Symbol">)</a>
</pre>
## 10 Conclusion

This section of the article features a series of 5 open problems.

> If a resolution to any of these open problems is formalized in the library,
> then it should be recorded here.

**Open Problem 10.1.** Can quasi-idempotents be split in MLTT without assuming
function extensionality? In particular, is there a more "finite" way to
construct such a splitting?

**Open Problem 10.2.** Is the map
$\operatorname{Idem}(X) → \operatorname{QIdem}(X)$ an embedding?

**Open Problem 10.3.** Is the map
$\operatorname{Idem}(X) → \operatorname{PIdem}(X)$ an embedding?

**Open Problem 10.4.** Can $\operatorname{Idem}(X)$ be defined without assuming
function extensionality?

**Open Problem 10.5.** Are there examples of other fully-coherent higher
homotopy structures that can be obtained from a finite amount of coherence by
splitting an idempotent?
