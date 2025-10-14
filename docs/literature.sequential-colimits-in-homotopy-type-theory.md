# Sequential Colimits in Homotopy Type Theory

This file collects references to formalization of constructions and theorems
from {{#cite SvDR20}}.

<pre class="Agda"><a id="157" class="Keyword">module</a> <a id="164" href="literature.sequential-colimits-in-homotopy-type-theory.html" class="Module">literature.sequential-colimits-in-homotopy-type-theory</a> <a id="219" class="Keyword">where</a>
</pre>
## 2 Homotopy Type Theory

The second section introduces basic notions from homotopy type theory, which we
import below for completeness.

<pre class="Agda"><a id="377" class="Keyword">open</a> <a id="382" class="Keyword">import</a> <a id="389" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a> <a id="416" class="Keyword">using</a>
  <a id="424" class="Symbol">(</a> <a id="426" href="Agda.Primitive.html#388" class="Primitive">UU</a>
  <a id="431" class="Symbol">)</a>
<a id="433" class="Keyword">open</a> <a id="438" class="Keyword">import</a> <a id="445" href="foundation.identity-types.html" class="Module">foundation.identity-types</a> <a id="471" class="Keyword">using</a>
  <a id="479" class="Symbol">(</a> <a id="481" href="foundation-core.identity-types.html#2641" class="Datatype">Id</a> <a id="484" class="Comment">-- &quot;path&quot;</a>
  <a id="496" class="Symbol">;</a> <a id="498" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="503" class="Comment">-- &quot;constant path&quot;</a>
  <a id="524" class="Symbol">;</a> <a id="526" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="530" class="Comment">-- &quot;inverse path&quot;</a>
  <a id="550" class="Symbol">;</a> <a id="552" href="foundation-core.identity-types.html#6114" class="Function">concat</a> <a id="559" class="Comment">-- &quot;concatenation of paths&quot;</a>
  <a id="589" class="Symbol">;</a> <a id="591" href="foundation-core.identity-types.html#7454" class="Function">assoc</a> <a id="597" class="Comment">-- &quot;associativity of concatenation&quot;</a>
  <a id="635" class="Symbol">)</a>
<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a> <a id="696" class="Keyword">using</a>
  <a id="704" class="Symbol">(</a> <a id="706" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="709" class="Comment">-- &quot;functions respect paths&quot;</a>
  <a id="740" class="Symbol">)</a>
<a id="742" class="Keyword">open</a> <a id="747" class="Keyword">import</a> <a id="754" href="foundation.homotopies.html" class="Module">foundation.homotopies</a> <a id="776" class="Keyword">using</a>
  <a id="784" class="Symbol">(</a> <a id="786" href="foundation-core.homotopies.html#2535" class="Function Operator">_~_</a> <a id="790" class="Comment">-- &quot;homotopy&quot;</a>
  <a id="806" class="Symbol">)</a>
<a id="808" class="Keyword">open</a> <a id="813" class="Keyword">import</a> <a id="820" href="foundation.equivalences.html" class="Module">foundation.equivalences</a> <a id="844" class="Keyword">using</a>
  <a id="852" class="Symbol">(</a> <a id="854" href="foundation-core.equivalences.html#2490" class="Function">equiv</a> <a id="860" class="Comment">-- &quot;equivalence&quot;</a>
  <a id="879" class="Symbol">)</a>
<a id="881" class="Keyword">open</a> <a id="886" class="Keyword">import</a> <a id="893" href="foundation.univalence.html" class="Module">foundation.univalence</a> <a id="915" class="Keyword">using</a>
  <a id="923" class="Symbol">(</a> <a id="925" href="foundation.univalence.html#2111" class="Function">univalence</a> <a id="936" class="Comment">-- &quot;the univalence axiom&quot;</a>
  <a id="964" class="Symbol">;</a> <a id="966" href="foundation-core.univalence.html#1522" class="Function">map-eq</a> <a id="973" class="Comment">-- &quot;function p̅ associated to a path&quot;</a>
  <a id="1013" class="Symbol">)</a>
<a id="1015" class="Keyword">open</a> <a id="1020" class="Keyword">import</a> <a id="1027" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a> <a id="1062" class="Keyword">using</a>
  <a id="1070" class="Symbol">(</a> <a id="1072" href="foundation.function-extensionality.html#4206" class="Function">funext</a> <a id="1079" class="Comment">-- &quot;the function extensionality axiom&quot;</a>
  <a id="1120" class="Symbol">)</a>
<a id="1122" class="Keyword">open</a> <a id="1127" class="Keyword">import</a> <a id="1134" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a> <a id="1160" class="Keyword">using</a>
  <a id="1168" class="Symbol">(</a> <a id="1170" href="foundation-core.fibers-of-maps.html#1067" class="Function">fiber</a> <a id="1176" class="Comment">-- &quot;the homotopy fiber of a function&quot;</a>
  <a id="1216" class="Symbol">)</a>
<a id="1218" class="Keyword">open</a> <a id="1223" class="Keyword">import</a> <a id="1230" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a> <a id="1273" class="Keyword">using</a>
  <a id="1281" class="Symbol">(</a> <a id="1283" href="foundation-core.transport-along-identifications.html#832" class="Function">tr</a> <a id="1286" class="Comment">-- &quot;transport&quot;</a>
  <a id="1303" class="Symbol">)</a>
<a id="1305" class="Keyword">open</a> <a id="1310" class="Keyword">import</a> <a id="1317" href="foundation.action-on-identifications-dependent-functions.html" class="Module">foundation.action-on-identifications-dependent-functions</a> <a id="1374" class="Keyword">using</a>
  <a id="1382" class="Symbol">(</a> <a id="1384" href="foundation.action-on-identifications-dependent-functions.html#1181" class="Function">apd</a> <a id="1388" class="Comment">-- &quot;dependent functions respect paths&quot;</a>
  <a id="1429" class="Symbol">)</a>
<a id="1431" class="Keyword">open</a> <a id="1436" class="Keyword">import</a> <a id="1443" href="foundation.truncated-types.html" class="Module">foundation.truncated-types</a> <a id="1470" class="Keyword">using</a>
  <a id="1478" class="Symbol">(</a> <a id="1480" href="foundation-core.truncated-types.html#1305" class="Function">is-trunc</a> <a id="1489" class="Comment">-- &quot;`n`-truncated types&quot;</a>
  <a id="1516" class="Symbol">)</a>
<a id="1518" class="Keyword">open</a> <a id="1523" class="Keyword">import</a> <a id="1530" href="foundation.truncations.html" class="Module">foundation.truncations</a> <a id="1553" class="Keyword">using</a>
  <a id="1561" class="Symbol">(</a> <a id="1563" href="foundation.truncations.html#1445" class="Function">trunc</a> <a id="1569" class="Comment">-- &quot;the `n`-truncation of a type&quot;</a>
  <a id="1605" class="Symbol">;</a> <a id="1607" href="foundation.truncations.html#1585" class="Postulate">unit-trunc</a> <a id="1618" class="Comment">-- &quot;the unit map into a type&#39;s `n`-truncation&quot;</a>
  <a id="1667" class="Symbol">;</a> <a id="1669" href="foundation.truncations.html#1663" class="Postulate">is-truncation-trunc</a> <a id="1689" class="Comment">-- &quot;precomposing by the unit is an equivalence&quot;</a>
  <a id="1739" class="Symbol">)</a>
<a id="1741" class="Keyword">open</a> <a id="1746" class="Keyword">import</a> <a id="1753" href="foundation.connected-types.html" class="Module">foundation.connected-types</a> <a id="1780" class="Keyword">using</a>
  <a id="1788" class="Symbol">(</a> <a id="1790" href="foundation.connected-types.html#1379" class="Function">is-connected</a> <a id="1803" class="Comment">-- &quot;`n`-connected types&quot;</a>
  <a id="1830" class="Symbol">)</a>
<a id="1832" class="Keyword">open</a> <a id="1837" class="Keyword">import</a> <a id="1844" href="foundation.truncated-maps.html" class="Module">foundation.truncated-maps</a> <a id="1870" class="Keyword">using</a>
  <a id="1878" class="Symbol">(</a> <a id="1880" href="foundation-core.truncated-maps.html#925" class="Function">is-trunc-map</a> <a id="1893" class="Comment">-- &quot;`n`-truncated functions&quot;</a>
  <a id="1924" class="Symbol">)</a>
<a id="1926" class="Keyword">open</a> <a id="1931" class="Keyword">import</a> <a id="1938" href="foundation.connected-maps.html" class="Module">foundation.connected-maps</a> <a id="1964" class="Keyword">using</a>
  <a id="1972" class="Symbol">(</a> <a id="1974" href="foundation.connected-maps.html#1763" class="Function">is-connected-map</a> <a id="1991" class="Comment">-- &quot;`n`-connected functions&quot;</a>
  <a id="2022" class="Symbol">)</a>
</pre>
## 3 Sequences and Sequential Colimits

The third section defines categorical properties of sequences (which are called
_sequential diagrams_ in agda-unimath) and the colimiting functor. It concludes
by defining shifts of sequences, showing that they induce equivalences on
sequential colimits, and defines lifts of elements in a sequential diagram.

**Definition 3.1.** Sequences.

<pre class="Agda"><a id="2420" class="Keyword">open</a> <a id="2425" class="Keyword">import</a> <a id="2432" href="synthetic-homotopy-theory.sequential-diagrams.html" class="Module">synthetic-homotopy-theory.sequential-diagrams</a> <a id="2478" class="Keyword">using</a>
  <a id="2486" class="Symbol">(</a> <a id="2488" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a>
  <a id="2509" class="Symbol">)</a>
</pre>
**Definition 3.2.** Sequential colimits and their induction and recursion
principles.

Induction and recursion are given by the dependent and non-dependent universal
properties, respectively. Since we work in a setting without computational
higher inductive types, the maps induced by induction and recursion only compute
up to a path, even on points. Our homotopies in the definitions of cocones go
from left to right (i.e. `iₙ ~ iₙ₊₁ ∘ aₙ`), instead of right to left.

Our formalization works with sequential colimits specified by a cocone with a
universal property, and results about the standard construction of colimits are
obtained by specialization to the canonical cocone.

<pre class="Agda"><a id="3206" class="Keyword">open</a> <a id="3211" class="Keyword">import</a> <a id="3218" href="synthetic-homotopy-theory.sequential-colimits.html" class="Module">synthetic-homotopy-theory.sequential-colimits</a> <a id="3264" class="Keyword">using</a>
  <a id="3272" class="Symbol">(</a> <a id="3274" href="synthetic-homotopy-theory.sequential-colimits.html#4019" class="Function">standard-sequential-colimit</a> <a id="3302" class="Comment">-- the canonical colimit type</a>
  <a id="3334" class="Symbol">;</a> <a id="3336" href="synthetic-homotopy-theory.sequential-colimits.html#5359" class="Function">map-cocone-standard-sequential-colimit</a> <a id="3375" class="Comment">-- &quot;the canonical injection&quot;</a>
  <a id="3406" class="Symbol">;</a> <a id="3408" href="synthetic-homotopy-theory.sequential-colimits.html#5596" class="Function">coherence-cocone-standard-sequential-colimit</a> <a id="3453" class="Comment">-- &quot;the glue&quot;</a>
  <a id="3469" class="Symbol">;</a> <a id="3471" href="synthetic-homotopy-theory.sequential-colimits.html#4494" class="Function">dup-standard-sequential-colimit</a> <a id="3503" class="Comment">-- &quot;the induction principle&quot;</a>
  <a id="3534" class="Symbol">;</a> <a id="3536" href="synthetic-homotopy-theory.sequential-colimits.html#4928" class="Function">up-standard-sequential-colimit</a> <a id="3567" class="Comment">-- &quot;the recursion principle&quot;</a>
  <a id="3598" class="Symbol">)</a>
</pre>
**Lemma 3.3.** Uniqueness property of the sequential colimit.

The data of a homotopy between two functions out of the standard sequential
colimit is specified by the type `htpy-out-of-standard-sequential-colimit`,
which we can then turn into a proper homotopy.

<pre class="Agda"><a id="3876" class="Keyword">open</a> <a id="3881" class="Keyword">import</a> <a id="3888" href="synthetic-homotopy-theory.sequential-colimits.html" class="Module">synthetic-homotopy-theory.sequential-colimits</a> <a id="3934" class="Keyword">using</a>
  <a id="3942" class="Symbol">(</a> <a id="3944" href="synthetic-homotopy-theory.sequential-colimits.html#8883" class="Function">htpy-out-of-standard-sequential-colimit</a> <a id="3984" class="Comment">-- data of a homotopy</a>
  <a id="4008" class="Symbol">;</a> <a id="4010" href="synthetic-homotopy-theory.sequential-colimits.html#9652" class="Function">htpy-htpy-out-of-standard-sequential-colimit</a> <a id="4055" class="Comment">-- &quot;data of a homotopy induces a homotopy&quot;</a>
  <a id="4100" class="Symbol">)</a>
</pre>
**Definition 3.4.** Natural transformations and natural equivalences between
sequential diagrams.

We call natural transformations _morphisms of sequential diagrams_, and natural
equivalences _equivalences of sequential diagrams_.

<pre class="Agda"><a id="4347" class="Keyword">open</a> <a id="4352" class="Keyword">import</a> <a id="4359" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.morphisms-sequential-diagrams</a> <a id="4415" class="Keyword">using</a>
  <a id="4423" class="Symbol">(</a> <a id="4425" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#1939" class="Function">hom-sequential-diagram</a> <a id="4448" class="Comment">-- &quot;natural transformation&quot;</a>
  <a id="4478" class="Symbol">;</a> <a id="4480" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#3242" class="Function">id-hom-sequential-diagram</a> <a id="4506" class="Comment">-- &quot;identity natural transformation&quot;</a>
  <a id="4545" class="Symbol">;</a> <a id="4547" href="synthetic-homotopy-theory.morphisms-sequential-diagrams.html#4579" class="Function">comp-hom-sequential-diagram</a> <a id="4575" class="Comment">-- &quot;composition of natural transformations&quot;</a>
  <a id="4621" class="Symbol">)</a>
<a id="4623" class="Keyword">open</a> <a id="4628" class="Keyword">import</a> <a id="4635" href="synthetic-homotopy-theory.equivalences-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.equivalences-sequential-diagrams</a> <a id="4694" class="Keyword">using</a>
  <a id="4702" class="Symbol">(</a> <a id="4704" href="synthetic-homotopy-theory.equivalences-sequential-diagrams.html#1566" class="Function">equiv-sequential-diagram</a> <a id="4729" class="Comment">-- &quot;natural equivalence&quot;</a>
  <a id="4756" class="Symbol">)</a>
</pre>
**Lemma 3.5.** Functoriality of the Sequential Colimit.

<pre class="Agda"><a id="4828" class="Keyword">open</a> <a id="4833" class="Keyword">import</a> <a id="4840" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html" class="Module">synthetic-homotopy-theory.functoriality-sequential-colimits</a> <a id="4900" class="Keyword">using</a>
  <a id="4908" class="Symbol">(</a> <a id="4910" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#23380" class="Function">map-hom-standard-sequential-colimit</a> <a id="4946" class="Comment">-- &quot;a natural transformation induces a map&quot;</a>
  <a id="4992" class="Symbol">;</a> <a id="4994" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#27477" class="Function">preserves-id-map-hom-standard-sequential-colimit</a> <a id="5043" class="Comment">-- &quot;1∞ ~ id(A∞)&quot;</a>
  <a id="5062" class="Symbol">;</a> <a id="5064" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#28133" class="Function">preserves-comp-map-hom-standard-sequential-colimit</a> <a id="5115" class="Comment">-- &quot;(σ ∘ τ)∞ ~ σ∞ ∘ τ∞&quot;</a>
  <a id="5141" class="Symbol">;</a> <a id="5143" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#26890" class="Function">htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram</a> <a id="5212" class="Comment">-- &quot;homotopy of natural transformations induces a homotopy&quot;</a>
  <a id="5274" class="Symbol">;</a> <a id="5276" href="synthetic-homotopy-theory.functoriality-sequential-colimits.html#29692" class="Function">equiv-equiv-standard-sequential-colimit</a> <a id="5316" class="Comment">-- &quot;if τ is an equivalence, then τ∞ is an equivalence&quot;</a>
  <a id="5373" class="Symbol">)</a>
</pre>
**Lemma 3.6.** Dropping a head of a sequential diagram preserves the sequential
colimit.

**Lemma 3.7.** Dropping finitely many vertices from the beginning of a
sequential diagram preserves the sequential colimit.

Denoting by `A[k]` the sequence `A` with the first `k` vertices removed, we show
that the type of cocones under `A[k]` is equivalent to the type of cocones under
`A`, and conclude that any sequential colimit of `A[k]` also has the universal
property of a colimit of `A`. Specializing to the standard sequential colimit,
we get and equivalence `A[k]∞ ≃ A∞`.

<pre class="Agda"><a id="5961" class="Keyword">open</a> <a id="5966" class="Keyword">import</a> <a id="5973" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.shifts-sequential-diagrams</a> <a id="6026" class="Keyword">using</a>
  <a id="6034" class="Symbol">(</a> <a id="6036" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24110" class="Function">compute-sequential-colimit-shift-sequential-diagram</a> <a id="6088" class="Comment">-- &quot;A[k]∞ ≃ A∞&quot;</a>
  <a id="6106" class="Symbol">)</a>
<a id="compute-sequential-colimit-shift-sequential-diagram-once"></a><a id="6108" href="literature.sequential-colimits-in-homotopy-type-theory.html#6108" class="Function">compute-sequential-colimit-shift-sequential-diagram-once</a> <a id="6165" class="Symbol">=</a>
  <a id="6169" class="Symbol">λ</a> <a id="6171" href="literature.sequential-colimits-in-homotopy-type-theory.html#6171" class="Bound">l</a> <a id="6173" class="Symbol">(</a><a id="6174" href="literature.sequential-colimits-in-homotopy-type-theory.html#6174" class="Bound">A</a> <a id="6176" class="Symbol">:</a> <a id="6178" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="6197" href="literature.sequential-colimits-in-homotopy-type-theory.html#6171" class="Bound">l</a><a id="6198" class="Symbol">)</a> <a id="6200" class="Symbol">→</a>
    <a id="6206" href="synthetic-homotopy-theory.shifts-sequential-diagrams.html#24110" class="Function">compute-sequential-colimit-shift-sequential-diagram</a> <a id="6258" href="literature.sequential-colimits-in-homotopy-type-theory.html#6174" class="Bound">A</a> <a id="6260" class="Number">1</a>
</pre>
## 4 Fibered Sequences

The fourth section defines fibered sequences, which we call _dependent
sequential diagrams_ in the library. It introduces the "Σ of a sequence", which
we call the _total sequential diagram_, and asks the main question about the
interplay between Σ and taking the colimit.

The paper defines fibered sequences as a family over the total space
`B : Σ ℕ A → 𝒰`, but we use the curried definition `B : (n : ℕ) → A(n) → 𝒰`.

**Definition 4.1.** Fibered sequences. Equifibered sequences.

<pre class="Agda"><a id="6782" class="Keyword">open</a> <a id="6787" class="Keyword">import</a> <a id="6794" href="synthetic-homotopy-theory.dependent-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.dependent-sequential-diagrams</a> <a id="6850" class="Keyword">using</a>
  <a id="6858" class="Symbol">(</a> <a id="6860" href="synthetic-homotopy-theory.dependent-sequential-diagrams.html#1271" class="Function">dependent-sequential-diagram</a> <a id="6889" class="Comment">-- &quot;A sequence (B, b) fibered over (A, a)&quot;</a>
  <a id="6934" class="Symbol">)</a>
</pre>
**Lemma 4.2.** The type of families over a colimit is equivalent to the type of
equifibered sequences.

This property is also called the _descent property of sequential colimits_,
because it characterizes families over a sequential colimit.

<pre class="Agda"><a id="7191" class="Comment">-- TODO</a>
</pre>
**Definition 4.3.** Σ of a fibered sequence.

<pre class="Agda"><a id="7258" class="Keyword">open</a> <a id="7263" class="Keyword">import</a> <a id="7270" href="synthetic-homotopy-theory.total-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.total-sequential-diagrams</a> <a id="7322" class="Keyword">using</a>
  <a id="7330" class="Symbol">(</a> <a id="7332" href="synthetic-homotopy-theory.total-sequential-diagrams.html#2154" class="Function">total-sequential-diagram</a> <a id="7357" class="Comment">-- &quot;Σ (A, a) (B, b)&quot;</a>
  <a id="7380" class="Symbol">;</a> <a id="7382" href="synthetic-homotopy-theory.total-sequential-diagrams.html#2533" class="Function">pr1-total-sequential-diagram</a> <a id="7411" class="Comment">-- &quot;the canonical projection&quot;</a>
  <a id="7443" class="Symbol">)</a>
</pre>
**Construction.** The equifibered family associated to a fibered sequence.

<pre class="Agda"><a id="7534" class="Comment">-- TODO</a>
</pre>
## 5 Colimits and Sums

**Theorem 5.1.** Interaction between `colim` and `Σ`.

<pre class="Agda"><a id="7634" class="Comment">-- TODO</a>
</pre>
## 6 Induction on the Sum of Sequential Colimits

<pre class="Agda"><a id="7705" class="Comment">-- TODO</a>
</pre>
## 7 Applications of the Main Theorem

**Lemma 7.1.** TODO description.

<pre class="Agda"><a id="7799" class="Comment">-- TODO</a>
</pre>
**Lemma 7.2.** Colimit of the terminal sequential diagram is contractible.

<pre class="Agda"><a id="7896" class="Comment">-- TODO</a>
</pre>
**Lemma 7.3.** Encode-decode.

This principle is called the _Fundamental theorem of identity types_ in the
library.

<pre class="Agda"><a id="8034" class="Keyword">open</a> <a id="8039" class="Keyword">import</a> <a id="8046" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a> <a id="8095" class="Keyword">using</a>
  <a id="8103" class="Symbol">(</a> <a id="8105" href="foundation.fundamental-theorem-of-identity-types.html#2039" class="Function">fundamental-theorem-id</a><a id="8127" class="Symbol">)</a>
</pre>
**Lemma 7.4.** Characterization of path spaces of images of the canonical maps
into the sequential colimit.

<pre class="Agda"><a id="8251" class="Comment">-- TODO</a>
</pre>
**Corollary 7.5.** The loop space of a sequential colimit is the sequential
colimit of loop spaces.

<pre class="Agda"><a id="8373" class="Comment">-- TODO</a>
</pre>
**Corollary 7.6.** For a morphism of sequential diagrams, the fibers of the
induced map between sequential colimits are characterized as sequential colimits
of the fibers.

<pre class="Agda"><a id="8567" class="Comment">-- TODO</a>
</pre>
**Corollary 7.7.1.** If each type in a sequential diagram is `k`-truncated, then
the colimit is `k`-truncated.

<pre class="Agda"><a id="8700" class="Comment">-- TODO</a>
</pre>
**Corollary 7.7.2.** The `k`-truncation of a sequential colimit is the
sequential colimit of `k`-truncations.

<pre class="Agda"><a id="8832" class="Comment">-- TODO</a>
</pre>
**Corollary 7.7.3.** If each type in a sequential diagram is `k`-connected, then
the colimit is `k`-connected.

<pre class="Agda"><a id="8965" class="Comment">-- TODO</a>
</pre>
**Corollary 7.7.4.** If each component of a morphism between sequential diagrams
is `k`-truncated/`k`-connected, then the induced map of sequential colimits is
`k`-truncated/`k`-connected.

<pre class="Agda"><a id="9176" class="Comment">-- TODO</a>
</pre>
**Corollary 7.7.5.** If each map in a sequential diagram is
`k`-truncated/`k`-connected, then the first injection into the colimit is
`k`-truncated/`k`-connected.

<pre class="Agda"><a id="9361" class="Comment">-- TODO</a>
</pre>