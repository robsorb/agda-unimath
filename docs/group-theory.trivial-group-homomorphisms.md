# Trivial group homomorphisms

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="group-theory.trivial-group-homomorphisms.html" class="Module">group-theory.trivial-group-homomorphisms</a> <a id="88" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="144" class="Keyword">open</a> <a id="149" class="Keyword">import</a> <a id="156" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="188" class="Keyword">open</a> <a id="193" class="Keyword">import</a> <a id="200" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="362" class="Keyword">open</a> <a id="367" class="Keyword">import</a> <a id="374" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
</pre>
</details>

## Idea

A **trivial group homomorphism** from `G` to `H` is a
[group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` such that
`f x ＝ 1` for every `x : G`.

## Definitions

### The predicate of being a trivial group homomorphism

<pre class="Agda"><a id="680" class="Keyword">module</a> <a id="687" href="group-theory.trivial-group-homomorphisms.html#687" class="Module">_</a>
  <a id="691" class="Symbol">{</a><a id="692" href="group-theory.trivial-group-homomorphisms.html#692" class="Bound">l1</a> <a id="695" href="group-theory.trivial-group-homomorphisms.html#695" class="Bound">l2</a> <a id="698" class="Symbol">:</a> <a id="700" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="705" class="Symbol">}</a> <a id="707" class="Symbol">(</a><a id="708" href="group-theory.trivial-group-homomorphisms.html#708" class="Bound">G</a> <a id="710" class="Symbol">:</a> <a id="712" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="718" href="group-theory.trivial-group-homomorphisms.html#692" class="Bound">l1</a><a id="720" class="Symbol">)</a> <a id="722" class="Symbol">(</a><a id="723" href="group-theory.trivial-group-homomorphisms.html#723" class="Bound">H</a> <a id="725" class="Symbol">:</a> <a id="727" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="733" href="group-theory.trivial-group-homomorphisms.html#695" class="Bound">l2</a><a id="735" class="Symbol">)</a> <a id="737" class="Symbol">(</a><a id="738" href="group-theory.trivial-group-homomorphisms.html#738" class="Bound">f</a> <a id="740" class="Symbol">:</a> <a id="742" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="752" href="group-theory.trivial-group-homomorphisms.html#708" class="Bound">G</a> <a id="754" href="group-theory.trivial-group-homomorphisms.html#723" class="Bound">H</a><a id="755" class="Symbol">)</a>
  <a id="759" class="Keyword">where</a>

  <a id="768" href="group-theory.trivial-group-homomorphisms.html#768" class="Function">is-trivial-prop-hom-Group</a> <a id="794" class="Symbol">:</a> <a id="796" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="801" class="Symbol">(</a><a id="802" href="group-theory.trivial-group-homomorphisms.html#692" class="Bound">l1</a> <a id="805" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="807" href="group-theory.trivial-group-homomorphisms.html#695" class="Bound">l2</a><a id="809" class="Symbol">)</a>
  <a id="813" href="group-theory.trivial-group-homomorphisms.html#768" class="Function">is-trivial-prop-hom-Group</a> <a id="839" class="Symbol">=</a>
    <a id="845" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="858" class="Symbol">(</a> <a id="860" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="871" href="group-theory.trivial-group-homomorphisms.html#708" class="Bound">G</a><a id="872" class="Symbol">)</a>
      <a id="880" class="Symbol">(</a> <a id="882" class="Symbol">λ</a> <a id="884" href="group-theory.trivial-group-homomorphisms.html#884" class="Bound">x</a> <a id="886" class="Symbol">→</a> <a id="888" href="foundation-core.sets.html#1141" class="Function">Id-Prop</a> <a id="896" class="Symbol">(</a><a id="897" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="907" href="group-theory.trivial-group-homomorphisms.html#723" class="Bound">H</a><a id="908" class="Symbol">)</a> <a id="910" class="Symbol">(</a><a id="911" href="group-theory.homomorphisms-groups.html#1812" class="Function">map-hom-Group</a> <a id="925" href="group-theory.trivial-group-homomorphisms.html#708" class="Bound">G</a> <a id="927" href="group-theory.trivial-group-homomorphisms.html#723" class="Bound">H</a> <a id="929" href="group-theory.trivial-group-homomorphisms.html#738" class="Bound">f</a> <a id="931" href="group-theory.trivial-group-homomorphisms.html#884" class="Bound">x</a><a id="932" class="Symbol">)</a> <a id="934" class="Symbol">(</a><a id="935" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="946" href="group-theory.trivial-group-homomorphisms.html#723" class="Bound">H</a><a id="947" class="Symbol">))</a>

  <a id="953" href="group-theory.trivial-group-homomorphisms.html#953" class="Function">is-trivial-hom-Group</a> <a id="974" class="Symbol">:</a> <a id="976" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="979" class="Symbol">(</a><a id="980" href="group-theory.trivial-group-homomorphisms.html#692" class="Bound">l1</a> <a id="983" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="985" href="group-theory.trivial-group-homomorphisms.html#695" class="Bound">l2</a><a id="987" class="Symbol">)</a>
  <a id="991" href="group-theory.trivial-group-homomorphisms.html#953" class="Function">is-trivial-hom-Group</a> <a id="1012" class="Symbol">=</a> <a id="1014" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1024" href="group-theory.trivial-group-homomorphisms.html#768" class="Function">is-trivial-prop-hom-Group</a>

  <a id="1053" href="group-theory.trivial-group-homomorphisms.html#1053" class="Function">is-prop-is-trivial-hom-Group</a> <a id="1082" class="Symbol">:</a> <a id="1084" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1092" href="group-theory.trivial-group-homomorphisms.html#953" class="Function">is-trivial-hom-Group</a>
  <a id="1115" href="group-theory.trivial-group-homomorphisms.html#1053" class="Function">is-prop-is-trivial-hom-Group</a> <a id="1144" class="Symbol">=</a> <a id="1146" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1164" href="group-theory.trivial-group-homomorphisms.html#768" class="Function">is-trivial-prop-hom-Group</a>
</pre>
### The trivial group homomorphism

<pre class="Agda"><a id="1239" class="Keyword">module</a> <a id="1246" href="group-theory.trivial-group-homomorphisms.html#1246" class="Module">_</a>
  <a id="1250" class="Symbol">{</a><a id="1251" href="group-theory.trivial-group-homomorphisms.html#1251" class="Bound">l1</a> <a id="1254" href="group-theory.trivial-group-homomorphisms.html#1254" class="Bound">l2</a> <a id="1257" class="Symbol">:</a> <a id="1259" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1264" class="Symbol">}</a> <a id="1266" class="Symbol">(</a><a id="1267" href="group-theory.trivial-group-homomorphisms.html#1267" class="Bound">G</a> <a id="1269" class="Symbol">:</a> <a id="1271" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1277" href="group-theory.trivial-group-homomorphisms.html#1251" class="Bound">l1</a><a id="1279" class="Symbol">)</a> <a id="1281" class="Symbol">(</a><a id="1282" href="group-theory.trivial-group-homomorphisms.html#1282" class="Bound">H</a> <a id="1284" class="Symbol">:</a> <a id="1286" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="1292" href="group-theory.trivial-group-homomorphisms.html#1254" class="Bound">l2</a><a id="1294" class="Symbol">)</a>
  <a id="1298" class="Keyword">where</a>

  <a id="1307" href="group-theory.trivial-group-homomorphisms.html#1307" class="Function">trivial-hom-Group</a> <a id="1325" class="Symbol">:</a> <a id="1327" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="1337" href="group-theory.trivial-group-homomorphisms.html#1267" class="Bound">G</a> <a id="1339" href="group-theory.trivial-group-homomorphisms.html#1282" class="Bound">H</a>
  <a id="1343" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1347" href="group-theory.trivial-group-homomorphisms.html#1307" class="Function">trivial-hom-Group</a> <a id="1365" href="group-theory.trivial-group-homomorphisms.html#1365" class="Bound">x</a> <a id="1367" class="Symbol">=</a> <a id="1369" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="1380" href="group-theory.trivial-group-homomorphisms.html#1282" class="Bound">H</a>
  <a id="1384" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1388" href="group-theory.trivial-group-homomorphisms.html#1307" class="Function">trivial-hom-Group</a> <a id="1406" class="Symbol">=</a> <a id="1408" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="1412" class="Symbol">(</a><a id="1413" href="group-theory.groups.html#4398" class="Function">left-unit-law-mul-Group</a> <a id="1437" href="group-theory.trivial-group-homomorphisms.html#1282" class="Bound">H</a> <a id="1439" class="Symbol">(</a><a id="1440" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="1451" href="group-theory.trivial-group-homomorphisms.html#1282" class="Bound">H</a><a id="1452" class="Symbol">))</a>
</pre>