# Commuting squares of group homomorphisms

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="group-theory.commuting-squares-of-group-homomorphisms.html" class="Module">group-theory.commuting-squares-of-group-homomorphisms</a> <a id="114" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="259" class="Keyword">open</a> <a id="264" class="Keyword">import</a> <a id="271" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="291" class="Keyword">open</a> <a id="296" class="Keyword">import</a> <a id="303" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
</pre>
</details>

## Idea

A square of [group homomorphisms](group-theory.homomorphisms-groups.md)

```text
        f
    G -----> H
    |        |
  g |        | h
    ∨        ∨
    K -----> L
        k
```

is said to **commute** if the underlying square of maps
[commutes](foundation.commuting-squares-of-maps.md), i.e., if `k ∘ g ~ h ∘ f`.

## Definitions

### Commuting squares of group homomorphisms

<pre class="Agda"><a id="752" class="Keyword">module</a> <a id="759" href="group-theory.commuting-squares-of-group-homomorphisms.html#759" class="Module">_</a>
  <a id="763" class="Symbol">{</a><a id="764" href="group-theory.commuting-squares-of-group-homomorphisms.html#764" class="Bound">l1</a> <a id="767" href="group-theory.commuting-squares-of-group-homomorphisms.html#767" class="Bound">l2</a> <a id="770" href="group-theory.commuting-squares-of-group-homomorphisms.html#770" class="Bound">l3</a> <a id="773" href="group-theory.commuting-squares-of-group-homomorphisms.html#773" class="Bound">l4</a> <a id="776" class="Symbol">:</a> <a id="778" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="783" class="Symbol">}</a>
  <a id="787" class="Symbol">(</a><a id="788" href="group-theory.commuting-squares-of-group-homomorphisms.html#788" class="Bound">G</a> <a id="790" class="Symbol">:</a> <a id="792" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="798" href="group-theory.commuting-squares-of-group-homomorphisms.html#764" class="Bound">l1</a><a id="800" class="Symbol">)</a> <a id="802" class="Symbol">(</a><a id="803" href="group-theory.commuting-squares-of-group-homomorphisms.html#803" class="Bound">H</a> <a id="805" class="Symbol">:</a> <a id="807" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="813" href="group-theory.commuting-squares-of-group-homomorphisms.html#767" class="Bound">l2</a><a id="815" class="Symbol">)</a> <a id="817" class="Symbol">(</a><a id="818" href="group-theory.commuting-squares-of-group-homomorphisms.html#818" class="Bound">K</a> <a id="820" class="Symbol">:</a> <a id="822" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="828" href="group-theory.commuting-squares-of-group-homomorphisms.html#770" class="Bound">l3</a><a id="830" class="Symbol">)</a> <a id="832" class="Symbol">(</a><a id="833" href="group-theory.commuting-squares-of-group-homomorphisms.html#833" class="Bound">L</a> <a id="835" class="Symbol">:</a> <a id="837" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="843" href="group-theory.commuting-squares-of-group-homomorphisms.html#773" class="Bound">l4</a><a id="845" class="Symbol">)</a>
  <a id="849" class="Symbol">(</a><a id="850" href="group-theory.commuting-squares-of-group-homomorphisms.html#850" class="Bound">f</a> <a id="852" class="Symbol">:</a> <a id="854" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="864" href="group-theory.commuting-squares-of-group-homomorphisms.html#788" class="Bound">G</a> <a id="866" href="group-theory.commuting-squares-of-group-homomorphisms.html#803" class="Bound">H</a><a id="867" class="Symbol">)</a> <a id="869" class="Symbol">(</a><a id="870" href="group-theory.commuting-squares-of-group-homomorphisms.html#870" class="Bound">g</a> <a id="872" class="Symbol">:</a> <a id="874" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="884" href="group-theory.commuting-squares-of-group-homomorphisms.html#788" class="Bound">G</a> <a id="886" href="group-theory.commuting-squares-of-group-homomorphisms.html#818" class="Bound">K</a><a id="887" class="Symbol">)</a>
  <a id="891" class="Symbol">(</a><a id="892" href="group-theory.commuting-squares-of-group-homomorphisms.html#892" class="Bound">h</a> <a id="894" class="Symbol">:</a> <a id="896" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="906" href="group-theory.commuting-squares-of-group-homomorphisms.html#803" class="Bound">H</a> <a id="908" href="group-theory.commuting-squares-of-group-homomorphisms.html#833" class="Bound">L</a><a id="909" class="Symbol">)</a> <a id="911" class="Symbol">(</a><a id="912" href="group-theory.commuting-squares-of-group-homomorphisms.html#912" class="Bound">k</a> <a id="914" class="Symbol">:</a> <a id="916" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="926" href="group-theory.commuting-squares-of-group-homomorphisms.html#818" class="Bound">K</a> <a id="928" href="group-theory.commuting-squares-of-group-homomorphisms.html#833" class="Bound">L</a><a id="929" class="Symbol">)</a>
  <a id="933" class="Keyword">where</a>

  <a id="942" href="group-theory.commuting-squares-of-group-homomorphisms.html#942" class="Function">coherence-square-hom-Group</a> <a id="969" class="Symbol">:</a> <a id="971" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="974" class="Symbol">(</a><a id="975" href="group-theory.commuting-squares-of-group-homomorphisms.html#764" class="Bound">l1</a> <a id="978" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="980" href="group-theory.commuting-squares-of-group-homomorphisms.html#773" class="Bound">l4</a><a id="982" class="Symbol">)</a>
  <a id="986" href="group-theory.commuting-squares-of-group-homomorphisms.html#942" class="Function">coherence-square-hom-Group</a> <a id="1013" class="Symbol">=</a>
    <a id="1019" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="1047" class="Symbol">(</a> <a id="1049" href="group-theory.homomorphisms-groups.html#1812" class="Function">map-hom-Group</a> <a id="1063" href="group-theory.commuting-squares-of-group-homomorphisms.html#788" class="Bound">G</a> <a id="1065" href="group-theory.commuting-squares-of-group-homomorphisms.html#803" class="Bound">H</a> <a id="1067" href="group-theory.commuting-squares-of-group-homomorphisms.html#850" class="Bound">f</a><a id="1068" class="Symbol">)</a>
      <a id="1076" class="Symbol">(</a> <a id="1078" href="group-theory.homomorphisms-groups.html#1812" class="Function">map-hom-Group</a> <a id="1092" href="group-theory.commuting-squares-of-group-homomorphisms.html#788" class="Bound">G</a> <a id="1094" href="group-theory.commuting-squares-of-group-homomorphisms.html#818" class="Bound">K</a> <a id="1096" href="group-theory.commuting-squares-of-group-homomorphisms.html#870" class="Bound">g</a><a id="1097" class="Symbol">)</a>
      <a id="1105" class="Symbol">(</a> <a id="1107" href="group-theory.homomorphisms-groups.html#1812" class="Function">map-hom-Group</a> <a id="1121" href="group-theory.commuting-squares-of-group-homomorphisms.html#803" class="Bound">H</a> <a id="1123" href="group-theory.commuting-squares-of-group-homomorphisms.html#833" class="Bound">L</a> <a id="1125" href="group-theory.commuting-squares-of-group-homomorphisms.html#892" class="Bound">h</a><a id="1126" class="Symbol">)</a>
      <a id="1134" class="Symbol">(</a> <a id="1136" href="group-theory.homomorphisms-groups.html#1812" class="Function">map-hom-Group</a> <a id="1150" href="group-theory.commuting-squares-of-group-homomorphisms.html#818" class="Bound">K</a> <a id="1152" href="group-theory.commuting-squares-of-group-homomorphisms.html#833" class="Bound">L</a> <a id="1154" href="group-theory.commuting-squares-of-group-homomorphisms.html#912" class="Bound">k</a><a id="1155" class="Symbol">)</a>
</pre>