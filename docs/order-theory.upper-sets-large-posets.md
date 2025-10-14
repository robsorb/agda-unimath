# Upper sets of large posets

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="order-theory.upper-sets-large-posets.html" class="Module">order-theory.upper-sets-large-posets</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="order-theory.large-posets.html" class="Module">order-theory.large-posets</a>
<a id="217" class="Keyword">open</a> <a id="222" class="Keyword">import</a> <a id="229" href="order-theory.large-subposets.html" class="Module">order-theory.large-subposets</a>
</pre>
</details>

## Idea

An **upper set** or **upwards closed set** in a
[large poset](order-theory.large-posets.md) is a
[large subposet](order-theory.large-subposets.md) that is upwards closed, i.e.,
that satisfies the condition that

```text
  ∀ (x y : P), (x ≤ y) → x ∈ S → y ∈ S.
```

## Definitions

### The predicate of being an upper set

<pre class="Agda"><a id="614" class="Keyword">module</a> <a id="621" href="order-theory.upper-sets-large-posets.html#621" class="Module">_</a>
  <a id="625" class="Symbol">{</a><a id="626" href="order-theory.upper-sets-large-posets.html#626" class="Bound">α</a> <a id="628" href="order-theory.upper-sets-large-posets.html#628" class="Bound">γ</a> <a id="630" class="Symbol">:</a> <a id="632" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="638" class="Symbol">→</a> <a id="640" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="645" class="Symbol">}</a> <a id="647" class="Symbol">{</a><a id="648" href="order-theory.upper-sets-large-posets.html#648" class="Bound">β</a> <a id="650" class="Symbol">:</a> <a id="652" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="658" class="Symbol">→</a> <a id="660" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="666" class="Symbol">→</a> <a id="668" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="673" class="Symbol">}</a>
  <a id="677" class="Symbol">(</a><a id="678" href="order-theory.upper-sets-large-posets.html#678" class="Bound">P</a> <a id="680" class="Symbol">:</a> <a id="682" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="694" href="order-theory.upper-sets-large-posets.html#626" class="Bound">α</a> <a id="696" href="order-theory.upper-sets-large-posets.html#648" class="Bound">β</a><a id="697" class="Symbol">)</a> <a id="699" class="Symbol">(</a><a id="700" href="order-theory.upper-sets-large-posets.html#700" class="Bound">S</a> <a id="702" class="Symbol">:</a> <a id="704" href="order-theory.large-subposets.html#1571" class="Record">Large-Subposet</a> <a id="719" href="order-theory.upper-sets-large-posets.html#628" class="Bound">γ</a> <a id="721" href="order-theory.upper-sets-large-posets.html#678" class="Bound">P</a><a id="722" class="Symbol">)</a>
  <a id="726" class="Keyword">where</a>

  <a id="735" href="order-theory.upper-sets-large-posets.html#735" class="Function">is-upper-set-Large-Subposet</a> <a id="763" class="Symbol">:</a> <a id="765" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="771" href="order-theory.upper-sets-large-posets.html#735" class="Function">is-upper-set-Large-Subposet</a> <a id="799" class="Symbol">=</a>
    <a id="805" class="Symbol">{</a><a id="806" href="order-theory.upper-sets-large-posets.html#806" class="Bound">l1</a> <a id="809" href="order-theory.upper-sets-large-posets.html#809" class="Bound">l2</a> <a id="812" class="Symbol">:</a> <a id="814" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="819" class="Symbol">}</a> <a id="821" class="Symbol">(</a><a id="822" href="order-theory.upper-sets-large-posets.html#822" class="Bound">x</a> <a id="824" class="Symbol">:</a> <a id="826" href="order-theory.large-posets.html#1534" class="Function">type-Large-Poset</a> <a id="843" href="order-theory.upper-sets-large-posets.html#678" class="Bound">P</a> <a id="845" href="order-theory.upper-sets-large-posets.html#806" class="Bound">l1</a><a id="847" class="Symbol">)</a> <a id="849" class="Symbol">(</a><a id="850" href="order-theory.upper-sets-large-posets.html#850" class="Bound">y</a> <a id="852" class="Symbol">:</a> <a id="854" href="order-theory.large-posets.html#1534" class="Function">type-Large-Poset</a> <a id="871" href="order-theory.upper-sets-large-posets.html#678" class="Bound">P</a> <a id="873" href="order-theory.upper-sets-large-posets.html#809" class="Bound">l2</a><a id="875" class="Symbol">)</a> <a id="877" class="Symbol">→</a>
    <a id="883" href="order-theory.large-posets.html#1798" class="Function">leq-Large-Poset</a> <a id="899" href="order-theory.upper-sets-large-posets.html#678" class="Bound">P</a> <a id="901" href="order-theory.upper-sets-large-posets.html#822" class="Bound">x</a> <a id="903" href="order-theory.upper-sets-large-posets.html#850" class="Bound">y</a> <a id="905" class="Symbol">→</a>
    <a id="911" href="order-theory.large-subposets.html#2251" class="Function">is-in-Large-Subposet</a> <a id="932" href="order-theory.upper-sets-large-posets.html#678" class="Bound">P</a> <a id="934" href="order-theory.upper-sets-large-posets.html#700" class="Bound">S</a> <a id="936" href="order-theory.upper-sets-large-posets.html#822" class="Bound">x</a> <a id="938" class="Symbol">→</a> <a id="940" href="order-theory.large-subposets.html#2251" class="Function">is-in-Large-Subposet</a> <a id="961" href="order-theory.upper-sets-large-posets.html#678" class="Bound">P</a> <a id="963" href="order-theory.upper-sets-large-posets.html#700" class="Bound">S</a> <a id="965" href="order-theory.upper-sets-large-posets.html#850" class="Bound">y</a>
</pre>
### Upper sets of a large poset

<pre class="Agda"><a id="1013" class="Keyword">module</a> <a id="1020" href="order-theory.upper-sets-large-posets.html#1020" class="Module">_</a>
  <a id="1024" class="Symbol">{</a><a id="1025" href="order-theory.upper-sets-large-posets.html#1025" class="Bound">α</a> <a id="1027" class="Symbol">:</a> <a id="1029" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1035" class="Symbol">→</a> <a id="1037" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1042" class="Symbol">}</a> <a id="1044" class="Symbol">{</a><a id="1045" href="order-theory.upper-sets-large-posets.html#1045" class="Bound">β</a> <a id="1047" class="Symbol">:</a> <a id="1049" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1055" class="Symbol">→</a> <a id="1057" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1063" class="Symbol">→</a> <a id="1065" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1070" class="Symbol">}</a> <a id="1072" class="Symbol">(</a><a id="1073" href="order-theory.upper-sets-large-posets.html#1073" class="Bound">γ</a> <a id="1075" class="Symbol">:</a> <a id="1077" href="Agda.Primitive.html#742" class="Postulate">Level</a> <a id="1083" class="Symbol">→</a> <a id="1085" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1090" class="Symbol">)</a>
  <a id="1094" class="Symbol">(</a><a id="1095" href="order-theory.upper-sets-large-posets.html#1095" class="Bound">P</a> <a id="1097" class="Symbol">:</a> <a id="1099" href="order-theory.large-posets.html#1060" class="Record">Large-Poset</a> <a id="1111" href="order-theory.upper-sets-large-posets.html#1025" class="Bound">α</a> <a id="1113" href="order-theory.upper-sets-large-posets.html#1045" class="Bound">β</a><a id="1114" class="Symbol">)</a>
  <a id="1118" class="Keyword">where</a>

  <a id="1127" class="Keyword">record</a>
    <a id="1138" href="order-theory.upper-sets-large-posets.html#1138" class="Record">upper-set-Large-Poset</a> <a id="1160" class="Symbol">:</a> <a id="1162" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
    <a id="1170" class="Keyword">where</a>
    <a id="1180" class="Keyword">field</a>
      <a id="1192" href="order-theory.upper-sets-large-posets.html#1192" class="Field">large-subposet-upper-set-Large-Poset</a> <a id="1229" class="Symbol">:</a>
        <a id="1239" href="order-theory.large-subposets.html#1571" class="Record">Large-Subposet</a> <a id="1254" href="order-theory.upper-sets-large-posets.html#1073" class="Bound">γ</a> <a id="1256" href="order-theory.upper-sets-large-posets.html#1095" class="Bound">P</a>
      <a id="1264" href="order-theory.upper-sets-large-posets.html#1264" class="Field">is-upper-set-upper-set-Large-Poset</a> <a id="1299" class="Symbol">:</a>
        <a id="1309" href="order-theory.upper-sets-large-posets.html#735" class="Function">is-upper-set-Large-Subposet</a> <a id="1337" href="order-theory.upper-sets-large-posets.html#1095" class="Bound">P</a> <a id="1339" href="order-theory.upper-sets-large-posets.html#1192" class="Field">large-subposet-upper-set-Large-Poset</a>

  <a id="1379" class="Keyword">open</a> <a id="1384" href="order-theory.upper-sets-large-posets.html#1138" class="Module">upper-set-Large-Poset</a> <a id="1406" class="Keyword">public</a>
</pre>
## See also

- [Lower sets](order-theory.lower-sets-large-posets.md)
- [Principal upper sets](order-theory.principal-upper-sets-large-posets.md)
