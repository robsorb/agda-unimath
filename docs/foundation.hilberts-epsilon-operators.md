# Hilbert's ε-operators

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="foundation.hilberts-epsilon-operators.html" class="Module">foundation.hilberts-epsilon-operators</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="327" class="Keyword">open</a> <a id="332" class="Keyword">import</a> <a id="339" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
</pre>
</details>

## Idea

{{#concept "Hilbert's ε-operator" Disambiguation="on types" Agda=ε-operator-Hilbert}}
on a type `A` is a map

```text
  ε : ║A║₋₁ → A
```

Some authors also refer to this as _split support_ {{#cite KECA17}}. Contrary to
Hilbert, we will not assume that such an operator exists for each type `A`.

## Definition

<pre class="Agda"><a id="ε-operator-Hilbert"></a><a id="716" href="foundation.hilberts-epsilon-operators.html#716" class="Function">ε-operator-Hilbert</a> <a id="735" class="Symbol">:</a> <a id="737" class="Symbol">{</a><a id="738" href="foundation.hilberts-epsilon-operators.html#738" class="Bound">l</a> <a id="740" class="Symbol">:</a> <a id="742" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="747" class="Symbol">}</a> <a id="749" class="Symbol">→</a> <a id="751" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="754" href="foundation.hilberts-epsilon-operators.html#738" class="Bound">l</a> <a id="756" class="Symbol">→</a> <a id="758" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="761" href="foundation.hilberts-epsilon-operators.html#738" class="Bound">l</a>
<a id="763" href="foundation.hilberts-epsilon-operators.html#716" class="Function">ε-operator-Hilbert</a> <a id="782" href="foundation.hilberts-epsilon-operators.html#782" class="Bound">A</a> <a id="784" class="Symbol">=</a> <a id="786" href="foundation.propositional-truncations.html#1578" class="Function">type-trunc-Prop</a> <a id="802" href="foundation.hilberts-epsilon-operators.html#782" class="Bound">A</a> <a id="804" class="Symbol">→</a> <a id="806" href="foundation.hilberts-epsilon-operators.html#782" class="Bound">A</a>
</pre>
## Properties

### The existence of Hilbert's `ε`-operators is invariant under equivalences

<pre class="Agda"><a id="ε-operator-equiv"></a><a id="914" href="foundation.hilberts-epsilon-operators.html#914" class="Function">ε-operator-equiv</a> <a id="931" class="Symbol">:</a>
  <a id="935" class="Symbol">{</a><a id="936" href="foundation.hilberts-epsilon-operators.html#936" class="Bound">l1</a> <a id="939" href="foundation.hilberts-epsilon-operators.html#939" class="Bound">l2</a> <a id="942" class="Symbol">:</a> <a id="944" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="949" class="Symbol">}</a> <a id="951" class="Symbol">{</a><a id="952" href="foundation.hilberts-epsilon-operators.html#952" class="Bound">X</a> <a id="954" class="Symbol">:</a> <a id="956" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="959" href="foundation.hilberts-epsilon-operators.html#936" class="Bound">l1</a><a id="961" class="Symbol">}</a> <a id="963" class="Symbol">{</a><a id="964" href="foundation.hilberts-epsilon-operators.html#964" class="Bound">Y</a> <a id="966" class="Symbol">:</a> <a id="968" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="971" href="foundation.hilberts-epsilon-operators.html#939" class="Bound">l2</a><a id="973" class="Symbol">}</a> <a id="975" class="Symbol">(</a><a id="976" href="foundation.hilberts-epsilon-operators.html#976" class="Bound">e</a> <a id="978" class="Symbol">:</a> <a id="980" href="foundation.hilberts-epsilon-operators.html#952" class="Bound">X</a> <a id="982" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="984" href="foundation.hilberts-epsilon-operators.html#964" class="Bound">Y</a><a id="985" class="Symbol">)</a> <a id="987" class="Symbol">→</a>
  <a id="991" href="foundation.hilberts-epsilon-operators.html#716" class="Function">ε-operator-Hilbert</a> <a id="1010" href="foundation.hilberts-epsilon-operators.html#952" class="Bound">X</a> <a id="1012" class="Symbol">→</a> <a id="1014" href="foundation.hilberts-epsilon-operators.html#716" class="Function">ε-operator-Hilbert</a> <a id="1033" href="foundation.hilberts-epsilon-operators.html#964" class="Bound">Y</a>
<a id="1035" href="foundation.hilberts-epsilon-operators.html#914" class="Function">ε-operator-equiv</a> <a id="1052" href="foundation.hilberts-epsilon-operators.html#1052" class="Bound">e</a> <a id="1054" href="foundation.hilberts-epsilon-operators.html#1054" class="Bound">f</a> <a id="1056" class="Symbol">=</a>
  <a id="1060" class="Symbol">(</a><a id="1061" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="1071" href="foundation.hilberts-epsilon-operators.html#1052" class="Bound">e</a> <a id="1073" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1075" href="foundation.hilberts-epsilon-operators.html#1054" class="Bound">f</a><a id="1076" class="Symbol">)</a> <a id="1078" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1080" class="Symbol">(</a><a id="1081" href="foundation.functoriality-propositional-truncation.html#1256" class="Function">map-trunc-Prop</a> <a id="1096" class="Symbol">(</a><a id="1097" href="foundation-core.equivalences.html#8070" class="Function">map-inv-equiv</a> <a id="1111" href="foundation.hilberts-epsilon-operators.html#1052" class="Bound">e</a><a id="1112" class="Symbol">))</a>

<a id="ε-operator-equiv&#39;"></a><a id="1116" href="foundation.hilberts-epsilon-operators.html#1116" class="Function">ε-operator-equiv&#39;</a> <a id="1134" class="Symbol">:</a>
  <a id="1138" class="Symbol">{</a><a id="1139" href="foundation.hilberts-epsilon-operators.html#1139" class="Bound">l1</a> <a id="1142" href="foundation.hilberts-epsilon-operators.html#1142" class="Bound">l2</a> <a id="1145" class="Symbol">:</a> <a id="1147" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1152" class="Symbol">}</a> <a id="1154" class="Symbol">{</a><a id="1155" href="foundation.hilberts-epsilon-operators.html#1155" class="Bound">X</a> <a id="1157" class="Symbol">:</a> <a id="1159" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1162" href="foundation.hilberts-epsilon-operators.html#1139" class="Bound">l1</a><a id="1164" class="Symbol">}</a> <a id="1166" class="Symbol">{</a><a id="1167" href="foundation.hilberts-epsilon-operators.html#1167" class="Bound">Y</a> <a id="1169" class="Symbol">:</a> <a id="1171" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1174" href="foundation.hilberts-epsilon-operators.html#1142" class="Bound">l2</a><a id="1176" class="Symbol">}</a> <a id="1178" class="Symbol">(</a><a id="1179" href="foundation.hilberts-epsilon-operators.html#1179" class="Bound">e</a> <a id="1181" class="Symbol">:</a> <a id="1183" href="foundation.hilberts-epsilon-operators.html#1155" class="Bound">X</a> <a id="1185" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1187" href="foundation.hilberts-epsilon-operators.html#1167" class="Bound">Y</a><a id="1188" class="Symbol">)</a> <a id="1190" class="Symbol">→</a>
  <a id="1194" href="foundation.hilberts-epsilon-operators.html#716" class="Function">ε-operator-Hilbert</a> <a id="1213" href="foundation.hilberts-epsilon-operators.html#1167" class="Bound">Y</a> <a id="1215" class="Symbol">→</a> <a id="1217" href="foundation.hilberts-epsilon-operators.html#716" class="Function">ε-operator-Hilbert</a> <a id="1236" href="foundation.hilberts-epsilon-operators.html#1155" class="Bound">X</a>
<a id="1238" href="foundation.hilberts-epsilon-operators.html#1116" class="Function">ε-operator-equiv&#39;</a> <a id="1256" href="foundation.hilberts-epsilon-operators.html#1256" class="Bound">e</a> <a id="1258" href="foundation.hilberts-epsilon-operators.html#1258" class="Bound">f</a> <a id="1260" class="Symbol">=</a>
  <a id="1264" class="Symbol">(</a><a id="1265" href="foundation-core.equivalences.html#8070" class="Function">map-inv-equiv</a> <a id="1279" href="foundation.hilberts-epsilon-operators.html#1256" class="Bound">e</a> <a id="1281" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1283" href="foundation.hilberts-epsilon-operators.html#1258" class="Bound">f</a><a id="1284" class="Symbol">)</a> <a id="1286" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="1288" class="Symbol">(</a><a id="1289" href="foundation.functoriality-propositional-truncation.html#1256" class="Function">map-trunc-Prop</a> <a id="1304" class="Symbol">(</a><a id="1305" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="1315" href="foundation.hilberts-epsilon-operators.html#1256" class="Bound">e</a><a id="1316" class="Symbol">))</a>
</pre>
## References

{{#bibliography}}

## See also

- [Global choice](foundation.global-choice.md)

## External links

- [Epsilon calculus](https://en.wikipedia.org/wiki/Epsilon_calculus) at
  Wikipedia
