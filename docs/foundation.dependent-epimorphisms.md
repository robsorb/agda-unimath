# Dependent epimorphisms

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="foundation.dependent-epimorphisms.html" class="Module">foundation.dependent-epimorphisms</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="foundation.epimorphisms.html" class="Module">foundation.epimorphisms</a>
<a id="168" class="Keyword">open</a> <a id="173" class="Keyword">import</a> <a id="180" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="208" class="Keyword">open</a> <a id="213" class="Keyword">import</a> <a id="220" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation-core.precomposition-dependent-functions.html" class="Module">foundation-core.precomposition-dependent-functions</a>
</pre>
</details>

## Idea

A **dependent epimorphism** is a map `f : A → B` such that the
[precomposition function](foundation.precomposition-dependent-functions.md)

```text
  - ∘ f : ((b : B) → C b) → ((a : A) → C (f a))
```

is an [embedding](foundation-core.embeddings.md) for every type family `C` over
`B`.

Clearly, every dependent epimorphism is an
[epimorphism](foundation.epimorphisms.md). The converse is also true, i.e.,
every epimorphism is a dependent epimorphism. Therefore it follows that a map
`f : A → B` is [acyclic](synthetic-homotopy-theory.acyclic-maps.md) if and only
if it is an epimorphism, if and only if it is a dependent epimorphism.

## Definitions

### The predicate of being a dependent epimorphism

<pre class="Agda"><a id="1048" class="Keyword">module</a> <a id="1055" href="foundation.dependent-epimorphisms.html#1055" class="Module">_</a>
  <a id="1059" class="Symbol">{</a><a id="1060" href="foundation.dependent-epimorphisms.html#1060" class="Bound">l1</a> <a id="1063" href="foundation.dependent-epimorphisms.html#1063" class="Bound">l2</a> <a id="1066" class="Symbol">:</a> <a id="1068" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1073" class="Symbol">}</a> <a id="1075" class="Symbol">{</a><a id="1076" href="foundation.dependent-epimorphisms.html#1076" class="Bound">A</a> <a id="1078" class="Symbol">:</a> <a id="1080" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1083" href="foundation.dependent-epimorphisms.html#1060" class="Bound">l1</a><a id="1085" class="Symbol">}</a> <a id="1087" class="Symbol">{</a><a id="1088" href="foundation.dependent-epimorphisms.html#1088" class="Bound">B</a> <a id="1090" class="Symbol">:</a> <a id="1092" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1095" href="foundation.dependent-epimorphisms.html#1063" class="Bound">l2</a><a id="1097" class="Symbol">}</a>
  <a id="1101" class="Keyword">where</a>

  <a id="1110" href="foundation.dependent-epimorphisms.html#1110" class="Function">is-dependent-epimorphism</a> <a id="1135" class="Symbol">:</a> <a id="1137" class="Symbol">(</a><a id="1138" href="foundation.dependent-epimorphisms.html#1076" class="Bound">A</a> <a id="1140" class="Symbol">→</a> <a id="1142" href="foundation.dependent-epimorphisms.html#1088" class="Bound">B</a><a id="1143" class="Symbol">)</a> <a id="1145" class="Symbol">→</a> <a id="1147" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="1153" href="foundation.dependent-epimorphisms.html#1110" class="Function">is-dependent-epimorphism</a> <a id="1178" href="foundation.dependent-epimorphisms.html#1178" class="Bound">f</a> <a id="1180" class="Symbol">=</a>
    <a id="1186" class="Symbol">{</a><a id="1187" href="foundation.dependent-epimorphisms.html#1187" class="Bound">l</a> <a id="1189" class="Symbol">:</a> <a id="1191" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1196" class="Symbol">}</a> <a id="1198" class="Symbol">(</a><a id="1199" href="foundation.dependent-epimorphisms.html#1199" class="Bound">C</a> <a id="1201" class="Symbol">:</a> <a id="1203" href="foundation.dependent-epimorphisms.html#1088" class="Bound">B</a> <a id="1205" class="Symbol">→</a> <a id="1207" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1210" href="foundation.dependent-epimorphisms.html#1187" class="Bound">l</a><a id="1211" class="Symbol">)</a> <a id="1213" class="Symbol">→</a> <a id="1215" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="1222" class="Symbol">(</a><a id="1223" href="foundation-core.precomposition-dependent-functions.html#744" class="Function">precomp-Π</a> <a id="1233" href="foundation.dependent-epimorphisms.html#1178" class="Bound">f</a> <a id="1235" href="foundation.dependent-epimorphisms.html#1199" class="Bound">C</a><a id="1236" class="Symbol">)</a>
</pre>
## Properties

### Every dependent epimorphism is an epimorphism

<pre class="Agda"><a id="1317" class="Keyword">module</a> <a id="1324" href="foundation.dependent-epimorphisms.html#1324" class="Module">_</a>
  <a id="1328" class="Symbol">{</a><a id="1329" href="foundation.dependent-epimorphisms.html#1329" class="Bound">l1</a> <a id="1332" href="foundation.dependent-epimorphisms.html#1332" class="Bound">l2</a> <a id="1335" class="Symbol">:</a> <a id="1337" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1342" class="Symbol">}</a> <a id="1344" class="Symbol">{</a><a id="1345" href="foundation.dependent-epimorphisms.html#1345" class="Bound">A</a> <a id="1347" class="Symbol">:</a> <a id="1349" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1352" href="foundation.dependent-epimorphisms.html#1329" class="Bound">l1</a><a id="1354" class="Symbol">}</a> <a id="1356" class="Symbol">{</a><a id="1357" href="foundation.dependent-epimorphisms.html#1357" class="Bound">B</a> <a id="1359" class="Symbol">:</a> <a id="1361" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1364" href="foundation.dependent-epimorphisms.html#1332" class="Bound">l2</a><a id="1366" class="Symbol">}</a> <a id="1368" class="Symbol">(</a><a id="1369" href="foundation.dependent-epimorphisms.html#1369" class="Bound">f</a> <a id="1371" class="Symbol">:</a> <a id="1373" href="foundation.dependent-epimorphisms.html#1345" class="Bound">A</a> <a id="1375" class="Symbol">→</a> <a id="1377" href="foundation.dependent-epimorphisms.html#1357" class="Bound">B</a><a id="1378" class="Symbol">)</a>
  <a id="1382" class="Keyword">where</a>

  <a id="1391" href="foundation.dependent-epimorphisms.html#1391" class="Function">is-epimorphism-is-dependent-epimorphism</a> <a id="1431" class="Symbol">:</a>
    <a id="1437" href="foundation.dependent-epimorphisms.html#1110" class="Function">is-dependent-epimorphism</a> <a id="1462" href="foundation.dependent-epimorphisms.html#1369" class="Bound">f</a> <a id="1464" class="Symbol">→</a> <a id="1466" href="foundation.epimorphisms.html#1382" class="Function">is-epimorphism</a> <a id="1481" href="foundation.dependent-epimorphisms.html#1369" class="Bound">f</a>
  <a id="1485" href="foundation.dependent-epimorphisms.html#1391" class="Function">is-epimorphism-is-dependent-epimorphism</a> <a id="1525" href="foundation.dependent-epimorphisms.html#1525" class="Bound">e</a> <a id="1527" href="foundation.dependent-epimorphisms.html#1527" class="Bound">X</a> <a id="1529" class="Symbol">=</a> <a id="1531" href="foundation.dependent-epimorphisms.html#1525" class="Bound">e</a> <a id="1533" class="Symbol">(λ</a> <a id="1536" href="foundation.dependent-epimorphisms.html#1536" class="Bound">_</a> <a id="1538" class="Symbol">→</a> <a id="1540" href="foundation.dependent-epimorphisms.html#1527" class="Bound">X</a><a id="1541" class="Symbol">)</a>
</pre>
The converse of the above, that every epimorphism is a dependent epimorphism,
can be found in the file on
[acyclic maps](synthetic-homotopy-theory.acyclic-maps.md).

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
