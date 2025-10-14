# Deloopable H-spaces

<pre class="Agda"><a id="32" class="Keyword">module</a> <a id="39" href="higher-group-theory.deloopable-h-spaces.html" class="Module">higher-group-theory.deloopable-h-spaces</a> <a id="79" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="135" class="Keyword">open</a> <a id="140" class="Keyword">import</a> <a id="147" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>

<a id="266" class="Keyword">open</a> <a id="271" class="Keyword">import</a> <a id="278" href="structured-types.equivalences-h-spaces.html" class="Module">structured-types.equivalences-h-spaces</a>
<a id="317" class="Keyword">open</a> <a id="322" class="Keyword">import</a> <a id="329" href="structured-types.h-spaces.html" class="Module">structured-types.h-spaces</a>
</pre>
</details>

## Idea

Consider an [H-space](structured-types.h-spaces.md) with underlying
[pointed type](structured-types.pointed-types.md) `(X , *)` and with
multiplication `μ` satisfying

```text
   left-unit-law : (x : X) → μ * x ＝ x
  right-unit-law : (x : X) → μ x * ＝ x
    coh-unit-law : left-unit-law * ＝ right-unit-law *.
```

A {{#concept "delooping" Disambiguation="H-space" Agda=delooping-H-Space}} of
the H-space `X` consists of an [∞-group](higher-group-theory.higher-groups.md)
`G` and an [equivalence of H-spaces](structured-types.equivalences-h-spaces.md)

```text
  X ≃ h-space-∞-Group G.
```

## Definitions

### Deloopings of H-spaces of a given universe level

<pre class="Agda"><a id="1049" class="Keyword">module</a> <a id="1056" href="higher-group-theory.deloopable-h-spaces.html#1056" class="Module">_</a>
  <a id="1060" class="Symbol">{</a><a id="1061" href="higher-group-theory.deloopable-h-spaces.html#1061" class="Bound">l1</a> <a id="1064" class="Symbol">:</a> <a id="1066" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1071" class="Symbol">}</a> <a id="1073" class="Symbol">(</a><a id="1074" href="higher-group-theory.deloopable-h-spaces.html#1074" class="Bound">l2</a> <a id="1077" class="Symbol">:</a> <a id="1079" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1084" class="Symbol">)</a> <a id="1086" class="Symbol">(</a><a id="1087" href="higher-group-theory.deloopable-h-spaces.html#1087" class="Bound">A</a> <a id="1089" class="Symbol">:</a> <a id="1091" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="1099" href="higher-group-theory.deloopable-h-spaces.html#1061" class="Bound">l1</a><a id="1101" class="Symbol">)</a>
  <a id="1105" class="Keyword">where</a>

  <a id="1114" href="higher-group-theory.deloopable-h-spaces.html#1114" class="Function">delooping-H-Space-Level</a> <a id="1138" class="Symbol">:</a> <a id="1140" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1143" class="Symbol">(</a><a id="1144" href="higher-group-theory.deloopable-h-spaces.html#1061" class="Bound">l1</a> <a id="1147" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1149" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1154" href="higher-group-theory.deloopable-h-spaces.html#1074" class="Bound">l2</a><a id="1156" class="Symbol">)</a>
  <a id="1160" href="higher-group-theory.deloopable-h-spaces.html#1114" class="Function">delooping-H-Space-Level</a> <a id="1184" class="Symbol">=</a>
    <a id="1190" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1192" class="Symbol">(</a><a id="1193" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="1201" href="higher-group-theory.deloopable-h-spaces.html#1074" class="Bound">l2</a><a id="1203" class="Symbol">)</a> <a id="1205" class="Symbol">(λ</a> <a id="1208" href="higher-group-theory.deloopable-h-spaces.html#1208" class="Bound">G</a> <a id="1210" class="Symbol">→</a> <a id="1212" href="structured-types.equivalences-h-spaces.html#7149" class="Function">equiv-H-Space</a> <a id="1226" href="higher-group-theory.deloopable-h-spaces.html#1087" class="Bound">A</a> <a id="1228" class="Symbol">(</a><a id="1229" href="higher-group-theory.higher-groups.html#2885" class="Function">h-space-∞-Group</a> <a id="1245" href="higher-group-theory.deloopable-h-spaces.html#1208" class="Bound">G</a><a id="1246" class="Symbol">))</a>
</pre>
### Deloopings of H-spaces

<pre class="Agda"><a id="1290" class="Keyword">module</a> <a id="1297" href="higher-group-theory.deloopable-h-spaces.html#1297" class="Module">_</a>
  <a id="1301" class="Symbol">{</a><a id="1302" href="higher-group-theory.deloopable-h-spaces.html#1302" class="Bound">l1</a> <a id="1305" class="Symbol">:</a> <a id="1307" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1312" class="Symbol">}</a> <a id="1314" class="Symbol">(</a><a id="1315" href="higher-group-theory.deloopable-h-spaces.html#1315" class="Bound">A</a> <a id="1317" class="Symbol">:</a> <a id="1319" href="structured-types.h-spaces.html#2494" class="Function">H-Space</a> <a id="1327" href="higher-group-theory.deloopable-h-spaces.html#1302" class="Bound">l1</a><a id="1329" class="Symbol">)</a>
  <a id="1333" class="Keyword">where</a>

  <a id="1342" href="higher-group-theory.deloopable-h-spaces.html#1342" class="Function">delooping-H-Space</a> <a id="1360" class="Symbol">:</a> <a id="1362" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1365" class="Symbol">(</a><a id="1366" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1371" href="higher-group-theory.deloopable-h-spaces.html#1302" class="Bound">l1</a><a id="1373" class="Symbol">)</a>
  <a id="1377" href="higher-group-theory.deloopable-h-spaces.html#1342" class="Function">delooping-H-Space</a> <a id="1395" class="Symbol">=</a> <a id="1397" href="higher-group-theory.deloopable-h-spaces.html#1114" class="Function">delooping-H-Space-Level</a> <a id="1421" href="higher-group-theory.deloopable-h-spaces.html#1302" class="Bound">l1</a> <a id="1424" href="higher-group-theory.deloopable-h-spaces.html#1315" class="Bound">A</a>
</pre>
## See also

- [Deloopable groups](higher-group-theory.deloopable-groups.md)
