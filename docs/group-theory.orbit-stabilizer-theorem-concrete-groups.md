# The orbit-stabilizer theorem for concrete groups

<pre class="Agda"><a id="61" class="Keyword">module</a> <a id="68" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html" class="Module">group-theory.orbit-stabilizer-theorem-concrete-groups</a> <a id="122" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="351" class="Keyword">open</a> <a id="356" class="Keyword">import</a> <a id="363" href="group-theory.mere-equivalences-concrete-group-actions.html" class="Module">group-theory.mere-equivalences-concrete-group-actions</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="group-theory.stabilizer-groups-concrete-group-actions.html" class="Module">group-theory.stabilizer-groups-concrete-group-actions</a>

<a id="484" class="Keyword">open</a> <a id="489" class="Keyword">import</a> <a id="496" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

The orbit stabilizer theorem for concrete groups asserts that the type
`Orbit(x)` of orbits of an element `x : X *` is deloopable and fits in a fiber
sequence

```text
  BG_x ----> BG ----> B(Orbit(x))
```

To see that this is indeed a formulation of the orbit-stabilizer theorem, note
that the delooping of `Orbit(x)` gives `Orbit(x)` the structure of a group.
Furthermore, this fiber sequence induces a short exact sequence

```text
  G_x ----> G ----> Orbit(x),
```

which induces a bijection from the cosets of the stabilizer subgroup `G_x` of
`G` to the type `Orbit(x)`.

## Definitions

<pre class="Agda"><a id="1154" class="Keyword">module</a> <a id="1161" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1161" class="Module">_</a>
  <a id="1165" class="Symbol">{</a><a id="1166" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1166" class="Bound">l1</a> <a id="1169" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1169" class="Bound">l2</a> <a id="1172" class="Symbol">:</a> <a id="1174" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1179" class="Symbol">}</a> <a id="1181" class="Symbol">(</a><a id="1182" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a> <a id="1184" class="Symbol">:</a> <a id="1186" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="1201" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1166" class="Bound">l1</a><a id="1203" class="Symbol">)</a> <a id="1205" class="Symbol">(</a><a id="1206" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1206" class="Bound">X</a> <a id="1208" class="Symbol">:</a> <a id="1210" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="1232" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1169" class="Bound">l2</a> <a id="1235" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a><a id="1236" class="Symbol">)</a>
  <a id="1240" class="Keyword">where</a>

  <a id="1249" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1249" class="Function">classifying-type-quotient-stabilizer-action-Concrete-Group</a> <a id="1308" class="Symbol">:</a>
    <a id="1314" href="group-theory.concrete-group-actions.html#1036" class="Function">type-action-Concrete-Group</a> <a id="1341" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a> <a id="1343" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1206" class="Bound">X</a> <a id="1345" class="Symbol">→</a> <a id="1347" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1350" class="Symbol">(</a><a id="1351" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1356" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1166" class="Bound">l1</a> <a id="1359" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1361" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1366" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1169" class="Bound">l2</a><a id="1368" class="Symbol">)</a>
  <a id="1372" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1249" class="Function">classifying-type-quotient-stabilizer-action-Concrete-Group</a> <a id="1431" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1431" class="Bound">x</a> <a id="1433" class="Symbol">=</a>
    <a id="1439" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1441" class="Symbol">(</a> <a id="1443" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="1465" class="Symbol">(</a><a id="1466" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1166" class="Bound">l1</a> <a id="1469" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1471" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1169" class="Bound">l2</a><a id="1473" class="Symbol">)</a> <a id="1475" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a><a id="1476" class="Symbol">)</a>
      <a id="1484" class="Symbol">(</a> <a id="1486" href="group-theory.mere-equivalences-concrete-group-actions.html#852" class="Function">mere-equiv-action-Concrete-Group</a> <a id="1519" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a>
        <a id="1529" class="Symbol">(</a> <a id="1531" href="group-theory.stabilizer-groups-concrete-group-actions.html#1333" class="Function">action-stabilizer-action-Concrete-Group</a> <a id="1571" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a> <a id="1573" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1206" class="Bound">X</a> <a id="1575" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1431" class="Bound">x</a><a id="1576" class="Symbol">))</a>

  <a id="1582" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1582" class="Function">point-classifying-type-quotient-stabilizer-action-Concrete-Group</a> <a id="1647" class="Symbol">:</a>
    <a id="1653" class="Symbol">(</a><a id="1654" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1654" class="Bound">x</a> <a id="1656" class="Symbol">:</a> <a id="1658" href="group-theory.concrete-group-actions.html#1036" class="Function">type-action-Concrete-Group</a> <a id="1685" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a> <a id="1687" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1206" class="Bound">X</a><a id="1688" class="Symbol">)</a> <a id="1690" class="Symbol">→</a>
    <a id="1696" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1249" class="Function">classifying-type-quotient-stabilizer-action-Concrete-Group</a> <a id="1755" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1654" class="Bound">x</a>
  <a id="1759" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1763" class="Symbol">(</a><a id="1764" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1582" class="Function">point-classifying-type-quotient-stabilizer-action-Concrete-Group</a> <a id="1829" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1829" class="Bound">x</a><a id="1830" class="Symbol">)</a> <a id="1832" class="Symbol">=</a>
    <a id="1838" href="group-theory.stabilizer-groups-concrete-group-actions.html#1333" class="Function">action-stabilizer-action-Concrete-Group</a> <a id="1878" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a> <a id="1880" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1206" class="Bound">X</a> <a id="1882" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1829" class="Bound">x</a>
  <a id="1886" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1890" class="Symbol">(</a><a id="1891" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1582" class="Function">point-classifying-type-quotient-stabilizer-action-Concrete-Group</a> <a id="1956" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1956" class="Bound">x</a><a id="1957" class="Symbol">)</a> <a id="1959" class="Symbol">=</a>
    <a id="1965" href="group-theory.mere-equivalences-concrete-group-actions.html#1437" class="Function">refl-mere-equiv-action-Concrete-Group</a> <a id="2003" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a>
      <a id="2011" class="Symbol">(</a><a id="2012" href="group-theory.stabilizer-groups-concrete-group-actions.html#1333" class="Function">action-stabilizer-action-Concrete-Group</a> <a id="2052" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a> <a id="2054" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1206" class="Bound">X</a> <a id="2056" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1956" class="Bound">x</a><a id="2057" class="Symbol">)</a>

  <a id="2062" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#2062" class="Function">classifying-pointed-type-stabilizer-action-Concrete-Group</a> <a id="2120" class="Symbol">:</a>
    <a id="2126" class="Symbol">(</a><a id="2127" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#2127" class="Bound">x</a> <a id="2129" class="Symbol">:</a> <a id="2131" href="group-theory.concrete-group-actions.html#1036" class="Function">type-action-Concrete-Group</a> <a id="2158" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1182" class="Bound">G</a> <a id="2160" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1206" class="Bound">X</a><a id="2161" class="Symbol">)</a> <a id="2163" class="Symbol">→</a>
    <a id="2169" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2182" class="Symbol">(</a><a id="2183" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2188" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1166" class="Bound">l1</a> <a id="2191" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2193" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2198" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1169" class="Bound">l2</a><a id="2200" class="Symbol">)</a>
  <a id="2204" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2208" class="Symbol">(</a><a id="2209" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#2062" class="Function">classifying-pointed-type-stabilizer-action-Concrete-Group</a> <a id="2267" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#2267" class="Bound">x</a><a id="2268" class="Symbol">)</a> <a id="2270" class="Symbol">=</a>
    <a id="2276" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1249" class="Function">classifying-type-quotient-stabilizer-action-Concrete-Group</a> <a id="2335" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#2267" class="Bound">x</a>
  <a id="2339" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2343" class="Symbol">(</a><a id="2344" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#2062" class="Function">classifying-pointed-type-stabilizer-action-Concrete-Group</a> <a id="2402" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#2402" class="Bound">x</a><a id="2403" class="Symbol">)</a> <a id="2405" class="Symbol">=</a>
    <a id="2411" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#1582" class="Function">point-classifying-type-quotient-stabilizer-action-Concrete-Group</a> <a id="2476" href="group-theory.orbit-stabilizer-theorem-concrete-groups.html#2402" class="Bound">x</a>
</pre>