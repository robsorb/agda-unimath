# Conjugation in higher groups

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="higher-group-theory.conjugation.html" class="Module">higher-group-theory.conjugation</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="208" class="Keyword">open</a> <a id="213" class="Keyword">import</a> <a id="220" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="248" class="Keyword">open</a> <a id="253" class="Keyword">import</a> <a id="260" href="higher-group-theory.higher-groups.html" class="Module">higher-group-theory.higher-groups</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="higher-group-theory.homomorphisms-higher-groups.html" class="Module">higher-group-theory.homomorphisms-higher-groups</a>

<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="structured-types.conjugation-pointed-types.html" class="Module">structured-types.conjugation-pointed-types</a>

<a id="411" class="Keyword">open</a> <a id="416" class="Keyword">import</a> <a id="423" href="synthetic-homotopy-theory.conjugation-loops.html" class="Module">synthetic-homotopy-theory.conjugation-loops</a>
</pre>
</details>

## Idea

The **conjugation homomorphism** on an
[∞-group](higher-group-theory.higher-groups.md) `G` is the
[conjugation map](structured-types.conjugation-pointed-types.md) of its
classifying [pointed type](structured-types.pointed-types.md) `BG`.

## Definition

<pre class="Agda"><a id="755" class="Keyword">module</a> <a id="762" href="higher-group-theory.conjugation.html#762" class="Module">_</a>
  <a id="766" class="Symbol">{</a><a id="767" href="higher-group-theory.conjugation.html#767" class="Bound">l</a> <a id="769" class="Symbol">:</a> <a id="771" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="776" class="Symbol">}</a> <a id="778" class="Symbol">(</a><a id="779" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="781" class="Symbol">:</a> <a id="783" href="higher-group-theory.higher-groups.html#993" class="Function">∞-Group</a> <a id="791" href="higher-group-theory.conjugation.html#767" class="Bound">l</a><a id="792" class="Symbol">)</a> <a id="794" class="Symbol">(</a><a id="795" href="higher-group-theory.conjugation.html#795" class="Bound">g</a> <a id="797" class="Symbol">:</a> <a id="799" href="higher-group-theory.higher-groups.html#3080" class="Function">type-∞-Group</a> <a id="812" href="higher-group-theory.conjugation.html#779" class="Bound">G</a><a id="813" class="Symbol">)</a>
  <a id="817" class="Keyword">where</a>

  <a id="826" href="higher-group-theory.conjugation.html#826" class="Function">conjugation-∞-Group</a> <a id="846" class="Symbol">:</a> <a id="848" href="higher-group-theory.homomorphisms-higher-groups.html#669" class="Function">hom-∞-Group</a> <a id="860" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="862" href="higher-group-theory.conjugation.html#779" class="Bound">G</a>
  <a id="866" href="higher-group-theory.conjugation.html#826" class="Function">conjugation-∞-Group</a> <a id="886" class="Symbol">=</a>
    <a id="892" href="structured-types.conjugation-pointed-types.html#1603" class="Function">conjugation-Pointed-Type</a> <a id="917" class="Symbol">(</a><a id="918" href="higher-group-theory.higher-groups.html#1156" class="Function">classifying-pointed-type-∞-Group</a> <a id="951" href="higher-group-theory.conjugation.html#779" class="Bound">G</a><a id="952" class="Symbol">)</a> <a id="954" href="higher-group-theory.conjugation.html#795" class="Bound">g</a>

  <a id="959" href="higher-group-theory.conjugation.html#959" class="Function">classifying-map-conjugation-∞-Group</a> <a id="995" class="Symbol">:</a>
    <a id="1001" href="higher-group-theory.higher-groups.html#1252" class="Function">classifying-type-∞-Group</a> <a id="1026" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="1028" class="Symbol">→</a> <a id="1030" href="higher-group-theory.higher-groups.html#1252" class="Function">classifying-type-∞-Group</a> <a id="1055" href="higher-group-theory.conjugation.html#779" class="Bound">G</a>
  <a id="1059" href="higher-group-theory.conjugation.html#959" class="Function">classifying-map-conjugation-∞-Group</a> <a id="1095" class="Symbol">=</a>
    <a id="1101" href="higher-group-theory.homomorphisms-higher-groups.html#792" class="Function">classifying-map-hom-∞-Group</a> <a id="1129" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="1131" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="1133" href="higher-group-theory.conjugation.html#826" class="Function">conjugation-∞-Group</a>

  <a id="1156" href="higher-group-theory.conjugation.html#1156" class="Function">preserves-point-classifying-map-conjugation-∞-Group</a> <a id="1208" class="Symbol">:</a>
    <a id="1214" href="higher-group-theory.conjugation.html#959" class="Function">classifying-map-conjugation-∞-Group</a> <a id="1250" class="Symbol">(</a><a id="1251" href="higher-group-theory.higher-groups.html#1371" class="Function">shape-∞-Group</a> <a id="1265" href="higher-group-theory.conjugation.html#779" class="Bound">G</a><a id="1266" class="Symbol">)</a> <a id="1268" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1270" href="higher-group-theory.higher-groups.html#1371" class="Function">shape-∞-Group</a> <a id="1284" href="higher-group-theory.conjugation.html#779" class="Bound">G</a>
  <a id="1288" href="higher-group-theory.conjugation.html#1156" class="Function">preserves-point-classifying-map-conjugation-∞-Group</a> <a id="1340" class="Symbol">=</a>
    <a id="1346" href="higher-group-theory.homomorphisms-higher-groups.html#947" class="Function">preserves-point-classifying-map-hom-∞-Group</a> <a id="1390" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="1392" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="1394" href="higher-group-theory.conjugation.html#826" class="Function">conjugation-∞-Group</a>

  <a id="1417" href="higher-group-theory.conjugation.html#1417" class="Function">map-conjugation-∞-Group</a> <a id="1441" class="Symbol">:</a> <a id="1443" href="higher-group-theory.higher-groups.html#3080" class="Function">type-∞-Group</a> <a id="1456" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="1458" class="Symbol">→</a> <a id="1460" href="higher-group-theory.higher-groups.html#3080" class="Function">type-∞-Group</a> <a id="1473" href="higher-group-theory.conjugation.html#779" class="Bound">G</a>
  <a id="1477" href="higher-group-theory.conjugation.html#1417" class="Function">map-conjugation-∞-Group</a> <a id="1501" class="Symbol">=</a> <a id="1503" href="higher-group-theory.homomorphisms-higher-groups.html#1170" class="Function">map-hom-∞-Group</a> <a id="1519" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="1521" href="higher-group-theory.conjugation.html#779" class="Bound">G</a> <a id="1523" href="higher-group-theory.conjugation.html#826" class="Function">conjugation-∞-Group</a>

  <a id="1546" href="higher-group-theory.conjugation.html#1546" class="Function">compute-map-conjugation-∞-Group</a> <a id="1578" class="Symbol">:</a>
    <a id="1584" href="synthetic-homotopy-theory.conjugation-loops.html#875" class="Function">map-conjugation-Ω</a> <a id="1602" href="higher-group-theory.conjugation.html#795" class="Bound">g</a> <a id="1604" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1606" href="higher-group-theory.conjugation.html#1417" class="Function">map-conjugation-∞-Group</a>
  <a id="1632" href="higher-group-theory.conjugation.html#1546" class="Function">compute-map-conjugation-∞-Group</a> <a id="1664" class="Symbol">=</a>
    <a id="1670" href="structured-types.conjugation-pointed-types.html#3592" class="Function">htpy-compute-action-on-loops-conjugation-Pointed-Type</a>
      <a id="1730" class="Symbol">(</a> <a id="1732" href="higher-group-theory.conjugation.html#795" class="Bound">g</a><a id="1733" class="Symbol">)</a>
</pre>