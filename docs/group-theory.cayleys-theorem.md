# Cayley's theorem

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="group-theory.cayleys-theorem.html" class="Module">group-theory.cayleys-theorem</a> <a id="65" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="121" class="Keyword">open</a> <a id="126" class="Keyword">import</a> <a id="133" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="165" class="Keyword">open</a> <a id="170" class="Keyword">import</a> <a id="177" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="foundation.equivalence-extensionality.html" class="Module">foundation.equivalence-extensionality</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="287" class="Keyword">open</a> <a id="292" class="Keyword">import</a> <a id="299" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="325" class="Keyword">open</a> <a id="330" class="Keyword">import</a> <a id="337" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="353" class="Keyword">open</a> <a id="358" class="Keyword">import</a> <a id="365" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="group-theory.embeddings-groups.html" class="Module">group-theory.embeddings-groups</a>
<a id="436" class="Keyword">open</a> <a id="441" class="Keyword">import</a> <a id="448" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="468" class="Keyword">open</a> <a id="473" class="Keyword">import</a> <a id="480" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
<a id="514" class="Keyword">open</a> <a id="519" class="Keyword">import</a> <a id="526" href="group-theory.symmetric-groups.html" class="Module">group-theory.symmetric-groups</a>
</pre>
</details>

## Idea

{{#concept "Cayley's theorem" Disambiguation="for abstract groups" WD="Cayley's theorem" WDID=Q179208 Agda=Cayleys-theorem}}
states that every [group](group-theory.groups.md) is a
[subgroup](group-theory.subgroups.md) of a
[symmetric group](group-theory.symmetric-groups.md).

## Theorem

### Direct proof of Cayley's theorem

<pre class="Agda"><a id="917" class="Keyword">module</a> <a id="924" href="group-theory.cayleys-theorem.html#924" class="Module">_</a>
  <a id="928" class="Symbol">{</a><a id="929" href="group-theory.cayleys-theorem.html#929" class="Bound">l1</a> <a id="932" class="Symbol">:</a> <a id="934" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="939" class="Symbol">}</a> <a id="941" class="Symbol">(</a><a id="942" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a> <a id="944" class="Symbol">:</a> <a id="946" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="952" href="group-theory.cayleys-theorem.html#929" class="Bound">l1</a><a id="954" class="Symbol">)</a>
  <a id="958" class="Keyword">where</a>

  <a id="967" href="group-theory.cayleys-theorem.html#967" class="Function">map-Cayleys-theorem</a> <a id="987" class="Symbol">:</a>
    <a id="993" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1004" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a> <a id="1006" class="Symbol">→</a> <a id="1008" href="group-theory.groups.html#2590" class="Function">type-Group</a> <a id="1019" class="Symbol">(</a><a id="1020" href="group-theory.symmetric-groups.html#2342" class="Function">symmetric-Group</a> <a id="1036" class="Symbol">(</a><a id="1037" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="1047" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a><a id="1048" class="Symbol">))</a>
  <a id="1053" href="group-theory.cayleys-theorem.html#967" class="Function">map-Cayleys-theorem</a> <a id="1073" class="Symbol">=</a> <a id="1075" href="group-theory.groups.html#8607" class="Function">equiv-mul-Group</a> <a id="1091" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a>

  <a id="1096" href="group-theory.cayleys-theorem.html#1096" class="Function">preserves-mul-map-Cayleys-theorem</a> <a id="1130" class="Symbol">:</a>
    <a id="1136" href="group-theory.homomorphisms-groups.html#971" class="Function">preserves-mul-Group</a> <a id="1156" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a> <a id="1158" class="Symbol">(</a><a id="1159" href="group-theory.symmetric-groups.html#2342" class="Function">symmetric-Group</a> <a id="1175" class="Symbol">(</a><a id="1176" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="1186" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a><a id="1187" class="Symbol">))</a> <a id="1190" href="group-theory.cayleys-theorem.html#967" class="Function">map-Cayleys-theorem</a>
  <a id="1212" href="group-theory.cayleys-theorem.html#1096" class="Function">preserves-mul-map-Cayleys-theorem</a> <a id="1246" class="Symbol">{</a><a id="1247" href="group-theory.cayleys-theorem.html#1247" class="Bound">x</a><a id="1248" class="Symbol">}</a> <a id="1250" class="Symbol">{</a><a id="1251" href="group-theory.cayleys-theorem.html#1251" class="Bound">y</a><a id="1252" class="Symbol">}</a> <a id="1254" class="Symbol">=</a>
    <a id="1260" href="foundation.equivalence-extensionality.html#2512" class="Function">eq-htpy-equiv</a> <a id="1274" class="Symbol">(</a><a id="1275" href="group-theory.groups.html#3174" class="Function">associative-mul-Group</a> <a id="1297" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a> <a id="1299" href="group-theory.cayleys-theorem.html#1247" class="Bound">x</a> <a id="1301" href="group-theory.cayleys-theorem.html#1251" class="Bound">y</a><a id="1302" class="Symbol">)</a>

  <a id="1307" href="group-theory.cayleys-theorem.html#1307" class="Function">hom-Cayleys-theorem</a> <a id="1327" class="Symbol">:</a> <a id="1329" href="group-theory.homomorphisms-groups.html#1698" class="Function">hom-Group</a> <a id="1339" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a> <a id="1341" class="Symbol">(</a><a id="1342" href="group-theory.symmetric-groups.html#2342" class="Function">symmetric-Group</a> <a id="1358" class="Symbol">(</a><a id="1359" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="1369" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a><a id="1370" class="Symbol">))</a>
  <a id="1375" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1379" href="group-theory.cayleys-theorem.html#1307" class="Function">hom-Cayleys-theorem</a> <a id="1399" class="Symbol">=</a> <a id="1401" href="group-theory.cayleys-theorem.html#967" class="Function">map-Cayleys-theorem</a>
  <a id="1423" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1427" href="group-theory.cayleys-theorem.html#1307" class="Function">hom-Cayleys-theorem</a> <a id="1447" class="Symbol">=</a> <a id="1449" href="group-theory.cayleys-theorem.html#1096" class="Function">preserves-mul-map-Cayleys-theorem</a>

  <a id="1486" href="group-theory.cayleys-theorem.html#1486" class="Function">is-injective-map-Cayleys-theorem</a> <a id="1519" class="Symbol">:</a> <a id="1521" href="foundation-core.injective-maps.html#1182" class="Function">is-injective</a> <a id="1534" href="group-theory.cayleys-theorem.html#967" class="Function">map-Cayleys-theorem</a>
  <a id="1556" href="group-theory.cayleys-theorem.html#1486" class="Function">is-injective-map-Cayleys-theorem</a> <a id="1589" class="Symbol">{</a><a id="1590" href="group-theory.cayleys-theorem.html#1590" class="Bound">x</a><a id="1591" class="Symbol">}</a> <a id="1593" class="Symbol">{</a><a id="1594" href="group-theory.cayleys-theorem.html#1594" class="Bound">y</a><a id="1595" class="Symbol">}</a> <a id="1597" href="group-theory.cayleys-theorem.html#1597" class="Bound">p</a> <a id="1599" class="Symbol">=</a>
    <a id="1605" class="Symbol">(</a> <a id="1607" href="foundation-core.identity-types.html#6358" class="Function">inv</a> <a id="1611" class="Symbol">(</a><a id="1612" href="group-theory.groups.html#4534" class="Function">right-unit-law-mul-Group</a> <a id="1637" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a> <a id="1639" href="group-theory.cayleys-theorem.html#1590" class="Bound">x</a><a id="1640" class="Symbol">))</a> <a id="1643" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="1649" class="Symbol">(</a> <a id="1651" href="foundation.equivalence-extensionality.html#2642" class="Function">htpy-eq-equiv</a> <a id="1665" href="group-theory.cayleys-theorem.html#1597" class="Bound">p</a> <a id="1667" class="Symbol">(</a><a id="1668" href="group-theory.groups.html#3628" class="Function">unit-Group</a> <a id="1679" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a><a id="1680" class="Symbol">))</a> <a id="1683" href="foundation-core.identity-types.html#6054" class="Function Operator">∙</a>
    <a id="1689" class="Symbol">(</a> <a id="1691" href="group-theory.groups.html#4534" class="Function">right-unit-law-mul-Group</a> <a id="1716" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a> <a id="1718" href="group-theory.cayleys-theorem.html#1594" class="Bound">y</a><a id="1719" class="Symbol">)</a>

  <a id="1724" href="group-theory.cayleys-theorem.html#1724" class="Function">is-emb-map-Cayleys-theorem</a> <a id="1751" class="Symbol">:</a> <a id="1753" href="foundation-core.embeddings.html#1178" class="Function">is-emb</a> <a id="1760" href="group-theory.cayleys-theorem.html#967" class="Function">map-Cayleys-theorem</a>
  <a id="1782" href="group-theory.cayleys-theorem.html#1724" class="Function">is-emb-map-Cayleys-theorem</a> <a id="1809" class="Symbol">=</a>
    <a id="1815" href="foundation.injective-maps.html#2001" class="Function">is-emb-is-injective</a>
      <a id="1841" class="Symbol">(</a> <a id="1843" href="group-theory.groups.html#2640" class="Function">is-set-type-Group</a> <a id="1861" class="Symbol">(</a><a id="1862" href="group-theory.symmetric-groups.html#2342" class="Function">symmetric-Group</a> <a id="1878" class="Symbol">(</a><a id="1879" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="1889" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a><a id="1890" class="Symbol">)))</a>
      <a id="1900" class="Symbol">(</a> <a id="1902" href="group-theory.cayleys-theorem.html#1486" class="Function">is-injective-map-Cayleys-theorem</a><a id="1934" class="Symbol">)</a>

  <a id="1939" href="group-theory.cayleys-theorem.html#1939" class="Function">Cayleys-theorem</a> <a id="1955" class="Symbol">:</a> <a id="1957" href="group-theory.embeddings-groups.html#697" class="Function">emb-Group</a> <a id="1967" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a> <a id="1969" class="Symbol">(</a><a id="1970" href="group-theory.symmetric-groups.html#2342" class="Function">symmetric-Group</a> <a id="1986" class="Symbol">(</a><a id="1987" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="1997" href="group-theory.cayleys-theorem.html#942" class="Bound">G</a><a id="1998" class="Symbol">))</a>
  <a id="2003" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2007" href="group-theory.cayleys-theorem.html#1939" class="Function">Cayleys-theorem</a> <a id="2023" class="Symbol">=</a> <a id="2025" href="group-theory.cayleys-theorem.html#1307" class="Function">hom-Cayleys-theorem</a>
  <a id="2047" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2051" href="group-theory.cayleys-theorem.html#1939" class="Function">Cayleys-theorem</a> <a id="2067" class="Symbol">=</a> <a id="2069" href="group-theory.cayleys-theorem.html#1724" class="Function">is-emb-map-Cayleys-theorem</a>
</pre>
### Cayley's theorem as a corollary of the Yoneda lemma

This is Corollary 2.2.10 of {{#cite Rie17}}, and remains to be formalized.

## References

{{#bibliography}}

## External links

- [Cayley's Theorem](https://1lab.dev/Algebra.Group.Cayley.html) at 1lab
- [Cayley's theorem](https://ncatlab.org/nlab/show/Cayley%27s+theorem) at $n$Lab
- [Cayley's theorem](https://en.wikipedia.org/wiki/Cayley%27s_theorem) at
  Wikipedia
- [Cayley's theorem](https://www.wikidata.org/wiki/Q179208) at Wikidata
