# Path-split maps

<pre class="Agda"><a id="28" class="Keyword">module</a> <a id="35" href="foundation.path-split-maps.html" class="Module">foundation.path-split-maps</a> <a id="62" class="Keyword">where</a>

<a id="69" class="Keyword">open</a> <a id="74" class="Keyword">import</a> <a id="81" href="foundation-core.path-split-maps.html" class="Module">foundation-core.path-split-maps</a> <a id="113" class="Keyword">public</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="214" class="Keyword">open</a> <a id="219" class="Keyword">import</a> <a id="226" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="250" class="Keyword">open</a> <a id="255" class="Keyword">import</a> <a id="262" href="foundation.iterated-dependent-product-types.html" class="Module">foundation.iterated-dependent-product-types</a>
<a id="306" class="Keyword">open</a> <a id="311" class="Keyword">import</a> <a id="318" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="350" class="Keyword">open</a> <a id="355" class="Keyword">import</a> <a id="362" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="390" class="Keyword">open</a> <a id="395" class="Keyword">import</a> <a id="402" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Properties

### Being path-split is a property

<pre class="Agda"><a id="554" class="Keyword">module</a> <a id="561" href="foundation.path-split-maps.html#561" class="Module">_</a>
  <a id="565" class="Symbol">{</a><a id="566" href="foundation.path-split-maps.html#566" class="Bound">l1</a> <a id="569" href="foundation.path-split-maps.html#569" class="Bound">l2</a> <a id="572" class="Symbol">:</a> <a id="574" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="579" class="Symbol">}</a> <a id="581" class="Symbol">{</a><a id="582" href="foundation.path-split-maps.html#582" class="Bound">A</a> <a id="584" class="Symbol">:</a> <a id="586" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="589" href="foundation.path-split-maps.html#566" class="Bound">l1</a><a id="591" class="Symbol">}</a> <a id="593" class="Symbol">{</a><a id="594" href="foundation.path-split-maps.html#594" class="Bound">B</a> <a id="596" class="Symbol">:</a> <a id="598" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="601" href="foundation.path-split-maps.html#569" class="Bound">l2</a><a id="603" class="Symbol">}</a>
  <a id="607" class="Keyword">where</a>

  <a id="616" class="Keyword">abstract</a>
    <a id="629" href="foundation.path-split-maps.html#629" class="Function">is-prop-is-path-split</a> <a id="651" class="Symbol">:</a> <a id="653" class="Symbol">(</a><a id="654" href="foundation.path-split-maps.html#654" class="Bound">f</a> <a id="656" class="Symbol">:</a> <a id="658" href="foundation.path-split-maps.html#582" class="Bound">A</a> <a id="660" class="Symbol">→</a> <a id="662" href="foundation.path-split-maps.html#594" class="Bound">B</a><a id="663" class="Symbol">)</a> <a id="665" class="Symbol">→</a> <a id="667" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="675" class="Symbol">(</a><a id="676" href="foundation-core.path-split-maps.html#1139" class="Function">is-path-split</a> <a id="690" href="foundation.path-split-maps.html#654" class="Bound">f</a><a id="691" class="Symbol">)</a>
    <a id="697" href="foundation.path-split-maps.html#629" class="Function">is-prop-is-path-split</a> <a id="719" href="foundation.path-split-maps.html#719" class="Bound">f</a> <a id="721" class="Symbol">=</a>
      <a id="729" href="foundation-core.propositions.html#3025" class="Function">is-prop-is-proof-irrelevant</a>
        <a id="765" class="Symbol">(</a> <a id="767" class="Symbol">λ</a> <a id="769" href="foundation.path-split-maps.html#769" class="Bound">is-path-split-f</a> <a id="785" class="Symbol">→</a>
          <a id="797" class="Symbol">(</a> <a id="799" href="foundation-core.contractible-types.html#4582" class="Function">is-contr-product</a>
            <a id="828" class="Symbol">(</a> <a id="830" href="foundation.equivalences.html#2804" class="Function">is-contr-section-is-equiv</a>
              <a id="870" class="Symbol">(</a> <a id="872" href="foundation-core.path-split-maps.html#2139" class="Function">is-equiv-is-path-split</a> <a id="895" href="foundation.path-split-maps.html#719" class="Bound">f</a> <a id="897" href="foundation.path-split-maps.html#769" class="Bound">is-path-split-f</a><a id="912" class="Symbol">))</a>
            <a id="927" class="Symbol">(</a> <a id="929" href="foundation.iterated-dependent-product-types.html#4901" class="Function">is-contr-iterated-Π</a> <a id="949" class="Number">2</a>
              <a id="965" class="Symbol">(</a> <a id="967" class="Symbol">λ</a> <a id="969" href="foundation.path-split-maps.html#969" class="Bound">x</a> <a id="971" href="foundation.path-split-maps.html#971" class="Bound">y</a> <a id="973" class="Symbol">→</a>
                <a id="991" href="foundation.equivalences.html#2804" class="Function">is-contr-section-is-equiv</a>
                  <a id="1035" class="Symbol">(</a> <a id="1037" href="foundation-core.equivalences.html#20409" class="Function">is-emb-is-equiv</a>
                    <a id="1073" class="Symbol">(</a> <a id="1075" href="foundation-core.path-split-maps.html#2139" class="Function">is-equiv-is-path-split</a> <a id="1098" href="foundation.path-split-maps.html#719" class="Bound">f</a> <a id="1100" href="foundation.path-split-maps.html#769" class="Bound">is-path-split-f</a><a id="1115" class="Symbol">)</a> <a id="1117" href="foundation.path-split-maps.html#969" class="Bound">x</a> <a id="1119" href="foundation.path-split-maps.html#971" class="Bound">y</a><a id="1120" class="Symbol">)))))</a>

  <a id="1129" class="Keyword">abstract</a>
    <a id="1142" href="foundation.path-split-maps.html#1142" class="Function">is-equiv-is-path-split-is-equiv</a> <a id="1174" class="Symbol">:</a>
      <a id="1182" class="Symbol">(</a><a id="1183" href="foundation.path-split-maps.html#1183" class="Bound">f</a> <a id="1185" class="Symbol">:</a> <a id="1187" href="foundation.path-split-maps.html#582" class="Bound">A</a> <a id="1189" class="Symbol">→</a> <a id="1191" href="foundation.path-split-maps.html#594" class="Bound">B</a><a id="1192" class="Symbol">)</a> <a id="1194" class="Symbol">→</a> <a id="1196" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1205" class="Symbol">(</a><a id="1206" href="foundation-core.path-split-maps.html#1419" class="Function">is-path-split-is-equiv</a> <a id="1229" href="foundation.path-split-maps.html#1183" class="Bound">f</a><a id="1230" class="Symbol">)</a>
    <a id="1236" href="foundation.path-split-maps.html#1142" class="Function">is-equiv-is-path-split-is-equiv</a> <a id="1268" href="foundation.path-split-maps.html#1268" class="Bound">f</a> <a id="1270" class="Symbol">=</a>
      <a id="1278" href="foundation.logical-equivalences.html#4351" class="Function">is-equiv-has-converse-is-prop</a>
        <a id="1316" class="Symbol">(</a> <a id="1318" href="foundation.equivalences.html#4907" class="Function">is-property-is-equiv</a> <a id="1339" href="foundation.path-split-maps.html#1268" class="Bound">f</a><a id="1340" class="Symbol">)</a>
        <a id="1350" class="Symbol">(</a> <a id="1352" href="foundation.path-split-maps.html#629" class="Function">is-prop-is-path-split</a> <a id="1374" href="foundation.path-split-maps.html#1268" class="Bound">f</a><a id="1375" class="Symbol">)</a>
        <a id="1385" class="Symbol">(</a> <a id="1387" href="foundation-core.path-split-maps.html#2139" class="Function">is-equiv-is-path-split</a> <a id="1410" href="foundation.path-split-maps.html#1268" class="Bound">f</a><a id="1411" class="Symbol">)</a>

  <a id="1416" href="foundation.path-split-maps.html#1416" class="Function">equiv-is-path-split-is-equiv</a> <a id="1445" class="Symbol">:</a> <a id="1447" class="Symbol">(</a><a id="1448" href="foundation.path-split-maps.html#1448" class="Bound">f</a> <a id="1450" class="Symbol">:</a> <a id="1452" href="foundation.path-split-maps.html#582" class="Bound">A</a> <a id="1454" class="Symbol">→</a> <a id="1456" href="foundation.path-split-maps.html#594" class="Bound">B</a><a id="1457" class="Symbol">)</a> <a id="1459" class="Symbol">→</a> <a id="1461" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1470" href="foundation.path-split-maps.html#1448" class="Bound">f</a> <a id="1472" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1474" href="foundation-core.path-split-maps.html#1139" class="Function">is-path-split</a> <a id="1488" href="foundation.path-split-maps.html#1448" class="Bound">f</a>
  <a id="1492" href="foundation.path-split-maps.html#1416" class="Function">equiv-is-path-split-is-equiv</a> <a id="1521" href="foundation.path-split-maps.html#1521" class="Bound">f</a> <a id="1523" class="Symbol">=</a>
    <a id="1529" href="foundation.dependent-pair-types.html#664" class="InductiveConstructor">pair</a> <a id="1534" class="Symbol">(</a><a id="1535" href="foundation-core.path-split-maps.html#1419" class="Function">is-path-split-is-equiv</a> <a id="1558" href="foundation.path-split-maps.html#1521" class="Bound">f</a><a id="1559" class="Symbol">)</a> <a id="1561" class="Symbol">(</a><a id="1562" href="foundation.path-split-maps.html#1142" class="Function">is-equiv-is-path-split-is-equiv</a> <a id="1594" href="foundation.path-split-maps.html#1521" class="Bound">f</a><a id="1595" class="Symbol">)</a>

  <a id="1600" class="Keyword">abstract</a>
    <a id="1613" href="foundation.path-split-maps.html#1613" class="Function">is-equiv-is-equiv-is-path-split</a> <a id="1645" class="Symbol">:</a>
      <a id="1653" class="Symbol">(</a><a id="1654" href="foundation.path-split-maps.html#1654" class="Bound">f</a> <a id="1656" class="Symbol">:</a> <a id="1658" href="foundation.path-split-maps.html#582" class="Bound">A</a> <a id="1660" class="Symbol">→</a> <a id="1662" href="foundation.path-split-maps.html#594" class="Bound">B</a><a id="1663" class="Symbol">)</a> <a id="1665" class="Symbol">→</a> <a id="1667" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1676" class="Symbol">(</a><a id="1677" href="foundation-core.path-split-maps.html#2139" class="Function">is-equiv-is-path-split</a> <a id="1700" href="foundation.path-split-maps.html#1654" class="Bound">f</a><a id="1701" class="Symbol">)</a>
    <a id="1707" href="foundation.path-split-maps.html#1613" class="Function">is-equiv-is-equiv-is-path-split</a> <a id="1739" href="foundation.path-split-maps.html#1739" class="Bound">f</a> <a id="1741" class="Symbol">=</a>
      <a id="1749" href="foundation.logical-equivalences.html#4351" class="Function">is-equiv-has-converse-is-prop</a>
        <a id="1787" class="Symbol">(</a> <a id="1789" href="foundation.path-split-maps.html#629" class="Function">is-prop-is-path-split</a> <a id="1811" href="foundation.path-split-maps.html#1739" class="Bound">f</a><a id="1812" class="Symbol">)</a>
        <a id="1822" class="Symbol">(</a> <a id="1824" href="foundation.equivalences.html#4907" class="Function">is-property-is-equiv</a> <a id="1845" href="foundation.path-split-maps.html#1739" class="Bound">f</a><a id="1846" class="Symbol">)</a>
        <a id="1856" class="Symbol">(</a> <a id="1858" href="foundation-core.path-split-maps.html#1419" class="Function">is-path-split-is-equiv</a> <a id="1881" href="foundation.path-split-maps.html#1739" class="Bound">f</a><a id="1882" class="Symbol">)</a>

  <a id="1887" href="foundation.path-split-maps.html#1887" class="Function">equiv-is-equiv-is-path-split</a> <a id="1916" class="Symbol">:</a> <a id="1918" class="Symbol">(</a><a id="1919" href="foundation.path-split-maps.html#1919" class="Bound">f</a> <a id="1921" class="Symbol">:</a> <a id="1923" href="foundation.path-split-maps.html#582" class="Bound">A</a> <a id="1925" class="Symbol">→</a> <a id="1927" href="foundation.path-split-maps.html#594" class="Bound">B</a><a id="1928" class="Symbol">)</a> <a id="1930" class="Symbol">→</a> <a id="1932" href="foundation-core.path-split-maps.html#1139" class="Function">is-path-split</a> <a id="1946" href="foundation.path-split-maps.html#1919" class="Bound">f</a> <a id="1948" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="1950" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1959" href="foundation.path-split-maps.html#1919" class="Bound">f</a>
  <a id="1963" href="foundation.path-split-maps.html#1887" class="Function">equiv-is-equiv-is-path-split</a> <a id="1992" href="foundation.path-split-maps.html#1992" class="Bound">f</a> <a id="1994" class="Symbol">=</a>
    <a id="2000" class="Symbol">(</a> <a id="2002" href="foundation-core.path-split-maps.html#2139" class="Function">is-equiv-is-path-split</a> <a id="2025" href="foundation.path-split-maps.html#1992" class="Bound">f</a> <a id="2027" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="2029" href="foundation.path-split-maps.html#1613" class="Function">is-equiv-is-equiv-is-path-split</a> <a id="2061" href="foundation.path-split-maps.html#1992" class="Bound">f</a><a id="2062" class="Symbol">)</a>
</pre>
## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of coherently invertible maps, also known as half-adjoint
  equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).

## References

{{#bibliography}} {{#reference UF13}} {{#reference Shu14UniversalProperties}}
