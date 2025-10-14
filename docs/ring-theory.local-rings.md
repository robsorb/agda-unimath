# Local rings

<pre class="Agda"><a id="24" class="Keyword">module</a> <a id="31" href="ring-theory.local-rings.html" class="Module">ring-theory.local-rings</a> <a id="55" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="111" class="Keyword">open</a> <a id="116" class="Keyword">import</a> <a id="123" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="155" class="Keyword">open</a> <a id="160" class="Keyword">import</a> <a id="167" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="254" class="Keyword">open</a> <a id="259" class="Keyword">import</a> <a id="266" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="ring-theory.invertible-elements-rings.html" class="Module">ring-theory.invertible-elements-rings</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

A local ring is a ring such that whenever a sum of elements is invertible, then
one of its summands is invertible. This implies that the noninvertible elements
form an ideal. However, the law of excluded middle is needed to show that any
ring of which the noninvertible elements form an ideal is a local ring.

## Definition

<pre class="Agda"><a id="is-local-prop-Ring"></a><a id="734" href="ring-theory.local-rings.html#734" class="Function">is-local-prop-Ring</a> <a id="753" class="Symbol">:</a> <a id="755" class="Symbol">{</a><a id="756" href="ring-theory.local-rings.html#756" class="Bound">l</a> <a id="758" class="Symbol">:</a> <a id="760" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="765" class="Symbol">}</a> <a id="767" class="Symbol">(</a><a id="768" href="ring-theory.local-rings.html#768" class="Bound">R</a> <a id="770" class="Symbol">:</a> <a id="772" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="777" href="ring-theory.local-rings.html#756" class="Bound">l</a><a id="778" class="Symbol">)</a> <a id="780" class="Symbol">→</a> <a id="782" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="787" href="ring-theory.local-rings.html#756" class="Bound">l</a>
<a id="789" href="ring-theory.local-rings.html#734" class="Function">is-local-prop-Ring</a> <a id="808" href="ring-theory.local-rings.html#808" class="Bound">R</a> <a id="810" class="Symbol">=</a>
  <a id="814" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
    <a id="825" class="Symbol">(</a> <a id="827" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="837" href="ring-theory.local-rings.html#808" class="Bound">R</a><a id="838" class="Symbol">)</a>
    <a id="844" class="Symbol">(</a> <a id="846" class="Symbol">λ</a> <a id="848" href="ring-theory.local-rings.html#848" class="Bound">a</a> <a id="850" class="Symbol">→</a>
      <a id="858" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
        <a id="873" class="Symbol">(</a> <a id="875" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="885" href="ring-theory.local-rings.html#808" class="Bound">R</a><a id="886" class="Symbol">)</a>
        <a id="896" class="Symbol">(</a> <a id="898" class="Symbol">λ</a> <a id="900" href="ring-theory.local-rings.html#900" class="Bound">b</a> <a id="902" class="Symbol">→</a>
          <a id="914" href="foundation-core.propositions.html#8326" class="Function">function-Prop</a>
            <a id="940" class="Symbol">(</a> <a id="942" href="ring-theory.invertible-elements-rings.html#3693" class="Function">is-invertible-element-Ring</a> <a id="969" href="ring-theory.local-rings.html#808" class="Bound">R</a> <a id="971" class="Symbol">(</a><a id="972" href="ring-theory.rings.html#2861" class="Function">add-Ring</a> <a id="981" href="ring-theory.local-rings.html#808" class="Bound">R</a> <a id="983" href="ring-theory.local-rings.html#848" class="Bound">a</a> <a id="985" href="ring-theory.local-rings.html#900" class="Bound">b</a><a id="986" class="Symbol">))</a>
            <a id="1001" class="Symbol">(</a> <a id="1003" href="foundation.disjunction.html#3468" class="Function">disjunction-Prop</a>
              <a id="1034" class="Symbol">(</a> <a id="1036" href="ring-theory.invertible-elements-rings.html#5042" class="Function">is-invertible-element-prop-Ring</a> <a id="1068" href="ring-theory.local-rings.html#808" class="Bound">R</a> <a id="1070" href="ring-theory.local-rings.html#848" class="Bound">a</a><a id="1071" class="Symbol">)</a>
              <a id="1087" class="Symbol">(</a> <a id="1089" href="ring-theory.invertible-elements-rings.html#5042" class="Function">is-invertible-element-prop-Ring</a> <a id="1121" href="ring-theory.local-rings.html#808" class="Bound">R</a> <a id="1123" href="ring-theory.local-rings.html#900" class="Bound">b</a><a id="1124" class="Symbol">))))</a>

<a id="is-local-Ring"></a><a id="1130" href="ring-theory.local-rings.html#1130" class="Function">is-local-Ring</a> <a id="1144" class="Symbol">:</a> <a id="1146" class="Symbol">{</a><a id="1147" href="ring-theory.local-rings.html#1147" class="Bound">l</a> <a id="1149" class="Symbol">:</a> <a id="1151" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1156" class="Symbol">}</a> <a id="1158" class="Symbol">→</a> <a id="1160" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1165" href="ring-theory.local-rings.html#1147" class="Bound">l</a> <a id="1167" class="Symbol">→</a> <a id="1169" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1172" href="ring-theory.local-rings.html#1147" class="Bound">l</a>
<a id="1174" href="ring-theory.local-rings.html#1130" class="Function">is-local-Ring</a> <a id="1188" href="ring-theory.local-rings.html#1188" class="Bound">R</a> <a id="1190" class="Symbol">=</a> <a id="1192" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1202" class="Symbol">(</a><a id="1203" href="ring-theory.local-rings.html#734" class="Function">is-local-prop-Ring</a> <a id="1222" href="ring-theory.local-rings.html#1188" class="Bound">R</a><a id="1223" class="Symbol">)</a>

<a id="is-prop-is-local-Ring"></a><a id="1226" href="ring-theory.local-rings.html#1226" class="Function">is-prop-is-local-Ring</a> <a id="1248" class="Symbol">:</a> <a id="1250" class="Symbol">{</a><a id="1251" href="ring-theory.local-rings.html#1251" class="Bound">l</a> <a id="1253" class="Symbol">:</a> <a id="1255" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1260" class="Symbol">}</a> <a id="1262" class="Symbol">(</a><a id="1263" href="ring-theory.local-rings.html#1263" class="Bound">R</a> <a id="1265" class="Symbol">:</a> <a id="1267" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1272" href="ring-theory.local-rings.html#1251" class="Bound">l</a><a id="1273" class="Symbol">)</a> <a id="1275" class="Symbol">→</a> <a id="1277" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1285" class="Symbol">(</a><a id="1286" href="ring-theory.local-rings.html#1130" class="Function">is-local-Ring</a> <a id="1300" href="ring-theory.local-rings.html#1263" class="Bound">R</a><a id="1301" class="Symbol">)</a>
<a id="1303" href="ring-theory.local-rings.html#1226" class="Function">is-prop-is-local-Ring</a> <a id="1325" href="ring-theory.local-rings.html#1325" class="Bound">R</a> <a id="1327" class="Symbol">=</a> <a id="1329" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1347" class="Symbol">(</a><a id="1348" href="ring-theory.local-rings.html#734" class="Function">is-local-prop-Ring</a> <a id="1367" href="ring-theory.local-rings.html#1325" class="Bound">R</a><a id="1368" class="Symbol">)</a>

<a id="Local-Ring"></a><a id="1371" href="ring-theory.local-rings.html#1371" class="Function">Local-Ring</a> <a id="1382" class="Symbol">:</a> <a id="1384" class="Symbol">(</a><a id="1385" href="ring-theory.local-rings.html#1385" class="Bound">l</a> <a id="1387" class="Symbol">:</a> <a id="1389" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1394" class="Symbol">)</a> <a id="1396" class="Symbol">→</a> <a id="1398" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1401" class="Symbol">(</a><a id="1402" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1407" href="ring-theory.local-rings.html#1385" class="Bound">l</a><a id="1408" class="Symbol">)</a>
<a id="1410" href="ring-theory.local-rings.html#1371" class="Function">Local-Ring</a> <a id="1421" href="ring-theory.local-rings.html#1421" class="Bound">l</a> <a id="1423" class="Symbol">=</a> <a id="1425" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1427" class="Symbol">(</a><a id="1428" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1433" href="ring-theory.local-rings.html#1421" class="Bound">l</a><a id="1434" class="Symbol">)</a> <a id="1436" href="ring-theory.local-rings.html#1130" class="Function">is-local-Ring</a>

<a id="1451" class="Keyword">module</a> <a id="1458" href="ring-theory.local-rings.html#1458" class="Module">_</a>
  <a id="1462" class="Symbol">{</a><a id="1463" href="ring-theory.local-rings.html#1463" class="Bound">l</a> <a id="1465" class="Symbol">:</a> <a id="1467" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1472" class="Symbol">}</a> <a id="1474" class="Symbol">(</a><a id="1475" href="ring-theory.local-rings.html#1475" class="Bound">R</a> <a id="1477" class="Symbol">:</a> <a id="1479" href="ring-theory.local-rings.html#1371" class="Function">Local-Ring</a> <a id="1490" href="ring-theory.local-rings.html#1463" class="Bound">l</a><a id="1491" class="Symbol">)</a>
  <a id="1495" class="Keyword">where</a>

  <a id="1504" href="ring-theory.local-rings.html#1504" class="Function">ring-Local-Ring</a> <a id="1520" class="Symbol">:</a> <a id="1522" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="1527" href="ring-theory.local-rings.html#1463" class="Bound">l</a>
  <a id="1531" href="ring-theory.local-rings.html#1504" class="Function">ring-Local-Ring</a> <a id="1547" class="Symbol">=</a> <a id="1549" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1553" href="ring-theory.local-rings.html#1475" class="Bound">R</a>

  <a id="1558" href="ring-theory.local-rings.html#1558" class="Function">set-Local-Ring</a> <a id="1573" class="Symbol">:</a> <a id="1575" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="1579" href="ring-theory.local-rings.html#1463" class="Bound">l</a>
  <a id="1583" href="ring-theory.local-rings.html#1558" class="Function">set-Local-Ring</a> <a id="1598" class="Symbol">=</a> <a id="1600" href="ring-theory.rings.html#2468" class="Function">set-Ring</a> <a id="1609" href="ring-theory.local-rings.html#1504" class="Function">ring-Local-Ring</a>

  <a id="1628" href="ring-theory.local-rings.html#1628" class="Function">type-Local-Ring</a> <a id="1644" class="Symbol">:</a> <a id="1646" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1649" href="ring-theory.local-rings.html#1463" class="Bound">l</a>
  <a id="1653" href="ring-theory.local-rings.html#1628" class="Function">type-Local-Ring</a> <a id="1669" class="Symbol">=</a> <a id="1671" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="1681" href="ring-theory.local-rings.html#1504" class="Function">ring-Local-Ring</a>

  <a id="1700" href="ring-theory.local-rings.html#1700" class="Function">is-local-ring-Local-Ring</a> <a id="1725" class="Symbol">:</a> <a id="1727" href="ring-theory.local-rings.html#1130" class="Function">is-local-Ring</a> <a id="1741" href="ring-theory.local-rings.html#1504" class="Function">ring-Local-Ring</a>
  <a id="1759" href="ring-theory.local-rings.html#1700" class="Function">is-local-ring-Local-Ring</a> <a id="1784" class="Symbol">=</a> <a id="1786" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1790" href="ring-theory.local-rings.html#1475" class="Bound">R</a>
</pre>