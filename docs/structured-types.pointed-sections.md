# Pointed sections of pointed maps

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="structured-types.pointed-sections.html" class="Module">structured-types.pointed-sections</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="256" class="Keyword">open</a> <a id="261" class="Keyword">import</a> <a id="268" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="296" class="Keyword">open</a> <a id="301" class="Keyword">import</a> <a id="308" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="344" class="Keyword">open</a> <a id="349" class="Keyword">import</a> <a id="356" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="386" class="Keyword">open</a> <a id="391" class="Keyword">import</a> <a id="398" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
</pre>
</details>

## Idea

A
{{#concept "pointed section" Disambiguation="pointed map" Agda=pointed-section}}
of a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` consists of a
pointed map `g : B →∗ A` equipped with a
[pointed homotopy](structured-types.pointed-homotopies.md) `H : f ∘∗ g ~∗ id`.

## Definitions

### The predicate of being a pointed section of a pointed map

<pre class="Agda"><a id="826" class="Keyword">module</a> <a id="833" href="structured-types.pointed-sections.html#833" class="Module">_</a>
  <a id="837" class="Symbol">{</a><a id="838" href="structured-types.pointed-sections.html#838" class="Bound">l1</a> <a id="841" href="structured-types.pointed-sections.html#841" class="Bound">l2</a> <a id="844" class="Symbol">:</a> <a id="846" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="851" class="Symbol">}</a> <a id="853" class="Symbol">{</a><a id="854" href="structured-types.pointed-sections.html#854" class="Bound">A</a> <a id="856" class="Symbol">:</a> <a id="858" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="871" href="structured-types.pointed-sections.html#838" class="Bound">l1</a><a id="873" class="Symbol">}</a> <a id="875" class="Symbol">{</a><a id="876" href="structured-types.pointed-sections.html#876" class="Bound">B</a> <a id="878" class="Symbol">:</a> <a id="880" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="893" href="structured-types.pointed-sections.html#841" class="Bound">l2</a><a id="895" class="Symbol">}</a> <a id="897" class="Symbol">(</a><a id="898" href="structured-types.pointed-sections.html#898" class="Bound">f</a> <a id="900" class="Symbol">:</a> <a id="902" href="structured-types.pointed-sections.html#854" class="Bound">A</a> <a id="904" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="907" href="structured-types.pointed-sections.html#876" class="Bound">B</a><a id="908" class="Symbol">)</a>
  <a id="912" class="Keyword">where</a>

  <a id="921" href="structured-types.pointed-sections.html#921" class="Function">is-pointed-section</a> <a id="940" class="Symbol">:</a> <a id="942" class="Symbol">(</a><a id="943" href="structured-types.pointed-sections.html#876" class="Bound">B</a> <a id="945" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="948" href="structured-types.pointed-sections.html#854" class="Bound">A</a><a id="949" class="Symbol">)</a> <a id="951" class="Symbol">→</a> <a id="953" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="956" href="structured-types.pointed-sections.html#841" class="Bound">l2</a>
  <a id="961" href="structured-types.pointed-sections.html#921" class="Function">is-pointed-section</a> <a id="980" href="structured-types.pointed-sections.html#980" class="Bound">g</a> <a id="982" class="Symbol">=</a> <a id="984" href="structured-types.pointed-sections.html#898" class="Bound">f</a> <a id="986" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="989" href="structured-types.pointed-sections.html#980" class="Bound">g</a> <a id="991" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="994" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a>
</pre>
### The type of pointed sections of a pointed map

<pre class="Agda"><a id="1073" class="Keyword">module</a> <a id="1080" href="structured-types.pointed-sections.html#1080" class="Module">_</a>
  <a id="1084" class="Symbol">{</a><a id="1085" href="structured-types.pointed-sections.html#1085" class="Bound">l1</a> <a id="1088" href="structured-types.pointed-sections.html#1088" class="Bound">l2</a> <a id="1091" class="Symbol">:</a> <a id="1093" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1098" class="Symbol">}</a> <a id="1100" class="Symbol">{</a><a id="1101" href="structured-types.pointed-sections.html#1101" class="Bound">A</a> <a id="1103" class="Symbol">:</a> <a id="1105" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1118" href="structured-types.pointed-sections.html#1085" class="Bound">l1</a><a id="1120" class="Symbol">}</a> <a id="1122" class="Symbol">{</a><a id="1123" href="structured-types.pointed-sections.html#1123" class="Bound">B</a> <a id="1125" class="Symbol">:</a> <a id="1127" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1140" href="structured-types.pointed-sections.html#1088" class="Bound">l2</a><a id="1142" class="Symbol">}</a> <a id="1144" class="Symbol">(</a><a id="1145" href="structured-types.pointed-sections.html#1145" class="Bound">f</a> <a id="1147" class="Symbol">:</a> <a id="1149" href="structured-types.pointed-sections.html#1101" class="Bound">A</a> <a id="1151" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1154" href="structured-types.pointed-sections.html#1123" class="Bound">B</a><a id="1155" class="Symbol">)</a>
  <a id="1159" class="Keyword">where</a>

  <a id="1168" href="structured-types.pointed-sections.html#1168" class="Function">pointed-section</a> <a id="1184" class="Symbol">:</a> <a id="1186" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1189" class="Symbol">(</a><a id="1190" href="structured-types.pointed-sections.html#1085" class="Bound">l1</a> <a id="1193" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1195" href="structured-types.pointed-sections.html#1088" class="Bound">l2</a><a id="1197" class="Symbol">)</a>
  <a id="1201" href="structured-types.pointed-sections.html#1168" class="Function">pointed-section</a> <a id="1217" class="Symbol">=</a>
    <a id="1223" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1225" class="Symbol">(</a><a id="1226" href="structured-types.pointed-sections.html#1123" class="Bound">B</a> <a id="1228" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1231" href="structured-types.pointed-sections.html#1101" class="Bound">A</a><a id="1232" class="Symbol">)</a> <a id="1234" class="Symbol">(</a><a id="1235" href="structured-types.pointed-sections.html#921" class="Function">is-pointed-section</a> <a id="1254" href="structured-types.pointed-sections.html#1145" class="Bound">f</a><a id="1255" class="Symbol">)</a>

  <a id="1260" class="Keyword">module</a> <a id="1267" href="structured-types.pointed-sections.html#1267" class="Module">_</a>
    <a id="1273" class="Symbol">(</a><a id="1274" href="structured-types.pointed-sections.html#1274" class="Bound">s</a> <a id="1276" class="Symbol">:</a> <a id="1278" href="structured-types.pointed-sections.html#1168" class="Function">pointed-section</a><a id="1293" class="Symbol">)</a>
    <a id="1299" class="Keyword">where</a>

    <a id="1310" href="structured-types.pointed-sections.html#1310" class="Function">pointed-map-pointed-section</a> <a id="1338" class="Symbol">:</a> <a id="1340" href="structured-types.pointed-sections.html#1123" class="Bound">B</a> <a id="1342" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1345" href="structured-types.pointed-sections.html#1101" class="Bound">A</a>
    <a id="1351" href="structured-types.pointed-sections.html#1310" class="Function">pointed-map-pointed-section</a> <a id="1379" class="Symbol">=</a> <a id="1381" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1385" href="structured-types.pointed-sections.html#1274" class="Bound">s</a>

    <a id="1392" href="structured-types.pointed-sections.html#1392" class="Function">is-pointed-section-pointed-section</a> <a id="1427" class="Symbol">:</a>
      <a id="1435" href="structured-types.pointed-sections.html#921" class="Function">is-pointed-section</a> <a id="1454" href="structured-types.pointed-sections.html#1145" class="Bound">f</a> <a id="1456" href="structured-types.pointed-sections.html#1310" class="Function">pointed-map-pointed-section</a>
    <a id="1488" href="structured-types.pointed-sections.html#1392" class="Function">is-pointed-section-pointed-section</a> <a id="1523" class="Symbol">=</a> <a id="1525" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1529" href="structured-types.pointed-sections.html#1274" class="Bound">s</a>

    <a id="1536" href="structured-types.pointed-sections.html#1536" class="Function">map-pointed-section</a> <a id="1556" class="Symbol">:</a> <a id="1558" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1576" href="structured-types.pointed-sections.html#1123" class="Bound">B</a> <a id="1578" class="Symbol">→</a> <a id="1580" href="structured-types.pointed-types.html#488" class="Function">type-Pointed-Type</a> <a id="1598" href="structured-types.pointed-sections.html#1101" class="Bound">A</a>
    <a id="1604" href="structured-types.pointed-sections.html#1536" class="Function">map-pointed-section</a> <a id="1624" class="Symbol">=</a> <a id="1626" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="1642" href="structured-types.pointed-sections.html#1310" class="Function">pointed-map-pointed-section</a>

    <a id="1675" href="structured-types.pointed-sections.html#1675" class="Function">preserves-point-pointed-map-pointed-section</a> <a id="1719" class="Symbol">:</a>
      <a id="1727" href="structured-types.pointed-sections.html#1536" class="Function">map-pointed-section</a> <a id="1747" class="Symbol">(</a><a id="1748" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1767" href="structured-types.pointed-sections.html#1123" class="Bound">B</a><a id="1768" class="Symbol">)</a> <a id="1770" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1772" href="structured-types.pointed-types.html#544" class="Function">point-Pointed-Type</a> <a id="1791" href="structured-types.pointed-sections.html#1101" class="Bound">A</a>
    <a id="1797" href="structured-types.pointed-sections.html#1675" class="Function">preserves-point-pointed-map-pointed-section</a> <a id="1841" class="Symbol">=</a>
      <a id="1849" href="structured-types.pointed-maps.html#1628" class="Function">preserves-point-pointed-map</a> <a id="1877" href="structured-types.pointed-sections.html#1310" class="Function">pointed-map-pointed-section</a>

    <a id="1910" href="structured-types.pointed-sections.html#1910" class="Function">is-section-pointed-section</a> <a id="1937" class="Symbol">:</a>
      <a id="1945" href="foundation-core.sections.html#1194" class="Function">is-section</a> <a id="1956" class="Symbol">(</a><a id="1957" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="1973" href="structured-types.pointed-sections.html#1145" class="Bound">f</a><a id="1974" class="Symbol">)</a> <a id="1976" href="structured-types.pointed-sections.html#1536" class="Function">map-pointed-section</a>
    <a id="2000" href="structured-types.pointed-sections.html#1910" class="Function">is-section-pointed-section</a> <a id="2027" class="Symbol">=</a>
      <a id="2035" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a> <a id="2053" href="structured-types.pointed-sections.html#1392" class="Function">is-pointed-section-pointed-section</a>

    <a id="2093" href="structured-types.pointed-sections.html#2093" class="Function">section-pointed-section</a> <a id="2117" class="Symbol">:</a> <a id="2119" href="foundation-core.sections.html#1373" class="Function">section</a> <a id="2127" class="Symbol">(</a><a id="2128" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2144" href="structured-types.pointed-sections.html#1145" class="Bound">f</a><a id="2145" class="Symbol">)</a>
    <a id="2151" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2155" href="structured-types.pointed-sections.html#2093" class="Function">section-pointed-section</a> <a id="2179" class="Symbol">=</a> <a id="2181" href="structured-types.pointed-sections.html#1536" class="Function">map-pointed-section</a>
    <a id="2205" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2209" href="structured-types.pointed-sections.html#2093" class="Function">section-pointed-section</a> <a id="2233" class="Symbol">=</a> <a id="2235" href="structured-types.pointed-sections.html#1910" class="Function">is-section-pointed-section</a>

    <a id="2267" href="structured-types.pointed-sections.html#2267" class="Function">coherence-point-is-section-pointed-section</a> <a id="2310" class="Symbol">:</a>
      <a id="2318" href="structured-types.pointed-homotopies.html#5970" class="Function">coherence-point-unpointed-htpy-pointed-Π</a>
        <a id="2367" class="Symbol">(</a> <a id="2369" href="structured-types.pointed-sections.html#1145" class="Bound">f</a> <a id="2371" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="2374" href="structured-types.pointed-sections.html#1310" class="Function">pointed-map-pointed-section</a><a id="2401" class="Symbol">)</a>
        <a id="2411" class="Symbol">(</a> <a id="2413" href="structured-types.pointed-maps.html#3573" class="Function">id-pointed-map</a><a id="2427" class="Symbol">)</a>
        <a id="2437" class="Symbol">(</a> <a id="2439" href="structured-types.pointed-sections.html#1910" class="Function">is-section-pointed-section</a><a id="2465" class="Symbol">)</a>
    <a id="2471" href="structured-types.pointed-sections.html#2267" class="Function">coherence-point-is-section-pointed-section</a> <a id="2514" class="Symbol">=</a>
      <a id="2522" href="structured-types.pointed-homotopies.html#6802" class="Function">coherence-point-pointed-htpy</a> <a id="2551" href="structured-types.pointed-sections.html#1392" class="Function">is-pointed-section-pointed-section</a>
</pre>