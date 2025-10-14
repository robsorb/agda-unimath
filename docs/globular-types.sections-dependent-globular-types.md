# Sections of dependent globular types

<pre class="Agda"><a id="49" class="Symbol">{-#</a> <a id="53" class="Keyword">OPTIONS</a> <a id="61" class="Pragma">--guardedness</a> <a id="75" class="Symbol">#-}</a>

<a id="80" class="Keyword">module</a> <a id="87" href="globular-types.sections-dependent-globular-types.html" class="Module">globular-types.sections-dependent-globular-types</a> <a id="136" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="globular-types.dependent-globular-types.html" class="Module">globular-types.dependent-globular-types</a>
<a id="284" class="Keyword">open</a> <a id="289" class="Keyword">import</a> <a id="296" href="globular-types.globular-types.html" class="Module">globular-types.globular-types</a>
</pre>
</details>

## Idea

Consider a [dependent globular type](globular-types.dependent-globular-types.md)
`H` over a [globular type](globular-types.globular-types.md) `G`. A
{{#concept "section" Disambiguation="dependent globular type" Agda=section-Dependent-Globular-Type}}
`f` of `H` consists of

```text
  s₀ : (x : G₀) → H₀ x
  s' : {x y : G₀} (y : H₀ x) (y' : H₀ x') → section (H' y y').
```

## Definitions

### Sections of dependent globular types

<pre class="Agda"><a id="791" class="Keyword">record</a>
  <a id="section-Dependent-Globular-Type"></a><a id="800" href="globular-types.sections-dependent-globular-types.html#800" class="Record">section-Dependent-Globular-Type</a>
    <a id="836" class="Symbol">{</a><a id="837" href="globular-types.sections-dependent-globular-types.html#837" class="Bound">l1</a> <a id="840" href="globular-types.sections-dependent-globular-types.html#840" class="Bound">l2</a> <a id="843" href="globular-types.sections-dependent-globular-types.html#843" class="Bound">l3</a> <a id="846" href="globular-types.sections-dependent-globular-types.html#846" class="Bound">l4</a> <a id="849" class="Symbol">:</a> <a id="851" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="856" class="Symbol">}</a> <a id="858" class="Symbol">{</a><a id="859" href="globular-types.sections-dependent-globular-types.html#859" class="Bound">G</a> <a id="861" class="Symbol">:</a> <a id="863" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="877" href="globular-types.sections-dependent-globular-types.html#837" class="Bound">l1</a> <a id="880" href="globular-types.sections-dependent-globular-types.html#840" class="Bound">l2</a><a id="882" class="Symbol">}</a>
    <a id="888" class="Symbol">(</a><a id="889" href="globular-types.sections-dependent-globular-types.html#889" class="Bound">H</a> <a id="891" class="Symbol">:</a> <a id="893" href="globular-types.dependent-globular-types.html#778" class="Record">Dependent-Globular-Type</a> <a id="917" href="globular-types.sections-dependent-globular-types.html#843" class="Bound">l3</a> <a id="920" href="globular-types.sections-dependent-globular-types.html#846" class="Bound">l4</a> <a id="923" href="globular-types.sections-dependent-globular-types.html#859" class="Bound">G</a><a id="924" class="Symbol">)</a> <a id="926" class="Symbol">:</a> <a id="928" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="931" class="Symbol">(</a><a id="932" href="globular-types.sections-dependent-globular-types.html#837" class="Bound">l1</a> <a id="935" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="937" href="globular-types.sections-dependent-globular-types.html#840" class="Bound">l2</a> <a id="940" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="942" href="globular-types.sections-dependent-globular-types.html#843" class="Bound">l3</a> <a id="945" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="947" href="globular-types.sections-dependent-globular-types.html#846" class="Bound">l4</a><a id="949" class="Symbol">)</a>
  <a id="953" class="Keyword">where</a>
  <a id="961" class="Keyword">coinductive</a>

  <a id="976" class="Keyword">field</a>
    <a id="section-Dependent-Globular-Type.0-cell-section-Dependent-Globular-Type"></a><a id="986" href="globular-types.sections-dependent-globular-types.html#986" class="Field">0-cell-section-Dependent-Globular-Type</a> <a id="1025" class="Symbol">:</a>
      <a id="1033" class="Symbol">(</a><a id="1034" href="globular-types.sections-dependent-globular-types.html#1034" class="Bound">x</a> <a id="1036" class="Symbol">:</a> <a id="1038" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1059" href="globular-types.sections-dependent-globular-types.html#859" class="Bound">G</a><a id="1060" class="Symbol">)</a> <a id="1062" class="Symbol">→</a> <a id="1064" href="globular-types.dependent-globular-types.html#937" class="Field">0-cell-Dependent-Globular-Type</a> <a id="1095" href="globular-types.sections-dependent-globular-types.html#889" class="Bound">H</a> <a id="1097" href="globular-types.sections-dependent-globular-types.html#1034" class="Bound">x</a>

  <a id="1102" class="Keyword">field</a>
    <a id="section-Dependent-Globular-Type.1-cell-section-section-Dependent-Globular-Type"></a><a id="1112" href="globular-types.sections-dependent-globular-types.html#1112" class="Field">1-cell-section-section-Dependent-Globular-Type</a> <a id="1159" class="Symbol">:</a>
      <a id="1167" class="Symbol">{</a><a id="1168" href="globular-types.sections-dependent-globular-types.html#1168" class="Bound">x</a> <a id="1170" href="globular-types.sections-dependent-globular-types.html#1170" class="Bound">x&#39;</a> <a id="1173" class="Symbol">:</a> <a id="1175" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1196" href="globular-types.sections-dependent-globular-types.html#859" class="Bound">G</a><a id="1197" class="Symbol">}</a> <a id="1199" class="Symbol">→</a>
      <a id="1207" href="globular-types.sections-dependent-globular-types.html#800" class="Record">section-Dependent-Globular-Type</a>
        <a id="1247" class="Symbol">(</a> <a id="1249" href="globular-types.dependent-globular-types.html#1011" class="Field">1-cell-dependent-globular-type-Dependent-Globular-Type</a> <a id="1304" href="globular-types.sections-dependent-globular-types.html#889" class="Bound">H</a>
          <a id="1316" class="Symbol">(</a> <a id="1318" href="globular-types.sections-dependent-globular-types.html#986" class="Field">0-cell-section-Dependent-Globular-Type</a> <a id="1357" href="globular-types.sections-dependent-globular-types.html#1168" class="Bound">x</a><a id="1358" class="Symbol">)</a>
          <a id="1370" class="Symbol">(</a> <a id="1372" href="globular-types.sections-dependent-globular-types.html#986" class="Field">0-cell-section-Dependent-Globular-Type</a> <a id="1411" href="globular-types.sections-dependent-globular-types.html#1170" class="Bound">x&#39;</a><a id="1413" class="Symbol">))</a>

<a id="1417" class="Keyword">open</a> <a id="1422" href="globular-types.sections-dependent-globular-types.html#800" class="Module">section-Dependent-Globular-Type</a> <a id="1454" class="Keyword">public</a>

<a id="1462" class="Keyword">module</a> <a id="1469" href="globular-types.sections-dependent-globular-types.html#1469" class="Module">_</a>
  <a id="1473" class="Symbol">{</a><a id="1474" href="globular-types.sections-dependent-globular-types.html#1474" class="Bound">l1</a> <a id="1477" href="globular-types.sections-dependent-globular-types.html#1477" class="Bound">l2</a> <a id="1480" href="globular-types.sections-dependent-globular-types.html#1480" class="Bound">l3</a> <a id="1483" href="globular-types.sections-dependent-globular-types.html#1483" class="Bound">l4</a> <a id="1486" class="Symbol">:</a> <a id="1488" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1493" class="Symbol">}</a> <a id="1495" class="Symbol">{</a><a id="1496" href="globular-types.sections-dependent-globular-types.html#1496" class="Bound">G</a> <a id="1498" class="Symbol">:</a> <a id="1500" href="globular-types.globular-types.html#4694" class="Record">Globular-Type</a> <a id="1514" href="globular-types.sections-dependent-globular-types.html#1474" class="Bound">l1</a> <a id="1517" href="globular-types.sections-dependent-globular-types.html#1477" class="Bound">l2</a><a id="1519" class="Symbol">}</a>
  <a id="1523" class="Symbol">(</a><a id="1524" href="globular-types.sections-dependent-globular-types.html#1524" class="Bound">H</a> <a id="1526" class="Symbol">:</a> <a id="1528" href="globular-types.dependent-globular-types.html#778" class="Record">Dependent-Globular-Type</a> <a id="1552" href="globular-types.sections-dependent-globular-types.html#1480" class="Bound">l3</a> <a id="1555" href="globular-types.sections-dependent-globular-types.html#1483" class="Bound">l4</a> <a id="1558" href="globular-types.sections-dependent-globular-types.html#1496" class="Bound">G</a><a id="1559" class="Symbol">)</a>
  <a id="1563" class="Symbol">(</a><a id="1564" href="globular-types.sections-dependent-globular-types.html#1564" class="Bound">s</a> <a id="1566" class="Symbol">:</a> <a id="1568" href="globular-types.sections-dependent-globular-types.html#800" class="Record">section-Dependent-Globular-Type</a> <a id="1600" href="globular-types.sections-dependent-globular-types.html#1524" class="Bound">H</a><a id="1601" class="Symbol">)</a>
  <a id="1605" class="Keyword">where</a>

  <a id="1614" href="globular-types.sections-dependent-globular-types.html#1614" class="Function">1-cell-section-Dependent-Globular-Type</a> <a id="1653" class="Symbol">:</a>
    <a id="1659" class="Symbol">{</a><a id="1660" href="globular-types.sections-dependent-globular-types.html#1660" class="Bound">x</a> <a id="1662" href="globular-types.sections-dependent-globular-types.html#1662" class="Bound">x&#39;</a> <a id="1665" class="Symbol">:</a> <a id="1667" href="globular-types.globular-types.html#4787" class="Field">0-cell-Globular-Type</a> <a id="1688" href="globular-types.sections-dependent-globular-types.html#1496" class="Bound">G</a><a id="1689" class="Symbol">}</a>
    <a id="1695" class="Symbol">(</a><a id="1696" href="globular-types.sections-dependent-globular-types.html#1696" class="Bound">f</a> <a id="1698" class="Symbol">:</a> <a id="1700" href="globular-types.globular-types.html#5823" class="Function">1-cell-Globular-Type</a> <a id="1721" href="globular-types.sections-dependent-globular-types.html#1496" class="Bound">G</a> <a id="1723" href="globular-types.sections-dependent-globular-types.html#1660" class="Bound">x</a> <a id="1725" href="globular-types.sections-dependent-globular-types.html#1662" class="Bound">x&#39;</a><a id="1727" class="Symbol">)</a> <a id="1729" class="Symbol">→</a>
    <a id="1735" href="globular-types.dependent-globular-types.html#1416" class="Function">1-cell-Dependent-Globular-Type</a> <a id="1766" href="globular-types.sections-dependent-globular-types.html#1524" class="Bound">H</a>
      <a id="1774" class="Symbol">(</a> <a id="1776" href="globular-types.sections-dependent-globular-types.html#986" class="Field">0-cell-section-Dependent-Globular-Type</a> <a id="1815" href="globular-types.sections-dependent-globular-types.html#1564" class="Bound">s</a> <a id="1817" href="globular-types.sections-dependent-globular-types.html#1660" class="Bound">x</a><a id="1818" class="Symbol">)</a>
      <a id="1826" class="Symbol">(</a> <a id="1828" href="globular-types.sections-dependent-globular-types.html#986" class="Field">0-cell-section-Dependent-Globular-Type</a> <a id="1867" href="globular-types.sections-dependent-globular-types.html#1564" class="Bound">s</a> <a id="1869" href="globular-types.sections-dependent-globular-types.html#1662" class="Bound">x&#39;</a><a id="1871" class="Symbol">)</a>
      <a id="1879" class="Symbol">(</a> <a id="1881" href="globular-types.sections-dependent-globular-types.html#1696" class="Bound">f</a><a id="1882" class="Symbol">)</a>
  <a id="1886" href="globular-types.sections-dependent-globular-types.html#1614" class="Function">1-cell-section-Dependent-Globular-Type</a> <a id="1925" class="Symbol">=</a>
    <a id="1931" href="globular-types.sections-dependent-globular-types.html#986" class="Field">0-cell-section-Dependent-Globular-Type</a>
      <a id="1976" class="Symbol">(</a> <a id="1978" href="globular-types.sections-dependent-globular-types.html#1112" class="Field">1-cell-section-section-Dependent-Globular-Type</a> <a id="2025" href="globular-types.sections-dependent-globular-types.html#1564" class="Bound">s</a><a id="2026" class="Symbol">)</a>
</pre>