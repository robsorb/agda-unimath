# Commuting squares of pointed maps

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="structured-types.commuting-squares-of-pointed-maps.html" class="Module">structured-types.commuting-squares-of-pointed-maps</a> <a id="104" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.commuting-squares-of-identifications.html" class="Module">foundation.commuting-squares-of-identifications</a>
<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="foundation.commuting-squares-of-maps.html" class="Module">foundation.commuting-squares-of-maps</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="410" class="Keyword">open</a> <a id="415" class="Keyword">import</a> <a id="422" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="448" class="Keyword">open</a> <a id="453" class="Keyword">import</a> <a id="460" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="487" class="Keyword">open</a> <a id="492" class="Keyword">import</a> <a id="499" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="545" class="Keyword">open</a> <a id="550" class="Keyword">import</a> <a id="557" href="structured-types.pointed-homotopies.html" class="Module">structured-types.pointed-homotopies</a>
<a id="593" class="Keyword">open</a> <a id="598" class="Keyword">import</a> <a id="605" href="structured-types.pointed-maps.html" class="Module">structured-types.pointed-maps</a>
<a id="635" class="Keyword">open</a> <a id="640" class="Keyword">import</a> <a id="647" href="structured-types.pointed-types.html" class="Module">structured-types.pointed-types</a>
<a id="678" class="Keyword">open</a> <a id="683" class="Keyword">import</a> <a id="690" href="structured-types.whiskering-pointed-homotopies-composition.html" class="Module">structured-types.whiskering-pointed-homotopies-composition</a>
</pre>
</details>

## Idea

Consider a square of [pointed maps](structured-types.pointed-maps.md)

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y.
          bottom
```

Such a square is said to be a
{{#concept "commuting square" Disambiguation="pointed maps" Agda=coherence-square-pointed-maps}}
of pointed maps if there is a
[pointed homotopy](structured-types.pointed-homotopies.md)

```text
  bottom ∘∗ left ~∗ right ∘∗ top.
```

Such a homotopy is referred to as the
{{#concept "coherence" Disambiguation="commuting squares of pointed maps" Agda=coherence-square-pointed-maps}}
of the commuting square of pointed maps.

## Definitions

### Coherences of commuting squares of pointed maps

<pre class="Agda"><a id="1536" class="Keyword">module</a> <a id="1543" href="structured-types.commuting-squares-of-pointed-maps.html#1543" class="Module">_</a>
  <a id="1547" class="Symbol">{</a><a id="1548" href="structured-types.commuting-squares-of-pointed-maps.html#1548" class="Bound">l1</a> <a id="1551" href="structured-types.commuting-squares-of-pointed-maps.html#1551" class="Bound">l2</a> <a id="1554" href="structured-types.commuting-squares-of-pointed-maps.html#1554" class="Bound">l3</a> <a id="1557" href="structured-types.commuting-squares-of-pointed-maps.html#1557" class="Bound">l4</a> <a id="1560" class="Symbol">:</a> <a id="1562" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1567" class="Symbol">}</a>
  <a id="1571" class="Symbol">{</a><a id="1572" href="structured-types.commuting-squares-of-pointed-maps.html#1572" class="Bound">A</a> <a id="1574" class="Symbol">:</a> <a id="1576" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1589" href="structured-types.commuting-squares-of-pointed-maps.html#1548" class="Bound">l1</a><a id="1591" class="Symbol">}</a> <a id="1593" class="Symbol">{</a><a id="1594" href="structured-types.commuting-squares-of-pointed-maps.html#1594" class="Bound">B</a> <a id="1596" class="Symbol">:</a> <a id="1598" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1611" href="structured-types.commuting-squares-of-pointed-maps.html#1551" class="Bound">l2</a><a id="1613" class="Symbol">}</a>
  <a id="1617" class="Symbol">{</a><a id="1618" href="structured-types.commuting-squares-of-pointed-maps.html#1618" class="Bound">C</a> <a id="1620" class="Symbol">:</a> <a id="1622" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1635" href="structured-types.commuting-squares-of-pointed-maps.html#1554" class="Bound">l3</a><a id="1637" class="Symbol">}</a> <a id="1639" class="Symbol">{</a><a id="1640" href="structured-types.commuting-squares-of-pointed-maps.html#1640" class="Bound">X</a> <a id="1642" class="Symbol">:</a> <a id="1644" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="1657" href="structured-types.commuting-squares-of-pointed-maps.html#1557" class="Bound">l4</a><a id="1659" class="Symbol">}</a>
  <a id="1663" class="Symbol">(</a><a id="1664" href="structured-types.commuting-squares-of-pointed-maps.html#1664" class="Bound">top</a> <a id="1668" class="Symbol">:</a> <a id="1670" href="structured-types.commuting-squares-of-pointed-maps.html#1618" class="Bound">C</a> <a id="1672" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1675" href="structured-types.commuting-squares-of-pointed-maps.html#1594" class="Bound">B</a><a id="1676" class="Symbol">)</a> <a id="1678" class="Symbol">(</a><a id="1679" href="structured-types.commuting-squares-of-pointed-maps.html#1679" class="Bound">left</a> <a id="1684" class="Symbol">:</a> <a id="1686" href="structured-types.commuting-squares-of-pointed-maps.html#1618" class="Bound">C</a> <a id="1688" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1691" href="structured-types.commuting-squares-of-pointed-maps.html#1572" class="Bound">A</a><a id="1692" class="Symbol">)</a> <a id="1694" class="Symbol">(</a><a id="1695" href="structured-types.commuting-squares-of-pointed-maps.html#1695" class="Bound">right</a> <a id="1701" class="Symbol">:</a> <a id="1703" href="structured-types.commuting-squares-of-pointed-maps.html#1594" class="Bound">B</a> <a id="1705" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1708" href="structured-types.commuting-squares-of-pointed-maps.html#1640" class="Bound">X</a><a id="1709" class="Symbol">)</a> <a id="1711" class="Symbol">(</a><a id="1712" href="structured-types.commuting-squares-of-pointed-maps.html#1712" class="Bound">bottom</a> <a id="1719" class="Symbol">:</a> <a id="1721" href="structured-types.commuting-squares-of-pointed-maps.html#1572" class="Bound">A</a> <a id="1723" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="1726" href="structured-types.commuting-squares-of-pointed-maps.html#1640" class="Bound">X</a><a id="1727" class="Symbol">)</a>
  <a id="1731" class="Keyword">where</a>

  <a id="1740" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="1770" class="Symbol">:</a> <a id="1772" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1775" class="Symbol">(</a><a id="1776" href="structured-types.commuting-squares-of-pointed-maps.html#1554" class="Bound">l3</a> <a id="1779" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1781" href="structured-types.commuting-squares-of-pointed-maps.html#1557" class="Bound">l4</a><a id="1783" class="Symbol">)</a>
  <a id="1787" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="1817" class="Symbol">=</a>
    <a id="1823" href="structured-types.commuting-squares-of-pointed-maps.html#1712" class="Bound">bottom</a> <a id="1830" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="1833" href="structured-types.commuting-squares-of-pointed-maps.html#1679" class="Bound">left</a> <a id="1838" href="structured-types.pointed-homotopies.html#6544" class="Function Operator">~∗</a> <a id="1841" href="structured-types.commuting-squares-of-pointed-maps.html#1695" class="Bound">right</a> <a id="1847" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="1850" href="structured-types.commuting-squares-of-pointed-maps.html#1664" class="Bound">top</a>

  <a id="1857" href="structured-types.commuting-squares-of-pointed-maps.html#1857" class="Function">coherence-square-maps-coherence-square-pointed-maps</a> <a id="1909" class="Symbol">:</a>
    <a id="1915" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="1945" class="Symbol">→</a>
    <a id="1951" href="foundation-core.commuting-squares-of-maps.html#1303" class="Function">coherence-square-maps</a>
      <a id="1979" class="Symbol">(</a> <a id="1981" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="1997" href="structured-types.commuting-squares-of-pointed-maps.html#1664" class="Bound">top</a><a id="2000" class="Symbol">)</a>
      <a id="2008" class="Symbol">(</a> <a id="2010" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2026" href="structured-types.commuting-squares-of-pointed-maps.html#1679" class="Bound">left</a><a id="2030" class="Symbol">)</a>
      <a id="2038" class="Symbol">(</a> <a id="2040" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2056" href="structured-types.commuting-squares-of-pointed-maps.html#1695" class="Bound">right</a><a id="2061" class="Symbol">)</a>
      <a id="2069" class="Symbol">(</a> <a id="2071" href="structured-types.pointed-maps.html#1532" class="Function">map-pointed-map</a> <a id="2087" href="structured-types.commuting-squares-of-pointed-maps.html#1712" class="Bound">bottom</a><a id="2093" class="Symbol">)</a>
  <a id="2097" href="structured-types.commuting-squares-of-pointed-maps.html#1857" class="Function">coherence-square-maps-coherence-square-pointed-maps</a> <a id="2149" class="Symbol">=</a>
    <a id="2155" href="structured-types.pointed-homotopies.html#6707" class="Function">htpy-pointed-htpy</a>
</pre>
## Operations

### Left whiskering of coherences of commuting squares of pointed maps

Consider a commuting square of pointed maps

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y
          bottom
```

and consider a pointed map `f : Y →∗ Z`. Then the square

```text
              top
       A -------------> X
       |                |
  left |                | f ∘∗ right
       ∨                ∨
       B -------------> Z
          f ∘∗ bottom
```

also commutes.

<pre class="Agda"><a id="2743" class="Keyword">module</a> <a id="2750" href="structured-types.commuting-squares-of-pointed-maps.html#2750" class="Module">_</a>
  <a id="2754" class="Symbol">{</a><a id="2755" href="structured-types.commuting-squares-of-pointed-maps.html#2755" class="Bound">l1</a> <a id="2758" href="structured-types.commuting-squares-of-pointed-maps.html#2758" class="Bound">l2</a> <a id="2761" href="structured-types.commuting-squares-of-pointed-maps.html#2761" class="Bound">l3</a> <a id="2764" href="structured-types.commuting-squares-of-pointed-maps.html#2764" class="Bound">l4</a> <a id="2767" href="structured-types.commuting-squares-of-pointed-maps.html#2767" class="Bound">l5</a> <a id="2770" class="Symbol">:</a> <a id="2772" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2777" class="Symbol">}</a>
  <a id="2781" class="Symbol">{</a><a id="2782" href="structured-types.commuting-squares-of-pointed-maps.html#2782" class="Bound">A</a> <a id="2784" class="Symbol">:</a> <a id="2786" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2799" href="structured-types.commuting-squares-of-pointed-maps.html#2755" class="Bound">l1</a><a id="2801" class="Symbol">}</a> <a id="2803" class="Symbol">{</a><a id="2804" href="structured-types.commuting-squares-of-pointed-maps.html#2804" class="Bound">B</a> <a id="2806" class="Symbol">:</a> <a id="2808" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2821" href="structured-types.commuting-squares-of-pointed-maps.html#2758" class="Bound">l2</a><a id="2823" class="Symbol">}</a>
  <a id="2827" class="Symbol">{</a><a id="2828" href="structured-types.commuting-squares-of-pointed-maps.html#2828" class="Bound">X</a> <a id="2830" class="Symbol">:</a> <a id="2832" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2845" href="structured-types.commuting-squares-of-pointed-maps.html#2761" class="Bound">l3</a><a id="2847" class="Symbol">}</a> <a id="2849" class="Symbol">{</a><a id="2850" href="structured-types.commuting-squares-of-pointed-maps.html#2850" class="Bound">Y</a> <a id="2852" class="Symbol">:</a> <a id="2854" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2867" href="structured-types.commuting-squares-of-pointed-maps.html#2764" class="Bound">l4</a><a id="2869" class="Symbol">}</a> <a id="2871" class="Symbol">{</a><a id="2872" href="structured-types.commuting-squares-of-pointed-maps.html#2872" class="Bound">Z</a> <a id="2874" class="Symbol">:</a> <a id="2876" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="2889" href="structured-types.commuting-squares-of-pointed-maps.html#2767" class="Bound">l5</a><a id="2891" class="Symbol">}</a>
  <a id="2895" class="Symbol">(</a><a id="2896" href="structured-types.commuting-squares-of-pointed-maps.html#2896" class="Bound">f</a> <a id="2898" class="Symbol">:</a> <a id="2900" href="structured-types.commuting-squares-of-pointed-maps.html#2850" class="Bound">Y</a> <a id="2902" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2905" href="structured-types.commuting-squares-of-pointed-maps.html#2872" class="Bound">Z</a><a id="2906" class="Symbol">)</a>
  <a id="2910" class="Symbol">(</a><a id="2911" href="structured-types.commuting-squares-of-pointed-maps.html#2911" class="Bound">top</a> <a id="2915" class="Symbol">:</a> <a id="2917" href="structured-types.commuting-squares-of-pointed-maps.html#2782" class="Bound">A</a> <a id="2919" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2922" href="structured-types.commuting-squares-of-pointed-maps.html#2828" class="Bound">X</a><a id="2923" class="Symbol">)</a> <a id="2925" class="Symbol">(</a><a id="2926" href="structured-types.commuting-squares-of-pointed-maps.html#2926" class="Bound">left</a> <a id="2931" class="Symbol">:</a> <a id="2933" href="structured-types.commuting-squares-of-pointed-maps.html#2782" class="Bound">A</a> <a id="2935" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2938" href="structured-types.commuting-squares-of-pointed-maps.html#2804" class="Bound">B</a><a id="2939" class="Symbol">)</a> <a id="2941" class="Symbol">(</a><a id="2942" href="structured-types.commuting-squares-of-pointed-maps.html#2942" class="Bound">right</a> <a id="2948" class="Symbol">:</a> <a id="2950" href="structured-types.commuting-squares-of-pointed-maps.html#2828" class="Bound">X</a> <a id="2952" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2955" href="structured-types.commuting-squares-of-pointed-maps.html#2850" class="Bound">Y</a><a id="2956" class="Symbol">)</a> <a id="2958" class="Symbol">(</a><a id="2959" href="structured-types.commuting-squares-of-pointed-maps.html#2959" class="Bound">bottom</a> <a id="2966" class="Symbol">:</a> <a id="2968" href="structured-types.commuting-squares-of-pointed-maps.html#2804" class="Bound">B</a> <a id="2970" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="2973" href="structured-types.commuting-squares-of-pointed-maps.html#2850" class="Bound">Y</a><a id="2974" class="Symbol">)</a>
  <a id="2978" class="Symbol">(</a><a id="2979" href="structured-types.commuting-squares-of-pointed-maps.html#2979" class="Bound">s</a> <a id="2981" class="Symbol">:</a> <a id="2983" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="3013" href="structured-types.commuting-squares-of-pointed-maps.html#2911" class="Bound">top</a> <a id="3017" href="structured-types.commuting-squares-of-pointed-maps.html#2926" class="Bound">left</a> <a id="3022" href="structured-types.commuting-squares-of-pointed-maps.html#2942" class="Bound">right</a> <a id="3028" href="structured-types.commuting-squares-of-pointed-maps.html#2959" class="Bound">bottom</a><a id="3034" class="Symbol">)</a>
  <a id="3038" class="Keyword">where</a>

  <a id="3047" href="structured-types.commuting-squares-of-pointed-maps.html#3047" class="Function">left-whisker-comp-coherence-square-pointed-maps</a> <a id="3095" class="Symbol">:</a>
    <a id="3101" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="3131" href="structured-types.commuting-squares-of-pointed-maps.html#2911" class="Bound">top</a> <a id="3135" href="structured-types.commuting-squares-of-pointed-maps.html#2926" class="Bound">left</a> <a id="3140" class="Symbol">(</a><a id="3141" href="structured-types.commuting-squares-of-pointed-maps.html#2896" class="Bound">f</a> <a id="3143" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="3146" href="structured-types.commuting-squares-of-pointed-maps.html#2942" class="Bound">right</a><a id="3151" class="Symbol">)</a> <a id="3153" class="Symbol">(</a><a id="3154" href="structured-types.commuting-squares-of-pointed-maps.html#2896" class="Bound">f</a> <a id="3156" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="3159" href="structured-types.commuting-squares-of-pointed-maps.html#2959" class="Bound">bottom</a><a id="3165" class="Symbol">)</a>
  <a id="3169" href="structured-types.commuting-squares-of-pointed-maps.html#3047" class="Function">left-whisker-comp-coherence-square-pointed-maps</a> <a id="3217" class="Symbol">=</a>
    <a id="3223" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
      <a id="3249" class="Symbol">(</a> <a id="3251" href="structured-types.pointed-homotopies.html#13283" class="Function">associative-comp-pointed-map</a> <a id="3280" href="structured-types.commuting-squares-of-pointed-maps.html#2896" class="Bound">f</a> <a id="3282" href="structured-types.commuting-squares-of-pointed-maps.html#2959" class="Bound">bottom</a> <a id="3289" href="structured-types.commuting-squares-of-pointed-maps.html#2926" class="Bound">left</a><a id="3293" class="Symbol">)</a>
      <a id="3301" class="Symbol">(</a> <a id="3303" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
        <a id="3331" class="Symbol">(</a> <a id="3333" href="structured-types.whiskering-pointed-homotopies-composition.html#4822" class="Function">left-whisker-comp-pointed-htpy</a> <a id="3364" href="structured-types.commuting-squares-of-pointed-maps.html#2896" class="Bound">f</a> <a id="3366" class="Symbol">_</a> <a id="3368" class="Symbol">_</a> <a id="3370" href="structured-types.commuting-squares-of-pointed-maps.html#2979" class="Bound">s</a><a id="3371" class="Symbol">)</a>
        <a id="3381" class="Symbol">(</a> <a id="3383" href="structured-types.pointed-homotopies.html#12607" class="Function">inv-associative-comp-pointed-map</a> <a id="3416" href="structured-types.commuting-squares-of-pointed-maps.html#2896" class="Bound">f</a> <a id="3418" href="structured-types.commuting-squares-of-pointed-maps.html#2942" class="Bound">right</a> <a id="3424" href="structured-types.commuting-squares-of-pointed-maps.html#2911" class="Bound">top</a><a id="3427" class="Symbol">))</a>
</pre>
### Left whiskering of coherences of commuting squares of pointed maps

Consider a commuting square of pointed maps

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y
          bottom
```

and consider a pointed map `f : Z →∗ A`. Then the square

```text
               f ∘∗ top
            A ----------> X
            |             |
  left ∘∗ f |             | right
            ∨             ∨
            B ----------> Z
                bottom
```

also commutes.

<pre class="Agda"><a id="3997" class="Keyword">module</a> <a id="4004" href="structured-types.commuting-squares-of-pointed-maps.html#4004" class="Module">_</a>
  <a id="4008" class="Symbol">{</a><a id="4009" href="structured-types.commuting-squares-of-pointed-maps.html#4009" class="Bound">l1</a> <a id="4012" href="structured-types.commuting-squares-of-pointed-maps.html#4012" class="Bound">l2</a> <a id="4015" href="structured-types.commuting-squares-of-pointed-maps.html#4015" class="Bound">l3</a> <a id="4018" href="structured-types.commuting-squares-of-pointed-maps.html#4018" class="Bound">l4</a> <a id="4021" href="structured-types.commuting-squares-of-pointed-maps.html#4021" class="Bound">l5</a> <a id="4024" class="Symbol">:</a> <a id="4026" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4031" class="Symbol">}</a>
  <a id="4035" class="Symbol">{</a><a id="4036" href="structured-types.commuting-squares-of-pointed-maps.html#4036" class="Bound">A</a> <a id="4038" class="Symbol">:</a> <a id="4040" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4053" href="structured-types.commuting-squares-of-pointed-maps.html#4009" class="Bound">l1</a><a id="4055" class="Symbol">}</a> <a id="4057" class="Symbol">{</a><a id="4058" href="structured-types.commuting-squares-of-pointed-maps.html#4058" class="Bound">B</a> <a id="4060" class="Symbol">:</a> <a id="4062" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4075" href="structured-types.commuting-squares-of-pointed-maps.html#4012" class="Bound">l2</a><a id="4077" class="Symbol">}</a>
  <a id="4081" class="Symbol">{</a><a id="4082" href="structured-types.commuting-squares-of-pointed-maps.html#4082" class="Bound">X</a> <a id="4084" class="Symbol">:</a> <a id="4086" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4099" href="structured-types.commuting-squares-of-pointed-maps.html#4015" class="Bound">l3</a><a id="4101" class="Symbol">}</a> <a id="4103" class="Symbol">{</a><a id="4104" href="structured-types.commuting-squares-of-pointed-maps.html#4104" class="Bound">Y</a> <a id="4106" class="Symbol">:</a> <a id="4108" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4121" href="structured-types.commuting-squares-of-pointed-maps.html#4018" class="Bound">l4</a><a id="4123" class="Symbol">}</a> <a id="4125" class="Symbol">{</a><a id="4126" href="structured-types.commuting-squares-of-pointed-maps.html#4126" class="Bound">Z</a> <a id="4128" class="Symbol">:</a> <a id="4130" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="4143" href="structured-types.commuting-squares-of-pointed-maps.html#4021" class="Bound">l5</a><a id="4145" class="Symbol">}</a>
  <a id="4149" class="Symbol">(</a><a id="4150" href="structured-types.commuting-squares-of-pointed-maps.html#4150" class="Bound">top</a> <a id="4154" class="Symbol">:</a> <a id="4156" href="structured-types.commuting-squares-of-pointed-maps.html#4036" class="Bound">A</a> <a id="4158" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="4161" href="structured-types.commuting-squares-of-pointed-maps.html#4082" class="Bound">X</a><a id="4162" class="Symbol">)</a> <a id="4164" class="Symbol">(</a><a id="4165" href="structured-types.commuting-squares-of-pointed-maps.html#4165" class="Bound">left</a> <a id="4170" class="Symbol">:</a> <a id="4172" href="structured-types.commuting-squares-of-pointed-maps.html#4036" class="Bound">A</a> <a id="4174" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="4177" href="structured-types.commuting-squares-of-pointed-maps.html#4058" class="Bound">B</a><a id="4178" class="Symbol">)</a> <a id="4180" class="Symbol">(</a><a id="4181" href="structured-types.commuting-squares-of-pointed-maps.html#4181" class="Bound">right</a> <a id="4187" class="Symbol">:</a> <a id="4189" href="structured-types.commuting-squares-of-pointed-maps.html#4082" class="Bound">X</a> <a id="4191" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="4194" href="structured-types.commuting-squares-of-pointed-maps.html#4104" class="Bound">Y</a><a id="4195" class="Symbol">)</a> <a id="4197" class="Symbol">(</a><a id="4198" href="structured-types.commuting-squares-of-pointed-maps.html#4198" class="Bound">bottom</a> <a id="4205" class="Symbol">:</a> <a id="4207" href="structured-types.commuting-squares-of-pointed-maps.html#4058" class="Bound">B</a> <a id="4209" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="4212" href="structured-types.commuting-squares-of-pointed-maps.html#4104" class="Bound">Y</a><a id="4213" class="Symbol">)</a>
  <a id="4217" class="Symbol">(</a><a id="4218" href="structured-types.commuting-squares-of-pointed-maps.html#4218" class="Bound">s</a> <a id="4220" class="Symbol">:</a> <a id="4222" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="4252" href="structured-types.commuting-squares-of-pointed-maps.html#4150" class="Bound">top</a> <a id="4256" href="structured-types.commuting-squares-of-pointed-maps.html#4165" class="Bound">left</a> <a id="4261" href="structured-types.commuting-squares-of-pointed-maps.html#4181" class="Bound">right</a> <a id="4267" href="structured-types.commuting-squares-of-pointed-maps.html#4198" class="Bound">bottom</a><a id="4273" class="Symbol">)</a>
  <a id="4277" class="Symbol">(</a><a id="4278" href="structured-types.commuting-squares-of-pointed-maps.html#4278" class="Bound">f</a> <a id="4280" class="Symbol">:</a> <a id="4282" href="structured-types.commuting-squares-of-pointed-maps.html#4126" class="Bound">Z</a> <a id="4284" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="4287" href="structured-types.commuting-squares-of-pointed-maps.html#4036" class="Bound">A</a><a id="4288" class="Symbol">)</a>
  <a id="4292" class="Keyword">where</a>

  <a id="4301" href="structured-types.commuting-squares-of-pointed-maps.html#4301" class="Function">right-whisker-comp-coherence-square-pointed-maps</a> <a id="4350" class="Symbol">:</a>
    <a id="4356" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="4386" class="Symbol">(</a><a id="4387" href="structured-types.commuting-squares-of-pointed-maps.html#4150" class="Bound">top</a> <a id="4391" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="4394" href="structured-types.commuting-squares-of-pointed-maps.html#4278" class="Bound">f</a><a id="4395" class="Symbol">)</a> <a id="4397" class="Symbol">(</a><a id="4398" href="structured-types.commuting-squares-of-pointed-maps.html#4165" class="Bound">left</a> <a id="4403" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="4406" href="structured-types.commuting-squares-of-pointed-maps.html#4278" class="Bound">f</a><a id="4407" class="Symbol">)</a> <a id="4409" href="structured-types.commuting-squares-of-pointed-maps.html#4181" class="Bound">right</a> <a id="4415" href="structured-types.commuting-squares-of-pointed-maps.html#4198" class="Bound">bottom</a>
  <a id="4424" href="structured-types.commuting-squares-of-pointed-maps.html#4301" class="Function">right-whisker-comp-coherence-square-pointed-maps</a> <a id="4473" class="Symbol">=</a>
    <a id="4479" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
      <a id="4505" class="Symbol">(</a> <a id="4507" href="structured-types.pointed-homotopies.html#12607" class="Function">inv-associative-comp-pointed-map</a> <a id="4540" href="structured-types.commuting-squares-of-pointed-maps.html#4198" class="Bound">bottom</a> <a id="4547" href="structured-types.commuting-squares-of-pointed-maps.html#4165" class="Bound">left</a> <a id="4552" href="structured-types.commuting-squares-of-pointed-maps.html#4278" class="Bound">f</a><a id="4553" class="Symbol">)</a>
      <a id="4561" class="Symbol">(</a> <a id="4563" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
        <a id="4591" class="Symbol">(</a> <a id="4593" href="structured-types.whiskering-pointed-homotopies-composition.html#7011" class="Function">right-whisker-comp-pointed-htpy</a> <a id="4625" class="Symbol">_</a> <a id="4627" class="Symbol">_</a> <a id="4629" href="structured-types.commuting-squares-of-pointed-maps.html#4218" class="Bound">s</a> <a id="4631" href="structured-types.commuting-squares-of-pointed-maps.html#4278" class="Bound">f</a><a id="4632" class="Symbol">)</a>
        <a id="4642" class="Symbol">(</a> <a id="4644" href="structured-types.pointed-homotopies.html#13283" class="Function">associative-comp-pointed-map</a> <a id="4673" href="structured-types.commuting-squares-of-pointed-maps.html#4181" class="Bound">right</a> <a id="4679" href="structured-types.commuting-squares-of-pointed-maps.html#4150" class="Bound">top</a> <a id="4683" href="structured-types.commuting-squares-of-pointed-maps.html#4278" class="Bound">f</a><a id="4684" class="Symbol">))</a>
</pre>
### Horizontal pasting of coherences of commuting squares of pointed maps

Consider two commuting squares of pointed maps, as in the diagram

```text
            top-left         top-right
       A -------------> B --------------> C
       |                |                 |
  left |                | middle          | right
       ∨                ∨                 ∨
       D -------------> E --------------> F
          bottom-left      bottom-right
```

with pointed homotopies

```text
  H : bottom-left ∘∗ left ~∗ middle ∘∗ top
  K : bottom-right ∘∗ middle ~∗ right ∘∗ top-right.
```

The
{{#concept "horizontal pasting" Disambiguation="commuting squares of pointed maps" Agda=horizontal-pasting-coherence-square-pointed-maps}}
of these coherences of commuting squares of pointed maps is the coherence of the
commuting square

```text
             top-right ∘∗ top-left
       A -----------------------------> C
       |                                |
  left |                                | right
       ∨                                ∨
       D -----------------------------> F
          bottom-right ∘∗ bottom-left
```

obtained by concatenation of the following three pointed homotopies:

```text
  (bottom-right ∘∗ bottom-left) ∘∗ left
  ~∗ (bottom-right ∘∗ middle) ∘∗ top-left
  ~∗ bottom-right ∘∗ (middle ∘∗ top-left)
  ~∗ right ∘∗ (top-right ∘∗ top-left).
```

The first and third homotopy in this concatenation are the whiskerings of
coherences of
[commuting triangles of pointed maps](structured-types.commuting-triangles-of-pointed-maps.md).

<pre class="Agda"><a id="6268" class="Keyword">module</a> <a id="6275" href="structured-types.commuting-squares-of-pointed-maps.html#6275" class="Module">_</a>
  <a id="6279" class="Symbol">{</a><a id="6280" href="structured-types.commuting-squares-of-pointed-maps.html#6280" class="Bound">l1</a> <a id="6283" href="structured-types.commuting-squares-of-pointed-maps.html#6283" class="Bound">l2</a> <a id="6286" href="structured-types.commuting-squares-of-pointed-maps.html#6286" class="Bound">l3</a> <a id="6289" href="structured-types.commuting-squares-of-pointed-maps.html#6289" class="Bound">l4</a> <a id="6292" href="structured-types.commuting-squares-of-pointed-maps.html#6292" class="Bound">l5</a> <a id="6295" href="structured-types.commuting-squares-of-pointed-maps.html#6295" class="Bound">l6</a> <a id="6298" class="Symbol">:</a> <a id="6300" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6305" class="Symbol">}</a>
  <a id="6309" class="Symbol">{</a><a id="6310" href="structured-types.commuting-squares-of-pointed-maps.html#6310" class="Bound">A</a> <a id="6312" class="Symbol">:</a> <a id="6314" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6327" href="structured-types.commuting-squares-of-pointed-maps.html#6280" class="Bound">l1</a><a id="6329" class="Symbol">}</a> <a id="6331" class="Symbol">{</a><a id="6332" href="structured-types.commuting-squares-of-pointed-maps.html#6332" class="Bound">B</a> <a id="6334" class="Symbol">:</a> <a id="6336" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6349" href="structured-types.commuting-squares-of-pointed-maps.html#6283" class="Bound">l2</a><a id="6351" class="Symbol">}</a>
  <a id="6355" class="Symbol">{</a><a id="6356" href="structured-types.commuting-squares-of-pointed-maps.html#6356" class="Bound">X</a> <a id="6358" class="Symbol">:</a> <a id="6360" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6373" href="structured-types.commuting-squares-of-pointed-maps.html#6286" class="Bound">l3</a><a id="6375" class="Symbol">}</a> <a id="6377" class="Symbol">{</a><a id="6378" href="structured-types.commuting-squares-of-pointed-maps.html#6378" class="Bound">Y</a> <a id="6380" class="Symbol">:</a> <a id="6382" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6395" href="structured-types.commuting-squares-of-pointed-maps.html#6289" class="Bound">l4</a><a id="6397" class="Symbol">}</a>
  <a id="6401" class="Symbol">{</a><a id="6402" href="structured-types.commuting-squares-of-pointed-maps.html#6402" class="Bound">U</a> <a id="6404" class="Symbol">:</a> <a id="6406" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6419" href="structured-types.commuting-squares-of-pointed-maps.html#6292" class="Bound">l5</a><a id="6421" class="Symbol">}</a> <a id="6423" class="Symbol">{</a><a id="6424" href="structured-types.commuting-squares-of-pointed-maps.html#6424" class="Bound">V</a> <a id="6426" class="Symbol">:</a> <a id="6428" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="6441" href="structured-types.commuting-squares-of-pointed-maps.html#6295" class="Bound">l6</a><a id="6443" class="Symbol">}</a>
  <a id="6447" class="Symbol">(</a><a id="6448" href="structured-types.commuting-squares-of-pointed-maps.html#6448" class="Bound">top-left</a> <a id="6457" class="Symbol">:</a> <a id="6459" href="structured-types.commuting-squares-of-pointed-maps.html#6310" class="Bound">A</a> <a id="6461" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6464" href="structured-types.commuting-squares-of-pointed-maps.html#6356" class="Bound">X</a><a id="6465" class="Symbol">)</a> <a id="6467" class="Symbol">(</a><a id="6468" href="structured-types.commuting-squares-of-pointed-maps.html#6468" class="Bound">top-right</a> <a id="6478" class="Symbol">:</a> <a id="6480" href="structured-types.commuting-squares-of-pointed-maps.html#6356" class="Bound">X</a> <a id="6482" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6485" href="structured-types.commuting-squares-of-pointed-maps.html#6402" class="Bound">U</a><a id="6486" class="Symbol">)</a>
  <a id="6490" class="Symbol">(</a><a id="6491" href="structured-types.commuting-squares-of-pointed-maps.html#6491" class="Bound">left</a> <a id="6496" class="Symbol">:</a> <a id="6498" href="structured-types.commuting-squares-of-pointed-maps.html#6310" class="Bound">A</a> <a id="6500" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6503" href="structured-types.commuting-squares-of-pointed-maps.html#6332" class="Bound">B</a><a id="6504" class="Symbol">)</a> <a id="6506" class="Symbol">(</a><a id="6507" href="structured-types.commuting-squares-of-pointed-maps.html#6507" class="Bound">middle</a> <a id="6514" class="Symbol">:</a> <a id="6516" href="structured-types.commuting-squares-of-pointed-maps.html#6356" class="Bound">X</a> <a id="6518" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6521" href="structured-types.commuting-squares-of-pointed-maps.html#6378" class="Bound">Y</a><a id="6522" class="Symbol">)</a> <a id="6524" class="Symbol">(</a><a id="6525" href="structured-types.commuting-squares-of-pointed-maps.html#6525" class="Bound">right</a> <a id="6531" class="Symbol">:</a> <a id="6533" href="structured-types.commuting-squares-of-pointed-maps.html#6402" class="Bound">U</a> <a id="6535" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6538" href="structured-types.commuting-squares-of-pointed-maps.html#6424" class="Bound">V</a><a id="6539" class="Symbol">)</a>
  <a id="6543" class="Symbol">(</a><a id="6544" href="structured-types.commuting-squares-of-pointed-maps.html#6544" class="Bound">bottom-left</a> <a id="6556" class="Symbol">:</a> <a id="6558" href="structured-types.commuting-squares-of-pointed-maps.html#6332" class="Bound">B</a> <a id="6560" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6563" href="structured-types.commuting-squares-of-pointed-maps.html#6378" class="Bound">Y</a><a id="6564" class="Symbol">)</a> <a id="6566" class="Symbol">(</a><a id="6567" href="structured-types.commuting-squares-of-pointed-maps.html#6567" class="Bound">bottom-right</a> <a id="6580" class="Symbol">:</a> <a id="6582" href="structured-types.commuting-squares-of-pointed-maps.html#6378" class="Bound">Y</a> <a id="6584" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="6587" href="structured-types.commuting-squares-of-pointed-maps.html#6424" class="Bound">V</a><a id="6588" class="Symbol">)</a>
  <a id="6592" class="Symbol">(</a><a id="6593" href="structured-types.commuting-squares-of-pointed-maps.html#6593" class="Bound">left-square</a> <a id="6605" class="Symbol">:</a>
    <a id="6611" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="6641" href="structured-types.commuting-squares-of-pointed-maps.html#6448" class="Bound">top-left</a> <a id="6650" href="structured-types.commuting-squares-of-pointed-maps.html#6491" class="Bound">left</a> <a id="6655" href="structured-types.commuting-squares-of-pointed-maps.html#6507" class="Bound">middle</a> <a id="6662" href="structured-types.commuting-squares-of-pointed-maps.html#6544" class="Bound">bottom-left</a><a id="6673" class="Symbol">)</a>
  <a id="6677" class="Symbol">(</a><a id="6678" href="structured-types.commuting-squares-of-pointed-maps.html#6678" class="Bound">right-square</a> <a id="6691" class="Symbol">:</a>
    <a id="6697" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="6727" href="structured-types.commuting-squares-of-pointed-maps.html#6468" class="Bound">top-right</a> <a id="6737" href="structured-types.commuting-squares-of-pointed-maps.html#6507" class="Bound">middle</a> <a id="6744" href="structured-types.commuting-squares-of-pointed-maps.html#6525" class="Bound">right</a> <a id="6750" href="structured-types.commuting-squares-of-pointed-maps.html#6567" class="Bound">bottom-right</a><a id="6762" class="Symbol">)</a>
  <a id="6766" class="Keyword">where</a>

  <a id="6775" href="structured-types.commuting-squares-of-pointed-maps.html#6775" class="Function">horizontal-pasting-coherence-square-pointed-maps</a> <a id="6824" class="Symbol">:</a>
    <a id="6830" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a>
      <a id="6866" class="Symbol">(</a> <a id="6868" href="structured-types.commuting-squares-of-pointed-maps.html#6468" class="Bound">top-right</a> <a id="6878" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="6881" href="structured-types.commuting-squares-of-pointed-maps.html#6448" class="Bound">top-left</a><a id="6889" class="Symbol">)</a>
      <a id="6897" class="Symbol">(</a> <a id="6899" href="structured-types.commuting-squares-of-pointed-maps.html#6491" class="Bound">left</a><a id="6903" class="Symbol">)</a>
      <a id="6911" class="Symbol">(</a> <a id="6913" href="structured-types.commuting-squares-of-pointed-maps.html#6525" class="Bound">right</a><a id="6918" class="Symbol">)</a>
      <a id="6926" class="Symbol">(</a> <a id="6928" href="structured-types.commuting-squares-of-pointed-maps.html#6567" class="Bound">bottom-right</a> <a id="6941" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="6944" href="structured-types.commuting-squares-of-pointed-maps.html#6544" class="Bound">bottom-left</a><a id="6955" class="Symbol">)</a>
  <a id="6959" href="structured-types.commuting-squares-of-pointed-maps.html#6775" class="Function">horizontal-pasting-coherence-square-pointed-maps</a> <a id="7008" class="Symbol">=</a>
    <a id="7014" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
      <a id="7040" class="Symbol">(</a> <a id="7042" href="structured-types.commuting-squares-of-pointed-maps.html#3047" class="Function">left-whisker-comp-coherence-square-pointed-maps</a>
        <a id="7098" class="Symbol">(</a> <a id="7100" href="structured-types.commuting-squares-of-pointed-maps.html#6567" class="Bound">bottom-right</a><a id="7112" class="Symbol">)</a>
        <a id="7122" class="Symbol">(</a> <a id="7124" href="structured-types.commuting-squares-of-pointed-maps.html#6448" class="Bound">top-left</a><a id="7132" class="Symbol">)</a>
        <a id="7142" class="Symbol">(</a> <a id="7144" href="structured-types.commuting-squares-of-pointed-maps.html#6491" class="Bound">left</a><a id="7148" class="Symbol">)</a>
        <a id="7158" class="Symbol">(</a> <a id="7160" href="structured-types.commuting-squares-of-pointed-maps.html#6507" class="Bound">middle</a><a id="7166" class="Symbol">)</a>
        <a id="7176" class="Symbol">(</a> <a id="7178" href="structured-types.commuting-squares-of-pointed-maps.html#6544" class="Bound">bottom-left</a><a id="7189" class="Symbol">)</a>
        <a id="7199" class="Symbol">(</a> <a id="7201" href="structured-types.commuting-squares-of-pointed-maps.html#6593" class="Bound">left-square</a><a id="7212" class="Symbol">))</a>
      <a id="7221" class="Symbol">(</a> <a id="7223" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
        <a id="7251" class="Symbol">(</a> <a id="7253" href="structured-types.pointed-homotopies.html#13283" class="Function">associative-comp-pointed-map</a> <a id="7282" href="structured-types.commuting-squares-of-pointed-maps.html#6567" class="Bound">bottom-right</a> <a id="7295" href="structured-types.commuting-squares-of-pointed-maps.html#6507" class="Bound">middle</a> <a id="7302" href="structured-types.commuting-squares-of-pointed-maps.html#6448" class="Bound">top-left</a><a id="7310" class="Symbol">)</a>
        <a id="7320" class="Symbol">(</a> <a id="7322" href="structured-types.commuting-squares-of-pointed-maps.html#4301" class="Function">right-whisker-comp-coherence-square-pointed-maps</a>
          <a id="7381" class="Symbol">(</a> <a id="7383" href="structured-types.commuting-squares-of-pointed-maps.html#6468" class="Bound">top-right</a><a id="7392" class="Symbol">)</a>
          <a id="7404" class="Symbol">(</a> <a id="7406" href="structured-types.commuting-squares-of-pointed-maps.html#6507" class="Bound">middle</a><a id="7412" class="Symbol">)</a>
          <a id="7424" class="Symbol">(</a> <a id="7426" href="structured-types.commuting-squares-of-pointed-maps.html#6525" class="Bound">right</a><a id="7431" class="Symbol">)</a>
          <a id="7443" class="Symbol">(</a> <a id="7445" href="structured-types.commuting-squares-of-pointed-maps.html#6567" class="Bound">bottom-right</a><a id="7457" class="Symbol">)</a>
          <a id="7469" class="Symbol">(</a> <a id="7471" href="structured-types.commuting-squares-of-pointed-maps.html#6678" class="Bound">right-square</a><a id="7483" class="Symbol">)</a>
          <a id="7495" class="Symbol">(</a> <a id="7497" href="structured-types.commuting-squares-of-pointed-maps.html#6448" class="Bound">top-left</a><a id="7505" class="Symbol">)))</a>
</pre>
### Vertical pasting of coherences of commuting squares of pointed maps

Consider two commuting squares of pointed maps, as in the diagram

```text
                   top
              A --------> B
              |           |
     top-left |           | top-right
              ∨  middle   ∨
              C --------> D
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              E --------> F
                 bottom
```

with pointed homotopies

```text
  H : middle ∘∗ top-left ~∗ top-right ∘∗ top
  K : bottom ∘∗ bottom-left ~∗  bottom-right ∘∗ middle.
```

The
{{#concept "vertical pasting" Disambiguation="commuting squares of pointed maps" Agda=vertical-pasting-coherence-square-pointed-maps}}
of these coherences of commuting squares of pointed maps is the coherence of the
commuting square

```text
                               top
                          A --------> B
                          |           |
  bottom-left ∘∗ top-left |           | bottom-right ∘∗ top-right
                          ∨           ∨
                          E --------> F
                             bottom
```

obtained by concatenation of the following three pointed homotopies:

```text
  bottom ∘∗ (bottom-left ∘∗ top-left)
  ~∗ bottom-right ∘∗ (middle ∘∗ top-left)
  ~∗ (bottom-right ∘∗ middle) ∘∗ top-left
  ~∗ (bottom-right ∘∗ top-right) ∘∗ top.
```

The first and third homotopy in this concatenation are the whiskerings of
coherences of
[commuting triangles of pointed maps](structured-types.commuting-triangles-of-pointed-maps.md).

<pre class="Agda"><a id="9115" class="Keyword">module</a> <a id="9122" href="structured-types.commuting-squares-of-pointed-maps.html#9122" class="Module">_</a>
  <a id="9126" class="Symbol">{</a><a id="9127" href="structured-types.commuting-squares-of-pointed-maps.html#9127" class="Bound">l1</a> <a id="9130" href="structured-types.commuting-squares-of-pointed-maps.html#9130" class="Bound">l2</a> <a id="9133" href="structured-types.commuting-squares-of-pointed-maps.html#9133" class="Bound">l3</a> <a id="9136" href="structured-types.commuting-squares-of-pointed-maps.html#9136" class="Bound">l4</a> <a id="9139" href="structured-types.commuting-squares-of-pointed-maps.html#9139" class="Bound">l5</a> <a id="9142" href="structured-types.commuting-squares-of-pointed-maps.html#9142" class="Bound">l6</a> <a id="9145" class="Symbol">:</a> <a id="9147" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="9152" class="Symbol">}</a>
  <a id="9156" class="Symbol">{</a><a id="9157" href="structured-types.commuting-squares-of-pointed-maps.html#9157" class="Bound">A</a> <a id="9159" class="Symbol">:</a> <a id="9161" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9174" href="structured-types.commuting-squares-of-pointed-maps.html#9127" class="Bound">l1</a><a id="9176" class="Symbol">}</a> <a id="9178" class="Symbol">{</a><a id="9179" href="structured-types.commuting-squares-of-pointed-maps.html#9179" class="Bound">B</a> <a id="9181" class="Symbol">:</a> <a id="9183" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9196" href="structured-types.commuting-squares-of-pointed-maps.html#9130" class="Bound">l2</a><a id="9198" class="Symbol">}</a>
  <a id="9202" class="Symbol">{</a><a id="9203" href="structured-types.commuting-squares-of-pointed-maps.html#9203" class="Bound">C</a> <a id="9205" class="Symbol">:</a> <a id="9207" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9220" href="structured-types.commuting-squares-of-pointed-maps.html#9133" class="Bound">l3</a><a id="9222" class="Symbol">}</a> <a id="9224" class="Symbol">{</a><a id="9225" href="structured-types.commuting-squares-of-pointed-maps.html#9225" class="Bound">D</a> <a id="9227" class="Symbol">:</a> <a id="9229" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9242" href="structured-types.commuting-squares-of-pointed-maps.html#9136" class="Bound">l4</a><a id="9244" class="Symbol">}</a>
  <a id="9248" class="Symbol">{</a><a id="9249" href="structured-types.commuting-squares-of-pointed-maps.html#9249" class="Bound">E</a> <a id="9251" class="Symbol">:</a> <a id="9253" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9266" href="structured-types.commuting-squares-of-pointed-maps.html#9139" class="Bound">l5</a><a id="9268" class="Symbol">}</a> <a id="9270" class="Symbol">{</a><a id="9271" href="structured-types.commuting-squares-of-pointed-maps.html#9271" class="Bound">F</a> <a id="9273" class="Symbol">:</a> <a id="9275" href="structured-types.pointed-types.html#355" class="Function">Pointed-Type</a> <a id="9288" href="structured-types.commuting-squares-of-pointed-maps.html#9142" class="Bound">l6</a><a id="9290" class="Symbol">}</a>
  <a id="9294" class="Symbol">(</a><a id="9295" href="structured-types.commuting-squares-of-pointed-maps.html#9295" class="Bound">top</a> <a id="9299" class="Symbol">:</a> <a id="9301" href="structured-types.commuting-squares-of-pointed-maps.html#9157" class="Bound">A</a> <a id="9303" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9306" href="structured-types.commuting-squares-of-pointed-maps.html#9179" class="Bound">B</a><a id="9307" class="Symbol">)</a> <a id="9309" class="Symbol">(</a><a id="9310" href="structured-types.commuting-squares-of-pointed-maps.html#9310" class="Bound">top-left</a> <a id="9319" class="Symbol">:</a> <a id="9321" href="structured-types.commuting-squares-of-pointed-maps.html#9157" class="Bound">A</a> <a id="9323" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9326" href="structured-types.commuting-squares-of-pointed-maps.html#9203" class="Bound">C</a><a id="9327" class="Symbol">)</a> <a id="9329" class="Symbol">(</a><a id="9330" href="structured-types.commuting-squares-of-pointed-maps.html#9330" class="Bound">top-right</a> <a id="9340" class="Symbol">:</a> <a id="9342" href="structured-types.commuting-squares-of-pointed-maps.html#9179" class="Bound">B</a> <a id="9344" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9347" href="structured-types.commuting-squares-of-pointed-maps.html#9225" class="Bound">D</a><a id="9348" class="Symbol">)</a> <a id="9350" class="Symbol">(</a><a id="9351" href="structured-types.commuting-squares-of-pointed-maps.html#9351" class="Bound">middle</a> <a id="9358" class="Symbol">:</a> <a id="9360" href="structured-types.commuting-squares-of-pointed-maps.html#9203" class="Bound">C</a> <a id="9362" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9365" href="structured-types.commuting-squares-of-pointed-maps.html#9225" class="Bound">D</a><a id="9366" class="Symbol">)</a>
  <a id="9370" class="Symbol">(</a><a id="9371" href="structured-types.commuting-squares-of-pointed-maps.html#9371" class="Bound">bottom-left</a> <a id="9383" class="Symbol">:</a> <a id="9385" href="structured-types.commuting-squares-of-pointed-maps.html#9203" class="Bound">C</a> <a id="9387" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9390" href="structured-types.commuting-squares-of-pointed-maps.html#9249" class="Bound">E</a><a id="9391" class="Symbol">)</a> <a id="9393" class="Symbol">(</a><a id="9394" href="structured-types.commuting-squares-of-pointed-maps.html#9394" class="Bound">bottom-right</a> <a id="9407" class="Symbol">:</a> <a id="9409" href="structured-types.commuting-squares-of-pointed-maps.html#9225" class="Bound">D</a> <a id="9411" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9414" href="structured-types.commuting-squares-of-pointed-maps.html#9271" class="Bound">F</a><a id="9415" class="Symbol">)</a> <a id="9417" class="Symbol">(</a><a id="9418" href="structured-types.commuting-squares-of-pointed-maps.html#9418" class="Bound">bottom</a> <a id="9425" class="Symbol">:</a> <a id="9427" href="structured-types.commuting-squares-of-pointed-maps.html#9249" class="Bound">E</a> <a id="9429" href="structured-types.pointed-maps.html#1157" class="Function Operator">→∗</a> <a id="9432" href="structured-types.commuting-squares-of-pointed-maps.html#9271" class="Bound">F</a><a id="9433" class="Symbol">)</a>
  <a id="9437" class="Symbol">(</a><a id="9438" href="structured-types.commuting-squares-of-pointed-maps.html#9438" class="Bound">top-square</a> <a id="9449" class="Symbol">:</a> <a id="9451" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="9481" href="structured-types.commuting-squares-of-pointed-maps.html#9295" class="Bound">top</a> <a id="9485" href="structured-types.commuting-squares-of-pointed-maps.html#9310" class="Bound">top-left</a> <a id="9494" href="structured-types.commuting-squares-of-pointed-maps.html#9330" class="Bound">top-right</a> <a id="9504" href="structured-types.commuting-squares-of-pointed-maps.html#9351" class="Bound">middle</a><a id="9510" class="Symbol">)</a>
  <a id="9514" class="Symbol">(</a><a id="9515" href="structured-types.commuting-squares-of-pointed-maps.html#9515" class="Bound">bottom-square</a> <a id="9529" class="Symbol">:</a>
    <a id="9535" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a> <a id="9565" href="structured-types.commuting-squares-of-pointed-maps.html#9351" class="Bound">middle</a> <a id="9572" href="structured-types.commuting-squares-of-pointed-maps.html#9371" class="Bound">bottom-left</a> <a id="9584" href="structured-types.commuting-squares-of-pointed-maps.html#9394" class="Bound">bottom-right</a> <a id="9597" href="structured-types.commuting-squares-of-pointed-maps.html#9418" class="Bound">bottom</a><a id="9603" class="Symbol">)</a>
  <a id="9607" class="Keyword">where</a>

  <a id="9616" href="structured-types.commuting-squares-of-pointed-maps.html#9616" class="Function">vertical-pasting-coherence-square-pointed-maps</a> <a id="9663" class="Symbol">:</a>
    <a id="9669" href="structured-types.commuting-squares-of-pointed-maps.html#1740" class="Function">coherence-square-pointed-maps</a>
      <a id="9705" class="Symbol">(</a> <a id="9707" href="structured-types.commuting-squares-of-pointed-maps.html#9295" class="Bound">top</a><a id="9710" class="Symbol">)</a>
      <a id="9718" class="Symbol">(</a> <a id="9720" href="structured-types.commuting-squares-of-pointed-maps.html#9371" class="Bound">bottom-left</a> <a id="9732" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="9735" href="structured-types.commuting-squares-of-pointed-maps.html#9310" class="Bound">top-left</a><a id="9743" class="Symbol">)</a>
      <a id="9751" class="Symbol">(</a> <a id="9753" href="structured-types.commuting-squares-of-pointed-maps.html#9394" class="Bound">bottom-right</a> <a id="9766" href="structured-types.pointed-maps.html#3415" class="Function Operator">∘∗</a> <a id="9769" href="structured-types.commuting-squares-of-pointed-maps.html#9330" class="Bound">top-right</a><a id="9778" class="Symbol">)</a>
      <a id="9786" class="Symbol">(</a> <a id="9788" href="structured-types.commuting-squares-of-pointed-maps.html#9418" class="Bound">bottom</a><a id="9794" class="Symbol">)</a>
  <a id="9798" href="structured-types.commuting-squares-of-pointed-maps.html#9616" class="Function">vertical-pasting-coherence-square-pointed-maps</a> <a id="9845" class="Symbol">=</a>
    <a id="9851" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
      <a id="9877" class="Symbol">(</a> <a id="9879" href="structured-types.commuting-squares-of-pointed-maps.html#4301" class="Function">right-whisker-comp-coherence-square-pointed-maps</a>
        <a id="9936" class="Symbol">(</a> <a id="9938" href="structured-types.commuting-squares-of-pointed-maps.html#9351" class="Bound">middle</a><a id="9944" class="Symbol">)</a>
        <a id="9954" class="Symbol">(</a> <a id="9956" href="structured-types.commuting-squares-of-pointed-maps.html#9371" class="Bound">bottom-left</a><a id="9967" class="Symbol">)</a>
        <a id="9977" class="Symbol">(</a> <a id="9979" href="structured-types.commuting-squares-of-pointed-maps.html#9394" class="Bound">bottom-right</a><a id="9991" class="Symbol">)</a>
        <a id="10001" class="Symbol">(</a> <a id="10003" href="structured-types.commuting-squares-of-pointed-maps.html#9418" class="Bound">bottom</a><a id="10009" class="Symbol">)</a>
        <a id="10019" class="Symbol">(</a> <a id="10021" href="structured-types.commuting-squares-of-pointed-maps.html#9515" class="Bound">bottom-square</a><a id="10034" class="Symbol">)</a>
        <a id="10044" class="Symbol">(</a> <a id="10046" href="structured-types.commuting-squares-of-pointed-maps.html#9310" class="Bound">top-left</a><a id="10054" class="Symbol">))</a>
      <a id="10063" class="Symbol">(</a> <a id="10065" href="structured-types.pointed-homotopies.html#8752" class="Function">concat-pointed-htpy</a>
        <a id="10093" class="Symbol">(</a> <a id="10095" href="structured-types.pointed-homotopies.html#12607" class="Function">inv-associative-comp-pointed-map</a> <a id="10128" href="structured-types.commuting-squares-of-pointed-maps.html#9394" class="Bound">bottom-right</a> <a id="10141" href="structured-types.commuting-squares-of-pointed-maps.html#9351" class="Bound">middle</a> <a id="10148" href="structured-types.commuting-squares-of-pointed-maps.html#9310" class="Bound">top-left</a><a id="10156" class="Symbol">)</a>
        <a id="10166" class="Symbol">(</a> <a id="10168" href="structured-types.commuting-squares-of-pointed-maps.html#3047" class="Function">left-whisker-comp-coherence-square-pointed-maps</a>
          <a id="10226" class="Symbol">(</a> <a id="10228" href="structured-types.commuting-squares-of-pointed-maps.html#9394" class="Bound">bottom-right</a><a id="10240" class="Symbol">)</a>
          <a id="10252" class="Symbol">(</a> <a id="10254" href="structured-types.commuting-squares-of-pointed-maps.html#9295" class="Bound">top</a><a id="10257" class="Symbol">)</a>
          <a id="10269" class="Symbol">(</a> <a id="10271" href="structured-types.commuting-squares-of-pointed-maps.html#9310" class="Bound">top-left</a><a id="10279" class="Symbol">)</a>
          <a id="10291" class="Symbol">(</a> <a id="10293" href="structured-types.commuting-squares-of-pointed-maps.html#9330" class="Bound">top-right</a><a id="10302" class="Symbol">)</a>
          <a id="10314" class="Symbol">(</a> <a id="10316" href="structured-types.commuting-squares-of-pointed-maps.html#9351" class="Bound">middle</a><a id="10322" class="Symbol">)</a>
          <a id="10334" class="Symbol">(</a> <a id="10336" href="structured-types.commuting-squares-of-pointed-maps.html#9438" class="Bound">top-square</a><a id="10346" class="Symbol">)))</a>
</pre>