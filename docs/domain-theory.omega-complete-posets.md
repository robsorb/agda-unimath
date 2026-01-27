# ω-Complete posets

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="domain-theory.omega-complete-posets.html" class="Module">domain-theory.omega-complete-posets</a> <a id="73" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="129" class="Keyword">open</a> <a id="134" class="Keyword">import</a> <a id="141" href="elementary-number-theory.decidable-total-order-natural-numbers.html" class="Module">elementary-number-theory.decidable-total-order-natural-numbers</a>
<a id="204" class="Keyword">open</a> <a id="209" class="Keyword">import</a> <a id="216" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="268" class="Keyword">open</a> <a id="273" class="Keyword">import</a> <a id="280" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="362" class="Keyword">open</a> <a id="367" class="Keyword">import</a> <a id="374" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="406" class="Keyword">open</a> <a id="411" class="Keyword">import</a> <a id="418" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="442" class="Keyword">open</a> <a id="447" class="Keyword">import</a> <a id="454" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="480" class="Keyword">open</a> <a id="485" class="Keyword">import</a> <a id="492" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="524" class="Keyword">open</a> <a id="529" class="Keyword">import</a> <a id="536" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="560" class="Keyword">open</a> <a id="565" class="Keyword">import</a> <a id="572" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="588" class="Keyword">open</a> <a id="593" class="Keyword">import</a> <a id="600" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="628" class="Keyword">open</a> <a id="633" class="Keyword">import</a> <a id="640" href="order-theory.least-upper-bounds-posets.html" class="Module">order-theory.least-upper-bounds-posets</a>
<a id="679" class="Keyword">open</a> <a id="684" class="Keyword">import</a> <a id="691" href="order-theory.order-preserving-maps-posets.html" class="Module">order-theory.order-preserving-maps-posets</a>
<a id="733" class="Keyword">open</a> <a id="738" class="Keyword">import</a> <a id="745" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="765" class="Keyword">open</a> <a id="770" class="Keyword">import</a> <a id="777" href="order-theory.upper-bounds-posets.html" class="Module">order-theory.upper-bounds-posets</a>
</pre>
</details>

## Idea

An
{{#concept "ω-complete poset" WD="complete partial order" WDID=Q3082805  Agda=ω-Complete-Poset}}
is a [poset](order-theory.posets.md) `P` such that every ascending
ω-[chain](order-theory.chains-posets.md)

```text
  α₀ ≤ α₁ ≤ α₂ ≤ α₃ ≤ …
```

in `P`, i.e., ascending chain indexed by the
[natural numbers](elementary-number-theory.natural-numbers.md), has a
[supremum](order-theory.least-upper-bounds-posets.md) `αω` in `P`.

## Definitions

### The predicate on posets of being ω-complete

<pre class="Agda"><a id="1338" class="Keyword">module</a> <a id="1345" href="domain-theory.omega-complete-posets.html#1345" class="Module">_</a>
  <a id="1349" class="Symbol">{</a><a id="1350" href="domain-theory.omega-complete-posets.html#1350" class="Bound">l1</a> <a id="1353" href="domain-theory.omega-complete-posets.html#1353" class="Bound">l2</a> <a id="1356" class="Symbol">:</a> <a id="1358" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1363" class="Symbol">}</a> <a id="1365" class="Symbol">(</a><a id="1366" href="domain-theory.omega-complete-posets.html#1366" class="Bound">P</a> <a id="1368" class="Symbol">:</a> <a id="1370" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1376" href="domain-theory.omega-complete-posets.html#1350" class="Bound">l1</a> <a id="1379" href="domain-theory.omega-complete-posets.html#1353" class="Bound">l2</a><a id="1381" class="Symbol">)</a>
  <a id="1385" class="Keyword">where</a>

  <a id="1394" href="domain-theory.omega-complete-posets.html#1394" class="Function">is-ω-complete-prop-Poset</a> <a id="1419" class="Symbol">:</a> <a id="1421" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1426" class="Symbol">(</a><a id="1427" href="domain-theory.omega-complete-posets.html#1350" class="Bound">l1</a> <a id="1430" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1432" href="domain-theory.omega-complete-posets.html#1353" class="Bound">l2</a><a id="1434" class="Symbol">)</a>
  <a id="1438" href="domain-theory.omega-complete-posets.html#1394" class="Function">is-ω-complete-prop-Poset</a> <a id="1463" class="Symbol">=</a>
    <a id="1469" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a>
      <a id="1482" class="Symbol">(</a> <a id="1484" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="1494" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="1502" href="domain-theory.omega-complete-posets.html#1366" class="Bound">P</a><a id="1503" class="Symbol">)</a>
      <a id="1511" class="Symbol">(</a> <a id="1513" class="Symbol">λ</a> <a id="1515" href="domain-theory.omega-complete-posets.html#1515" class="Bound">F</a> <a id="1517" class="Symbol">→</a>
        <a id="1527" href="order-theory.least-upper-bounds-posets.html#10572" class="Function">has-least-upper-bound-family-of-elements-prop-Poset</a> <a id="1579" href="domain-theory.omega-complete-posets.html#1366" class="Bound">P</a>
          <a id="1591" class="Symbol">(</a> <a id="1593" href="order-theory.order-preserving-maps-posets.html#1716" class="Function">map-hom-Poset</a> <a id="1607" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="1615" href="domain-theory.omega-complete-posets.html#1366" class="Bound">P</a> <a id="1617" href="domain-theory.omega-complete-posets.html#1515" class="Bound">F</a><a id="1618" class="Symbol">))</a>

  <a id="1624" href="domain-theory.omega-complete-posets.html#1624" class="Function">is-ω-complete-Poset</a> <a id="1644" class="Symbol">:</a> <a id="1646" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1649" class="Symbol">(</a><a id="1650" href="domain-theory.omega-complete-posets.html#1350" class="Bound">l1</a> <a id="1653" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1655" href="domain-theory.omega-complete-posets.html#1353" class="Bound">l2</a><a id="1657" class="Symbol">)</a>
  <a id="1661" href="domain-theory.omega-complete-posets.html#1624" class="Function">is-ω-complete-Poset</a> <a id="1681" class="Symbol">=</a>
    <a id="1687" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="1697" href="domain-theory.omega-complete-posets.html#1394" class="Function">is-ω-complete-prop-Poset</a>

  <a id="1725" href="domain-theory.omega-complete-posets.html#1725" class="Function">is-prop-is-ω-complete-Poset</a> <a id="1753" class="Symbol">:</a> <a id="1755" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1763" href="domain-theory.omega-complete-posets.html#1624" class="Function">is-ω-complete-Poset</a>
  <a id="1785" href="domain-theory.omega-complete-posets.html#1725" class="Function">is-prop-is-ω-complete-Poset</a> <a id="1813" class="Symbol">=</a>
    <a id="1819" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="1837" href="domain-theory.omega-complete-posets.html#1394" class="Function">is-ω-complete-prop-Poset</a>

<a id="1863" class="Keyword">module</a> <a id="1870" href="domain-theory.omega-complete-posets.html#1870" class="Module">_</a>
  <a id="1874" class="Symbol">{</a><a id="1875" href="domain-theory.omega-complete-posets.html#1875" class="Bound">l1</a> <a id="1878" href="domain-theory.omega-complete-posets.html#1878" class="Bound">l2</a> <a id="1881" class="Symbol">:</a> <a id="1883" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1888" class="Symbol">}</a> <a id="1890" class="Symbol">(</a><a id="1891" href="domain-theory.omega-complete-posets.html#1891" class="Bound">P</a> <a id="1893" class="Symbol">:</a> <a id="1895" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="1901" href="domain-theory.omega-complete-posets.html#1875" class="Bound">l1</a> <a id="1904" href="domain-theory.omega-complete-posets.html#1878" class="Bound">l2</a><a id="1906" class="Symbol">)</a> <a id="1908" class="Symbol">(</a><a id="1909" href="domain-theory.omega-complete-posets.html#1909" class="Bound">H</a> <a id="1911" class="Symbol">:</a> <a id="1913" href="domain-theory.omega-complete-posets.html#1624" class="Function">is-ω-complete-Poset</a> <a id="1933" href="domain-theory.omega-complete-posets.html#1891" class="Bound">P</a><a id="1934" class="Symbol">)</a>
  <a id="1938" class="Keyword">where</a>

  <a id="1947" href="domain-theory.omega-complete-posets.html#1947" class="Function">sup-is-ω-complete-Poset</a> <a id="1971" class="Symbol">:</a> <a id="1973" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="1983" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="1991" href="domain-theory.omega-complete-posets.html#1891" class="Bound">P</a> <a id="1993" class="Symbol">→</a> <a id="1995" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="2006" href="domain-theory.omega-complete-posets.html#1891" class="Bound">P</a>
  <a id="2010" href="domain-theory.omega-complete-posets.html#1947" class="Function">sup-is-ω-complete-Poset</a> <a id="2034" href="domain-theory.omega-complete-posets.html#2034" class="Bound">F</a> <a id="2036" class="Symbol">=</a> <a id="2038" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2042" class="Symbol">(</a><a id="2043" href="domain-theory.omega-complete-posets.html#1909" class="Bound">H</a> <a id="2045" href="domain-theory.omega-complete-posets.html#2034" class="Bound">F</a><a id="2046" class="Symbol">)</a>

  <a id="2051" href="domain-theory.omega-complete-posets.html#2051" class="Function">is-least-upper-bound-sup-is-ω-complete-Poset</a> <a id="2096" class="Symbol">:</a>
    <a id="2102" class="Symbol">(</a><a id="2103" href="domain-theory.omega-complete-posets.html#2103" class="Bound">x</a> <a id="2105" class="Symbol">:</a> <a id="2107" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="2117" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="2125" href="domain-theory.omega-complete-posets.html#1891" class="Bound">P</a><a id="2126" class="Symbol">)</a> <a id="2128" class="Symbol">→</a>
    <a id="2134" href="order-theory.least-upper-bounds-posets.html#7511" class="Function">is-least-upper-bound-family-of-elements-Poset</a> <a id="2180" href="domain-theory.omega-complete-posets.html#1891" class="Bound">P</a>
      <a id="2188" class="Symbol">(</a> <a id="2190" href="order-theory.order-preserving-maps-posets.html#1716" class="Function">map-hom-Poset</a> <a id="2204" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="2212" href="domain-theory.omega-complete-posets.html#1891" class="Bound">P</a> <a id="2214" href="domain-theory.omega-complete-posets.html#2103" class="Bound">x</a><a id="2215" class="Symbol">)</a>
      <a id="2223" class="Symbol">(</a> <a id="2225" href="domain-theory.omega-complete-posets.html#1947" class="Function">sup-is-ω-complete-Poset</a> <a id="2249" href="domain-theory.omega-complete-posets.html#2103" class="Bound">x</a><a id="2250" class="Symbol">)</a>
  <a id="2254" href="domain-theory.omega-complete-posets.html#2051" class="Function">is-least-upper-bound-sup-is-ω-complete-Poset</a> <a id="2299" href="domain-theory.omega-complete-posets.html#2299" class="Bound">F</a> <a id="2301" class="Symbol">=</a> <a id="2303" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2307" class="Symbol">(</a><a id="2308" href="domain-theory.omega-complete-posets.html#1909" class="Bound">H</a> <a id="2310" href="domain-theory.omega-complete-posets.html#2299" class="Bound">F</a><a id="2311" class="Symbol">)</a>
</pre>
### ω-Complete posets

<pre class="Agda"><a id="ω-Complete-Poset"></a><a id="2349" href="domain-theory.omega-complete-posets.html#2349" class="Function">ω-Complete-Poset</a> <a id="2366" class="Symbol">:</a>
  <a id="2370" class="Symbol">(</a><a id="2371" href="domain-theory.omega-complete-posets.html#2371" class="Bound">l1</a> <a id="2374" href="domain-theory.omega-complete-posets.html#2374" class="Bound">l2</a> <a id="2377" class="Symbol">:</a> <a id="2379" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2384" class="Symbol">)</a> <a id="2386" class="Symbol">→</a> <a id="2388" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2391" class="Symbol">(</a><a id="2392" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2397" href="domain-theory.omega-complete-posets.html#2371" class="Bound">l1</a> <a id="2400" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2402" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2407" href="domain-theory.omega-complete-posets.html#2374" class="Bound">l2</a><a id="2409" class="Symbol">)</a>
<a id="2411" href="domain-theory.omega-complete-posets.html#2349" class="Function">ω-Complete-Poset</a> <a id="2428" href="domain-theory.omega-complete-posets.html#2428" class="Bound">l1</a> <a id="2431" href="domain-theory.omega-complete-posets.html#2431" class="Bound">l2</a> <a id="2434" class="Symbol">=</a>
  <a id="2438" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2440" class="Symbol">(</a><a id="2441" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2447" href="domain-theory.omega-complete-posets.html#2428" class="Bound">l1</a> <a id="2450" href="domain-theory.omega-complete-posets.html#2431" class="Bound">l2</a><a id="2452" class="Symbol">)</a> <a id="2454" class="Symbol">(</a><a id="2455" href="domain-theory.omega-complete-posets.html#1624" class="Function">is-ω-complete-Poset</a><a id="2474" class="Symbol">)</a>

<a id="2477" class="Keyword">module</a> <a id="2484" href="domain-theory.omega-complete-posets.html#2484" class="Module">_</a>
  <a id="2488" class="Symbol">{</a><a id="2489" href="domain-theory.omega-complete-posets.html#2489" class="Bound">l1</a> <a id="2492" href="domain-theory.omega-complete-posets.html#2492" class="Bound">l2</a> <a id="2495" class="Symbol">:</a> <a id="2497" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2502" class="Symbol">}</a> <a id="2504" class="Symbol">(</a><a id="2505" href="domain-theory.omega-complete-posets.html#2505" class="Bound">A</a> <a id="2507" class="Symbol">:</a> <a id="2509" href="domain-theory.omega-complete-posets.html#2349" class="Function">ω-Complete-Poset</a> <a id="2526" href="domain-theory.omega-complete-posets.html#2489" class="Bound">l1</a> <a id="2529" href="domain-theory.omega-complete-posets.html#2492" class="Bound">l2</a><a id="2531" class="Symbol">)</a>
  <a id="2535" class="Keyword">where</a>

  <a id="2544" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a> <a id="2567" class="Symbol">:</a> <a id="2569" href="order-theory.posets.html#1114" class="Function">Poset</a> <a id="2575" href="domain-theory.omega-complete-posets.html#2489" class="Bound">l1</a> <a id="2578" href="domain-theory.omega-complete-posets.html#2492" class="Bound">l2</a>
  <a id="2583" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a> <a id="2606" class="Symbol">=</a> <a id="2608" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2612" href="domain-theory.omega-complete-posets.html#2505" class="Bound">A</a>

  <a id="2617" href="domain-theory.omega-complete-posets.html#2617" class="Function">type-ω-Complete-Poset</a> <a id="2639" class="Symbol">:</a> <a id="2641" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2644" href="domain-theory.omega-complete-posets.html#2489" class="Bound">l1</a>
  <a id="2649" href="domain-theory.omega-complete-posets.html#2617" class="Function">type-ω-Complete-Poset</a> <a id="2671" class="Symbol">=</a>
    <a id="2677" href="order-theory.posets.html#1347" class="Function">type-Poset</a> <a id="2688" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="2714" href="domain-theory.omega-complete-posets.html#2714" class="Function">leq-prop-ω-Complete-Poset</a> <a id="2740" class="Symbol">:</a>
    <a id="2746" class="Symbol">(</a><a id="2747" href="domain-theory.omega-complete-posets.html#2747" class="Bound">x</a> <a id="2749" href="domain-theory.omega-complete-posets.html#2749" class="Bound">y</a> <a id="2751" class="Symbol">:</a> <a id="2753" href="domain-theory.omega-complete-posets.html#2617" class="Function">type-ω-Complete-Poset</a><a id="2774" class="Symbol">)</a> <a id="2776" class="Symbol">→</a> <a id="2778" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2783" href="domain-theory.omega-complete-posets.html#2492" class="Bound">l2</a>
  <a id="2788" href="domain-theory.omega-complete-posets.html#2714" class="Function">leq-prop-ω-Complete-Poset</a> <a id="2814" class="Symbol">=</a>
    <a id="2820" href="order-theory.posets.html#1413" class="Function">leq-prop-Poset</a> <a id="2835" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="2861" href="domain-theory.omega-complete-posets.html#2861" class="Function">leq-ω-Complete-Poset</a> <a id="2882" class="Symbol">:</a>
    <a id="2888" class="Symbol">(</a><a id="2889" href="domain-theory.omega-complete-posets.html#2889" class="Bound">x</a> <a id="2891" href="domain-theory.omega-complete-posets.html#2891" class="Bound">y</a> <a id="2893" class="Symbol">:</a> <a id="2895" href="domain-theory.omega-complete-posets.html#2617" class="Function">type-ω-Complete-Poset</a><a id="2916" class="Symbol">)</a> <a id="2918" class="Symbol">→</a> <a id="2920" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2923" href="domain-theory.omega-complete-posets.html#2492" class="Bound">l2</a>
  <a id="2928" href="domain-theory.omega-complete-posets.html#2861" class="Function">leq-ω-Complete-Poset</a> <a id="2949" class="Symbol">=</a>
    <a id="2955" href="order-theory.posets.html#1514" class="Function">leq-Poset</a> <a id="2965" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="2991" href="domain-theory.omega-complete-posets.html#2991" class="Function">is-prop-leq-ω-Complete-Poset</a> <a id="3020" class="Symbol">:</a>
    <a id="3026" class="Symbol">(</a><a id="3027" href="domain-theory.omega-complete-posets.html#3027" class="Bound">x</a> <a id="3029" href="domain-theory.omega-complete-posets.html#3029" class="Bound">y</a> <a id="3031" class="Symbol">:</a> <a id="3033" href="domain-theory.omega-complete-posets.html#2617" class="Function">type-ω-Complete-Poset</a><a id="3054" class="Symbol">)</a> <a id="3056" class="Symbol">→</a>
    <a id="3062" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="3070" class="Symbol">(</a><a id="3071" href="domain-theory.omega-complete-posets.html#2861" class="Function">leq-ω-Complete-Poset</a> <a id="3092" href="domain-theory.omega-complete-posets.html#3027" class="Bound">x</a> <a id="3094" href="domain-theory.omega-complete-posets.html#3029" class="Bound">y</a><a id="3095" class="Symbol">)</a>
  <a id="3099" href="domain-theory.omega-complete-posets.html#2991" class="Function">is-prop-leq-ω-Complete-Poset</a> <a id="3128" class="Symbol">=</a>
    <a id="3134" href="order-theory.posets.html#1598" class="Function">is-prop-leq-Poset</a> <a id="3152" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="3178" href="domain-theory.omega-complete-posets.html#3178" class="Function">refl-leq-ω-Complete-Poset</a> <a id="3204" class="Symbol">:</a>
    <a id="3210" class="Symbol">(</a><a id="3211" href="domain-theory.omega-complete-posets.html#3211" class="Bound">x</a> <a id="3213" class="Symbol">:</a> <a id="3215" href="domain-theory.omega-complete-posets.html#2617" class="Function">type-ω-Complete-Poset</a><a id="3236" class="Symbol">)</a> <a id="3238" class="Symbol">→</a>
    <a id="3244" href="domain-theory.omega-complete-posets.html#2861" class="Function">leq-ω-Complete-Poset</a> <a id="3265" href="domain-theory.omega-complete-posets.html#3211" class="Bound">x</a> <a id="3267" href="domain-theory.omega-complete-posets.html#3211" class="Bound">x</a>
  <a id="3271" href="domain-theory.omega-complete-posets.html#3178" class="Function">refl-leq-ω-Complete-Poset</a> <a id="3297" class="Symbol">=</a>
    <a id="3303" href="order-theory.posets.html#2603" class="Function">refl-leq-Poset</a> <a id="3318" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="3344" href="domain-theory.omega-complete-posets.html#3344" class="Function">antisymmetric-leq-ω-Complete-Poset</a> <a id="3379" class="Symbol">:</a>
    <a id="3385" href="foundation.binary-relations.html#6436" class="Function">is-antisymmetric</a> <a id="3402" href="domain-theory.omega-complete-posets.html#2861" class="Function">leq-ω-Complete-Poset</a>
  <a id="3425" href="domain-theory.omega-complete-posets.html#3344" class="Function">antisymmetric-leq-ω-Complete-Poset</a> <a id="3460" class="Symbol">=</a>
    <a id="3466" href="order-theory.posets.html#3131" class="Function">antisymmetric-leq-Poset</a> <a id="3490" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="3516" href="domain-theory.omega-complete-posets.html#3516" class="Function">transitive-leq-ω-Complete-Poset</a> <a id="3548" class="Symbol">:</a>
    <a id="3554" href="foundation.binary-relations.html#4481" class="Function">is-transitive</a> <a id="3568" href="domain-theory.omega-complete-posets.html#2861" class="Function">leq-ω-Complete-Poset</a>
  <a id="3591" href="domain-theory.omega-complete-posets.html#3516" class="Function">transitive-leq-ω-Complete-Poset</a> <a id="3623" class="Symbol">=</a>
    <a id="3629" href="order-theory.posets.html#2698" class="Function">transitive-leq-Poset</a> <a id="3650" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="3676" href="domain-theory.omega-complete-posets.html#3676" class="Function">is-set-type-ω-Complete-Poset</a> <a id="3705" class="Symbol">:</a>
    <a id="3711" href="foundation-core.sets.html#847" class="Function">is-set</a> <a id="3718" href="domain-theory.omega-complete-posets.html#2617" class="Function">type-ω-Complete-Poset</a>
  <a id="3742" href="domain-theory.omega-complete-posets.html#3676" class="Function">is-set-type-ω-Complete-Poset</a> <a id="3771" class="Symbol">=</a>
    <a id="3777" href="order-theory.posets.html#3221" class="Function">is-set-type-Poset</a> <a id="3795" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="3821" href="domain-theory.omega-complete-posets.html#3821" class="Function">set-ω-Complete-Poset</a> <a id="3842" class="Symbol">:</a> <a id="3844" href="foundation-core.sets.html#922" class="Function">Set</a> <a id="3848" href="domain-theory.omega-complete-posets.html#2489" class="Bound">l1</a>
  <a id="3853" href="domain-theory.omega-complete-posets.html#3821" class="Function">set-ω-Complete-Poset</a> <a id="3874" class="Symbol">=</a>
    <a id="3880" href="order-theory.posets.html#3542" class="Function">set-Poset</a> <a id="3890" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>

  <a id="3916" href="domain-theory.omega-complete-posets.html#3916" class="Function">is-ω-complete-ω-Complete-Poset</a> <a id="3947" class="Symbol">:</a>
    <a id="3953" href="domain-theory.omega-complete-posets.html#1624" class="Function">is-ω-complete-Poset</a> <a id="3973" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a>
  <a id="3998" href="domain-theory.omega-complete-posets.html#3916" class="Function">is-ω-complete-ω-Complete-Poset</a> <a id="4029" class="Symbol">=</a> <a id="4031" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4035" href="domain-theory.omega-complete-posets.html#2505" class="Bound">A</a>

  <a id="4040" href="domain-theory.omega-complete-posets.html#4040" class="Function">sup-ω-Complete-Poset</a> <a id="4061" class="Symbol">:</a>
    <a id="4067" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="4077" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="4085" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a> <a id="4108" class="Symbol">→</a>
    <a id="4114" href="domain-theory.omega-complete-posets.html#2617" class="Function">type-ω-Complete-Poset</a>
  <a id="4138" href="domain-theory.omega-complete-posets.html#4040" class="Function">sup-ω-Complete-Poset</a> <a id="4159" class="Symbol">=</a>
    <a id="4165" href="domain-theory.omega-complete-posets.html#1947" class="Function">sup-is-ω-complete-Poset</a>
      <a id="4195" class="Symbol">(</a> <a id="4197" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a><a id="4219" class="Symbol">)</a>
      <a id="4227" class="Symbol">(</a> <a id="4229" href="domain-theory.omega-complete-posets.html#3916" class="Function">is-ω-complete-ω-Complete-Poset</a><a id="4259" class="Symbol">)</a>

  <a id="4264" href="domain-theory.omega-complete-posets.html#4264" class="Function">is-least-upper-bound-sup-ω-Complete-Poset</a> <a id="4306" class="Symbol">:</a>
    <a id="4312" class="Symbol">(</a><a id="4313" href="domain-theory.omega-complete-posets.html#4313" class="Bound">x</a> <a id="4315" class="Symbol">:</a> <a id="4317" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="4327" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="4335" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a><a id="4357" class="Symbol">)</a> <a id="4359" class="Symbol">→</a>
    <a id="4365" href="order-theory.least-upper-bounds-posets.html#7511" class="Function">is-least-upper-bound-family-of-elements-Poset</a>
      <a id="4417" class="Symbol">(</a> <a id="4419" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a><a id="4441" class="Symbol">)</a>
      <a id="4449" class="Symbol">(</a> <a id="4451" href="order-theory.order-preserving-maps-posets.html#1716" class="Function">map-hom-Poset</a> <a id="4465" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="4473" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a> <a id="4496" href="domain-theory.omega-complete-posets.html#4313" class="Bound">x</a><a id="4497" class="Symbol">)</a>
      <a id="4505" class="Symbol">(</a> <a id="4507" href="domain-theory.omega-complete-posets.html#4040" class="Function">sup-ω-Complete-Poset</a> <a id="4528" href="domain-theory.omega-complete-posets.html#4313" class="Bound">x</a><a id="4529" class="Symbol">)</a>
  <a id="4533" href="domain-theory.omega-complete-posets.html#4264" class="Function">is-least-upper-bound-sup-ω-Complete-Poset</a> <a id="4575" class="Symbol">=</a>
    <a id="4581" href="domain-theory.omega-complete-posets.html#2051" class="Function">is-least-upper-bound-sup-is-ω-complete-Poset</a>
      <a id="4632" class="Symbol">(</a> <a id="4634" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a><a id="4656" class="Symbol">)</a>
      <a id="4664" class="Symbol">(</a> <a id="4666" href="domain-theory.omega-complete-posets.html#3916" class="Function">is-ω-complete-ω-Complete-Poset</a><a id="4696" class="Symbol">)</a>

  <a id="4701" href="domain-theory.omega-complete-posets.html#4701" class="Function">is-upper-bound-sup-ω-Complete-Poset</a> <a id="4737" class="Symbol">:</a>
    <a id="4743" class="Symbol">(</a><a id="4744" href="domain-theory.omega-complete-posets.html#4744" class="Bound">x</a> <a id="4746" class="Symbol">:</a> <a id="4748" href="order-theory.order-preserving-maps-posets.html#1641" class="Function">hom-Poset</a> <a id="4758" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="4766" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a><a id="4788" class="Symbol">)</a> <a id="4790" class="Symbol">→</a>
    <a id="4796" href="order-theory.upper-bounds-posets.html#1919" class="Function">is-upper-bound-family-of-elements-Poset</a>
      <a id="4842" class="Symbol">(</a> <a id="4844" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a><a id="4866" class="Symbol">)</a>
      <a id="4874" class="Symbol">(</a> <a id="4876" href="order-theory.order-preserving-maps-posets.html#1716" class="Function">map-hom-Poset</a> <a id="4890" href="elementary-number-theory.inequality-natural-numbers.html#3817" class="Function">ℕ-Poset</a> <a id="4898" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a> <a id="4921" href="domain-theory.omega-complete-posets.html#4744" class="Bound">x</a><a id="4922" class="Symbol">)</a>
      <a id="4930" class="Symbol">(</a> <a id="4932" href="domain-theory.omega-complete-posets.html#4040" class="Function">sup-ω-Complete-Poset</a> <a id="4953" href="domain-theory.omega-complete-posets.html#4744" class="Bound">x</a><a id="4954" class="Symbol">)</a>
  <a id="4958" href="domain-theory.omega-complete-posets.html#4701" class="Function">is-upper-bound-sup-ω-Complete-Poset</a> <a id="4994" href="domain-theory.omega-complete-posets.html#4994" class="Bound">x</a> <a id="4996" class="Symbol">=</a>
    <a id="5002" href="order-theory.least-upper-bounds-posets.html#8766" class="Function">is-upper-bound-is-least-upper-bound-family-of-elements-Poset</a>
      <a id="5069" class="Symbol">(</a> <a id="5071" href="domain-theory.omega-complete-posets.html#2544" class="Function">poset-ω-Complete-Poset</a><a id="5093" class="Symbol">)</a>
      <a id="5101" class="Symbol">(</a> <a id="5103" href="domain-theory.omega-complete-posets.html#4264" class="Function">is-least-upper-bound-sup-ω-Complete-Poset</a> <a id="5145" href="domain-theory.omega-complete-posets.html#4994" class="Bound">x</a><a id="5146" class="Symbol">)</a>
</pre>