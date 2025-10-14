# Functors between nonunital precategories

<pre class="Agda"><a id="53" class="Keyword">module</a> <a id="60" href="category-theory.functors-nonunital-precategories.html" class="Module">category-theory.functors-nonunital-precategories</a> <a id="109" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="165" class="Keyword">open</a> <a id="170" class="Keyword">import</a> <a id="177" href="category-theory.functors-set-magmoids.html" class="Module">category-theory.functors-set-magmoids</a>
<a id="215" class="Keyword">open</a> <a id="220" class="Keyword">import</a> <a id="227" href="category-theory.maps-set-magmoids.html" class="Module">category-theory.maps-set-magmoids</a>
<a id="261" class="Keyword">open</a> <a id="266" class="Keyword">import</a> <a id="273" href="category-theory.nonunital-precategories.html" class="Module">category-theory.nonunital-precategories</a>

<a id="314" class="Keyword">open</a> <a id="319" class="Keyword">import</a> <a id="326" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="358" class="Keyword">open</a> <a id="363" class="Keyword">import</a> <a id="370" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="394" class="Keyword">open</a> <a id="399" class="Keyword">import</a> <a id="406" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="466" class="Keyword">open</a> <a id="471" class="Keyword">import</a> <a id="478" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="504" class="Keyword">open</a> <a id="509" class="Keyword">import</a> <a id="516" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A **functor** from a [precategory](category-theory.precategories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identity holds:
- `F₁ (g ∘ f) = F₁ g ∘ F₁ f`.

## Definition

### functors between nonunital precategories

<pre class="Agda"><a id="909" class="Keyword">module</a> <a id="916" href="category-theory.functors-nonunital-precategories.html#916" class="Module">_</a>
  <a id="920" class="Symbol">{</a><a id="921" href="category-theory.functors-nonunital-precategories.html#921" class="Bound">l1</a> <a id="924" href="category-theory.functors-nonunital-precategories.html#924" class="Bound">l2</a> <a id="927" href="category-theory.functors-nonunital-precategories.html#927" class="Bound">l3</a> <a id="930" href="category-theory.functors-nonunital-precategories.html#930" class="Bound">l4</a> <a id="933" class="Symbol">:</a> <a id="935" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="940" class="Symbol">}</a>
  <a id="944" class="Symbol">(</a><a id="945" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a> <a id="947" class="Symbol">:</a> <a id="949" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="971" href="category-theory.functors-nonunital-precategories.html#921" class="Bound">l1</a> <a id="974" href="category-theory.functors-nonunital-precategories.html#924" class="Bound">l2</a><a id="976" class="Symbol">)</a>
  <a id="980" class="Symbol">(</a><a id="981" href="category-theory.functors-nonunital-precategories.html#981" class="Bound">D</a> <a id="983" class="Symbol">:</a> <a id="985" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="1007" href="category-theory.functors-nonunital-precategories.html#927" class="Bound">l3</a> <a id="1010" href="category-theory.functors-nonunital-precategories.html#930" class="Bound">l4</a><a id="1012" class="Symbol">)</a>
  <a id="1016" class="Keyword">where</a>

  <a id="1025" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="1055" class="Symbol">:</a> <a id="1057" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1060" class="Symbol">(</a><a id="1061" href="category-theory.functors-nonunital-precategories.html#921" class="Bound">l1</a> <a id="1064" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1066" href="category-theory.functors-nonunital-precategories.html#924" class="Bound">l2</a> <a id="1069" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1071" href="category-theory.functors-nonunital-precategories.html#927" class="Bound">l3</a> <a id="1074" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1076" href="category-theory.functors-nonunital-precategories.html#930" class="Bound">l4</a><a id="1078" class="Symbol">)</a>
  <a id="1082" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="1112" class="Symbol">=</a>
    <a id="1118" href="category-theory.functors-set-magmoids.html#3451" class="Function">functor-Set-Magmoid</a>
      <a id="1144" class="Symbol">(</a> <a id="1146" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="1180" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a><a id="1181" class="Symbol">)</a>
      <a id="1189" class="Symbol">(</a> <a id="1191" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="1225" href="category-theory.functors-nonunital-precategories.html#981" class="Bound">D</a><a id="1226" class="Symbol">)</a>

  <a id="1231" href="category-theory.functors-nonunital-precategories.html#1231" class="Function">obj-functor-Nonunital-Precategory</a> <a id="1265" class="Symbol">:</a>
    <a id="1271" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="1301" class="Symbol">→</a>
    <a id="1307" href="category-theory.nonunital-precategories.html#1618" class="Function">obj-Nonunital-Precategory</a> <a id="1333" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a> <a id="1335" class="Symbol">→</a>
    <a id="1341" href="category-theory.nonunital-precategories.html#1618" class="Function">obj-Nonunital-Precategory</a> <a id="1367" href="category-theory.functors-nonunital-precategories.html#981" class="Bound">D</a>
  <a id="1371" href="category-theory.functors-nonunital-precategories.html#1231" class="Function">obj-functor-Nonunital-Precategory</a> <a id="1405" class="Symbol">=</a> <a id="1407" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a>

  <a id="1414" href="category-theory.functors-nonunital-precategories.html#1414" class="Function">hom-functor-Nonunital-Precategory</a> <a id="1448" class="Symbol">:</a>
    <a id="1454" class="Symbol">(</a><a id="1455" href="category-theory.functors-nonunital-precategories.html#1455" class="Bound">F</a> <a id="1457" class="Symbol">:</a> <a id="1459" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a><a id="1488" class="Symbol">)</a> <a id="1490" class="Symbol">→</a>
    <a id="1496" class="Symbol">{</a><a id="1497" href="category-theory.functors-nonunital-precategories.html#1497" class="Bound">x</a> <a id="1499" href="category-theory.functors-nonunital-precategories.html#1499" class="Bound">y</a> <a id="1501" class="Symbol">:</a> <a id="1503" href="category-theory.nonunital-precategories.html#1618" class="Function">obj-Nonunital-Precategory</a> <a id="1529" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a><a id="1530" class="Symbol">}</a> <a id="1532" class="Symbol">→</a>
    <a id="1538" class="Symbol">(</a><a id="1539" href="category-theory.functors-nonunital-precategories.html#1539" class="Bound">f</a> <a id="1541" class="Symbol">:</a> <a id="1543" href="category-theory.nonunital-precategories.html#1815" class="Function">hom-Nonunital-Precategory</a> <a id="1569" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a> <a id="1571" href="category-theory.functors-nonunital-precategories.html#1497" class="Bound">x</a> <a id="1573" href="category-theory.functors-nonunital-precategories.html#1499" class="Bound">y</a><a id="1574" class="Symbol">)</a> <a id="1576" class="Symbol">→</a>
    <a id="1582" href="category-theory.nonunital-precategories.html#1815" class="Function">hom-Nonunital-Precategory</a> <a id="1608" href="category-theory.functors-nonunital-precategories.html#981" class="Bound">D</a>
      <a id="1616" class="Symbol">(</a> <a id="1618" href="category-theory.functors-nonunital-precategories.html#1231" class="Function">obj-functor-Nonunital-Precategory</a> <a id="1652" href="category-theory.functors-nonunital-precategories.html#1455" class="Bound">F</a> <a id="1654" href="category-theory.functors-nonunital-precategories.html#1497" class="Bound">x</a><a id="1655" class="Symbol">)</a>
      <a id="1663" class="Symbol">(</a> <a id="1665" href="category-theory.functors-nonunital-precategories.html#1231" class="Function">obj-functor-Nonunital-Precategory</a> <a id="1699" href="category-theory.functors-nonunital-precategories.html#1455" class="Bound">F</a> <a id="1701" href="category-theory.functors-nonunital-precategories.html#1499" class="Bound">y</a><a id="1702" class="Symbol">)</a>
  <a id="1706" href="category-theory.functors-nonunital-precategories.html#1414" class="Function">hom-functor-Nonunital-Precategory</a> <a id="1740" href="category-theory.functors-nonunital-precategories.html#1740" class="Bound">F</a> <a id="1742" class="Symbol">=</a> <a id="1744" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1748" class="Symbol">(</a><a id="1749" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1753" href="category-theory.functors-nonunital-precategories.html#1740" class="Bound">F</a><a id="1754" class="Symbol">)</a>

  <a id="1759" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="1793" class="Symbol">:</a>
    <a id="1799" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="1829" class="Symbol">→</a>
    <a id="1835" href="category-theory.maps-set-magmoids.html#832" class="Function">map-Set-Magmoid</a>
      <a id="1857" class="Symbol">(</a> <a id="1859" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="1893" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a><a id="1894" class="Symbol">)</a>
      <a id="1902" class="Symbol">(</a> <a id="1904" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="1938" href="category-theory.functors-nonunital-precategories.html#981" class="Bound">D</a><a id="1939" class="Symbol">)</a>
  <a id="1943" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1947" class="Symbol">(</a><a id="1948" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="1982" href="category-theory.functors-nonunital-precategories.html#1982" class="Bound">F</a><a id="1983" class="Symbol">)</a> <a id="1985" class="Symbol">=</a>
    <a id="1991" href="category-theory.functors-nonunital-precategories.html#1231" class="Function">obj-functor-Nonunital-Precategory</a> <a id="2025" href="category-theory.functors-nonunital-precategories.html#1982" class="Bound">F</a>
  <a id="2029" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2033" class="Symbol">(</a><a id="2034" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="2068" href="category-theory.functors-nonunital-precategories.html#2068" class="Bound">F</a><a id="2069" class="Symbol">)</a> <a id="2071" class="Symbol">=</a>
    <a id="2077" href="category-theory.functors-nonunital-precategories.html#1414" class="Function">hom-functor-Nonunital-Precategory</a> <a id="2111" href="category-theory.functors-nonunital-precategories.html#2068" class="Bound">F</a>

  <a id="2116" href="category-theory.functors-nonunital-precategories.html#2116" class="Function">preserves-comp-functor-Nonunital-Precategory</a> <a id="2161" class="Symbol">:</a>
    <a id="2167" class="Symbol">(</a><a id="2168" href="category-theory.functors-nonunital-precategories.html#2168" class="Bound">F</a> <a id="2170" class="Symbol">:</a> <a id="2172" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a><a id="2201" class="Symbol">)</a>
    <a id="2207" class="Symbol">{</a><a id="2208" href="category-theory.functors-nonunital-precategories.html#2208" class="Bound">x</a> <a id="2210" href="category-theory.functors-nonunital-precategories.html#2210" class="Bound">y</a> <a id="2212" href="category-theory.functors-nonunital-precategories.html#2212" class="Bound">z</a> <a id="2214" class="Symbol">:</a> <a id="2216" href="category-theory.nonunital-precategories.html#1618" class="Function">obj-Nonunital-Precategory</a> <a id="2242" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a><a id="2243" class="Symbol">}</a>
    <a id="2249" class="Symbol">(</a><a id="2250" href="category-theory.functors-nonunital-precategories.html#2250" class="Bound">g</a> <a id="2252" class="Symbol">:</a> <a id="2254" href="category-theory.nonunital-precategories.html#1815" class="Function">hom-Nonunital-Precategory</a> <a id="2280" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a> <a id="2282" href="category-theory.functors-nonunital-precategories.html#2210" class="Bound">y</a> <a id="2284" href="category-theory.functors-nonunital-precategories.html#2212" class="Bound">z</a><a id="2285" class="Symbol">)</a>
    <a id="2291" class="Symbol">(</a><a id="2292" href="category-theory.functors-nonunital-precategories.html#2292" class="Bound">f</a> <a id="2294" class="Symbol">:</a> <a id="2296" href="category-theory.nonunital-precategories.html#1815" class="Function">hom-Nonunital-Precategory</a> <a id="2322" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a> <a id="2324" href="category-theory.functors-nonunital-precategories.html#2208" class="Bound">x</a> <a id="2326" href="category-theory.functors-nonunital-precategories.html#2210" class="Bound">y</a><a id="2327" class="Symbol">)</a> <a id="2329" class="Symbol">→</a>
    <a id="2335" class="Symbol">(</a> <a id="2337" href="category-theory.functors-nonunital-precategories.html#1414" class="Function">hom-functor-Nonunital-Precategory</a> <a id="2371" href="category-theory.functors-nonunital-precategories.html#2168" class="Bound">F</a>
      <a id="2379" class="Symbol">(</a> <a id="2381" href="category-theory.nonunital-precategories.html#2406" class="Function">comp-hom-Nonunital-Precategory</a> <a id="2412" href="category-theory.functors-nonunital-precategories.html#945" class="Bound">C</a> <a id="2414" href="category-theory.functors-nonunital-precategories.html#2250" class="Bound">g</a> <a id="2416" href="category-theory.functors-nonunital-precategories.html#2292" class="Bound">f</a><a id="2417" class="Symbol">))</a> <a id="2420" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2426" class="Symbol">(</a> <a id="2428" href="category-theory.nonunital-precategories.html#2406" class="Function">comp-hom-Nonunital-Precategory</a> <a id="2459" href="category-theory.functors-nonunital-precategories.html#981" class="Bound">D</a>
      <a id="2467" class="Symbol">(</a> <a id="2469" href="category-theory.functors-nonunital-precategories.html#1414" class="Function">hom-functor-Nonunital-Precategory</a> <a id="2503" href="category-theory.functors-nonunital-precategories.html#2168" class="Bound">F</a> <a id="2505" href="category-theory.functors-nonunital-precategories.html#2250" class="Bound">g</a><a id="2506" class="Symbol">)</a>
      <a id="2514" class="Symbol">(</a> <a id="2516" href="category-theory.functors-nonunital-precategories.html#1414" class="Function">hom-functor-Nonunital-Precategory</a> <a id="2550" href="category-theory.functors-nonunital-precategories.html#2168" class="Bound">F</a> <a id="2552" href="category-theory.functors-nonunital-precategories.html#2292" class="Bound">f</a><a id="2553" class="Symbol">))</a>
  <a id="2558" href="category-theory.functors-nonunital-precategories.html#2116" class="Function">preserves-comp-functor-Nonunital-Precategory</a> <a id="2603" class="Symbol">=</a> <a id="2605" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="2609" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2611" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a>
</pre>
## Examples

### The identity nonunital functor

There is an identity functor on any nonunital precategory.

<pre class="Agda"><a id="id-functor-Nonunital-Precategory"></a><a id="2737" href="category-theory.functors-nonunital-precategories.html#2737" class="Function">id-functor-Nonunital-Precategory</a> <a id="2770" class="Symbol">:</a>
  <a id="2774" class="Symbol">{</a><a id="2775" href="category-theory.functors-nonunital-precategories.html#2775" class="Bound">l1</a> <a id="2778" href="category-theory.functors-nonunital-precategories.html#2778" class="Bound">l2</a> <a id="2781" class="Symbol">:</a> <a id="2783" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2788" class="Symbol">}</a> <a id="2790" class="Symbol">(</a><a id="2791" href="category-theory.functors-nonunital-precategories.html#2791" class="Bound">C</a> <a id="2793" class="Symbol">:</a> <a id="2795" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="2817" href="category-theory.functors-nonunital-precategories.html#2775" class="Bound">l1</a> <a id="2820" href="category-theory.functors-nonunital-precategories.html#2778" class="Bound">l2</a><a id="2822" class="Symbol">)</a> <a id="2824" class="Symbol">→</a>
  <a id="2828" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="2858" href="category-theory.functors-nonunital-precategories.html#2791" class="Bound">C</a> <a id="2860" href="category-theory.functors-nonunital-precategories.html#2791" class="Bound">C</a>
<a id="2862" href="category-theory.functors-nonunital-precategories.html#2737" class="Function">id-functor-Nonunital-Precategory</a> <a id="2895" href="category-theory.functors-nonunital-precategories.html#2895" class="Bound">C</a> <a id="2897" class="Symbol">=</a>
  <a id="2901" href="category-theory.functors-set-magmoids.html#4832" class="Function">id-functor-Set-Magmoid</a> <a id="2924" class="Symbol">(</a><a id="2925" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="2959" href="category-theory.functors-nonunital-precategories.html#2895" class="Bound">C</a><a id="2960" class="Symbol">)</a>
</pre>
### Composition of nonunital functors

Any two compatible nonunital functors can be composed to a new nonunital
functor.

<pre class="Agda"><a id="3097" class="Keyword">module</a> <a id="3104" href="category-theory.functors-nonunital-precategories.html#3104" class="Module">_</a>
  <a id="3108" class="Symbol">{</a><a id="3109" href="category-theory.functors-nonunital-precategories.html#3109" class="Bound">l1</a> <a id="3112" href="category-theory.functors-nonunital-precategories.html#3112" class="Bound">l2</a> <a id="3115" href="category-theory.functors-nonunital-precategories.html#3115" class="Bound">l3</a> <a id="3118" href="category-theory.functors-nonunital-precategories.html#3118" class="Bound">l4</a> <a id="3121" href="category-theory.functors-nonunital-precategories.html#3121" class="Bound">l5</a> <a id="3124" href="category-theory.functors-nonunital-precategories.html#3124" class="Bound">l6</a> <a id="3127" class="Symbol">:</a> <a id="3129" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3134" class="Symbol">}</a>
  <a id="3138" class="Symbol">(</a><a id="3139" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a> <a id="3141" class="Symbol">:</a> <a id="3143" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="3165" href="category-theory.functors-nonunital-precategories.html#3109" class="Bound">l1</a> <a id="3168" href="category-theory.functors-nonunital-precategories.html#3112" class="Bound">l2</a><a id="3170" class="Symbol">)</a>
  <a id="3174" class="Symbol">(</a><a id="3175" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a> <a id="3177" class="Symbol">:</a> <a id="3179" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="3201" href="category-theory.functors-nonunital-precategories.html#3115" class="Bound">l3</a> <a id="3204" href="category-theory.functors-nonunital-precategories.html#3118" class="Bound">l4</a><a id="3206" class="Symbol">)</a>
  <a id="3210" class="Symbol">(</a><a id="3211" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a> <a id="3213" class="Symbol">:</a> <a id="3215" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="3237" href="category-theory.functors-nonunital-precategories.html#3121" class="Bound">l5</a> <a id="3240" href="category-theory.functors-nonunital-precategories.html#3124" class="Bound">l6</a><a id="3242" class="Symbol">)</a>
  <a id="3246" class="Symbol">(</a><a id="3247" href="category-theory.functors-nonunital-precategories.html#3247" class="Bound">G</a> <a id="3249" class="Symbol">:</a> <a id="3251" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="3281" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a> <a id="3283" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a><a id="3284" class="Symbol">)</a>
  <a id="3288" class="Symbol">(</a><a id="3289" href="category-theory.functors-nonunital-precategories.html#3289" class="Bound">F</a> <a id="3291" class="Symbol">:</a> <a id="3293" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="3323" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a> <a id="3325" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a><a id="3326" class="Symbol">)</a>
  <a id="3330" class="Keyword">where</a>

  <a id="3339" href="category-theory.functors-nonunital-precategories.html#3339" class="Function">obj-comp-functor-Nonunital-Precategory</a> <a id="3378" class="Symbol">:</a>
    <a id="3384" href="category-theory.nonunital-precategories.html#1618" class="Function">obj-Nonunital-Precategory</a> <a id="3410" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a> <a id="3412" class="Symbol">→</a> <a id="3414" href="category-theory.nonunital-precategories.html#1618" class="Function">obj-Nonunital-Precategory</a> <a id="3440" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a>
  <a id="3444" href="category-theory.functors-nonunital-precategories.html#3339" class="Function">obj-comp-functor-Nonunital-Precategory</a> <a id="3483" class="Symbol">=</a>
    <a id="3489" href="category-theory.functors-nonunital-precategories.html#1231" class="Function">obj-functor-Nonunital-Precategory</a> <a id="3523" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a> <a id="3525" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a> <a id="3527" href="category-theory.functors-nonunital-precategories.html#3247" class="Bound">G</a> <a id="3529" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
    <a id="3535" href="category-theory.functors-nonunital-precategories.html#1231" class="Function">obj-functor-Nonunital-Precategory</a> <a id="3569" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a> <a id="3571" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a> <a id="3573" href="category-theory.functors-nonunital-precategories.html#3289" class="Bound">F</a>

  <a id="3578" href="category-theory.functors-nonunital-precategories.html#3578" class="Function">hom-comp-functor-Nonunital-Precategory</a> <a id="3617" class="Symbol">:</a>
    <a id="3623" class="Symbol">{</a><a id="3624" href="category-theory.functors-nonunital-precategories.html#3624" class="Bound">x</a> <a id="3626" href="category-theory.functors-nonunital-precategories.html#3626" class="Bound">y</a> <a id="3628" class="Symbol">:</a> <a id="3630" href="category-theory.nonunital-precategories.html#1618" class="Function">obj-Nonunital-Precategory</a> <a id="3656" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a><a id="3657" class="Symbol">}</a> <a id="3659" class="Symbol">→</a>
    <a id="3665" href="category-theory.nonunital-precategories.html#1815" class="Function">hom-Nonunital-Precategory</a> <a id="3691" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a> <a id="3693" href="category-theory.functors-nonunital-precategories.html#3624" class="Bound">x</a> <a id="3695" href="category-theory.functors-nonunital-precategories.html#3626" class="Bound">y</a> <a id="3697" class="Symbol">→</a>
    <a id="3703" href="category-theory.nonunital-precategories.html#1815" class="Function">hom-Nonunital-Precategory</a> <a id="3729" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a>
      <a id="3737" class="Symbol">(</a> <a id="3739" href="category-theory.functors-nonunital-precategories.html#3339" class="Function">obj-comp-functor-Nonunital-Precategory</a> <a id="3778" href="category-theory.functors-nonunital-precategories.html#3624" class="Bound">x</a><a id="3779" class="Symbol">)</a>
      <a id="3787" class="Symbol">(</a> <a id="3789" href="category-theory.functors-nonunital-precategories.html#3339" class="Function">obj-comp-functor-Nonunital-Precategory</a> <a id="3828" href="category-theory.functors-nonunital-precategories.html#3626" class="Bound">y</a><a id="3829" class="Symbol">)</a>
  <a id="3833" href="category-theory.functors-nonunital-precategories.html#3578" class="Function">hom-comp-functor-Nonunital-Precategory</a> <a id="3872" class="Symbol">=</a>
    <a id="3878" href="category-theory.functors-nonunital-precategories.html#1414" class="Function">hom-functor-Nonunital-Precategory</a> <a id="3912" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a> <a id="3914" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a> <a id="3916" href="category-theory.functors-nonunital-precategories.html#3247" class="Bound">G</a> <a id="3918" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
    <a id="3924" href="category-theory.functors-nonunital-precategories.html#1414" class="Function">hom-functor-Nonunital-Precategory</a> <a id="3958" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a> <a id="3960" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a> <a id="3962" href="category-theory.functors-nonunital-precategories.html#3289" class="Bound">F</a>

  <a id="3967" href="category-theory.functors-nonunital-precategories.html#3967" class="Function">map-comp-functor-Nonunital-Precategory</a> <a id="4006" class="Symbol">:</a>
    <a id="4012" href="category-theory.maps-set-magmoids.html#832" class="Function">map-Set-Magmoid</a>
      <a id="4034" class="Symbol">(</a> <a id="4036" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="4070" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a><a id="4071" class="Symbol">)</a>
      <a id="4079" class="Symbol">(</a> <a id="4081" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="4115" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a><a id="4116" class="Symbol">)</a>
  <a id="4120" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="4124" href="category-theory.functors-nonunital-precategories.html#3967" class="Function">map-comp-functor-Nonunital-Precategory</a> <a id="4163" class="Symbol">=</a>
    <a id="4169" href="category-theory.functors-nonunital-precategories.html#3339" class="Function">obj-comp-functor-Nonunital-Precategory</a>
  <a id="4210" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="4214" href="category-theory.functors-nonunital-precategories.html#3967" class="Function">map-comp-functor-Nonunital-Precategory</a> <a id="4253" class="Symbol">=</a>
    <a id="4259" href="category-theory.functors-nonunital-precategories.html#3578" class="Function">hom-comp-functor-Nonunital-Precategory</a>

  <a id="4301" href="category-theory.functors-nonunital-precategories.html#4301" class="Function">preserves-comp-comp-functor-Nonunital-Precategory</a> <a id="4351" class="Symbol">=</a>
    <a id="4357" href="category-theory.functors-set-magmoids.html#5966" class="Function">preserves-comp-comp-functor-Set-Magmoid</a>
      <a id="4403" class="Symbol">(</a> <a id="4405" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="4439" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a><a id="4440" class="Symbol">)</a>
      <a id="4448" class="Symbol">(</a> <a id="4450" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="4484" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a><a id="4485" class="Symbol">)</a>
      <a id="4493" class="Symbol">(</a> <a id="4495" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="4529" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a><a id="4530" class="Symbol">)</a>
      <a id="4538" class="Symbol">(</a> <a id="4540" href="category-theory.functors-nonunital-precategories.html#3247" class="Bound">G</a><a id="4541" class="Symbol">)</a> <a id="4543" class="Symbol">(</a><a id="4544" href="category-theory.functors-nonunital-precategories.html#3289" class="Bound">F</a><a id="4545" class="Symbol">)</a>

  <a id="4550" href="category-theory.functors-nonunital-precategories.html#4550" class="Function">comp-functor-Nonunital-Precategory</a> <a id="4585" class="Symbol">:</a> <a id="4587" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="4617" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a> <a id="4619" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a>
  <a id="4623" href="category-theory.functors-nonunital-precategories.html#4550" class="Function">comp-functor-Nonunital-Precategory</a> <a id="4658" class="Symbol">=</a>
    <a id="4664" href="category-theory.functors-set-magmoids.html#6403" class="Function">comp-functor-Set-Magmoid</a>
      <a id="4695" class="Symbol">(</a> <a id="4697" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="4731" href="category-theory.functors-nonunital-precategories.html#3139" class="Bound">A</a><a id="4732" class="Symbol">)</a>
      <a id="4740" class="Symbol">(</a> <a id="4742" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="4776" href="category-theory.functors-nonunital-precategories.html#3175" class="Bound">B</a><a id="4777" class="Symbol">)</a>
      <a id="4785" class="Symbol">(</a> <a id="4787" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="4821" href="category-theory.functors-nonunital-precategories.html#3211" class="Bound">C</a><a id="4822" class="Symbol">)</a>
      <a id="4830" class="Symbol">(</a> <a id="4832" href="category-theory.functors-nonunital-precategories.html#3247" class="Bound">G</a><a id="4833" class="Symbol">)</a> <a id="4835" class="Symbol">(</a><a id="4836" href="category-theory.functors-nonunital-precategories.html#3289" class="Bound">F</a><a id="4837" class="Symbol">)</a>
</pre>
## Properties

### Extensionality of functors between nonunital precategories

#### Equality of functors is equality of underlying maps

<pre class="Agda"><a id="4989" class="Keyword">module</a> <a id="4996" href="category-theory.functors-nonunital-precategories.html#4996" class="Module">_</a>
  <a id="5000" class="Symbol">{</a><a id="5001" href="category-theory.functors-nonunital-precategories.html#5001" class="Bound">l1</a> <a id="5004" href="category-theory.functors-nonunital-precategories.html#5004" class="Bound">l2</a> <a id="5007" href="category-theory.functors-nonunital-precategories.html#5007" class="Bound">l3</a> <a id="5010" href="category-theory.functors-nonunital-precategories.html#5010" class="Bound">l4</a> <a id="5013" class="Symbol">:</a> <a id="5015" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5020" class="Symbol">}</a>
  <a id="5024" class="Symbol">(</a><a id="5025" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a> <a id="5027" class="Symbol">:</a> <a id="5029" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="5051" href="category-theory.functors-nonunital-precategories.html#5001" class="Bound">l1</a> <a id="5054" href="category-theory.functors-nonunital-precategories.html#5004" class="Bound">l2</a><a id="5056" class="Symbol">)</a>
  <a id="5060" class="Symbol">(</a><a id="5061" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a> <a id="5063" class="Symbol">:</a> <a id="5065" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="5087" href="category-theory.functors-nonunital-precategories.html#5007" class="Bound">l3</a> <a id="5090" href="category-theory.functors-nonunital-precategories.html#5010" class="Bound">l4</a><a id="5092" class="Symbol">)</a>
  <a id="5096" class="Symbol">(</a><a id="5097" href="category-theory.functors-nonunital-precategories.html#5097" class="Bound">F</a> <a id="5099" href="category-theory.functors-nonunital-precategories.html#5099" class="Bound">G</a> <a id="5101" class="Symbol">:</a> <a id="5103" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="5133" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a> <a id="5135" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a><a id="5136" class="Symbol">)</a>
  <a id="5140" class="Keyword">where</a>

  <a id="5149" href="category-theory.functors-nonunital-precategories.html#5149" class="Function">equiv-eq-map-eq-functor-Nonunital-Precategory</a> <a id="5195" class="Symbol">:</a>
    <a id="5201" class="Symbol">(</a> <a id="5203" href="category-theory.functors-nonunital-precategories.html#5097" class="Bound">F</a> <a id="5205" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="5207" href="category-theory.functors-nonunital-precategories.html#5099" class="Bound">G</a><a id="5208" class="Symbol">)</a> <a id="5210" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a>
    <a id="5216" class="Symbol">(</a> <a id="5218" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="5252" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a> <a id="5254" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a> <a id="5256" href="category-theory.functors-nonunital-precategories.html#5097" class="Bound">F</a> <a id="5258" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="5266" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="5300" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a> <a id="5302" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a> <a id="5304" href="category-theory.functors-nonunital-precategories.html#5099" class="Bound">G</a><a id="5305" class="Symbol">)</a>
  <a id="5309" href="category-theory.functors-nonunital-precategories.html#5149" class="Function">equiv-eq-map-eq-functor-Nonunital-Precategory</a> <a id="5355" class="Symbol">=</a>
    <a id="5361" href="category-theory.functors-set-magmoids.html#6967" class="Function">equiv-eq-map-eq-functor-Set-Magmoid</a>
      <a id="5403" class="Symbol">(</a> <a id="5405" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="5439" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a><a id="5440" class="Symbol">)</a>
      <a id="5448" class="Symbol">(</a> <a id="5450" href="category-theory.nonunital-precategories.html#4384" class="Function">set-magmoid-Nonunital-Precategory</a> <a id="5484" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a><a id="5485" class="Symbol">)</a>
      <a id="5493" class="Symbol">(</a> <a id="5495" href="category-theory.functors-nonunital-precategories.html#5097" class="Bound">F</a><a id="5496" class="Symbol">)</a> <a id="5498" class="Symbol">(</a><a id="5499" href="category-theory.functors-nonunital-precategories.html#5099" class="Bound">G</a><a id="5500" class="Symbol">)</a>

  <a id="5505" href="category-theory.functors-nonunital-precategories.html#5505" class="Function">eq-map-eq-functor-Nonunital-Precategory</a> <a id="5545" class="Symbol">:</a>
    <a id="5551" class="Symbol">(</a> <a id="5553" href="category-theory.functors-nonunital-precategories.html#5097" class="Bound">F</a> <a id="5555" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="5557" href="category-theory.functors-nonunital-precategories.html#5099" class="Bound">G</a><a id="5558" class="Symbol">)</a> <a id="5560" class="Symbol">→</a>
    <a id="5566" class="Symbol">(</a> <a id="5568" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="5602" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a> <a id="5604" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a> <a id="5606" href="category-theory.functors-nonunital-precategories.html#5097" class="Bound">F</a> <a id="5608" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="5616" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="5650" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a> <a id="5652" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a> <a id="5654" href="category-theory.functors-nonunital-precategories.html#5099" class="Bound">G</a><a id="5655" class="Symbol">)</a>
  <a id="5659" href="category-theory.functors-nonunital-precategories.html#5505" class="Function">eq-map-eq-functor-Nonunital-Precategory</a> <a id="5699" class="Symbol">=</a>
    <a id="5705" href="foundation-core.equivalences.html#2754" class="Function">map-equiv</a> <a id="5715" href="category-theory.functors-nonunital-precategories.html#5149" class="Function">equiv-eq-map-eq-functor-Nonunital-Precategory</a>

  <a id="5764" href="category-theory.functors-nonunital-precategories.html#5764" class="Function">eq-eq-map-functor-Nonunital-Precategory</a> <a id="5804" class="Symbol">:</a>
    <a id="5810" class="Symbol">(</a> <a id="5812" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="5846" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a> <a id="5848" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a> <a id="5850" href="category-theory.functors-nonunital-precategories.html#5097" class="Bound">F</a> <a id="5852" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
      <a id="5860" href="category-theory.functors-nonunital-precategories.html#1759" class="Function">map-functor-Nonunital-Precategory</a> <a id="5894" href="category-theory.functors-nonunital-precategories.html#5025" class="Bound">C</a> <a id="5896" href="category-theory.functors-nonunital-precategories.html#5061" class="Bound">D</a> <a id="5898" href="category-theory.functors-nonunital-precategories.html#5099" class="Bound">G</a><a id="5899" class="Symbol">)</a> <a id="5901" class="Symbol">→</a>
    <a id="5907" class="Symbol">(</a> <a id="5909" href="category-theory.functors-nonunital-precategories.html#5097" class="Bound">F</a> <a id="5911" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="5913" href="category-theory.functors-nonunital-precategories.html#5099" class="Bound">G</a><a id="5914" class="Symbol">)</a>
  <a id="5918" href="category-theory.functors-nonunital-precategories.html#5764" class="Function">eq-eq-map-functor-Nonunital-Precategory</a> <a id="5958" class="Symbol">=</a>
    <a id="5964" href="foundation-core.equivalences.html#8070" class="Function">map-inv-equiv</a> <a id="5978" href="category-theory.functors-nonunital-precategories.html#5149" class="Function">equiv-eq-map-eq-functor-Nonunital-Precategory</a>

  <a id="6027" href="category-theory.functors-nonunital-precategories.html#6027" class="Function">is-section-eq-eq-map-functor-Nonunital-Precategory</a> <a id="6078" class="Symbol">:</a>
    <a id="6084" href="category-theory.functors-nonunital-precategories.html#5505" class="Function">eq-map-eq-functor-Nonunital-Precategory</a> <a id="6124" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
    <a id="6130" href="category-theory.functors-nonunital-precategories.html#5764" class="Function">eq-eq-map-functor-Nonunital-Precategory</a> <a id="6170" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="6176" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="6181" href="category-theory.functors-nonunital-precategories.html#6027" class="Function">is-section-eq-eq-map-functor-Nonunital-Precategory</a> <a id="6232" class="Symbol">=</a>
    <a id="6238" href="foundation-core.equivalences.html#8153" class="Function">is-section-map-inv-equiv</a> <a id="6263" href="category-theory.functors-nonunital-precategories.html#5149" class="Function">equiv-eq-map-eq-functor-Nonunital-Precategory</a>

  <a id="6312" href="category-theory.functors-nonunital-precategories.html#6312" class="Function">is-retraction-eq-eq-map-functor-Nonunital-Precategory</a> <a id="6366" class="Symbol">:</a>
    <a id="6372" href="category-theory.functors-nonunital-precategories.html#5764" class="Function">eq-eq-map-functor-Nonunital-Precategory</a> <a id="6412" href="foundation-core.function-types.html#504" class="Function Operator">∘</a>
    <a id="6418" href="category-theory.functors-nonunital-precategories.html#5505" class="Function">eq-map-eq-functor-Nonunital-Precategory</a> <a id="6458" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a>
    <a id="6464" href="foundation-core.function-types.html#307" class="Function">id</a>
  <a id="6469" href="category-theory.functors-nonunital-precategories.html#6312" class="Function">is-retraction-eq-eq-map-functor-Nonunital-Precategory</a> <a id="6523" class="Symbol">=</a>
    <a id="6529" href="foundation-core.equivalences.html#8302" class="Function">is-retraction-map-inv-equiv</a> <a id="6557" href="category-theory.functors-nonunital-precategories.html#5149" class="Function">equiv-eq-map-eq-functor-Nonunital-Precategory</a>
</pre>
### Categorical laws for nonunital functor composition

#### Unit laws for nonunital functor composition

<pre class="Agda"><a id="6722" class="Keyword">module</a> <a id="6729" href="category-theory.functors-nonunital-precategories.html#6729" class="Module">_</a>
  <a id="6733" class="Symbol">{</a><a id="6734" href="category-theory.functors-nonunital-precategories.html#6734" class="Bound">l1</a> <a id="6737" href="category-theory.functors-nonunital-precategories.html#6737" class="Bound">l2</a> <a id="6740" href="category-theory.functors-nonunital-precategories.html#6740" class="Bound">l3</a> <a id="6743" href="category-theory.functors-nonunital-precategories.html#6743" class="Bound">l4</a> <a id="6746" class="Symbol">:</a> <a id="6748" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6753" class="Symbol">}</a>
  <a id="6757" class="Symbol">(</a><a id="6758" href="category-theory.functors-nonunital-precategories.html#6758" class="Bound">C</a> <a id="6760" class="Symbol">:</a> <a id="6762" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="6784" href="category-theory.functors-nonunital-precategories.html#6734" class="Bound">l1</a> <a id="6787" href="category-theory.functors-nonunital-precategories.html#6737" class="Bound">l2</a><a id="6789" class="Symbol">)</a> <a id="6791" class="Symbol">(</a><a id="6792" href="category-theory.functors-nonunital-precategories.html#6792" class="Bound">D</a> <a id="6794" class="Symbol">:</a> <a id="6796" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="6818" href="category-theory.functors-nonunital-precategories.html#6740" class="Bound">l3</a> <a id="6821" href="category-theory.functors-nonunital-precategories.html#6743" class="Bound">l4</a><a id="6823" class="Symbol">)</a>
  <a id="6827" class="Symbol">(</a><a id="6828" href="category-theory.functors-nonunital-precategories.html#6828" class="Bound">F</a> <a id="6830" class="Symbol">:</a> <a id="6832" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="6862" href="category-theory.functors-nonunital-precategories.html#6758" class="Bound">C</a> <a id="6864" href="category-theory.functors-nonunital-precategories.html#6792" class="Bound">D</a><a id="6865" class="Symbol">)</a>
  <a id="6869" class="Keyword">where</a>

  <a id="6878" href="category-theory.functors-nonunital-precategories.html#6878" class="Function">left-unit-law-comp-functor-Nonunital-Precategory</a> <a id="6927" class="Symbol">:</a>
    <a id="6933" href="category-theory.functors-nonunital-precategories.html#4550" class="Function">comp-functor-Nonunital-Precategory</a> <a id="6968" href="category-theory.functors-nonunital-precategories.html#6758" class="Bound">C</a> <a id="6970" href="category-theory.functors-nonunital-precategories.html#6792" class="Bound">D</a> <a id="6972" href="category-theory.functors-nonunital-precategories.html#6792" class="Bound">D</a>
      <a id="6980" class="Symbol">(</a> <a id="6982" href="category-theory.functors-nonunital-precategories.html#2737" class="Function">id-functor-Nonunital-Precategory</a> <a id="7015" href="category-theory.functors-nonunital-precategories.html#6792" class="Bound">D</a><a id="7016" class="Symbol">)</a> <a id="7018" class="Symbol">(</a><a id="7019" href="category-theory.functors-nonunital-precategories.html#6828" class="Bound">F</a><a id="7020" class="Symbol">)</a> <a id="7022" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="7028" href="category-theory.functors-nonunital-precategories.html#6828" class="Bound">F</a>
  <a id="7032" href="category-theory.functors-nonunital-precategories.html#6878" class="Function">left-unit-law-comp-functor-Nonunital-Precategory</a> <a id="7081" class="Symbol">=</a>
    <a id="7087" href="category-theory.functors-nonunital-precategories.html#5764" class="Function">eq-eq-map-functor-Nonunital-Precategory</a> <a id="7127" href="category-theory.functors-nonunital-precategories.html#6758" class="Bound">C</a> <a id="7129" href="category-theory.functors-nonunital-precategories.html#6792" class="Bound">D</a> <a id="7131" class="Symbol">_</a> <a id="7133" class="Symbol">_</a> <a id="7135" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="7143" href="category-theory.functors-nonunital-precategories.html#7143" class="Function">right-unit-law-comp-functor-Nonunital-Precategory</a> <a id="7193" class="Symbol">:</a>
    <a id="7199" href="category-theory.functors-nonunital-precategories.html#4550" class="Function">comp-functor-Nonunital-Precategory</a> <a id="7234" href="category-theory.functors-nonunital-precategories.html#6758" class="Bound">C</a> <a id="7236" href="category-theory.functors-nonunital-precategories.html#6758" class="Bound">C</a> <a id="7238" href="category-theory.functors-nonunital-precategories.html#6792" class="Bound">D</a>
      <a id="7246" class="Symbol">(</a> <a id="7248" href="category-theory.functors-nonunital-precategories.html#6828" class="Bound">F</a><a id="7249" class="Symbol">)</a> <a id="7251" class="Symbol">(</a><a id="7252" href="category-theory.functors-nonunital-precategories.html#2737" class="Function">id-functor-Nonunital-Precategory</a> <a id="7285" href="category-theory.functors-nonunital-precategories.html#6758" class="Bound">C</a><a id="7286" class="Symbol">)</a> <a id="7288" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="7294" href="category-theory.functors-nonunital-precategories.html#6828" class="Bound">F</a>
  <a id="7298" href="category-theory.functors-nonunital-precategories.html#7143" class="Function">right-unit-law-comp-functor-Nonunital-Precategory</a> <a id="7348" class="Symbol">=</a> <a id="7350" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
#### Associativity of functor composition

<pre class="Agda"><a id="7411" class="Keyword">module</a> <a id="7418" href="category-theory.functors-nonunital-precategories.html#7418" class="Module">_</a>
  <a id="7422" class="Symbol">{</a><a id="7423" href="category-theory.functors-nonunital-precategories.html#7423" class="Bound">l1</a> <a id="7426" href="category-theory.functors-nonunital-precategories.html#7426" class="Bound">l1&#39;</a> <a id="7430" href="category-theory.functors-nonunital-precategories.html#7430" class="Bound">l2</a> <a id="7433" href="category-theory.functors-nonunital-precategories.html#7433" class="Bound">l2&#39;</a> <a id="7437" href="category-theory.functors-nonunital-precategories.html#7437" class="Bound">l3</a> <a id="7440" href="category-theory.functors-nonunital-precategories.html#7440" class="Bound">l3&#39;</a> <a id="7444" href="category-theory.functors-nonunital-precategories.html#7444" class="Bound">l4</a> <a id="7447" href="category-theory.functors-nonunital-precategories.html#7447" class="Bound">l4&#39;</a> <a id="7451" class="Symbol">:</a> <a id="7453" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="7458" class="Symbol">}</a>
  <a id="7462" class="Symbol">(</a><a id="7463" href="category-theory.functors-nonunital-precategories.html#7463" class="Bound">A</a> <a id="7465" class="Symbol">:</a> <a id="7467" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="7489" href="category-theory.functors-nonunital-precategories.html#7423" class="Bound">l1</a> <a id="7492" href="category-theory.functors-nonunital-precategories.html#7426" class="Bound">l1&#39;</a><a id="7495" class="Symbol">)</a>
  <a id="7499" class="Symbol">(</a><a id="7500" href="category-theory.functors-nonunital-precategories.html#7500" class="Bound">B</a> <a id="7502" class="Symbol">:</a> <a id="7504" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="7526" href="category-theory.functors-nonunital-precategories.html#7430" class="Bound">l2</a> <a id="7529" href="category-theory.functors-nonunital-precategories.html#7433" class="Bound">l2&#39;</a><a id="7532" class="Symbol">)</a>
  <a id="7536" class="Symbol">(</a><a id="7537" href="category-theory.functors-nonunital-precategories.html#7537" class="Bound">C</a> <a id="7539" class="Symbol">:</a> <a id="7541" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="7563" href="category-theory.functors-nonunital-precategories.html#7437" class="Bound">l3</a> <a id="7566" href="category-theory.functors-nonunital-precategories.html#7440" class="Bound">l3&#39;</a><a id="7569" class="Symbol">)</a>
  <a id="7573" class="Symbol">(</a><a id="7574" href="category-theory.functors-nonunital-precategories.html#7574" class="Bound">D</a> <a id="7576" class="Symbol">:</a> <a id="7578" href="category-theory.nonunital-precategories.html#1333" class="Function">Nonunital-Precategory</a> <a id="7600" href="category-theory.functors-nonunital-precategories.html#7444" class="Bound">l4</a> <a id="7603" href="category-theory.functors-nonunital-precategories.html#7447" class="Bound">l4&#39;</a><a id="7606" class="Symbol">)</a>
  <a id="7610" class="Symbol">(</a><a id="7611" href="category-theory.functors-nonunital-precategories.html#7611" class="Bound">F</a> <a id="7613" class="Symbol">:</a> <a id="7615" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="7645" href="category-theory.functors-nonunital-precategories.html#7463" class="Bound">A</a> <a id="7647" href="category-theory.functors-nonunital-precategories.html#7500" class="Bound">B</a><a id="7648" class="Symbol">)</a>
  <a id="7652" class="Symbol">(</a><a id="7653" href="category-theory.functors-nonunital-precategories.html#7653" class="Bound">G</a> <a id="7655" class="Symbol">:</a> <a id="7657" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="7687" href="category-theory.functors-nonunital-precategories.html#7500" class="Bound">B</a> <a id="7689" href="category-theory.functors-nonunital-precategories.html#7537" class="Bound">C</a><a id="7690" class="Symbol">)</a>
  <a id="7694" class="Symbol">(</a><a id="7695" href="category-theory.functors-nonunital-precategories.html#7695" class="Bound">H</a> <a id="7697" class="Symbol">:</a> <a id="7699" href="category-theory.functors-nonunital-precategories.html#1025" class="Function">functor-Nonunital-Precategory</a> <a id="7729" href="category-theory.functors-nonunital-precategories.html#7537" class="Bound">C</a> <a id="7731" href="category-theory.functors-nonunital-precategories.html#7574" class="Bound">D</a><a id="7732" class="Symbol">)</a>
  <a id="7736" class="Keyword">where</a>

  <a id="7745" href="category-theory.functors-nonunital-precategories.html#7745" class="Function">associative-comp-functor-Nonunital-Precategory</a> <a id="7792" class="Symbol">:</a>
    <a id="7798" href="category-theory.functors-nonunital-precategories.html#4550" class="Function">comp-functor-Nonunital-Precategory</a> <a id="7833" href="category-theory.functors-nonunital-precategories.html#7463" class="Bound">A</a> <a id="7835" href="category-theory.functors-nonunital-precategories.html#7500" class="Bound">B</a> <a id="7837" href="category-theory.functors-nonunital-precategories.html#7574" class="Bound">D</a>
      <a id="7845" class="Symbol">(</a> <a id="7847" href="category-theory.functors-nonunital-precategories.html#4550" class="Function">comp-functor-Nonunital-Precategory</a> <a id="7882" href="category-theory.functors-nonunital-precategories.html#7500" class="Bound">B</a> <a id="7884" href="category-theory.functors-nonunital-precategories.html#7537" class="Bound">C</a> <a id="7886" href="category-theory.functors-nonunital-precategories.html#7574" class="Bound">D</a> <a id="7888" href="category-theory.functors-nonunital-precategories.html#7695" class="Bound">H</a> <a id="7890" href="category-theory.functors-nonunital-precategories.html#7653" class="Bound">G</a><a id="7891" class="Symbol">)</a> <a id="7893" class="Symbol">(</a><a id="7894" href="category-theory.functors-nonunital-precategories.html#7611" class="Bound">F</a><a id="7895" class="Symbol">)</a> <a id="7897" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="7903" href="category-theory.functors-nonunital-precategories.html#4550" class="Function">comp-functor-Nonunital-Precategory</a> <a id="7938" href="category-theory.functors-nonunital-precategories.html#7463" class="Bound">A</a> <a id="7940" href="category-theory.functors-nonunital-precategories.html#7537" class="Bound">C</a> <a id="7942" href="category-theory.functors-nonunital-precategories.html#7574" class="Bound">D</a>
      <a id="7950" class="Symbol">(</a> <a id="7952" href="category-theory.functors-nonunital-precategories.html#7695" class="Bound">H</a><a id="7953" class="Symbol">)</a> <a id="7955" class="Symbol">(</a><a id="7956" href="category-theory.functors-nonunital-precategories.html#4550" class="Function">comp-functor-Nonunital-Precategory</a> <a id="7991" href="category-theory.functors-nonunital-precategories.html#7463" class="Bound">A</a> <a id="7993" href="category-theory.functors-nonunital-precategories.html#7500" class="Bound">B</a> <a id="7995" href="category-theory.functors-nonunital-precategories.html#7537" class="Bound">C</a> <a id="7997" href="category-theory.functors-nonunital-precategories.html#7653" class="Bound">G</a> <a id="7999" href="category-theory.functors-nonunital-precategories.html#7611" class="Bound">F</a><a id="8000" class="Symbol">)</a>
  <a id="8004" href="category-theory.functors-nonunital-precategories.html#7745" class="Function">associative-comp-functor-Nonunital-Precategory</a> <a id="8051" class="Symbol">=</a>
    <a id="8057" href="category-theory.functors-nonunital-precategories.html#5764" class="Function">eq-eq-map-functor-Nonunital-Precategory</a> <a id="8097" href="category-theory.functors-nonunital-precategories.html#7463" class="Bound">A</a> <a id="8099" href="category-theory.functors-nonunital-precategories.html#7574" class="Bound">D</a> <a id="8101" class="Symbol">_</a> <a id="8103" class="Symbol">_</a> <a id="8105" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
#### Mac Lane pentagon for nonunital functor composition

```text
    (I(GH))F ---- I((GH)F)
          /        \
         /          \
  ((IH)G)F          I(H(GF))
          \        /
            \    /
           (IH)(GF)
```

The proof remains to be formalized.

```text
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Nonunital-Precategory l1 l1')
  (B : Nonunital-Precategory l2 l2')
  (C : Nonunital-Precategory l3 l3')
  (D : Nonunital-Precategory l4 l4')
  (E : Nonunital-Precategory l4 l4')
  (F : functor-Nonunital-Precategory A B)
  (G : functor-Nonunital-Precategory B C)
  (H : functor-Nonunital-Precategory C D)
  (I : functor-Nonunital-Precategory D E)
  where

  mac-lane-pentagon-comp-functor-Nonunital-Precategory :
    coherence-pentagon-identifications
      { x =
        comp-functor-Nonunital-Precategory A B E
        ( comp-functor-Nonunital-Precategory B D E I
          ( comp-functor-Nonunital-Precategory B C D H G))
        ( F)}
      { comp-functor-Nonunital-Precategory A D E I
        ( comp-functor-Nonunital-Precategory A B D
          ( comp-functor-Nonunital-Precategory B C D H G)
          ( F))}
      { comp-functor-Nonunital-Precategory A B E
        ( comp-functor-Nonunital-Precategory B C E
          ( comp-functor-Nonunital-Precategory C D E I H)
          ( G))
        ( F)}
      { comp-functor-Nonunital-Precategory A D E
        ( I)
        ( comp-functor-Nonunital-Precategory A C D
          ( H)
          ( comp-functor-Nonunital-Precategory A B C G F))}
      { comp-functor-Nonunital-Precategory A C E
        ( comp-functor-Nonunital-Precategory C D E I H)
        ( comp-functor-Nonunital-Precategory A B C G F)}
      ( associative-comp-functor-Nonunital-Precategory A B D E
        ( F) (comp-functor-Nonunital-Precategory B C D H G) (I))
      ( ap
        ( λ p → comp-functor-Nonunital-Precategory A B E p F)
        ( inv (associative-comp-functor-Nonunital-Precategory B C D E G H I)))
      ( ap
        ( λ p → comp-functor-Nonunital-Precategory A D E I p)
        ( associative-comp-functor-Nonunital-Precategory A B C D F G H))
      ( associative-comp-functor-Nonunital-Precategory A B C E
        ( F) (G) (comp-functor-Nonunital-Precategory C D E I H))
      ( inv
        ( associative-comp-functor-Nonunital-Precategory A C D E
          (comp-functor-Nonunital-Precategory A B C G F) H I))
  mac-lane-pentagon-comp-functor-Nonunital-Precategory = {!!}
```

## External links

- [semifunctor](https://ncatlab.org/nlab/show/semifunctor) at $n$Lab
