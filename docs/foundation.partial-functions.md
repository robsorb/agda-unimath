# Partial functions

<pre class="Agda"><a id="30" class="Keyword">module</a> <a id="37" href="foundation.partial-functions.html" class="Module">foundation.partial-functions</a> <a id="66" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="122" class="Keyword">open</a> <a id="127" class="Keyword">import</a> <a id="134" href="foundation.partial-elements.html" class="Module">foundation.partial-elements</a>
<a id="162" class="Keyword">open</a> <a id="167" class="Keyword">import</a> <a id="174" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="202" class="Keyword">open</a> <a id="207" class="Keyword">import</a> <a id="214" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
</pre>
</details>

## Idea

A {{#concept "partial function" Agda=partial-function}} from `A` to `B` is a
function from `A` into the type of
[partial elements](foundation.partial-elements.md) of `B`. In other words, a
partial function is a function

```text
  A → Σ (P : Prop), (P → B).
```

Given a partial function `f : A → B` and an element `a : A`, we say that `f` is
{{#concept "defined" Disambiguation="partial function" Agda=is-defined-partial-function}}
at `a` if the partial element `f a` of `A` is defined.

Partial functions can be described
[equivalently](foundation-core.equivalences.md) as
[morphisms of arrows](foundation.morphisms-arrows.md)

```text
  ∅     1   ∅
  |     |   |
  |  ⇒  | ∘ |
  ∨     ∨   ∨
  A   Prop  B
```

where the composition operation is
[composition](species.composition-cauchy-series-species-of-types.md) of
[polynomial endofunctors](trees.polynomial-endofunctors.md).

## Definitions

### Partial dependent functions

<pre class="Agda"><a id="partial-dependent-function"></a><a id="1208" href="foundation.partial-functions.html#1208" class="Function">partial-dependent-function</a> <a id="1235" class="Symbol">:</a>
  <a id="1239" class="Symbol">{</a><a id="1240" href="foundation.partial-functions.html#1240" class="Bound">l1</a> <a id="1243" href="foundation.partial-functions.html#1243" class="Bound">l2</a> <a id="1246" class="Symbol">:</a> <a id="1248" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1253" class="Symbol">}</a> <a id="1255" class="Symbol">(</a><a id="1256" href="foundation.partial-functions.html#1256" class="Bound">l3</a> <a id="1259" class="Symbol">:</a> <a id="1261" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1266" class="Symbol">)</a> <a id="1268" class="Symbol">(</a><a id="1269" href="foundation.partial-functions.html#1269" class="Bound">A</a> <a id="1271" class="Symbol">:</a> <a id="1273" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1276" href="foundation.partial-functions.html#1240" class="Bound">l1</a><a id="1278" class="Symbol">)</a> <a id="1280" class="Symbol">(</a><a id="1281" href="foundation.partial-functions.html#1281" class="Bound">B</a> <a id="1283" class="Symbol">:</a> <a id="1285" href="foundation.partial-functions.html#1269" class="Bound">A</a> <a id="1287" class="Symbol">→</a> <a id="1289" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1292" href="foundation.partial-functions.html#1243" class="Bound">l2</a><a id="1294" class="Symbol">)</a> <a id="1296" class="Symbol">→</a>
  <a id="1300" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1303" class="Symbol">(</a><a id="1304" href="foundation.partial-functions.html#1240" class="Bound">l1</a> <a id="1307" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1309" href="foundation.partial-functions.html#1243" class="Bound">l2</a> <a id="1312" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1314" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1319" href="foundation.partial-functions.html#1256" class="Bound">l3</a><a id="1321" class="Symbol">)</a>
<a id="1323" href="foundation.partial-functions.html#1208" class="Function">partial-dependent-function</a> <a id="1350" href="foundation.partial-functions.html#1350" class="Bound">l3</a> <a id="1353" href="foundation.partial-functions.html#1353" class="Bound">A</a> <a id="1355" href="foundation.partial-functions.html#1355" class="Bound">B</a> <a id="1357" class="Symbol">=</a>
  <a id="1361" class="Symbol">(</a><a id="1362" href="foundation.partial-functions.html#1362" class="Bound">x</a> <a id="1364" class="Symbol">:</a> <a id="1366" href="foundation.partial-functions.html#1353" class="Bound">A</a><a id="1367" class="Symbol">)</a> <a id="1369" class="Symbol">→</a> <a id="1371" href="foundation.partial-elements.html#1254" class="Function">partial-element</a> <a id="1387" href="foundation.partial-functions.html#1350" class="Bound">l3</a> <a id="1390" class="Symbol">(</a><a id="1391" href="foundation.partial-functions.html#1355" class="Bound">B</a> <a id="1393" href="foundation.partial-functions.html#1362" class="Bound">x</a><a id="1394" class="Symbol">)</a>
</pre>
### Partial functions

<pre class="Agda"><a id="partial-function"></a><a id="1432" href="foundation.partial-functions.html#1432" class="Function">partial-function</a> <a id="1449" class="Symbol">:</a>
  <a id="1453" class="Symbol">{</a><a id="1454" href="foundation.partial-functions.html#1454" class="Bound">l1</a> <a id="1457" href="foundation.partial-functions.html#1457" class="Bound">l2</a> <a id="1460" class="Symbol">:</a> <a id="1462" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1467" class="Symbol">}</a> <a id="1469" class="Symbol">(</a><a id="1470" href="foundation.partial-functions.html#1470" class="Bound">l3</a> <a id="1473" class="Symbol">:</a> <a id="1475" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1480" class="Symbol">)</a> <a id="1482" class="Symbol">→</a> <a id="1484" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1487" href="foundation.partial-functions.html#1454" class="Bound">l1</a> <a id="1490" class="Symbol">→</a> <a id="1492" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1495" href="foundation.partial-functions.html#1457" class="Bound">l2</a> <a id="1498" class="Symbol">→</a> <a id="1500" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1503" class="Symbol">(</a><a id="1504" href="foundation.partial-functions.html#1454" class="Bound">l1</a> <a id="1507" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1509" href="foundation.partial-functions.html#1457" class="Bound">l2</a> <a id="1512" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1514" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1519" href="foundation.partial-functions.html#1470" class="Bound">l3</a><a id="1521" class="Symbol">)</a>
<a id="1523" href="foundation.partial-functions.html#1432" class="Function">partial-function</a> <a id="1540" href="foundation.partial-functions.html#1540" class="Bound">l3</a> <a id="1543" href="foundation.partial-functions.html#1543" class="Bound">A</a> <a id="1545" href="foundation.partial-functions.html#1545" class="Bound">B</a> <a id="1547" class="Symbol">=</a> <a id="1549" href="foundation.partial-functions.html#1208" class="Function">partial-dependent-function</a> <a id="1576" href="foundation.partial-functions.html#1540" class="Bound">l3</a> <a id="1579" href="foundation.partial-functions.html#1543" class="Bound">A</a> <a id="1581" class="Symbol">(λ</a> <a id="1584" href="foundation.partial-functions.html#1584" class="Bound">_</a> <a id="1586" class="Symbol">→</a> <a id="1588" href="foundation.partial-functions.html#1545" class="Bound">B</a><a id="1589" class="Symbol">)</a>
</pre>
### The predicate on partial dependent functions of being defined at an element in the domain

<pre class="Agda"><a id="1699" class="Keyword">module</a> <a id="1706" href="foundation.partial-functions.html#1706" class="Module">_</a>
  <a id="1710" class="Symbol">{</a><a id="1711" href="foundation.partial-functions.html#1711" class="Bound">l1</a> <a id="1714" href="foundation.partial-functions.html#1714" class="Bound">l2</a> <a id="1717" href="foundation.partial-functions.html#1717" class="Bound">l3</a> <a id="1720" class="Symbol">:</a> <a id="1722" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1727" class="Symbol">}</a> <a id="1729" class="Symbol">{</a><a id="1730" href="foundation.partial-functions.html#1730" class="Bound">A</a> <a id="1732" class="Symbol">:</a> <a id="1734" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1737" href="foundation.partial-functions.html#1711" class="Bound">l1</a><a id="1739" class="Symbol">}</a> <a id="1741" class="Symbol">{</a><a id="1742" href="foundation.partial-functions.html#1742" class="Bound">B</a> <a id="1744" class="Symbol">:</a> <a id="1746" href="foundation.partial-functions.html#1730" class="Bound">A</a> <a id="1748" class="Symbol">→</a> <a id="1750" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1753" href="foundation.partial-functions.html#1714" class="Bound">l2</a><a id="1755" class="Symbol">}</a>
  <a id="1759" class="Symbol">(</a><a id="1760" href="foundation.partial-functions.html#1760" class="Bound">f</a> <a id="1762" class="Symbol">:</a> <a id="1764" href="foundation.partial-functions.html#1208" class="Function">partial-dependent-function</a> <a id="1791" href="foundation.partial-functions.html#1717" class="Bound">l3</a> <a id="1794" href="foundation.partial-functions.html#1730" class="Bound">A</a> <a id="1796" href="foundation.partial-functions.html#1742" class="Bound">B</a><a id="1797" class="Symbol">)</a> <a id="1799" class="Symbol">(</a><a id="1800" href="foundation.partial-functions.html#1800" class="Bound">a</a> <a id="1802" class="Symbol">:</a> <a id="1804" href="foundation.partial-functions.html#1730" class="Bound">A</a><a id="1805" class="Symbol">)</a>
  <a id="1809" class="Keyword">where</a>

  <a id="1818" href="foundation.partial-functions.html#1818" class="Function">is-defined-prop-partial-dependent-function</a> <a id="1861" class="Symbol">:</a> <a id="1863" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1868" href="foundation.partial-functions.html#1717" class="Bound">l3</a>
  <a id="1873" href="foundation.partial-functions.html#1818" class="Function">is-defined-prop-partial-dependent-function</a> <a id="1916" class="Symbol">=</a>
    <a id="1922" href="foundation.partial-elements.html#1463" class="Function">is-defined-prop-partial-element</a> <a id="1954" class="Symbol">(</a><a id="1955" href="foundation.partial-functions.html#1760" class="Bound">f</a> <a id="1957" href="foundation.partial-functions.html#1800" class="Bound">a</a><a id="1958" class="Symbol">)</a>

  <a id="1963" href="foundation.partial-functions.html#1963" class="Function">is-defined-partial-dependent-function</a> <a id="2001" class="Symbol">:</a> <a id="2003" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2006" href="foundation.partial-functions.html#1717" class="Bound">l3</a>
  <a id="2011" href="foundation.partial-functions.html#1963" class="Function">is-defined-partial-dependent-function</a> <a id="2049" class="Symbol">=</a>
    <a id="2055" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2065" href="foundation.partial-functions.html#1818" class="Function">is-defined-prop-partial-dependent-function</a>
</pre>
### The predicate on partial functions of being defined at an element in the domain

<pre class="Agda"><a id="2206" class="Keyword">module</a> <a id="2213" href="foundation.partial-functions.html#2213" class="Module">_</a>
  <a id="2217" class="Symbol">{</a><a id="2218" href="foundation.partial-functions.html#2218" class="Bound">l1</a> <a id="2221" href="foundation.partial-functions.html#2221" class="Bound">l2</a> <a id="2224" href="foundation.partial-functions.html#2224" class="Bound">l3</a> <a id="2227" class="Symbol">:</a> <a id="2229" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2234" class="Symbol">}</a> <a id="2236" class="Symbol">{</a><a id="2237" href="foundation.partial-functions.html#2237" class="Bound">A</a> <a id="2239" class="Symbol">:</a> <a id="2241" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2244" href="foundation.partial-functions.html#2218" class="Bound">l1</a><a id="2246" class="Symbol">}</a> <a id="2248" class="Symbol">{</a><a id="2249" href="foundation.partial-functions.html#2249" class="Bound">B</a> <a id="2251" class="Symbol">:</a> <a id="2253" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2256" href="foundation.partial-functions.html#2221" class="Bound">l2</a><a id="2258" class="Symbol">}</a> <a id="2260" class="Symbol">(</a><a id="2261" href="foundation.partial-functions.html#2261" class="Bound">f</a> <a id="2263" class="Symbol">:</a> <a id="2265" href="foundation.partial-functions.html#1432" class="Function">partial-function</a> <a id="2282" href="foundation.partial-functions.html#2224" class="Bound">l3</a> <a id="2285" href="foundation.partial-functions.html#2237" class="Bound">A</a> <a id="2287" href="foundation.partial-functions.html#2249" class="Bound">B</a><a id="2288" class="Symbol">)</a>
  <a id="2292" class="Symbol">(</a><a id="2293" href="foundation.partial-functions.html#2293" class="Bound">a</a> <a id="2295" class="Symbol">:</a> <a id="2297" href="foundation.partial-functions.html#2237" class="Bound">A</a><a id="2298" class="Symbol">)</a>
  <a id="2302" class="Keyword">where</a>

  <a id="2311" href="foundation.partial-functions.html#2311" class="Function">is-defined-prop-partial-function</a> <a id="2344" class="Symbol">:</a> <a id="2346" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="2351" href="foundation.partial-functions.html#2224" class="Bound">l3</a>
  <a id="2356" href="foundation.partial-functions.html#2311" class="Function">is-defined-prop-partial-function</a> <a id="2389" class="Symbol">=</a>
    <a id="2395" href="foundation.partial-functions.html#1818" class="Function">is-defined-prop-partial-dependent-function</a> <a id="2438" href="foundation.partial-functions.html#2261" class="Bound">f</a> <a id="2440" href="foundation.partial-functions.html#2293" class="Bound">a</a>

  <a id="2445" href="foundation.partial-functions.html#2445" class="Function">is-defined-partial-function</a> <a id="2473" class="Symbol">:</a> <a id="2475" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2478" href="foundation.partial-functions.html#2224" class="Bound">l3</a>
  <a id="2483" href="foundation.partial-functions.html#2445" class="Function">is-defined-partial-function</a> <a id="2511" class="Symbol">=</a>
    <a id="2517" href="foundation.partial-functions.html#1963" class="Function">is-defined-partial-dependent-function</a> <a id="2555" href="foundation.partial-functions.html#2261" class="Bound">f</a> <a id="2557" href="foundation.partial-functions.html#2293" class="Bound">a</a>
</pre>
### The partial dependent function obtained from a dependent function

<pre class="Agda"><a id="2643" class="Keyword">module</a> <a id="2650" href="foundation.partial-functions.html#2650" class="Module">_</a>
  <a id="2654" class="Symbol">{</a><a id="2655" href="foundation.partial-functions.html#2655" class="Bound">l1</a> <a id="2658" href="foundation.partial-functions.html#2658" class="Bound">l2</a> <a id="2661" class="Symbol">:</a> <a id="2663" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2668" class="Symbol">}</a> <a id="2670" class="Symbol">{</a><a id="2671" href="foundation.partial-functions.html#2671" class="Bound">A</a> <a id="2673" class="Symbol">:</a> <a id="2675" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2678" href="foundation.partial-functions.html#2655" class="Bound">l1</a><a id="2680" class="Symbol">}</a> <a id="2682" class="Symbol">{</a><a id="2683" href="foundation.partial-functions.html#2683" class="Bound">B</a> <a id="2685" class="Symbol">:</a> <a id="2687" href="foundation.partial-functions.html#2671" class="Bound">A</a> <a id="2689" class="Symbol">→</a> <a id="2691" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2694" href="foundation.partial-functions.html#2658" class="Bound">l2</a><a id="2696" class="Symbol">}</a> <a id="2698" class="Symbol">(</a><a id="2699" href="foundation.partial-functions.html#2699" class="Bound">f</a> <a id="2701" class="Symbol">:</a> <a id="2703" class="Symbol">(</a><a id="2704" href="foundation.partial-functions.html#2704" class="Bound">x</a> <a id="2706" class="Symbol">:</a> <a id="2708" href="foundation.partial-functions.html#2671" class="Bound">A</a><a id="2709" class="Symbol">)</a> <a id="2711" class="Symbol">→</a> <a id="2713" href="foundation.partial-functions.html#2683" class="Bound">B</a> <a id="2715" href="foundation.partial-functions.html#2704" class="Bound">x</a><a id="2716" class="Symbol">)</a>
  <a id="2720" class="Keyword">where</a>

  <a id="2729" href="foundation.partial-functions.html#2729" class="Function">partial-dependent-function-dependent-function</a> <a id="2775" class="Symbol">:</a>
    <a id="2781" href="foundation.partial-functions.html#1208" class="Function">partial-dependent-function</a> <a id="2808" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="2814" href="foundation.partial-functions.html#2671" class="Bound">A</a> <a id="2816" href="foundation.partial-functions.html#2683" class="Bound">B</a>
  <a id="2820" href="foundation.partial-functions.html#2729" class="Function">partial-dependent-function-dependent-function</a> <a id="2866" href="foundation.partial-functions.html#2866" class="Bound">a</a> <a id="2868" class="Symbol">=</a>
    <a id="2874" href="foundation.partial-elements.html#1717" class="Function">unit-partial-element</a> <a id="2895" class="Symbol">(</a><a id="2896" href="foundation.partial-functions.html#2699" class="Bound">f</a> <a id="2898" href="foundation.partial-functions.html#2866" class="Bound">a</a><a id="2899" class="Symbol">)</a>
</pre>
### The partial function obtained from a function

<pre class="Agda"><a id="2965" class="Keyword">module</a> <a id="2972" href="foundation.partial-functions.html#2972" class="Module">_</a>
  <a id="2976" class="Symbol">{</a><a id="2977" href="foundation.partial-functions.html#2977" class="Bound">l1</a> <a id="2980" href="foundation.partial-functions.html#2980" class="Bound">l2</a> <a id="2983" class="Symbol">:</a> <a id="2985" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2990" class="Symbol">}</a> <a id="2992" class="Symbol">{</a><a id="2993" href="foundation.partial-functions.html#2993" class="Bound">A</a> <a id="2995" class="Symbol">:</a> <a id="2997" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3000" href="foundation.partial-functions.html#2977" class="Bound">l1</a><a id="3002" class="Symbol">}</a> <a id="3004" class="Symbol">{</a><a id="3005" href="foundation.partial-functions.html#3005" class="Bound">B</a> <a id="3007" class="Symbol">:</a> <a id="3009" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3012" href="foundation.partial-functions.html#2980" class="Bound">l2</a><a id="3014" class="Symbol">}</a> <a id="3016" class="Symbol">(</a><a id="3017" href="foundation.partial-functions.html#3017" class="Bound">f</a> <a id="3019" class="Symbol">:</a> <a id="3021" href="foundation.partial-functions.html#2993" class="Bound">A</a> <a id="3023" class="Symbol">→</a> <a id="3025" href="foundation.partial-functions.html#3005" class="Bound">B</a><a id="3026" class="Symbol">)</a>
  <a id="3030" class="Keyword">where</a>

  <a id="3039" href="foundation.partial-functions.html#3039" class="Function">partial-function-function</a> <a id="3065" class="Symbol">:</a> <a id="3067" href="foundation.partial-functions.html#1432" class="Function">partial-function</a> <a id="3084" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="3090" href="foundation.partial-functions.html#2993" class="Bound">A</a> <a id="3092" href="foundation.partial-functions.html#3005" class="Bound">B</a>
  <a id="3096" href="foundation.partial-functions.html#3039" class="Function">partial-function-function</a> <a id="3122" class="Symbol">=</a> <a id="3124" href="foundation.partial-functions.html#2729" class="Function">partial-dependent-function-dependent-function</a> <a id="3170" href="foundation.partial-functions.html#3017" class="Bound">f</a>
</pre>
## See also

- [Copartial functions](foundation.copartial-functions.md)
- [Partial elements](foundation.partial-elements.md)
- [Partial sequences](lists.partial-sequences.md)
