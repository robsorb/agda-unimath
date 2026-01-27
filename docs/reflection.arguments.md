# Arguments

<pre class="Agda"><a id="22" class="Keyword">module</a> <a id="29" href="reflection.arguments.html" class="Module">reflection.arguments</a> <a id="50" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="106" class="Keyword">open</a> <a id="111" class="Keyword">import</a> <a id="118" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

An argument to a function is a term together with some information about it. The
argument has three properties:

1. Visibility: whether they are visible, hidden, or an instance
2. Relevance: whether they are relevant or not (see,
   [docs](https://agda.readthedocs.io/en/latest/language/irrelevance.html))
3. Quantity: whether they are run-time relevant or not (see,
   [docs](https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html))

The properties of `Relevance-Argument-Agda` and `Quantity-Argument-Agda` are
combined in one, called `Modality-Argument-Agda`.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definitions

<pre class="Agda"><a id="858" class="Keyword">data</a> <a id="Visibility-Argument-Agda"></a><a id="863" href="reflection.arguments.html#863" class="Datatype">Visibility-Argument-Agda</a> <a id="888" class="Symbol">:</a> <a id="890" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="893" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="899" class="Keyword">where</a>
  <a id="Visibility-Argument-Agda.visible-Visibility-Argument-Agda"></a><a id="907" href="reflection.arguments.html#907" class="InductiveConstructor">visible-Visibility-Argument-Agda</a> <a id="940" class="Symbol">:</a> <a id="942" href="reflection.arguments.html#863" class="Datatype">Visibility-Argument-Agda</a>
  <a id="Visibility-Argument-Agda.hidden-Visibility-Argument-Agda"></a><a id="969" href="reflection.arguments.html#969" class="InductiveConstructor">hidden-Visibility-Argument-Agda</a> <a id="1001" class="Symbol">:</a> <a id="1003" href="reflection.arguments.html#863" class="Datatype">Visibility-Argument-Agda</a>
  <a id="Visibility-Argument-Agda.instance-Visibility-Argument-Agda"></a><a id="1030" href="reflection.arguments.html#1030" class="InductiveConstructor">instance-Visibility-Argument-Agda</a> <a id="1064" class="Symbol">:</a> <a id="1066" href="reflection.arguments.html#863" class="Datatype">Visibility-Argument-Agda</a>

<a id="1092" class="Keyword">data</a> <a id="Relevance-Argument-Agda"></a><a id="1097" href="reflection.arguments.html#1097" class="Datatype">Relevance-Argument-Agda</a> <a id="1121" class="Symbol">:</a> <a id="1123" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1126" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1132" class="Keyword">where</a>
  <a id="Relevance-Argument-Agda.relevant-Relevance-Argument-Agda"></a><a id="1140" href="reflection.arguments.html#1140" class="InductiveConstructor">relevant-Relevance-Argument-Agda</a> <a id="1173" class="Symbol">:</a> <a id="1175" href="reflection.arguments.html#1097" class="Datatype">Relevance-Argument-Agda</a>
  <a id="Relevance-Argument-Agda.irrelevant-Relevance-Argument-Agda"></a><a id="1201" href="reflection.arguments.html#1201" class="InductiveConstructor">irrelevant-Relevance-Argument-Agda</a> <a id="1236" class="Symbol">:</a> <a id="1238" href="reflection.arguments.html#1097" class="Datatype">Relevance-Argument-Agda</a>

<a id="1263" class="Keyword">data</a> <a id="Quantity-Argument-Agda"></a><a id="1268" href="reflection.arguments.html#1268" class="Datatype">Quantity-Argument-Agda</a> <a id="1291" class="Symbol">:</a> <a id="1293" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1296" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1302" class="Keyword">where</a>
  <a id="Quantity-Argument-Agda.zero-Quantity-Argument-Agda"></a><a id="1310" href="reflection.arguments.html#1310" class="InductiveConstructor">zero-Quantity-Argument-Agda</a> <a id="1338" class="Symbol">:</a> <a id="1340" href="reflection.arguments.html#1268" class="Datatype">Quantity-Argument-Agda</a>
  <a id="Quantity-Argument-Agda.omega-Quantity-Argument-Agda"></a><a id="1365" href="reflection.arguments.html#1365" class="InductiveConstructor">omega-Quantity-Argument-Agda</a> <a id="1394" class="Symbol">:</a> <a id="1396" href="reflection.arguments.html#1268" class="Datatype">Quantity-Argument-Agda</a>

<a id="1420" class="Keyword">data</a> <a id="Modality-Argument-Agda"></a><a id="1425" href="reflection.arguments.html#1425" class="Datatype">Modality-Argument-Agda</a> <a id="1448" class="Symbol">:</a> <a id="1450" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1453" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1459" class="Keyword">where</a>
  <a id="Modality-Argument-Agda.cons-Modality-Argument-Agda"></a><a id="1467" href="reflection.arguments.html#1467" class="InductiveConstructor">cons-Modality-Argument-Agda</a> <a id="1495" class="Symbol">:</a>
    <a id="1501" href="reflection.arguments.html#1097" class="Datatype">Relevance-Argument-Agda</a> <a id="1525" class="Symbol">→</a> <a id="1527" href="reflection.arguments.html#1268" class="Datatype">Quantity-Argument-Agda</a> <a id="1550" class="Symbol">→</a> <a id="1552" href="reflection.arguments.html#1425" class="Datatype">Modality-Argument-Agda</a>

<a id="1576" class="Keyword">data</a> <a id="Info-Argument-Agda"></a><a id="1581" href="reflection.arguments.html#1581" class="Datatype">Info-Argument-Agda</a> <a id="1600" class="Symbol">:</a> <a id="1602" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1605" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="1611" class="Keyword">where</a>
  <a id="Info-Argument-Agda.cons-Info-Argument-Agda"></a><a id="1619" href="reflection.arguments.html#1619" class="InductiveConstructor">cons-Info-Argument-Agda</a> <a id="1643" class="Symbol">:</a>
    <a id="1649" href="reflection.arguments.html#863" class="Datatype">Visibility-Argument-Agda</a> <a id="1674" class="Symbol">→</a> <a id="1676" href="reflection.arguments.html#1425" class="Datatype">Modality-Argument-Agda</a> <a id="1699" class="Symbol">→</a> <a id="1701" href="reflection.arguments.html#1581" class="Datatype">Info-Argument-Agda</a>

<a id="1721" class="Keyword">data</a> <a id="Argument-Agda"></a><a id="1726" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="1740" class="Symbol">{</a><a id="1741" href="reflection.arguments.html#1741" class="Bound">l</a> <a id="1743" class="Symbol">:</a> <a id="1745" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1750" class="Symbol">}</a> <a id="1752" class="Symbol">(</a><a id="1753" href="reflection.arguments.html#1753" class="Bound">A</a> <a id="1755" class="Symbol">:</a> <a id="1757" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1760" href="reflection.arguments.html#1741" class="Bound">l</a><a id="1761" class="Symbol">)</a> <a id="1763" class="Symbol">:</a> <a id="1765" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1768" href="reflection.arguments.html#1741" class="Bound">l</a> <a id="1770" class="Keyword">where</a>
  <a id="Argument-Agda.cons-Argument-Agda"></a><a id="1778" href="reflection.arguments.html#1778" class="InductiveConstructor">cons-Argument-Agda</a> <a id="1797" class="Symbol">:</a> <a id="1799" href="reflection.arguments.html#1581" class="Datatype">Info-Argument-Agda</a> <a id="1818" class="Symbol">→</a> <a id="1820" href="reflection.arguments.html#1753" class="Bound">A</a> <a id="1822" class="Symbol">→</a> <a id="1824" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="1838" href="reflection.arguments.html#1753" class="Bound">A</a>
</pre>
<details><summary>Bindings</summary>

<pre class="Agda"><a id="1891" class="Symbol">{-#</a> <a id="1895" class="Keyword">BUILTIN</a> <a id="1903" class="Keyword">HIDING</a> <a id="1910" href="reflection.arguments.html#863" class="Datatype">Visibility-Argument-Agda</a> <a id="1935" class="Symbol">#-}</a>
<a id="1939" class="Symbol">{-#</a> <a id="1943" class="Keyword">BUILTIN</a> <a id="1951" class="Keyword">VISIBLE</a> <a id="1959" href="reflection.arguments.html#907" class="InductiveConstructor">visible-Visibility-Argument-Agda</a> <a id="1992" class="Symbol">#-}</a>
<a id="1996" class="Symbol">{-#</a> <a id="2000" class="Keyword">BUILTIN</a> <a id="2008" class="Keyword">HIDDEN</a> <a id="2015" href="reflection.arguments.html#969" class="InductiveConstructor">hidden-Visibility-Argument-Agda</a> <a id="2047" class="Symbol">#-}</a>
<a id="2051" class="Symbol">{-#</a> <a id="2055" class="Keyword">BUILTIN</a> <a id="2063" class="Keyword">INSTANCE</a> <a id="2072" href="reflection.arguments.html#1030" class="InductiveConstructor">instance-Visibility-Argument-Agda</a> <a id="2106" class="Symbol">#-}</a>

<a id="2111" class="Symbol">{-#</a> <a id="2115" class="Keyword">BUILTIN</a> <a id="2123" class="Keyword">RELEVANCE</a> <a id="2133" href="reflection.arguments.html#1097" class="Datatype">Relevance-Argument-Agda</a> <a id="2157" class="Symbol">#-}</a>
<a id="2161" class="Symbol">{-#</a> <a id="2165" class="Keyword">BUILTIN</a> <a id="2173" class="Keyword">RELEVANT</a> <a id="2182" href="reflection.arguments.html#1140" class="InductiveConstructor">relevant-Relevance-Argument-Agda</a> <a id="2215" class="Symbol">#-}</a>
<a id="2219" class="Symbol">{-#</a> <a id="2223" class="Keyword">BUILTIN</a> <a id="2231" class="Keyword">IRRELEVANT</a> <a id="2242" href="reflection.arguments.html#1201" class="InductiveConstructor">irrelevant-Relevance-Argument-Agda</a> <a id="2277" class="Symbol">#-}</a>

<a id="2282" class="Symbol">{-#</a> <a id="2286" class="Keyword">BUILTIN</a> <a id="2294" class="Keyword">QUANTITY</a> <a id="2303" href="reflection.arguments.html#1268" class="Datatype">Quantity-Argument-Agda</a> <a id="2326" class="Symbol">#-}</a>
<a id="2330" class="Symbol">{-#</a> <a id="2334" class="Keyword">BUILTIN</a> <a id="2342" class="Keyword">QUANTITY-0</a> <a id="2353" href="reflection.arguments.html#1310" class="InductiveConstructor">zero-Quantity-Argument-Agda</a> <a id="2381" class="Symbol">#-}</a>
<a id="2385" class="Symbol">{-#</a> <a id="2389" class="Keyword">BUILTIN</a> <a id="2397" class="Keyword">QUANTITY-ω</a> <a id="2408" href="reflection.arguments.html#1365" class="InductiveConstructor">omega-Quantity-Argument-Agda</a> <a id="2437" class="Symbol">#-}</a>

<a id="2442" class="Symbol">{-#</a> <a id="2446" class="Keyword">BUILTIN</a> <a id="2454" class="Keyword">MODALITY</a> <a id="2463" href="reflection.arguments.html#1425" class="Datatype">Modality-Argument-Agda</a> <a id="2486" class="Symbol">#-}</a>
<a id="2490" class="Symbol">{-#</a> <a id="2494" class="Keyword">BUILTIN</a> <a id="2502" class="Keyword">MODALITY-CONSTRUCTOR</a> <a id="2523" href="reflection.arguments.html#1467" class="InductiveConstructor">cons-Modality-Argument-Agda</a> <a id="2551" class="Symbol">#-}</a>

<a id="2556" class="Symbol">{-#</a> <a id="2560" class="Keyword">BUILTIN</a> <a id="2568" class="Keyword">ARGINFO</a> <a id="2576" href="reflection.arguments.html#1581" class="Datatype">Info-Argument-Agda</a> <a id="2595" class="Symbol">#-}</a>
<a id="2599" class="Symbol">{-#</a> <a id="2603" class="Keyword">BUILTIN</a> <a id="2611" class="Keyword">ARGARGINFO</a> <a id="2622" href="reflection.arguments.html#1619" class="InductiveConstructor">cons-Info-Argument-Agda</a> <a id="2646" class="Symbol">#-}</a>

<a id="2651" class="Symbol">{-#</a> <a id="2655" class="Keyword">BUILTIN</a> <a id="2663" class="Keyword">ARG</a> <a id="2667" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="2681" class="Symbol">#-}</a>
<a id="2685" class="Symbol">{-#</a> <a id="2689" class="Keyword">BUILTIN</a> <a id="2697" class="Keyword">ARGARG</a> <a id="2704" href="reflection.arguments.html#1778" class="InductiveConstructor">cons-Argument-Agda</a> <a id="2723" class="Symbol">#-}</a>
</pre>
</details>

## Helpers

We create helper patterns for the two most common type of arguments.

<pre class="Agda"><a id="2834" class="Comment">-- visible-Argument-Agda : {l : Level} {A : UU l} → A → Argument-Agda A</a>
<a id="2906" class="Keyword">pattern</a> <a id="visible-Argument-Agda"></a><a id="2914" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="2936" href="reflection.arguments.html#3161" class="Bound">t</a> <a id="2938" class="Symbol">=</a>
  <a id="2942" href="reflection.arguments.html#1778" class="InductiveConstructor">cons-Argument-Agda</a>
    <a id="2965" class="Symbol">(</a> <a id="2967" href="reflection.arguments.html#1619" class="InductiveConstructor">cons-Info-Argument-Agda</a>
      <a id="2997" class="Symbol">(</a> <a id="2999" href="reflection.arguments.html#907" class="InductiveConstructor">visible-Visibility-Argument-Agda</a><a id="3031" class="Symbol">)</a>
      <a id="3039" class="Symbol">(</a> <a id="3041" href="reflection.arguments.html#1467" class="InductiveConstructor">cons-Modality-Argument-Agda</a>
        <a id="3077" class="Symbol">(</a> <a id="3079" href="reflection.arguments.html#1140" class="InductiveConstructor">relevant-Relevance-Argument-Agda</a><a id="3111" class="Symbol">)</a>
        <a id="3121" class="Symbol">(</a> <a id="3123" href="reflection.arguments.html#1365" class="InductiveConstructor">omega-Quantity-Argument-Agda</a><a id="3151" class="Symbol">)))</a>
    <a id="3159" class="Symbol">(</a> <a id="3161" href="reflection.arguments.html#3161" class="Bound">t</a><a id="3162" class="Symbol">)</a>

<a id="3165" class="Comment">-- hidden-Argument-Agda : {l : Level} {A : UU l} → A → Argument-Agda A</a>
<a id="3236" class="Keyword">pattern</a> <a id="hidden-Argument-Agda"></a><a id="3244" href="reflection.arguments.html#3244" class="InductiveConstructor">hidden-Argument-Agda</a> <a id="3265" href="reflection.arguments.html#3489" class="Bound">t</a> <a id="3267" class="Symbol">=</a>
  <a id="3271" href="reflection.arguments.html#1778" class="InductiveConstructor">cons-Argument-Agda</a>
    <a id="3294" class="Symbol">(</a> <a id="3296" href="reflection.arguments.html#1619" class="InductiveConstructor">cons-Info-Argument-Agda</a>
      <a id="3326" class="Symbol">(</a> <a id="3328" href="reflection.arguments.html#969" class="InductiveConstructor">hidden-Visibility-Argument-Agda</a><a id="3359" class="Symbol">)</a>
      <a id="3367" class="Symbol">(</a> <a id="3369" href="reflection.arguments.html#1467" class="InductiveConstructor">cons-Modality-Argument-Agda</a>
        <a id="3405" class="Symbol">(</a> <a id="3407" href="reflection.arguments.html#1140" class="InductiveConstructor">relevant-Relevance-Argument-Agda</a><a id="3439" class="Symbol">)</a>
        <a id="3449" class="Symbol">(</a> <a id="3451" href="reflection.arguments.html#1365" class="InductiveConstructor">omega-Quantity-Argument-Agda</a><a id="3479" class="Symbol">)))</a>
    <a id="3487" class="Symbol">(</a> <a id="3489" href="reflection.arguments.html#3489" class="Bound">t</a><a id="3490" class="Symbol">)</a>
</pre>