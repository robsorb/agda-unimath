# Definitions

<pre class="Agda"><a id="24" class="Keyword">module</a> <a id="31" href="reflection.definitions.html" class="Module">reflection.definitions</a> <a id="54" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="110" class="Keyword">open</a> <a id="115" class="Keyword">import</a> <a id="122" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>

<a id="164" class="Keyword">open</a> <a id="169" class="Keyword">import</a> <a id="176" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="208" class="Keyword">open</a> <a id="213" class="Keyword">import</a> <a id="220" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="330" class="Keyword">open</a> <a id="335" class="Keyword">import</a> <a id="342" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="370" class="Keyword">open</a> <a id="375" class="Keyword">import</a> <a id="382" href="lists.lists.html" class="Module">lists.lists</a>

<a id="395" class="Keyword">open</a> <a id="400" class="Keyword">import</a> <a id="407" href="reflection.abstractions.html" class="Module">reflection.abstractions</a>
<a id="431" class="Keyword">open</a> <a id="436" class="Keyword">import</a> <a id="443" href="reflection.arguments.html" class="Module">reflection.arguments</a>
<a id="464" class="Keyword">open</a> <a id="469" class="Keyword">import</a> <a id="476" href="reflection.literals.html" class="Module">reflection.literals</a>
<a id="496" class="Keyword">open</a> <a id="501" class="Keyword">import</a> <a id="508" href="reflection.names.html" class="Module">reflection.names</a>
<a id="525" class="Keyword">open</a> <a id="530" class="Keyword">import</a> <a id="537" href="reflection.terms.html" class="Module">reflection.terms</a>
</pre>
</details>

## Idea

The `Definition-Agda` type represents a definition in Agda.

## Definition

<pre class="Agda"><a id="664" class="Keyword">data</a> <a id="Definition-Agda"></a><a id="669" href="reflection.definitions.html#669" class="Datatype">Definition-Agda</a> <a id="685" class="Symbol">:</a> <a id="687" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="690" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="696" class="Keyword">where</a>

  <a id="Definition-Agda.function-Definition-Agda"></a><a id="705" href="reflection.definitions.html#705" class="InductiveConstructor">function-Definition-Agda</a> <a id="730" class="Symbol">:</a>
    <a id="736" href="lists.lists.html#1328" class="Datatype">list</a> <a id="741" href="reflection.terms.html#910" class="Datatype">Clause-Agda</a> <a id="753" class="Symbol">→</a> <a id="755" href="reflection.definitions.html#669" class="Datatype">Definition-Agda</a>

  <a id="Definition-Agda.data-type-Definition-Agda"></a><a id="774" href="reflection.definitions.html#774" class="InductiveConstructor">data-type-Definition-Agda</a> <a id="800" class="Symbol">:</a>
    <a id="806" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="808" class="Symbol">→</a> <a id="810" href="lists.lists.html#1328" class="Datatype">list</a> <a id="815" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="825" class="Symbol">→</a> <a id="827" href="reflection.definitions.html#669" class="Datatype">Definition-Agda</a>

  <a id="Definition-Agda.record-type-Definition-Agda"></a><a id="846" href="reflection.definitions.html#846" class="InductiveConstructor">record-type-Definition-Agda</a> <a id="874" class="Symbol">:</a>
    <a id="880" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="890" class="Symbol">→</a> <a id="892" href="lists.lists.html#1328" class="Datatype">list</a> <a id="897" class="Symbol">(</a><a id="898" href="reflection.arguments.html#1726" class="Datatype">Argument-Agda</a> <a id="912" href="reflection.names.html#720" class="Postulate">Name-Agda</a><a id="921" class="Symbol">)</a> <a id="923" class="Symbol">→</a> <a id="925" href="reflection.definitions.html#669" class="Datatype">Definition-Agda</a>

  <a id="Definition-Agda.data-constructor-Definition-Agda"></a><a id="944" href="reflection.definitions.html#944" class="InductiveConstructor">data-constructor-Definition-Agda</a> <a id="977" class="Symbol">:</a>
    <a id="983" href="reflection.names.html#720" class="Postulate">Name-Agda</a> <a id="993" class="Symbol">→</a> <a id="995" href="reflection.arguments.html#1268" class="Datatype">Quantity-Argument-Agda</a> <a id="1018" class="Symbol">→</a> <a id="1020" href="reflection.definitions.html#669" class="Datatype">Definition-Agda</a>

  <a id="Definition-Agda.postulate-Definition-Agda"></a><a id="1039" href="reflection.definitions.html#1039" class="InductiveConstructor">postulate-Definition-Agda</a> <a id="1065" class="Symbol">:</a>
    <a id="1071" href="reflection.definitions.html#669" class="Datatype">Definition-Agda</a>

  <a id="Definition-Agda.primitive-function-Definition-Agda"></a><a id="1090" href="reflection.definitions.html#1090" class="InductiveConstructor">primitive-function-Definition-Agda</a> <a id="1125" class="Symbol">:</a>
    <a id="1131" href="reflection.definitions.html#669" class="Datatype">Definition-Agda</a>
</pre>
## Bindings

<pre class="Agda"><a id="1173" class="Symbol">{-#</a> <a id="1177" class="Keyword">BUILTIN</a> <a id="1185" class="Keyword">AGDADEFINITION</a> <a id="1200" href="reflection.definitions.html#669" class="Datatype">Definition-Agda</a> <a id="1216" class="Symbol">#-}</a>
<a id="1220" class="Symbol">{-#</a> <a id="1224" class="Keyword">BUILTIN</a> <a id="1232" class="Keyword">AGDADEFINITIONFUNDEF</a> <a id="1253" href="reflection.definitions.html#705" class="InductiveConstructor">function-Definition-Agda</a> <a id="1278" class="Symbol">#-}</a>
<a id="1282" class="Symbol">{-#</a> <a id="1286" class="Keyword">BUILTIN</a> <a id="1294" class="Keyword">AGDADEFINITIONDATADEF</a> <a id="1316" href="reflection.definitions.html#774" class="InductiveConstructor">data-type-Definition-Agda</a> <a id="1342" class="Symbol">#-}</a>
<a id="1346" class="Symbol">{-#</a> <a id="1350" class="Keyword">BUILTIN</a> <a id="1358" class="Keyword">AGDADEFINITIONRECORDDEF</a> <a id="1382" href="reflection.definitions.html#846" class="InductiveConstructor">record-type-Definition-Agda</a> <a id="1410" class="Symbol">#-}</a>
<a id="1414" class="Symbol">{-#</a> <a id="1418" class="Keyword">BUILTIN</a> <a id="1426" class="Keyword">AGDADEFINITIONDATACONSTRUCTOR</a> <a id="1456" href="reflection.definitions.html#944" class="InductiveConstructor">data-constructor-Definition-Agda</a> <a id="1489" class="Symbol">#-}</a>
<a id="1493" class="Symbol">{-#</a> <a id="1497" class="Keyword">BUILTIN</a> <a id="1505" class="Keyword">AGDADEFINITIONPOSTULATE</a> <a id="1529" href="reflection.definitions.html#1039" class="InductiveConstructor">postulate-Definition-Agda</a> <a id="1555" class="Symbol">#-}</a>
<a id="1559" class="Symbol">{-#</a> <a id="1563" class="Keyword">BUILTIN</a> <a id="1571" class="Keyword">AGDADEFINITIONPRIMITIVE</a> <a id="1595" href="reflection.definitions.html#1090" class="InductiveConstructor">primitive-function-Definition-Agda</a> <a id="1630" class="Symbol">#-}</a>
</pre>
## Examples

### Constructors and definitions

<pre class="Agda"><a id="1694" href="reflection.definitions.html#1694" class="Function">_</a> <a id="1696" class="Symbol">:</a> <a id="1698" class="Keyword">quoteTerm</a> <a id="1708" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="1710" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1712" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="1733" class="Symbol">(</a><a id="1734" class="Keyword">quote</a> <a id="1740" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="1741" class="Symbol">)</a> <a id="1743" href="lists.lists.html#1371" class="InductiveConstructor">nil</a>
<a id="1747" class="Symbol">_</a> <a id="1749" class="Symbol">=</a> <a id="1751" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="1757" href="reflection.definitions.html#1757" class="Function">_</a> <a id="1759" class="Symbol">:</a>
  <a id="1763" class="Keyword">quoteTerm</a> <a id="1773" class="Symbol">(</a><a id="1774" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="1781" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="1787" class="Symbol">)</a> <a id="1789" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
  <a id="1793" class="InductiveConstructor">constructor-Term-Agda</a>
    <a id="1819" class="Symbol">(</a> <a id="1821" class="Keyword">quote</a> <a id="1827" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a><a id="1833" class="Symbol">)</a>
    <a id="1839" class="Symbol">(</a> <a id="1841" href="lists.lists.html#2507" class="Function">unit-list</a>
      <a id="1857" class="Symbol">(</a> <a id="1859" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="1881" class="Symbol">(</a><a id="1882" class="InductiveConstructor">constructor-Term-Agda</a> <a id="1904" class="Symbol">(</a><a id="1905" class="Keyword">quote</a> <a id="1911" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="1917" class="Symbol">)</a> <a id="1919" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="1922" class="Symbol">)))</a>
<a id="1926" class="Symbol">_</a> <a id="1928" class="Symbol">=</a> <a id="1930" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="1936" href="reflection.definitions.html#1936" class="Function">_</a> <a id="1938" class="Symbol">:</a>
  <a id="1942" class="Symbol">{</a><a id="1943" href="reflection.definitions.html#1943" class="Bound">l</a> <a id="1945" class="Symbol">:</a> <a id="1947" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1952" class="Symbol">}</a> <a id="1954" class="Symbol">{</a><a id="1955" href="reflection.definitions.html#1955" class="Bound">A</a> <a id="1957" class="Symbol">:</a> <a id="1959" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1962" href="reflection.definitions.html#1943" class="Bound">l</a><a id="1963" class="Symbol">}</a> <a id="1965" class="Symbol">→</a>
  <a id="1969" class="Keyword">quoteTerm</a> <a id="1979" class="Symbol">(</a><a id="1980" href="foundation.propositional-truncations.html#1578" class="Function">type-trunc-Prop</a> <a id="1996" href="reflection.definitions.html#1955" class="Bound">A</a><a id="1997" class="Symbol">)</a> <a id="1999" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
  <a id="2003" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a>
    <a id="2028" class="Symbol">(</a> <a id="2030" class="Keyword">quote</a> <a id="2036" href="foundation.propositional-truncations.html#1578" class="Function">type-trunc-Prop</a><a id="2051" class="Symbol">)</a>
    <a id="2057" class="Symbol">(</a> <a id="2059" href="lists.lists.html#1386" class="InductiveConstructor">cons</a>
      <a id="2070" class="Symbol">(</a> <a id="2072" href="reflection.arguments.html#3244" class="InductiveConstructor">hidden-Argument-Agda</a> <a id="2093" class="Symbol">(</a><a id="2094" class="InductiveConstructor">variable-Term-Agda</a> <a id="2113" class="Number">1</a> <a id="2115" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="2118" class="Symbol">))</a>
      <a id="2127" class="Symbol">(</a> <a id="2129" href="lists.lists.html#2507" class="Function">unit-list</a> <a id="2139" class="Symbol">(</a><a id="2140" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="2162" class="Symbol">(</a><a id="2163" class="InductiveConstructor">variable-Term-Agda</a> <a id="2182" class="Number">0</a> <a id="2184" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="2187" class="Symbol">))))</a>
<a id="2192" class="Symbol">_</a> <a id="2194" class="Symbol">=</a> <a id="2196" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### Lambda abstractions

<pre class="Agda"><a id="2239" href="reflection.definitions.html#2239" class="Function">_</a> <a id="2241" class="Symbol">:</a>
  <a id="2245" class="Keyword">quoteTerm</a> <a id="2255" class="Symbol">(λ</a> <a id="2258" class="Symbol">(</a><a id="2259" href="reflection.definitions.html#2259" class="Bound">x</a> <a id="2261" class="Symbol">:</a> <a id="2263" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2264" class="Symbol">)</a> <a id="2266" class="Symbol">→</a> <a id="2268" href="reflection.definitions.html#2259" class="Bound">x</a><a id="2269" class="Symbol">)</a> <a id="2271" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
  <a id="2275" href="reflection.terms.html#1384" class="InductiveConstructor">lambda-Term-Agda</a> <a id="2292" href="reflection.arguments.html#907" class="InductiveConstructor">visible-Visibility-Argument-Agda</a>
    <a id="2329" class="Symbol">(</a> <a id="2331" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a> <a id="2353" class="String">&quot;x&quot;</a> <a id="2357" class="Symbol">(</a><a id="2358" class="InductiveConstructor">variable-Term-Agda</a> <a id="2377" class="Number">0</a> <a id="2379" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="2382" class="Symbol">))</a>
<a id="2385" class="Symbol">_</a> <a id="2387" class="Symbol">=</a> <a id="2389" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="2395" href="reflection.definitions.html#2395" class="Function">_</a> <a id="2397" class="Symbol">:</a>
  <a id="2401" class="Keyword">quoteTerm</a> <a id="2411" class="Symbol">(λ</a> <a id="2414" class="Symbol">{</a><a id="2415" href="reflection.definitions.html#2415" class="Bound">x</a> <a id="2417" class="Symbol">:</a> <a id="2419" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2420" class="Symbol">}</a> <a id="2422" class="Symbol">(</a><a id="2423" href="reflection.definitions.html#2423" class="Bound">y</a> <a id="2425" class="Symbol">:</a> <a id="2427" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2428" class="Symbol">)</a> <a id="2430" class="Symbol">→</a> <a id="2432" href="reflection.definitions.html#2415" class="Bound">x</a><a id="2433" class="Symbol">)</a> <a id="2435" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
  <a id="2439" href="reflection.terms.html#1384" class="InductiveConstructor">lambda-Term-Agda</a> <a id="2456" href="reflection.arguments.html#969" class="InductiveConstructor">hidden-Visibility-Argument-Agda</a>
    <a id="2492" class="Symbol">(</a> <a id="2494" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a>
      <a id="2522" class="Symbol">(</a> <a id="2524" class="String">&quot;x&quot;</a><a id="2527" class="Symbol">)</a>
      <a id="2535" class="Symbol">(</a> <a id="2537" href="reflection.terms.html#1384" class="InductiveConstructor">lambda-Term-Agda</a> <a id="2554" href="reflection.arguments.html#907" class="InductiveConstructor">visible-Visibility-Argument-Agda</a>
        <a id="2595" class="Symbol">(</a> <a id="2597" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a> <a id="2619" class="String">&quot;y&quot;</a> <a id="2623" class="Symbol">(</a><a id="2624" class="InductiveConstructor">variable-Term-Agda</a> <a id="2643" class="Number">1</a> <a id="2645" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="2648" class="Symbol">))))</a>
<a id="2653" class="Symbol">_</a> <a id="2655" class="Symbol">=</a> <a id="2657" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="2663" class="Keyword">private</a>
  <a id="helper"></a><a id="2673" href="reflection.definitions.html#2673" class="Function">helper</a> <a id="2680" class="Symbol">:</a> <a id="2682" class="Symbol">(</a><a id="2683" href="reflection.definitions.html#2683" class="Bound">A</a> <a id="2685" class="Symbol">:</a> <a id="2687" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2690" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="2695" class="Symbol">)</a> <a id="2697" class="Symbol">→</a> <a id="2699" href="reflection.definitions.html#2683" class="Bound">A</a> <a id="2701" class="Symbol">→</a> <a id="2703" href="reflection.definitions.html#2683" class="Bound">A</a>
  <a id="2707" href="reflection.definitions.html#2673" class="Function">helper</a> <a id="2714" href="reflection.definitions.html#2714" class="Bound">A</a> <a id="2716" href="reflection.definitions.html#2716" class="Bound">x</a> <a id="2718" class="Symbol">=</a> <a id="2720" href="reflection.definitions.html#2716" class="Bound">x</a>

  <a id="2725" href="reflection.definitions.html#2725" class="Function">_</a> <a id="2727" class="Symbol">:</a>
    <a id="2733" class="Keyword">quoteTerm</a> <a id="2743" class="Symbol">(</a><a id="2744" href="reflection.definitions.html#2673" class="Function">helper</a> <a id="2751" class="Symbol">(</a><a id="2752" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="2754" class="Symbol">→</a> <a id="2756" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="2757" class="Symbol">)</a> <a id="2759" class="Symbol">(λ</a> <a id="2762" class="Symbol">{</a> <a id="2764" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="2771" class="Symbol">→</a> <a id="2773" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a> <a id="2780" class="Symbol">;</a> <a id="2782" class="Symbol">(</a><a id="2783" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a> <a id="2790" href="reflection.definitions.html#2790" class="Bound">x</a><a id="2791" class="Symbol">)</a> <a id="2793" class="Symbol">→</a> <a id="2795" href="reflection.definitions.html#2790" class="Bound">x</a><a id="2796" class="Symbol">}))</a> <a id="2800" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="2806" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a>
      <a id="2833" class="Symbol">(</a> <a id="2835" class="Keyword">quote</a> <a id="2841" href="reflection.definitions.html#2673" class="Function">helper</a><a id="2847" class="Symbol">)</a>
      <a id="2855" class="Symbol">(</a> <a id="2857" href="lists.lists.html#1386" class="InductiveConstructor">cons</a>
        <a id="2870" class="Comment">-- ℕ → ℕ</a>
        <a id="2887" class="Symbol">(</a> <a id="2889" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a>
          <a id="2921" class="Symbol">(</a> <a id="2923" href="reflection.terms.html#1585" class="InductiveConstructor">dependent-product-Term-Agda</a>
            <a id="2963" class="Symbol">(</a> <a id="2965" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="2987" class="Symbol">(</a><a id="2988" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="3009" class="Symbol">(</a><a id="3010" class="Keyword">quote</a> <a id="3016" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="3017" class="Symbol">)</a> <a id="3019" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="3022" class="Symbol">))</a>
            <a id="3037" class="Symbol">(</a> <a id="3039" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a> <a id="3061" class="String">&quot;_&quot;</a> <a id="3065" class="Symbol">(</a><a id="3066" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="3087" class="Symbol">(</a><a id="3088" class="Keyword">quote</a> <a id="3094" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="3095" class="Symbol">)</a> <a id="3097" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="3100" class="Symbol">))))</a>
        <a id="3113" class="Symbol">(</a> <a id="3115" href="lists.lists.html#2507" class="Function">unit-list</a>
          <a id="3135" class="Comment">-- The pattern matching lambda</a>
          <a id="3176" class="Symbol">(</a> <a id="3178" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a>
            <a id="3212" class="Symbol">(</a> <a id="3214" href="reflection.terms.html#1475" class="InductiveConstructor">pattern-lambda-Term-Agda</a>
              <a id="3253" class="Symbol">(</a> <a id="3255" href="lists.lists.html#1386" class="InductiveConstructor">cons</a>
                <a id="3276" class="Comment">-- zero-ℕ clause-Clause-Agda</a>
                <a id="3321" class="Symbol">(</a> <a id="3323" href="reflection.terms.html#2961" class="InductiveConstructor">clause-Clause-Agda</a>
                  <a id="3360" class="Comment">-- No telescope</a>
                  <a id="3394" class="Symbol">(</a> <a id="3396" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="3399" class="Symbol">)</a>
                  <a id="3419" class="Comment">-- Left side of the first lambda case</a>
                  <a id="3475" class="Symbol">(</a> <a id="3477" href="lists.lists.html#2507" class="Function">unit-list</a>
                    <a id="3507" class="Symbol">(</a> <a id="3509" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a>
                      <a id="3553" class="Symbol">(</a> <a id="3555" class="InductiveConstructor">constructor-Term-Agda</a> <a id="3577" class="Symbol">(</a><a id="3578" class="Keyword">quote</a> <a id="3584" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="3590" class="Symbol">)</a> <a id="3592" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="3595" class="Symbol">)))</a>
                  <a id="3617" class="Comment">-- Right side of the first lambda case</a>
                  <a id="3674" class="Symbol">(</a> <a id="3676" class="InductiveConstructor">constructor-Term-Agda</a> <a id="3698" class="Symbol">(</a><a id="3699" class="Keyword">quote</a> <a id="3705" href="elementary-number-theory.natural-numbers.html#846" class="InductiveConstructor">zero-ℕ</a><a id="3711" class="Symbol">)</a> <a id="3713" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="3716" class="Symbol">))</a>
                <a id="3735" class="Symbol">(</a> <a id="3737" href="lists.lists.html#2507" class="Function">unit-list</a>
                  <a id="3765" class="Comment">-- succ-ℕ clause-Clause-Agda</a>
                  <a id="3812" class="Symbol">(</a> <a id="3814" href="reflection.terms.html#2961" class="InductiveConstructor">clause-Clause-Agda</a>
                    <a id="3853" class="Comment">-- Telescope-Agda matching the &quot;x&quot;</a>
                    <a id="3908" class="Symbol">(</a> <a id="3910" href="lists.lists.html#2507" class="Function">unit-list</a>
                      <a id="3942" class="Symbol">(</a> <a id="3944" class="String">&quot;x&quot;</a> <a id="3948" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
                        <a id="3974" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a>
                          <a id="4022" class="Symbol">(</a> <a id="4024" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="4045" class="Symbol">(</a><a id="4046" class="Keyword">quote</a> <a id="4052" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="4053" class="Symbol">)</a> <a id="4055" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="4058" class="Symbol">)))</a>
                    <a id="4082" class="Comment">-- Left side of the second lambda case</a>
                    <a id="4141" class="Symbol">(</a> <a id="4143" href="lists.lists.html#2507" class="Function">unit-list</a>
                      <a id="4175" class="Symbol">(</a> <a id="4177" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a>
                        <a id="4223" class="Symbol">(</a> <a id="4225" class="InductiveConstructor">constructor-Term-Agda</a>
                          <a id="4273" class="Symbol">(</a> <a id="4275" class="Keyword">quote</a> <a id="4281" href="elementary-number-theory.natural-numbers.html#859" class="InductiveConstructor">succ-ℕ</a><a id="4287" class="Symbol">)</a>
                          <a id="4315" class="Symbol">(</a> <a id="4317" href="lists.lists.html#2507" class="Function">unit-list</a>
                            <a id="4355" class="Symbol">(</a> <a id="4357" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="4379" class="Symbol">(</a><a id="4380" class="InductiveConstructor">variable-Term-Agda</a> <a id="4399" class="Number">0</a><a id="4400" class="Symbol">))))))</a>
                    <a id="4427" class="Comment">-- Right side of the second lambda case</a>
                    <a id="4487" class="Symbol">(</a> <a id="4489" class="InductiveConstructor">variable-Term-Agda</a> <a id="4508" class="Number">0</a> <a id="4510" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="4513" class="Symbol">))))</a>
              <a id="4532" class="Symbol">(</a> <a id="4534" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="4537" class="Symbol">)))))</a>
  <a id="4545" class="Symbol">_</a> <a id="4547" class="Symbol">=</a> <a id="4549" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="4557" href="reflection.definitions.html#4557" class="Function">_</a> <a id="4559" class="Symbol">:</a>
    <a id="4565" class="Keyword">quoteTerm</a> <a id="4575" class="Symbol">(</a><a id="4576" href="reflection.definitions.html#2673" class="Function">helper</a> <a id="4583" class="Symbol">(</a><a id="4584" href="foundation-core.empty-types.html#801" class="Datatype">empty</a> <a id="4590" class="Symbol">→</a> <a id="4592" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="4593" class="Symbol">)</a> <a id="4595" class="Symbol">(λ</a> <a id="4598" class="Symbol">()))</a> <a id="4603" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="4609" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a>
      <a id="4636" class="Symbol">(</a> <a id="4638" class="Keyword">quote</a> <a id="4644" href="reflection.definitions.html#2673" class="Function">helper</a><a id="4650" class="Symbol">)</a>
      <a id="4658" class="Symbol">(</a> <a id="4660" href="lists.lists.html#1386" class="InductiveConstructor">cons</a>
        <a id="4673" class="Symbol">(</a> <a id="4675" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a>
          <a id="4707" class="Symbol">(</a> <a id="4709" href="reflection.terms.html#1585" class="InductiveConstructor">dependent-product-Term-Agda</a>
            <a id="4749" class="Symbol">(</a> <a id="4751" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="4773" class="Symbol">(</a><a id="4774" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="4795" class="Symbol">(</a><a id="4796" class="Keyword">quote</a> <a id="4802" href="foundation-core.empty-types.html#801" class="Datatype">empty</a><a id="4807" class="Symbol">)</a> <a id="4809" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="4812" class="Symbol">))</a>
          <a id="4825" class="Symbol">(</a> <a id="4827" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a> <a id="4849" class="String">&quot;_&quot;</a> <a id="4853" class="Symbol">(</a><a id="4854" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="4875" class="Symbol">(</a><a id="4876" class="Keyword">quote</a> <a id="4882" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="4883" class="Symbol">)</a> <a id="4885" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="4888" class="Symbol">))))</a>
        <a id="4901" class="Symbol">(</a> <a id="4903" href="lists.lists.html#2507" class="Function">unit-list</a>
          <a id="4923" class="Symbol">(</a> <a id="4925" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a>
            <a id="4959" class="Comment">-- Lambda</a>
            <a id="4981" class="Symbol">(</a> <a id="4983" href="reflection.terms.html#1475" class="InductiveConstructor">pattern-lambda-Term-Agda</a>
              <a id="5022" class="Symbol">(</a> <a id="5024" href="lists.lists.html#2507" class="Function">unit-list</a>
                <a id="5050" class="Comment">-- Clause-Agda</a>
                <a id="5081" class="Symbol">(</a> <a id="5083" href="reflection.terms.html#3065" class="InductiveConstructor">absurd-Clause-Agda</a>
                  <a id="5120" class="Symbol">(</a> <a id="5122" href="lists.lists.html#2507" class="Function">unit-list</a>
                    <a id="5152" class="Symbol">(</a> <a id="5154" class="String">&quot;()&quot;</a> <a id="5159" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a>
                      <a id="5183" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a>
                        <a id="5229" class="Symbol">(</a> <a id="5231" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="5252" class="Symbol">(</a><a id="5253" class="Keyword">quote</a> <a id="5259" href="foundation-core.empty-types.html#801" class="Datatype">empty</a><a id="5264" class="Symbol">)</a> <a id="5266" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="5269" class="Symbol">)))</a>
                  <a id="5291" class="Symbol">(</a> <a id="5293" href="lists.lists.html#2507" class="Function">unit-list</a>
                    <a id="5323" class="Symbol">(</a> <a id="5325" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="5347" class="Symbol">(</a><a id="5348" href="reflection.terms.html#2843" class="InductiveConstructor">absurd-Pattern-Agda</a> <a id="5368" class="Number">0</a><a id="5369" class="Symbol">)))))</a>
              <a id="5389" class="Symbol">(</a> <a id="5391" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="5394" class="Symbol">)))))</a>
  <a id="5402" class="Symbol">_</a> <a id="5404" class="Symbol">=</a> <a id="5406" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### Pi terms

<pre class="Agda"><a id="5438" href="reflection.definitions.html#5438" class="Function">_</a> <a id="5440" class="Symbol">:</a> <a id="5442" class="Keyword">quoteTerm</a> <a id="5452" class="Symbol">(</a><a id="5453" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a> <a id="5455" class="Symbol">→</a> <a id="5457" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="5458" class="Symbol">)</a> <a id="5460" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="5466" href="reflection.terms.html#1585" class="InductiveConstructor">dependent-product-Term-Agda</a>
      <a id="5500" class="Symbol">(</a> <a id="5502" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="5524" class="Symbol">(</a><a id="5525" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="5546" class="Symbol">(</a><a id="5547" class="Keyword">quote</a> <a id="5553" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="5554" class="Symbol">)</a> <a id="5556" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="5559" class="Symbol">))</a>
      <a id="5568" class="Symbol">(</a> <a id="5570" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a> <a id="5592" class="String">&quot;_&quot;</a> <a id="5596" class="Symbol">(</a><a id="5597" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="5618" class="Symbol">(</a><a id="5619" class="Keyword">quote</a> <a id="5625" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="5626" class="Symbol">)</a> <a id="5628" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="5631" class="Symbol">))</a>
<a id="5634" class="Symbol">_</a> <a id="5636" class="Symbol">=</a> <a id="5638" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="5644" href="reflection.definitions.html#5644" class="Function">_</a> <a id="5646" class="Symbol">:</a> <a id="5648" class="Keyword">quoteTerm</a> <a id="5658" class="Symbol">((</a><a id="5660" href="reflection.definitions.html#5660" class="Bound">x</a> <a id="5662" class="Symbol">:</a> <a id="5664" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="5665" class="Symbol">)</a> <a id="5667" class="Symbol">→</a> <a id="5669" href="elementary-number-theory.natural-numbers.html#1299" class="Function">is-zero-ℕ</a> <a id="5679" href="reflection.definitions.html#5660" class="Bound">x</a><a id="5680" class="Symbol">)</a> <a id="5682" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
    <a id="5688" href="reflection.terms.html#1585" class="InductiveConstructor">dependent-product-Term-Agda</a>
      <a id="5722" class="Symbol">(</a> <a id="5724" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="5746" class="Symbol">(</a><a id="5747" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a> <a id="5768" class="Symbol">(</a><a id="5769" class="Keyword">quote</a> <a id="5775" href="elementary-number-theory.natural-numbers.html#825" class="Datatype">ℕ</a><a id="5776" class="Symbol">)</a> <a id="5778" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="5781" class="Symbol">))</a>
      <a id="5790" class="Symbol">(</a> <a id="5792" href="reflection.abstractions.html#354" class="InductiveConstructor">cons-Abstraction-Agda</a> <a id="5814" class="String">&quot;x&quot;</a>
        <a id="5826" class="Symbol">(</a> <a id="5828" href="reflection.terms.html#1278" class="InductiveConstructor">definition-Term-Agda</a>
          <a id="5859" class="Symbol">(</a> <a id="5861" class="Keyword">quote</a> <a id="5867" href="elementary-number-theory.natural-numbers.html#1299" class="Function">is-zero-ℕ</a><a id="5876" class="Symbol">)</a>
          <a id="5888" class="Symbol">(</a> <a id="5890" href="lists.lists.html#1386" class="InductiveConstructor">cons</a>
            <a id="5907" class="Symbol">(</a> <a id="5909" href="reflection.arguments.html#2914" class="InductiveConstructor">visible-Argument-Agda</a> <a id="5931" class="Symbol">(</a><a id="5932" class="InductiveConstructor">variable-Term-Agda</a> <a id="5951" class="Number">0</a> <a id="5953" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="5956" class="Symbol">))</a>
            <a id="5971" class="Symbol">(</a> <a id="5973" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="5976" class="Symbol">))))</a>
<a id="5981" class="Symbol">_</a> <a id="5983" class="Symbol">=</a> <a id="5985" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### Universes

<pre class="Agda"><a id="6018" href="reflection.definitions.html#6018" class="Function">_</a> <a id="6020" class="Symbol">:</a>
  <a id="6024" class="Symbol">{</a><a id="6025" href="reflection.definitions.html#6025" class="Bound">l</a> <a id="6027" class="Symbol">:</a> <a id="6029" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="6034" class="Symbol">}</a> <a id="6036" class="Symbol">→</a>
  <a id="6040" class="Keyword">quoteTerm</a> <a id="6050" class="Symbol">(</a><a id="6051" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6054" href="reflection.definitions.html#6025" class="Bound">l</a><a id="6055" class="Symbol">)</a> <a id="6057" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a>
  <a id="6061" href="reflection.terms.html#1722" class="InductiveConstructor">sort-Term-Agda</a> <a id="6076" class="Symbol">(</a><a id="6077" href="reflection.terms.html#2067" class="InductiveConstructor">universe-Sort-Agda</a> <a id="6096" class="Symbol">(</a><a id="6097" class="InductiveConstructor">variable-Term-Agda</a> <a id="6116" class="Number">0</a> <a id="6118" href="lists.lists.html#1371" class="InductiveConstructor">nil</a><a id="6121" class="Symbol">))</a>
<a id="6124" class="Symbol">_</a> <a id="6126" class="Symbol">=</a> <a id="6128" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="6134" href="reflection.definitions.html#6134" class="Function">_</a> <a id="6136" class="Symbol">:</a> <a id="6138" class="Keyword">quoteTerm</a> <a id="6148" class="Symbol">(</a><a id="6149" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="6152" class="Symbol">(</a><a id="6153" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="6158" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="6163" class="Symbol">))</a> <a id="6166" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6168" href="reflection.terms.html#1722" class="InductiveConstructor">sort-Term-Agda</a> <a id="6183" class="Symbol">(</a><a id="6184" href="reflection.terms.html#2154" class="InductiveConstructor">fixed-universe-Sort-Agda</a> <a id="6209" class="Number">1</a><a id="6210" class="Symbol">)</a>
<a id="6212" class="Symbol">_</a> <a id="6214" class="Symbol">=</a> <a id="6216" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="6222" href="reflection.definitions.html#6222" class="Function">_</a> <a id="6224" class="Symbol">:</a> <a id="6226" class="Keyword">quoteTerm</a> <a id="6236" class="Symbol">(</a><a id="6237" href="Agda.Primitive.html#512" class="Primitive">UUω</a><a id="6240" class="Symbol">)</a> <a id="6242" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6244" href="reflection.terms.html#1722" class="InductiveConstructor">sort-Term-Agda</a> <a id="6259" class="Symbol">(</a><a id="6260" href="reflection.terms.html#2402" class="InductiveConstructor">fixed-large-universe-Sort-Agda</a> <a id="6291" class="Number">0</a><a id="6292" class="Symbol">)</a>
<a id="6294" class="Symbol">_</a> <a id="6296" class="Symbol">=</a> <a id="6298" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### Literals

<pre class="Agda"><a id="6330" href="reflection.definitions.html#6330" class="Function">_</a> <a id="6332" class="Symbol">:</a> <a id="6334" class="Keyword">quoteTerm</a> <a id="6344" class="Number">3</a> <a id="6346" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6348" class="InductiveConstructor">literal-Term-Agda</a> <a id="6366" class="Symbol">(</a><a id="6367" href="reflection.literals.html#623" class="InductiveConstructor">nat-Literal-Agda</a> <a id="6384" class="Number">3</a><a id="6385" class="Symbol">)</a>
<a id="6387" class="Symbol">_</a> <a id="6389" class="Symbol">=</a> <a id="6391" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

<a id="6397" href="reflection.definitions.html#6397" class="Function">_</a> <a id="6399" class="Symbol">:</a> <a id="6401" class="Keyword">quoteTerm</a> <a id="6411" class="String">&quot;hello&quot;</a> <a id="6419" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="6421" class="InductiveConstructor">literal-Term-Agda</a> <a id="6439" class="Symbol">(</a><a id="6440" href="reflection.literals.html#793" class="InductiveConstructor">string-Literal-Agda</a> <a id="6460" class="String">&quot;hello&quot;</a><a id="6467" class="Symbol">)</a>
<a id="6469" class="Symbol">_</a> <a id="6471" class="Symbol">=</a> <a id="6473" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>